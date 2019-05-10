zeroAxialVector = (n) -> transpose matrix { toList(n:0) }
standardAxialVector = (i, n) -> transpose matrix { toList( splice( (i:0, 1, n-i-1:0) ) ) }

JordanTable = n -> hashTable {
    {1,1} => set {1}, {1,0} => set {}, {1,n} => set {n},
    {0,1} => set {}, {0,0} => set {0}, {0,n} => set {n},
    {n,1} => set {n}, {n,0} => set {n}, {n,n} => set {1,0}
}

MonsterTable = (a,b) -> hashTable {
    {1,1} => set {1}, {1,0} => set {}, {1,a} => set {a}, {1,b} => set {b},
    {0,1} => set {}, {0,0} => set {0}, {0,a} => set {a}, {0,b} => set {b},
    {a,1} => set {a}, {a,0} => set {a}, {a,a} => set {1,0}, {a,b} => set {b},
    {b,1} => set {b}, {b,0} => set {b}, {b,a} => set {b}, {b,b} => set {1, 0, a}
}

dihedralAlgebraSetup = { field => QQ, primitive => true } >> opts -> (evals, tbl) -> (
    n := #evals;
    -- Set up algebra hash table
    algebra := new MutableHashTable;
    algebra.evals = evals;
    algebra.tbl = tbl;
    algebra.field = opts.field;
    algebra.primitive = opts.primitive;
    algebra.span = {0,1} | apply(toList(1..n-1), x -> {0,x});
    -- Add products as list of lists
    algebra.products = new MutableList from {};
    for i to n - 1 do (
        algebra.products#i = new MutableList from {};
        for j to n - 1 do algebra.products#i#j = false;
        );
    for i to 1 do algebra.products#i#i = standardAxialVector(i, n + 1);
    for i in 1..n-1 do algebra.products#0#i = standardAxialVector(i + 1, n + 1);
    for i in 1..n-1 do algebra.products#i#0 = standardAxialVector(i + 1, n + 1);
    -- Add first eigenvectors
    algebra.evecs = new MutableHashTable;
    for ev in delete( set({}), unique(values(tbl))) do (
        algebra.evecs#ev = zeroAxialVector(n + 1);
    --for ev in apply(subsets evals, set) do (
    --    if #ev =!= 0 and #ev =!= n then algebra.evecs#ev = zeroAxialVector(n + 1);
        );
    evecs := findFirstEigenvectors(evals, algebra.field);
    for i to n - 1 do algebra.evecs#(set {evals#i}) = matrix evecs_{i};
    -- If we assume primitivity then change the field to a polynomial ring
    if algebra.primitive = true then (
        changeRingOfAlgebra(algebra, algebra.field[symbol x, symbol y]);
        vec := algebra.evecs#(set {1}) - x*sub(standardAxialVector(0,n + 1), ring(x));
        quotientNullVec(algebra, vec);
        n = #algebra.span;
        algebra.evecs#(set {1}) = sub(standardAxialVector(0, n), algebra.field);
        )
    else algebra.evecs#(set {1}) = algebra.evecs#(set {1})|standardAxialVector(0, n + 1);
    for s in unique(values(tbl)) do (
        if #(toList s) > 1 then (
            for ev in (toList s) do (
                algebra.evecs#s = algebra.evecs#s|algebra.evecs#(set {ev});
                algebra.evecs#s = groebnerBasis algebra.evecs#s;
                );
            );
        );
    algebra.polynomials = {};
    performFlip algebra;
    algebra
    )

fusionRule = (set0, set1, tbl) -> (
    rule := {};
    for ev0 in toList(set0) do (
        for ev1 in toList(set1) do (
            if #tbl#({ev0, ev1}) > 0 then (
                rule = join(rule, toList tbl#({ev0, ev1}));
                );
            );
        );
    set rule
    )

fusion = {expand => true} >> opts -> algebra -> (
    algebra.temp = copy algebra.evecs;
    n := #(keys algebra.evecs);
    for i to n - 1  do (
        set0 := (keys algebra.evecs)#i;
        for j in (i .. n - 1) do (
            set1 := (keys algebra.evecs)#j;
            rule := fusionRule(set0, set1, algebra.tbl);
            if rule =!= set(algebra.evals) then (
                for i to numgens source algebra.evecs#set0 - 1 do (
                    for j to numgens source algebra.evecs#set1 - 1 do (
                        if i < numgens source algebra.evecs#set0 and j < numgens source algebra.evecs#set1 then (
                            u := (algebra.evecs#set0)_{i};
                            v := (algebra.evecs#set1)_{j};
                            unknowns := {};
                            prod := axialSeparateProduct(u, v, unknowns, algebra.products);
                            unknowns = prod.l;
                            if opts.expand == true then (
                                for k to #unknowns - 1 do (
                                    x := unknowns#k;
                                    algebra.span = append(algebra.span, x);
                                    expandAlgebra algebra;
                                    n := #algebra.span;
                                    algebra.products#(x#0)#(x#1) = sub(standardAxialVector(n-1, n), algebra.field);
                                    algebra.products#(x#1)#(x#0) = sub(standardAxialVector(n-1, n), algebra.field);
                                    prod.vec = prod.vec || matrix({{0}});
                                    prod.vec = prod.vec - algebra.products#(x#1)#(x#0)*(prod.mat_(k,0));
                                    );
                                );
                            if opts.expand == true or all(entries prod.mat, x -> x#0 == 0) then (
                                if rule === set {} then quotientNullVec(algebra, prod.vec)
                                else (
                                    for s in unique values algebra.tbl do(
                                        if isSubset(rule, s) then (
                                            algebra.temp#s = algebra.temp#s | prod.vec;
                                            );
                                        );
                                    );
                                );
                            );
                        );
                    );
                );
            );
        );
        for ev in keys algebra.temp do algebra.evecs#ev = mingens(image algebra.temp#ev);
        remove(algebra, temp);
        performFlip algebra;
        -- Implement intersect algorithm?
    )

expandAlgebra = algebra -> (
    n := #algebra.span;
    k := #algebra.products;
    for i to k - 1 do algebra.products#i = join(algebra.products#i , new MutableList from (n-k):false) ;
    algebra.products = join(algebra.products, new MutableList from (n-k):(new MutableList from (n:false)));
    for i to n - 1 do (
        for j to n - 1 do (
            if algebra.products#i#j =!= false then (
                algebra.products#i#j = algebra.products#i#j || matrix({{0}})
                );
            );
        );
    for ev in keys algebra.evecs do (
        d := numgens source algebra.evecs#ev;
        algebra.evecs#ev = algebra.evecs#ev || matrix( {toList(d:0)});
        );
    if algebra#?temp then (
        for ev in keys algebra.temp do (
            d := numgens source algebra.temp#ev;
            algebra.temp#ev = algebra.temp#ev || matrix( {toList(d:0)});
            );
        );
    )

findNewEigenvectors = algebra -> (
    a := sub(standardAxialVector(0, #algebra.span), algebra.field);
    for s in keys algebra.evecs do (
        for i to numgens source algebra.evecs#s - 1 do (
            if i < numgens source algebra.evecs#s then (
                u := algebra.evecs#s_{i};
                prod := axialProduct(a, u, algebra.products);
                if prod =!= false then
                    if #s == 1 then quotientNullVec(algebra, prod - u*(toList s)#0)
                    else (
                        for ev in toList s do (
                            d := s - set {ev};
                            if algebra.evecs#?d then algebra.evecs#d = algebra.evecs#d | (prod - ev*u); -- maybe want to expand evecs to power set of evals
                            );
                        );
                    );
                );
            );
    for s in keys algebra.evecs do algebra.evecs#s = mingens image algebra.evecs#s
    )

findNullVectors = algebra -> (
    -- intersect distinct eigenspaces
    algebra.nullspace = sub(zeroAxialVector (#algebra.span), algebra.field);
    test := {};
    n := #(keys algebra.evecs);
    for i to n - 1 do (
        ev0 := (keys algebra.evecs)#i;
        for j in (i + 1 .. n - 1) do (
            ev1 := (keys algebra.evecs)#j;
            if ev0 * ev1 === set {} then (
                algebra.nullspace = mingens intersect(image algebra.evecs#ev0, image algebra.evecs#ev1);
                test = append(test, numgens image algebra.nullspace);
                for i in reverse toList(0 .. numgens image algebra.nullspace - 1) do (
                    quotientNullVec(algebra, algebra.nullspace_{i});
                    );
                );
            );
        );
    if sum test > 0 then print test;
    --algebra.nullspace = mingens image algebra.nullspace;
    --if numgens image algebra.nullspace > 0 then print test;
    -- for i in reverse toList(0..numgens image algebra.nullspace - 1) do (
    --    quotientNullVec(algebra, algebra.nullspace_{i});
    --    );
    -- while true do ( -- quite ugly
    --    k := findNullIndex algebra.nullspace;
    --    if k === false then break;
    --    i := quotientNullVec(algebra, algebra.nullspace_{k});
    --    if i === false then (
    --        algebra.nullspace = algebra.nullspace_(toList( drop(0..numgens image algebra.nullspace - 1, {k,k})));
    --        );
    --    );
    remove(algebra, nullspace);
    quotientNullPolynomials algebra;
    performFlip algebra;
    )

findNullIndex = mat -> (
    n := numgens image mat;
    if n == 0 then return false;
    ind := apply( toList (0..n-1), i -> positions( entries mat_{i}, x -> x#0 != 0 ) );
    ind = apply( ind, x -> if x == {} then return 0 else return last x);
    if max ind == 0 then return false;
    return position( ind, i -> i == max ind );
    )

findFirstEigenvectors = (evals, field) -> (
    n := #evals;
    mat := toList apply( 0..n-1, i -> toList apply( 0..n-1, j -> (evals#i)^j ));
    mat = matrix(field, mat);
    mat = inverse mat;
    z := transpose zeroAxialVector n;
    z || mat
    )

changeRingOfAlgebra = (algebra, r) -> (
    algebra.field = r;
    n := #algebra.products;
    -- Change the algebra products
    for i to n-1 do (
        for j to n-1 do (
            if algebra.products#i#j =!= false then (
                algebra.products#i#j = sub(algebra.products#i#j, r);
            );
        );
    );
    -- Change the eigenvectors
    for ev in keys algebra.evecs do algebra.evecs#ev = sub(algebra.evecs#ev, r);
    )

reduceSpanningVec = (vec, k) -> (
    if member (vec, {0,1}) then return vec;
    if vec#0 > k and vec#1 > k then return {vec#0 - 1, vec#1 - 1};
    if vec#0 > k then return {vec#0 - 1, vec#1};
    if vec#1 > k then return {vec#0, vec#1 -1};
    vec
    )

-- ugly but here we go
-- this is a hacky fix to get around the fact that M2 can't calculate
-- gcd's over iterated polynomials

GCD = (vec, algebra) -> (
    r := coefficientRing algebra.field;
    if #gens(r) == 0 then return gcd vec;
    s := coefficientRing r;
    coeffs := apply(vec, p -> flatten( entries((coefficients p)#1)));
    coeffs = apply(coeffs, x -> apply(x, y -> sub(y, r)));
    denoms = apply(coeffs, x -> apply(x, denominator));
    d := sub(lcm(flatten denoms), algebra.field);
    coeffs = flatten(entries((matrix apply(vec, x -> {x}))*d));
    R := s[ join(gens r, gens algebra.field) ];
    coeffs = apply(coeffs, x -> sub(x, R));
    sub(gcd coeffs, algebra.field)
    )


quotientNullVec = (algebra, vec) -> (
    old := #algebra.span;
    if vec == 0 then return;
    vec = entries vec;
    nonzero := positions(vec, x -> x#0 != 0);
    if #nonzero == 0 then return;
    d := GCD(flatten vec, algebra);
    if #support d == 1 then error "polynomial";
    if #support d > 0 then (
        algebra.polynomials = append(algebra.polynomials, d);
        quotientNullPolynomials algebra;
        return;
        );
    d = sub(d, coefficientRing algebra.field);
    if d != 1 then vec = apply(vec, x -> {x#0*sub(1/d, algebra.field)});
    if all(nonzero, i -> #support vec#i#0 > 0) then ( -- all poly mat
        print "All poly mat";
        return false;
        );
    k := last select(nonzero, i -> #support vec#i#0 == 0);
    print k;
    if k == 0 or k == 1 then error "Is the algebra zero?";
    vec = sub(matrix vec, algebra.field);
    entry := sub(vec_(k,0), coefficientRing algebra.field);
    n := #algebra.span;
    prod := standardAxialVector(k,n) - vec*(sub(1/entry, algebra.field));
    vec = vec*sub(1/entry, algebra.field);
    for i in k+1 .. n-1 do (
        if i < #algebra.span then (
            x := algebra.span#i;
            if member(k,x) then (
                if x#0 == k then u := prod
                else u = standardAxialVector(x#0,n);
                if x#1 == k then v := prod
                else v = standardAxialVector(x#1,n);
                newProd := axialProduct(u, v, algebra.products);
                --if newProd === false then error "Cannot find product";
                if newProd === false then print("Cannot quotient vector ", k); return;
                quotientNullVec(algebra, standardAxialVector(i,n) - newProd);
                n = #algebra.span;
                vec = vec^(toList (0..n-1));
                prod = prod^(toList (0..n-1));
                );
            );
        );
    algebra.span = apply(algebra.span, x -> reduceSpanningVec(x, k));

    reduction := toList drop(0..n - 1,{k,k});
    algebra.products = drop(algebra.products,{k,k});
    for i to #algebra.products - 1 do (
        algebra.products#i = drop(algebra.products#i,{k,k});
        for j to #algebra.products#i - 1 do (
            if algebra.products#i#j =!= false then (
                algebra.products#i#j = (reduce(algebra.products#i#j, vec, k))^reduction;
                );
            );
        );
    for ev in keys algebra.evecs do (
        algebra.evecs#ev = (reduce(algebra.evecs#ev, vec, k))^reduction;
        algebra.evecs#ev = mingens (image algebra.evecs#ev);
        );
    if algebra#?temp then (
        for ev in keys algebra.temp do (
            algebra.temp#ev = (reduce(algebra.temp#ev, vec, k))^reduction;
            algebra.temp#ev = mingens( image algebra.temp#ev);
            );
        );
    if algebra#?nullspace then (
        algebra.nullspace = (reduce(algebra.nullspace, vec, k))^reduction;
        );
    algebra.span = drop(algebra.span, {k,k});
    print({old, #algebra.span})
    )

quotientNullPolynomials = algebra -> (
    if #algebra.polynomials == 0 then return;
    I := ideal algebra.polynomials;
    for i to #algebra.products - 1 do (
        for j to #algebra.products - 1 do (
            if algebra.products#i#j =!= false then (
                algebra.products#i#j = algebra.products#i#j % I;
                );
            );
        );
    for ev in keys algebra.evecs do (
        algebra.evecs#ev = algebra.evecs#ev % I;
        );
    if algebra#?temp then (
        for ev in keys algebra.temp do (
            algebra.temp#ev = algebra.temp#ev % I;
            );
        );
    if algebra#?nullspace then (
        algebra.nullspace = algebra.nullspace % I;
        );
    )

reduce = (u, v, k) -> u - v*u^{k}

-- might want to swap lhs and rhs now that we are working with columns
axialSeparateProduct = (u,  v, unknowns, products) -> (
    r := ring products#0#0;
    n := #products;
    lhs := new MutableList from (n^2:0);
    rhs := {};
    for i to numgens target u - 1 do (
        if u_(i,0) != 0 then (
            for j to numgens target v - 1 do (
                if v_(j,0) != 0 then (
                    if products#i#j === false then (
                        pos := position( unknowns, x -> x == sort {i,j} );
                        if pos === null then (
                            unknowns = append(unknowns, sort {i,j});
                            pos = #unknowns - 1;
                            );
                        lhs#pos = lhs#pos + u_(i,0)*v_(j,0);
                        )
                    else rhs = append( rhs, (u_(i,0)*v_(j,0))*products#i#j );
                    );
                );
            );
        );
    lhs = matrix(algebra.field, toList apply(lhs, x -> {x}));
    new MutableHashTable from {vec => -sum(rhs), mat => lhs, l => unknowns }
    )

axialProduct = (u, v, products) -> (
    l := {};
    for i to numgens target u - 1 do (
        if u_(i,0) != 0 then (
            for j to numgens target v - 1 do (
                if v_(j,0) != 0 then (
                    if products#i#j === false then return false;
                    l = append( l, (u_(i,0))*(v_(j,0))*products#i#j );
                    );
                );
            );
        );
    sum l
    )

findFlip = algebra -> (
    n := #algebra.span;
    f := {1, 0, 2};
    if n < 4 then return f;
    for i in (3..n-1) do (
        x :=  algebra.span#i;
        im := f_x;
        if member(null, im) then f = append(f, null)
        else f = append(f, position(algebra.span, y -> y === im) );
        );
    f
    )

flipVector = (vec, f, algebra) -> (
    r := ring vec;
    v := apply( entries vec, p -> sub(p#0, {r_0 => r_1, r_1 => r_0}));
    if #algebra.polynomials > 0 then (
        v = apply( v, p -> p % (ideal algebra.polynomials));
        );
    res := sub(zeroAxialVector(#v), r);
    for i to #v - 1 do (
        k := f#i;
        if k === null then (
            im := f_(algebra.span#i);
            if member(null, im) then return false;
            -- TODO this means that we cannot find the image of this vector under the flip
            -- should we add this image to the spanning set and expand the algebra?S
            if algebra.products#(im#0)#(im#1) =!= false then (
                res = res + algebra.products#(im#0)#(im#1)*(v#i)
                )
            else (
                algebra.span = append(algebra.span, sort(im));
                n := #algebra.span;
                expandAlgebra(algebra);
                algebra.products#(im#0)#(im#1) = sub(standardAxialVector(n-1, n), algebra.field);
                algebra.products#(im#1)#(im#0) = sub(standardAxialVector(n-1, n), algebra.field);
                f = findFlip algebra;
                res = res || matrix({{0}});
                res = res + sub(standardAxialVector(n - 1, n),r)*v#i;
                );
        )
        else res = res + sub(standardAxialVector(k, #algebra.span),r)*v#i;
    );
    res
    )

performFlip = algebra -> (
    n := #algebra.span;
    f := findFlip algebra;
    -- might need to be more careful with the indices if a nullspace vec occurs here
    for i to n -1 do (
        for j to n - 1 do (
            if i < #algebra.products and j < #algebra.products then (
                im := f_{i,j};
                if not member(null, im) and algebra.products#i#j =!= false then (
                    f = findFlip algebra;
                    vec := flipVector(algebra.products#i#j, f, algebra);
                    if vec =!= false then (
                        if algebra.products#(im#0)#(im#1) === false then (
                            algebra.products#(im#0)#(im#1) = vec;
                            algebra.products#(im#1)#(im#0) = vec;
                            )
                        else if vec != algebra.products#(im#0)#(im#1) then (
                            quotientNullVec(algebra, vec-algebra.products#(im#0)#(im#1));
                            );
                        );
                    );
                );
            );
        );
    )

testEvecs = algebra -> (
    a := sub(standardAxialVector(0, #algebra.span), algebra.field);
    for ev in algebra.evals do (
        for i to numgens source algebra.evecs#(set {ev}) - 1 do (
            u := algebra.evecs#(set {ev})_{i};
            v := axialProduct(a, u, algebra.products);
            if v =!= false and v - ev*u != 0 then "evecs error";
            );
        );
    )

howManyUnknowns = algebra -> (
    n := #algebra.span;
    unknowns := {};
    for i to n - 1 do (
        for j from i to n - 1 do (
            if algebra.products#i#j === false then unknowns = unknowns | {{i,j}};
            );
        );
    #unknowns
    )

mainLoop = algebra -> (
    while true do (
        n := howManyUnknowns algebra;
        findNewEigenvectors algebra;
        findNullVectors algebra;
        if howManyUnknowns algebra == n then return;
        );
    )

-- formerly in findAlgebraProducts

--pos := positions(flatten(entries(eqn.mat)), x -> x != 0);
--if #pos == 1 then (
    --x := system.unknowns#(pos#0);
    --if #support(eqn.mat_(pos#0,0)) > 0 then error "polynomial coeff";
    --y := 1/sub(eqn.mat_(pos#0,0), coefficientRing algebra.field);
    --algebra.products#(x#0)#(x#1) = eqn.vec*y;
    --algebra.products#(x#1)#(x#0) = eqn.vec*y; )
--else (
    --system.mat = system.mat | eqn.mat;
    --system.vec = system.vec | eqn.vec;
    --);
