-- build generic vectors
zeroAxialVector = (n) -> transpose matrix { toList(n:0) }
standardAxialVector = (i, n) -> transpose matrix { toList( splice( (i:0, 1, n-i-1:0) ) ) }

-- automotically construct the Jordan and Monster fusion tables
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

InfiniteFamilyTable = a -> hashTable{
    {1,1} => set {1}, {1,0} => set {}, {1,1/2} => set {1/2}, {1,3/8} => set {3/8}, {1, a} => set {a},
    {0,1} => set {}, {0,0} => set {0}, {0,1/2} => set {1/2}, {0,3/8} => set {3/8}, {0, a} => set {a},
    {1/2,1} => set {1/2}, {1/2,0} => set {1/2}, {1/2,1/2} => set {1,0}, {1/2,3/8} => set {3/8}, {1/2, a} => set {a},
    {3/8,1} => set {3/8}, {3/8,0} => set {3/8}, {3/8,1/2} => set {3/8}, {3/8,3/8} => set {1, 0, 1/2}, {3/8,a} => set {},
    {a, 1} => set {a}, {a, 0} => set {a}, {a, 1/2} => set {a}, {a, 3/8} => set {}, {a, a} => set {1, 0, 1/2}
}

dihedralAlgebraSetup = { field => QQ, primitive => true, form => true } >> opts -> (evals, tbl) -> (
    n := #evals;
    -- Set up algebra hash table
    algebra := new MutableHashTable;
    algebra.evals = evals;
    algebra.tbl = tbl;
    algebra.usefulpairs = usefulPairs(evals, tbl);
    algebra.field = opts.field;
    algebra.primitive = opts.primitive;
    algebra.polynomials = {};
    algebra.polys = false;
    --algebra.allpolynullvecs = sub( zeroAxialVector (n + 1), algebra.field );
    algebra.span = {0,1} | apply(toList(1..n-1), x -> {0,x});
    -- Add products as list of lists
    algebra.products = new MutableList from {};
    for i to n do (
        algebra.products#i = new MutableList from {};
        for j to n do algebra.products#i#j = false;
        );
    for i to 1 do algebra.products#i#i = sub(standardAxialVector(i, n + 1), algebra.field);
    for i in 1..n-1 do algebra.products#0#i = sub(standardAxialVector(i + 1, n + 1), algebra.field);
    for i in 1..n-1 do algebra.products#i#0 = sub(standardAxialVector(i + 1, n + 1), algebra.field);
    -- Add first eigenvectors
    algebra.evecs = new MutableHashTable;
    for ev in select( subsets evals, x -> #x != 0 and #x != n )/set do (
        algebra.evecs#ev = zeroAxialVector(n + 1);
        );
    evecs := findFirstEigenvectors(evals, algebra.field);
    for i to n - 1 do algebra.evecs#(set {evals#i}) = algebra.evecs#(set {evals#i}) | (matrix evecs_{i});
    -- If we assume primitivity then change the field to a polynomial ring
    if algebra.primitive then (
        changeRingOfAlgebra(algebra, algebra.field[symbol x, symbol y]);
        vec := algebra.evecs#(set {1})_{1} - x*sub(standardAxialVector(0,n + 1), ring(x));
        quotientNullspace (algebra, vec);
        n = #algebra.span;
        algebra.evecs#(set {1}) = sub(standardAxialVector(0, n), algebra.field);
        )
    else algebra.evecs#(set {1}) = algebra.evecs#(set {1})|standardAxialVector(0, n + 1);
    -- If we assume that the alg admits a form then x = y
    if opts.form and opts.primitive then (
        algebra.polynomials = {algebra.field_0 - algebra.field_1}; -- pretty but not so efficient
        quotientNullPolynomials algebra;
        );
    -- Build the full eigenspaces
    for s in keys algebra.evecs do (
        if #(toList s) > 1 then (
            for ev in (toList s) do (
                algebra.evecs#s = algebra.evecs#s|algebra.evecs#(set {ev});
                );
            );
        algebra.evecs#s = mingens image algebra.evecs#s;
        );
    --performFlip algebra;
    algebra
    )

usefulPairs = (evals, tbl) -> (
    pset := select( subsets evals, x -> #x != 0 and #x != #evals );
    evalpairs := toList((set pset)**(set pset))/toList;
    useful := {};
    for p in evalpairs do (
        rule := fusionRule(p#0, p#1, tbl);
        if #rule < #evals then (
            sets0 := select(pset, x -> isSubset(p#0, x) and x != p#0);
            sets1 := select(pset, x -> isSubset(p#1, x) and x != p#1);
            rules = apply(sets0, x -> fusionRule(x, p#1, tbl));
            rules = rules | apply(sets1, x -> fusionRule(x, p#0, tbl));
            if not member(rule, rules) then useful = append(useful, set(p/set));
            );
        );
    useful = (unique useful)/toList;
    return apply(useful, x -> if #x == 1 then {x#0, x#0} else x);
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
    if opts.expand == true then print "Performing fusion with expansion"
    else print "Performing fusion without expansion";
    r := algebra.field;
    algebra.temp = copy algebra.evecs;
    for p in algebra.usefulpairs do (
        rule := fusionRule(p#0, p#1, algebra.tbl);
            for i to numgens source algebra.evecs#(p#0) - 1 do (
                if p#0 === p#1 then start := i else start = 0;
                for j in (start .. numgens source algebra.evecs#(p#1) - 1) do (
                    if i < numgens source algebra.evecs#(p#0) and j < numgens source algebra.evecs#(p#1) then (
                        u := (algebra.evecs#(p#0))_{i};
                        v := (algebra.evecs#(p#1))_{j};
                        if opts.expand then (
                            unknowns := findUnknowns(u, v, algebra.products);
                            expandAlgebra(algebra, unknowns);
                            );
                        prod := axialProduct(u, v, algebra.products);
                        if prod =!= false and prod != 0 then recordEvec(prod, rule, algebra);
                        if algebra.polys and any(algebra.polynomials, x -> #(set(support x)*set(gens r)) == 1) then return;
                        );
                    );
                );
            );
        for ev in keys algebra.temp do algebra.evecs#ev = algebra.temp#ev;
        remove(algebra, temp);
        --performFlip algebra;
    )

recordEvec = (v, rule, algebra) -> (
    if rule === set {} then quotientNullspace (algebra, v)
    else (
        for s in keys algebra.temp do (
            if rule*s === set {} then (
                z := mingens intersect(image v, image algebra.temp#s);
                if z != 0 then (
                    quotientNullspace (algebra, z);
                    return;
                    )
                )
            else if isSubset(rule, s) then (
                algebra.temp#s = mingens image(algebra.temp#s | v);
                )
            else (
                z = mingens intersect(image v, image algebra.temp#s);
                if z != 0 then (
                    algebra.temp#(s*rule) = mingens image (algebra.temp#(s*rule) | z);
                    )
                );
            );
        );
    )

expandAlgebra = (algebra, unknowns) -> (
    if #unknowns == 0 then return;
    k := #unknowns;
    n := #algebra.span;
    for i to n - 1 do algebra.products#i = join(algebra.products#i, new MutableList from k:false) ;
    algebra.products = join(algebra.products, new MutableList from k:(new MutableList from (n+k):false));
    for i to n + k - 1 do (
        for j to n + k - 1 do (
            if algebra.products#i#j =!= false then (
                algebra.products#i#j = algebra.products#i#j || matrix(toList(k:{0}));
                );
            );
        );
    for ev in keys algebra.evecs do (
        d := numgens source algebra.evecs#ev;
        algebra.evecs#ev = algebra.evecs#ev || matrix( toList(k:toList(d:0)));
        );
    --d = numgens source algebra.allpolynullvecs;
    --algebra.allpolynullvecs = algebra.allpolynullvecs || matrix( toList(k:toList(d:0)));
    if algebra#?temp then (
        for ev in keys algebra.temp do (
            d = numgens source algebra.temp#ev;
            algebra.temp#ev = algebra.temp#ev || matrix( toList(k:toList(d:0)));
            );
        );
    if algebra#?nullspace then (
        d = numgens source algebra.nullspace;
        algebra.nullspace = algebra.nullspace || matrix( toList(k:toList(d:0)));
        );
    for i to k - 1 do (
        x := unknowns#i;
        algebra.products#(x#0)#(x#1) = sub(standardAxialVector(n + i, n + k), algebra.field);
        algebra.products#(x#1)#(x#0) = algebra.products#(x#0)#(x#1);
        );
    algebra.span = algebra.span | unknowns;
    )

findNewEigenvectors = {expand => true} >> opts -> algebra -> (
    if opts.expand then print "Finding new eigenvectors with expansion"
    else print "Finding new eigenvectors without expansion";
    a := sub(standardAxialVector(0, #algebra.span), algebra.field);
    for s in keys algebra.evecs do (
        for i to numgens source algebra.evecs#s - 1 do (
            if i < numgens source algebra.evecs#s then (
                u := algebra.evecs#s_{i};
                if opts.expand then (
                    unknowns := findUnknowns(a, u, algebra.products);
                    expandAlgebra(algebra, unknowns);
                    a = sub(standardAxialVector(0, #algebra.span), algebra.field);
                    u = algebra.evecs#s_{i};
                    );
                prod := axialProduct(a, u, algebra.products);
                if prod =!= false then
                    if #s == 1 then quotientNullspace (algebra, prod - u*(toList s)#0)
                    else (
                        for ev in toList s do (
                            d := s - set {ev};
                            if algebra.evecs#?d then algebra.evecs#d = algebra.evecs#d | (prod - ev*u); -- maybe want to expand evecs to power set of evals
                            );
                        );
                    );
                );
            );
    for s in keys algebra.evecs do algebra.evecs#s = mingens image algebra.evecs#s;
    --performFlip algebra;
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
    if algebra#?nullspace then algebra.nullspace = algebra.nullspace % I;
    --algebra.allpolynullvecs = algebra.allpolynullvecs % I;
    )

findNullVectors = algebra -> (
    while true do (
        n := howManyUnknowns algebra;
        findNewEigenvectors(algebra, expand => false);
        -- intersect distinct eigenspaces
        print "Finding null vectors";
        for ev in select(algebra.usefulpairs, x -> (x#0)*(x#1) === set {}) do (
            za := mingens intersect(image algebra.evecs#(ev#0), image algebra.evecs#(ev#1));
            quotientNullspace (algebra, za);
            );
        --performFlip algebra;
        --quotientAllPolyNullVecs algebra;
        if member(howManyUnknowns algebra, {0,n}) then break;
        );
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
    -- Change the polynomials
    algebra.polynomials = apply(algebra.polynomials, x -> sub(x, r));
    )

reduceSpanningVec = (vec, k) -> (
    if member (vec, {0,1}) then return vec;
    if vec#0 > k and vec#1 > k then return {vec#0 - 1, vec#1 - 1};
    if vec#0 > k then return {vec#0 - 1, vec#1};
    if vec#1 > k then return {vec#0, vec#1 -1};
    vec
    )

quotientNullspace = (algebra, mat) -> (
    if mat == 0 then return;
    algebra.nullspace = mat;
    n := #algebra.span;
    d := numgens image algebra.nullspace;
    --for i to n - 1 do (
    --    a := standardAxialVector(i, n);
    --    for j to d - 1 do (
    --        prod := axialProduct( a, algebra.nullspace_{j}, algebra.products );
    --        if prod =!= false then algebra.nullspace = algebra.nullspace | prod;
    --        );
    --    );
    --algebra.nullspace = mingens image algebra.nullspace;
    --d = numgens image algebra.nullspace;
    for i to d - 1 do (
        v := flipVector(algebra.nullspace_{i}, algebra);
        if v =!= false then algebra.nullspace = algebra.nullspace | v;
        );
    algebra.nullspace = mingens image algebra.nullspace;
    for j in reverse toList(0 .. numgens image algebra.nullspace - 1) do (
        quotientNullVec(algebra, algebra.nullspace_{j});
        );
    remove (algebra, nullspace);
    )

quotientNullVec = (algebra, vec) -> (
    if vec == 0 then return;
    r := algebra.field;
    vec = entries vec;
    nonzero := positions(vec, x -> x#0 != 0);
    if #nonzero == 0 then return;
    k := last nonzero;
    if algebra.primitive and #(set(support vec#k#0)*set(gens r)) > 0 then ( -- all poly mat
        if all(nonzero, i -> i < 3) then (
            polys := unique select(flatten vec, p -> #(set(support vec#k#0)*set(gens r)) > 0);
            polys = flatten entries groebnerBasis ideal (algebra.polynomials | polys);
            if #polys != #algebra.polynomials then (
                print vec_{0,1,2};
                algebra.polynomials = polys;
                quotientNullPolynomials algebra;
                );
            return false;
            )
        else return false;
        );
    --if algebra.primitive then k := last select(nonzero, i -> #support vec#i#0 == 0)
    --else k = last nonzero;
    if k == 0 or k == 1 then ( -- algebra is zero
        algebra.span = {};
        algebra.products = new MutableList from {};
        algebra.nullspace = matrix 0;
        for ev in keys algebra.evecs do algebra.evecs#ev = matrix 0;
        return;
        );
    vec = sub(matrix vec, algebra.field);
    if algebra.primitive then entry := sub(vec_(k,0), coefficientRing algebra.field)
    else entry = vec_(k,0);
    n := #algebra.span;
    prod := standardAxialVector(k,n) - vec*(sub(1/entry, algebra.field));
    vec = vec*sub(1/entry, algebra.field);
    z := zeroAxialVector n;
    for i in k+1 .. n-1 do (
        if i < #algebra.span then (
            x := algebra.span#i;
            if member(k,x) then (
                if x#0 == k then u := prod
                else u = standardAxialVector(x#0,n);
                if x#1 == k then v := prod
                else v = standardAxialVector(x#1,n);
                unknowns := findUnknowns(u, v, algebra.products);
                --if #unknowns > 0 then print ("Expanding in quotient func", i, n);
                --if #unknowns > 0 then print unknowns;
                if #unknowns > 0 then return false;
                --expandAlgebra(algebra, unknowns);
                newProd := axialProduct(u, v, algebra.products);
                if newProd_(i, 0) == 1 then return false; -- cannot find quotient
                --n = #algebra.span;
                --if algebra#?one and #algebra.span == 9 then error "";
                --quotientNullVec(algebra, standardAxialVector(i,n) - newProd);
                z = z | (standardAxialVector(i,n) - newProd);
                );
            );
        );
    z = mingens image z;
    if numgens image z > 0 then (
        z = mingens image z;
        d := numgens image z;
        for i in reverse (0 .. d-1) do (
            print i;
            n = #algebra.span;
            quotientNullVec(algebra, z_{i}^(toList(0..n-1)));
            );
        );
    n = #algebra.span;
    if k > n - 1 then return;
    d = n - numgens target vec;
    if d < 0 then vec = vec^(toList (0..n-1))
    else if d > 0 then vec = vec || matrix(toList(d:{0}));
    -- Now we quotient the algebra by this null vec
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
    --if algebra#?allpolynullvecs then (
    --    algebra.allpolynullvecs = (reduce(algebra.allpolynullvecs, vec, k))^reduction;
    --    );
    if algebra#?nullspace then (
        algebra.nullspace = (reduce(algebra.nullspace, vec, k))^reduction;
        );
    algebra.span = drop(algebra.span, {k,k});
    n = #algebra.span;
    --if any(algebra.span, x -> not member(x, {0,1}) and algebra.products#(x#0)#(x#1) === false) then error "another problem";
    if any(toList (2..n-1), i -> member(i, algebra.span#i)) then error "here";
    )

quotientAllPolyNullVecs = algebra -> (
    if not algebra.primitive then return;
    algebra.allpolynullvecs = mingens image algebra.allpolynullvecs;
    n := numgens image algebra.allpolynullvecs;
    for i in reverse toList(0..n - 1) do (
        vec := flatten entries algebra.allpolynullvecs_{i};
        if any(vec, x -> x !=0 and #support x == 0 ) then (
            quotientNullVec (algebra, algebra.allpolynullvecs_{i});
            );
        );
    )

reduce = (u, v, k) -> u - v*u^{k}

reduceMat = (u, mat) -> (
    r := ring u;
    n := numgens image mat - 1;
    for i to n do (
        v := mat_{i};
        vec := entries v;
        k := last positions(vec, x -> x#0 != 0);
        entry := vec#k#0;
        v = v*sub(1/entry, r);
        u = mingens image reduce(u, v, k);
        );
    return u;
    )

findUnknowns = (u, v, products) -> (
    unknowns := {};
    n := numgens target u - 1;
    m := numgens target v - 1;
    for i to n do (
        if u_(i,0) != 0 then (
            for j to m do (
                if v_(j,0) != 0 then (
                    if products#i#j === false then (
                        unknowns = append(unknowns, sort {i,j});
                        );
                    );
                );
            );
        );
    return unique unknowns;
    )

axialProduct = (u, v, products) -> (
    l := {};
    n := numgens (target u) - 1;
    m := numgens (target v) - 1;
    for i in reverse(toList(0..n)) do (
        if u_(i,0) != 0 then (
            for j in reverse(toList(0..m)) do (
                if v_(j,0) != 0 then (
                    if products#i#j === false then return false;
                    l = append(l, (u_(i,0))*(v_(j,0))*products#i#j);
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

-- this is elegant but not convinced it is correct
imageFlip = (i, f, algebra) -> (
    n := #algebra.span;
    if f_i =!= null then return sub(standardAxialVector(f_i, n), algebra.field);
    x := algebra.span#i;
    im0 := f_(x#0);
    im1 := f_(x#1);
    if im1 =!= null and im0 =!= null then (
        if algebra.products#im0#im1 === false then (
            expandAlgebra(algebra, {{im0, im1}});
            );
        return algebra.products#im0#im1;
        );
    if im0 === null then im0 = imageFlip(x#0, f, algebra)
    else im0 =  sub(standardAxialVector(im0, n), algebra.field);
    if im0 === false then return false;
    if im1 === null then im1 = imageFlip(x#1, f, algebra)
    else im1 =  sub(standardAxialVector(im1, n), algebra.field);
    if im1 === false then return false;
    unknowns := findUnknowns (im0, im1, algebra.products);
    expandAlgebra (algebra, unknowns);
    return axialProduct(im0, im1, algebra.products);
    )

flipVector = (vec, algebra) -> (
    f := findFlip algebra;
    r := ring vec;
    v := flatten entries vec;
    if algebra.primitive then v = apply( v, p -> sub(p, {r_0 => r_1, r_1 => r_0}));
    if #algebra.polynomials > 0 then (
        v = apply( v, p -> p % (ideal algebra.polynomials));
        );
    res := sub(zeroAxialVector(#v), r);
    for i in positions(v, x -> x !=0 ) do (
        im := imageFlip(i, f, algebra);
        if im === false then return false;
        if #algebra.span != numgens target res then (
            res = res || matrix( toList ((#algebra.span - numgens target res):{0}) );
            );
        res = res + im*v#i;
        );
    res
    )

performFlip = algebra -> (
    n := #algebra.span;
    -- might need to be more careful with the indices if a nullspace vec occurs here
    for i to n -1 do (
        for j to n - 1 do (
            if i < #algebra.products and j < #algebra.products then (
                f := findFlip algebra;
                im := f_{i,j};
                --if not member(null, im) and algebra.products#i#j =!= false then (
                if algebra.products#i#j =!= false then (
                    if member(null, im) then error "Can't perform flip";
                    vec := flipVector(algebra.products#i#j, algebra);
                    if vec =!= false then (
                        if algebra.products#(im#0)#(im#1) === false then (
                            algebra.products#(im#0)#(im#1) = vec;
                            algebra.products#(im#1)#(im#0) = vec;
                            )
                        else if vec != algebra.products#(im#0)#(im#1) then (
                            quotientNullspace (algebra, vec-algebra.products#(im#0)#(im#1));
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
    r := algebra.field;
    ind := set(gens r);
    while true do (
        n := howManyUnknowns algebra;
        findNewEigenvectors algebra;
        findNullVectors algebra;
        print (n, howManyUnknowns algebra);
        if member(howManyUnknowns algebra, {0,n}) then break;
        if algebra.polys and any(algebra.polynomials, x -> #(set(support x)*ind) == 1) then return;
        );
    fusion algebra;
    if algebra.polys and any(algebra.polynomials, x -> #(set(support x)*ind) == 1) then return;
    findNullVectors algebra;
    if algebra.polys and any(algebra.polynomials, x -> #(set(support x)*ind) == 1) then return;
    )

universalDihedralAlgebra = { field => QQ, primitive => true, form => true } >> opts -> (evals, tbl) -> (
    algebra := dihedralAlgebraSetup(evals, tbl, field => opts.field, primitive => opts.primitive, form => opts.form);
    while howManyUnknowns algebra > 0 do (
        t1 := cpuTime();
        mainLoop algebra;
        print( "Time taken:", cpuTime() - t1 );
        );
    return algebra;
    )

dihedralAlgebras = { field => QQ, primitive => true, form => true } >> opts -> (evals, tbl) -> (
    algebra := dihedralAlgebraSetup(evals, tbl, field => opts.field, primitive => opts.primitive, form => opts.form);
    r := algebra.field;
    ind := set(gens r);
    if #ind > 0 then algebra.polys = true;
    while howManyUnknowns algebra > 0 do (
        t1 := cpuTime();
        mainLoop algebra;
        if any(algebra.polynomials, x -> #(set(support x)*ind) == 1) then break;
        print( "Time taken:", cpuTime() - t1 );
        );
    if all(algebra.polynomials, x -> #(set(support x)*ind) != 1) then fusion algebra;
    algebras := {};
    p := (select(algebra.polynomials, x -> #(set(support x)*ind) == 1))#0;
    y := (toList(set(support p)*ind))#0;
    r = coefficientRing(algebra.field)[y];
    p = sub(p, r);
    vals := (roots p)/(x -> x^(coefficientRing(algebra.field)));
    --for x in select(vals, x -> x != 0) do (
    for x in unique(vals) do (
        print ("Using value", x);
        newalgebra := dihedralAlgebraSetup(evals, tbl, field => opts.field, primitive => opts.primitive, form => opts.form);
        changeRingOfAlgebra(newalgebra, algebra.field);
        newalgebra.polynomials = append(algebra.polynomials, y - x);
        quotientNullPolynomials newalgebra;
        while howManyUnknowns newalgebra > 0 do mainLoop newalgebra;
        algebras = append(algebras, newalgebra);
        print "Found new algebra";
        );
    return {algebras, vals}
    )

tauMaps = (algebra, plusEvals, minusEvals) -> (
    n := #algebra.span;
    espace := zeroAxialVector n;
    mat0 := zeroAxialVector n;
    for ev in plusEvals do espace = espace | algebra.evecs#(set {ev});
    k := numgens image espace - 1;
    for ev in minusEvals do espace = espace | algebra.evecs#(set {ev});
    espace = espace_{1..n};
    for i to n - 1 do (
        a = sub(standardAxialVector(i, n), algebra.field);
        v = a//espace;
        v = v^{0..k-1} || -v^{k..n-1};
        mat0 = mat0 | (espace*v);
        );
    mat0 = mat0_{1..n};
    mat1 := new MutableMatrix from mat0;
    f = findFlip algebra;
    for i to n - 1 do (
        for j to n - 1 do (
            im = f_{i,j};
            mat1_(im#0, im#1) = mat0_(i,j);
            );
        );
    return {mat0, matrix mat1};
    )
