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
    algebra.allpolynullvecs = sub( zeroAxialVector (n + 1), algebra.field );
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
    for ev in flatten algebra.usefulpairs do (
        algebra.evecs#ev = zeroAxialVector(n + 1);
        );
    evecs := findFirstEigenvectors(evals, algebra.field);
    for i to n - 1 do algebra.evecs#(set {evals#i}) = matrix evecs_{i};
    -- If we assume primitivity then change the field to a polynomial ring
    if algebra.primitive then (
        changeRingOfAlgebra(algebra, algebra.field[symbol x, symbol y]);
        vec := algebra.evecs#(set {1}) - x*sub(standardAxialVector(0,n + 1), ring(x));
        quotientNullspace (algebra, vec);
        n = #algebra.span;
        algebra.evecs#(set {1}) = sub(standardAxialVector(0, n), algebra.field);
        )
    else algebra.evecs#(set {1}) = algebra.evecs#(set {1})|standardAxialVector(0, n + 1);
    -- If we assume that the alg admits a form then x = y
    if opts.form and opts.primitive then algebra.polynomials = {algebra.field_0 - algebra.field_1}; -- pretty but not so efficient
    -- Build the full eigenspaces
    for s in keys algebra.evecs do (
        if #(toList s) > 1 then (
            for ev in (toList s) do (
                algebra.evecs#s = algebra.evecs#s|algebra.evecs#(set {ev});
                algebra.evecs#s = groebnerBasis algebra.evecs#s;
                );
            );
        );
    performFlip algebra;
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
            if not member(rule, rules) then useful = append(useful, p/set);
            );
        );
    useful
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
    algebra.temp = copy algebra.evecs;
    n := #(keys algebra.evecs);
    for p in algebra.usefulpairs do (
        rule := fusionRule(p#0, p#1, algebra.tbl);
        if rule =!= set(algebra.evals) then (
            for i to numgens source algebra.evecs#(p#0) - 1 do (
                for j to numgens source algebra.evecs#(p#1) - 1 do (
                    if i < numgens source algebra.evecs#(p#0) and j < numgens source algebra.evecs#(p#1) then (
                        u := (algebra.evecs#(p#0))_{i};
                        v := (algebra.evecs#(p#1))_{j};
                        if opts.expand then (
                            unknowns := findUnknowns(u, v, algebra.products);
                            expandAlgebra(algebra, unknowns);
                            );
                        prod := axialProduct(u, v, algebra.products);
                        if prod =!= false then (
                            if rule === set {} then quotientNullspace (algebra, prod)
                            else (
                                for s in keys algebra.temp do(
                                    if isSubset(rule, s) then (
                                        algebra.temp#s = algebra.temp#s | prod;
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
    d = numgens source algebra.allpolynullvecs;
    algebra.allpolynullvecs = algebra.allpolynullvecs || matrix( toList(k:toList(d:0)));
    if algebra#?temp then (
        for ev in keys algebra.temp do (
            d = numgens source algebra.temp#ev;
            algebra.temp#ev = algebra.temp#ev || matrix( toList(k:toList(d:0)));
            );
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
    performFlip algebra;
    )

quotientNullPolynomials = algebra -> (
    algebra.polynomials = flatten entries groebnerBasis ideal algebra.polynomials;
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
    algebra.allpolynullvecs = algebra.allpolynullvecs % I;
    )

findNullVectors = algebra -> (
    -- intersect distinct eigenspaces
    print "Finding null vectors";
    for ev in select(algebra.usefulpairs, x -> (x#0)*(x#1) === set {}) do (
        za := mingens intersect(image algebra.evecs#(ev#0), image algebra.evecs#(ev#1));
        quotientNullspace (algebra, za);
        );
    performFlip algebra;
    quotientAllPolyNullVecs algebra;
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

quotientNullspace = (algebra, mat) -> (
    if mat == 0 then return;
    algebra.nullspace = mat;
    n := #algebra.span;
    d := numgens image algebra.nullspace;
    for i to n - 1 do (
        a := standardAxialVector(i, n);
        for j to d - 1 do (
            prod := axialProduct( a, algebra.nullspace_{j}, algebra.products );
            if prod =!= false then algebra.nullspace = algebra.nullspace | prod;
            );
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
    k = last nonzero;
    if algebra.primitive and #support vec#k#0 > 0 then ( -- all poly mat
        if all(nonzero, i -> i < 3) then (
            print vec;
            polys := unique select(flatten vec, p -> #support p > 0);
            polys = polys | apply(polys, p -> sub(p, {r_0 => r_1, r_1 => r_0} ));
            algebra.polynomials = algebra.polynomials | polys;
            print algebra.polynomials;
            quotientNullPolynomials algebra;
            return false;
            )
        else (
            algebra.allpolynullvecs = algebra.allpolynullvecs | matrix(algebra.field, vec);
            return false;
            );
        );
    --if algebra.primitive then k := last select(nonzero, i -> #support vec#i#0 == 0)
    --else k = last nonzero;
    if k == 0 or k == 1 then error "Is the algebra zero?";
    vec = sub(matrix vec, algebra.field);
    if algebra.primitive then entry := sub(vec_(k,0), coefficientRing algebra.field)
    else entry = vec_(k,0);
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
                unknowns := findUnknowns(u, v, algebra.products);
                if #unknowns > 0 then print ("Expanding in quotient func", i);
                expandAlgebra(algebra, unknowns);
                newProd := axialProduct(u, v, algebra.products);
                n = #algebra.span;
                quotientNullVec(algebra, standardAxialVector(i,n) - newProd);
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
    if algebra#?allpolynullvecs then (
        algebra.allpolynullvecs = (reduce(algebra.allpolynullvecs, vec, k))^reduction;
        );
    if algebra#?nullspace then (
        algebra.nullspace = (reduce(algebra.nullspace, vec, k))^reduction;
        );
    algebra.span = drop(algebra.span, {k,k});
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

findUnknowns = (u, v, products) -> (
    unknowns := {};
    for i to numgens target u - 1 do (
        if u_(i,0) != 0 then (
            for j to numgens target v - 1 do (
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
                if not member(null, im) and algebra.products#i#j =!= false then (
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
    while true do (
        m := howManyUnknowns algebra;
        while true do (
            n := howManyUnknowns algebra;
            findNullVectors algebra;
            findNewEigenvectors(algebra, expand => false);
            print (n, howManyUnknowns algebra);
            if howManyUnknowns algebra == n then break;
            );
        fusion(algebra, expand => false);
        if howManyUnknowns algebra == m then return;
        );
    )

dihedralAlgebra = { field => QQ, primitive => true, form => true } >> opts -> (evals, tbl) -> (
    algebra := dihedralAlgebraSetup(evals, tbl, field => opts.field, primitive => opts.primitive, form => opts.form);
    while howManyUnknowns algebra > 0 do (
        while true do (
            n := howManyUnknowns algebra;
            findNewEigenvectors algebra;
            mainLoop algebra;
            if howManyUnknowns algebra == n then break;
            );
        fusion algebra;
        mainLoop algebra;
        );
    return algebra;
    )
