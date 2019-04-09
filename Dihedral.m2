AxialAlgebra = new Type of MutableHashTable
AxialVector  = new Type of MutableList

zeroAxialVector = (n) -> transpose matrix { toList(n:0) }
standardAxialVector = (i, n) -> transpose matrix { toList( splice( (i:0, 1, n-i-1:0) ) ) }

JordanTable = n -> hashTable {
    {1,1} => set {1}, {1,0} => set {}, {1,n} => set {n},
    {0,1} => set {}, {0,0} => set {0}, {0,n} => set {n},
    {n,1} => set {n}, {n,0} => set {n}, {n,n} => set {1,0}
}

dihedralAlgebraSetup = method( TypicalValue => AxialAlgebra, Options => { field => QQ, primitive => true } )
dihedralAlgebraSetup(List, HashTable ) := opts -> (evals, tbl) -> (
    n := #evals;
    -- Set up algebra hash table
    algebra := new MutableHashTable;
    algebra.evals = evals;
    algebra.tbl = tbl;
    algebra.field = opts.field;
    algebra.primitive = opts.primitive;
    algebra.span = new MutableList from {0,1} | apply(toList(1..n-1), x -> new MutableList from {0,x});
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
        );
    evecs := findFirstEigenvectors(evals, algebra.field);
    for i to n - 1 do algebra.evecs#(set {evals#i}) = matrix evecs_{i};
    -- If we assume primitivity then change the field to a polynomial ring
    if algebra.primitive = true then (
        changeRingOfAlgebra(algebra, algebra.field[x,y]);
        vec := algebra.evecs#(set {1}) - x*sub(standardAxialVector(0,n + 1), ring(x));
        quotientNullVec(algebra, vec);
        n = #algebra.span;
        algebra.evecs#(set {1}) = standardAxialVector(0, n);
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
    algebra
    )

fusion = algebra -> (
    for ev0 in algebra.evals do (
        for ev1 in algebra.evals do (
            ev := algebra.tbl#({ev0,ev1});
            for i to numgens target algebra.evecs#(set {ev0}) do (
                for j to numgens target algebra.evecs#(set {ev1}) do (
                    u := (algebra.evecs#(set {ev0}))_i;
                    v := (algebra.evecs#(set {ev1}))_j;
                    unknowns := {};
                    prod := axialSeparateProduct(u, v, unknowns, algebra.products);
                    for k to #unknowns - 1 do (
                        x := unknowns#k;
                        algebra.span = append(algebra.span, x);
                        expandAlgebra algebra;
                        n := #algebra.span;
                        algebra.products#(x#0)(x#1) = standardAxialVector(n-1, n);
                        algebra.products#(x#1)(x#0) = standardAxialVector(n-1, n);
                        prod.rhs = prod.rhs || matrix({{0}});
                        prod.rhs = prod.rhs - algebra.products#(x#1)(x#0)*(prod.lhs)#k;
                        );
                    if ev === set {} then quotientNullVec(algebra, prod.rhs)
                    else (
                        for s in unique values tbl do(
                            if isSubset(ev, sum) then (
                                algebra.evecs#s = algebra.evecs#s | -prod.rhs;
                                );
                            );
                        );
                    );
                );
            );
        );
        performFlip algebra;
    )

expandAlgebra = algebra -> (
    n := #algebra.span;
    k := #algebra.products;
    for i to k do algebra.products#i = append(algebra.products#i, (k - n):false );
    algebra.products = append(algebra.products, (n-k):(n-1:false));
    for i to n - 1 do (
        for j to n - 1 do (
            if algebra.products#i'j =!= false then (
                algebra.products#i#j = algebra.products#i#j || matrix({{0}})
                );
            );
        );
    for ev in keys algebra.evecs do (
        d := #numgens target algebra.evecs#ev;
        algebra.evecs#ev = algebra.evecs#ev || matrix( {toList(d:0)});
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
    )

quotientNullVec = (algebra, vec) -> (
    nonzero := positions( flatten(entries(vec)), i -> i != 0);
    if #nonzero == 0 then return;
    n := #algebra.span;
    k := last nonzero;
    entry := vec_(k,0);
    if #nonzero == 1 then (
        if isPolynomialRing(algebra.field) and #support(entry) > 0 then (
            algebra.polynomials = append(algebra.polynomials, entry);
            return;
            )
        else prod := vec*0;
        )
    else if #nonzero > 1 then (
        if isPolynomialRing(algebra.field) and #support(entry) > 0 then (
            error "Leading coefficient of null vector is a polynomial")
        else prod = standardAxialVector(k,n) - vec*(sub(1/entry, ring(vec)));
        );
    vec = vec*sub(1/entry, ring(vec));
    for i in k+1 .. n-1 do (
        x := algebra.span#i;
        if member(k,x) then (
            if x#0 == k then u := prod
            else u = standardAxialVector(0,n);
            if x#1 == k then v := prod
            else v = standardAxialVector(1,n);
            newProd := axialProduct(u, v, algebra.products);
            if newProd === false then error "Cannot find product";
            quotientNullVec(algebra, standardAxialVector(i,n) - newProd);
            );
        );
    for i in k+1 .. n-1 do (
        if algebra.span#i#0 > k then algebra.span#i#0 = algebra.span#i#0 - 1;
        if algebra.span#i#1 > k then algebra.span#i#1 = algebra.span#i#1 - 1;
        );
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
        algebra.evecs#ev = groebnerBasis algebra.evecs#ev;
        );
    algebra.span = drop(algebra.span, {k,k});
    )

reduce = (u, v, k) -> u - v*u^{k}

-- might want to swap lhs and rhs now that we are working with columns
axialSeparateProduct = (u,  v, unknowns, products) -> (
    lhs := new MutableList from {};
    rhs := {};
    for i to #u do (
        if u_i =!= 0 then (
            for j to #v do (
                if v_j =!= 0 then (
                    if products#i#j === false then (
                        pos = position( sort {i,j}, unknowns );
                        if pos === null then (
                            unknowns = append(unknowns, sort {i,j});
                            pos = #unknowns;
                            );
                        lhs#pos = {u_i*v_j}
                        )
                    else rhs = append( rhs, (u_i)*(v_j)*products#i#j );
                    );
                );
            );
        );
    new hashTable from ( "rhs" => rhs, "lhs" => sum(lhs) )
    )

axialProduct = (u, v, products) -> (
    l := {};
    for i to #u do (
        if u#i != 0 then (
            for j to #v do (
                if v#j != 0 then (
                    if products#i#j === false then return false;
                    l = append( l, (u#i)*(v#j)*products#i#j );
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
    for x in algebra.span_(toList(3..n-1)) do (
        im := sort f_x;
        f = append(f, position(im, algebra.span));
        );
    f
    )

flipVector = (vec, f) -> (
    r := ring vec;
    vec = apply( entries vec, p -> sub(p#0, {r_0 => r_1, r_1 => r_0}));
    res := sub(zeroAxialVector(#vec), r);
    for i to #vec - 1 do (
        k := f#i;
        if k === null then (
            im := f_(algebra.span#i);
            if member(null, im) then error "Can't find image of vec under flip";
            if algebra.products#(im#0)#(im#1) =!= false then (
                res = res + algebra.products#(im#0)#(im#1)*(vec#i)
                )
            else (
                algebra.span = append(algebra.span, sort im);
                expandAlgebra(algebra);
                res = res || matrix({{0}});
                res = res + sub(standardAxialVector(#res - 1, #res - 1),r)*vec#i;
                );
        )
        else res = res + sub(standardAxialVector(k, #algebra.span),r)*vec#i;
    );
    res
    )

performFlip = algebra -> (
    n = #algebra.span;
    f = findFlip algebra;
    -- might need to be more careful with the indices if a nullspace vec occurs here
    for i to n -1 do (
        for j to n - 1 do (
            im := f_{i,j};
            if not member(null, im) and algebra.products#i#j =!= false then (
                vec := flipVector(algebra.products#i#j, f);
                if algebra.products#(im#0)#(im#1) === false then (
                    algebra.products#(im#0)#(im#1) = vec;
                    algebra.products#(im#1)#(im#0) = vec;
                    )
                else quotientNullVec(algebra, vec-algebra.products#(im#0)#(im#1));
                );
            );
        );
    );
