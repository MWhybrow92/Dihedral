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
    algebra.span = new MutableList from {1,2} | apply({2..n}, x -> new MutableList from {1,x});
    -- Add products as list of lists
    algebra.products = new MutableList from {};
    for i to n - 1 do (
        algebra.products#i = new MutableList from {};
        for j to n - 1 do algebra.products#i#j = false;
        );
    for i to n - 1 do algebra.products#i#i = standardAxialVector(i, n);
    -- Add first eigenvectors
    algebra.evecs = new MutableHashTable;
    for ev in delete( set({}), unique(values(tbl))) do (
        algebra.evecs#ev = zeroAxialVector n;
        );
    evecs := findFirstEigenvectors(evals, algebra.field);
    for i to n - 1 do algebra.evecs#({evals#i}) = matrix evecs_{i};
    -- If we assume primitivity then change the field to a polynomial ring
    if algebra.primitive = true then (
        changeRingOfAlgebra(algebra, algebra.field[x,y]);
        vec := algebra.evecs#{1} - x*sub(standardAxialVector(0,n), ring(x));
        quotientNullVec(algebra, vec);
        n = #algebra.span;
        algebra.evecs#{1} = standardAxialVector(0, n);
        )
    else algebra.evecs#{1} = algebra.evecs#{1}|standardAxialVector(0, n);
    for sum in unique(values(tbl)) do (
        if #(toList sum) > 1 then (
            for ev in (toList sum) do algebra.evecs#sum = algebra.evecs#sum|algebra.evecs#({ev})
            );
        );
    performFlip(algebra);
    algebra
    )

findFirstEigenvectors = (evals, field) -> (
    n := #evals;
    mat := toList apply( 0..n-1, i -> toList apply( 0..n-1, j -> (evals#i)^j ));
    mat = matrix(field, mat);
    inverse mat
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
    entry := vec_(k-1,0);
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
                algebra.products#i#j = (algebra.products#i#j%vec)^reduction;
                );
            );
        );
    for ev in keys algebra.evecs do (
        algebra.evecs#ev = (algebra.evecs#ev%vec)^reduction;
        -- find basis of evecs?
        );
    algebra.span = drop(algebra.span, {k,k});
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

performFlip = algebra -> (

    )
