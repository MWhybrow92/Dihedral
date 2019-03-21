AxialAlgebra = new Type of MutableHashTable
AxialVector  = new Type of MutableList

zeroAxialVector = (n) -> matrix { toList(n:0) }
standardAxialVector = (i, n) -> matrix { toList( splice( (i:0, 1, n-i-1:0) ) ) }

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
    algebra.spanningset = new mutableList from {1,2} | apply({2..n}, x -> new mutableList from {1,x});
    -- Add products as list of lists
    algebra.products = new MutableList from {};
    for i to n do (
        algebra.products#i = new MutableList from {};
        for j to n do algebra.products#i#j = false;
        );
    for i to n do algebra.products#i#i = standardAxialVector(i, n);
    -- Add first eigenvectors
    algebra.evecs = new MutableHashTable;
    for ev in delete( set({}), unique(keys(tbl))) do (
        algebra.evecs#ev = zeroAxialVector n;
        );
    evecs := findFirstEigenvectors(evals, algebra.field);
    for i to n - 1 do algebra.evecs#({evals#i}) = matrix evecs^{i};
    -- If we assume primitivity then change the field to a polynomial ring
    if algebra.primitive = true then (
        changeRingOfAlgebra(algebra, algebra.field[x,y]);
        vec := mutableMatrix algebra.evecs#{1};
        vec_(0,0) = vec_(0,0) - x;
        quotientNullVec(algebra, vec);
        algebra.evecs#{1} = standardAxialVector(1, n);
        )
    else algebra.evecs#{1} = algebra.evecs#{1}|standardAxialVector(1, n);
    for sum in unique(keys(tbl)) do (
        if #sum > 1 then (
            for ev in sum do algebra.evecs#sum = algebra.evecs#sum|algebra.evecs#ev
            );
        );
    performFlip(algebra);
    algebra
    )

findFirstEigenvectors = (evals, field) -> (
    n := #evals;
    mat := toList apply( 0..n-1, i -> toList apply( 0..n-1, j -> (evals#i)^j ));
    mat = matrix(field, mat);
    transpose inverse mat
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
    if #nonzero = 0 then return;
    k := last nonzero;
    entry := vec_(0,k);
    if #nonzero = 1 then (
        if isPolynomialRing(algebra.field) and #support(entry) > 0 then (
            algebra.polynomials = append(algebra.polynomials, entry);
            return;
            );
        else prod := vec*0;
    else if #nonzero > 1 then (
        if isPolynomialRing(algebra.field) and #support(entry) > 0 then (
            error "Leading coefficient of null vector is a polynomial";
        else prod := standardAxialVector(k, #prod) - vec*(1/entry);
        );

    for i in k+1 .. #algebra.spanningset do (
        x := algebra.spanningset#i;
        if member(k,x) then (
            if x#0 == k then u := prod;
            else u := standardAxialVector(0,#prod);
            if x#1 == k then v := prod;
            else v := standardAxialVector(1,#prod);

            new := axialProduct(u, v, algebra.products);
            if new = false then error "Cannot find product";
            quotientNullVec(algebra, standardAxialVector(i, #new) - new);
            );

    for i in k+1 .. #algebra.spanningset do (
        if
        )




    )

axialProduct = (u, v, products) -> -- Is this the right way to do it? Probably not
    l := {};
    for i to #u do (
        if u#i != 0 then (
            for j to #v do (
                if v#j != 0 then (
                    if products#i#j = false then return false;
                    l = append( l, (u#i)*(v#j)*products#i#j );
                    );
                );
            );
        );
    sum l
    )

performFlip = algebra -> (

    )
