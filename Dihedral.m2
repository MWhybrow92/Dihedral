AxialAlgebra = new Type of MutableHashTable
AxialVector  = new Type of MutableList

zeroAxialVector = (n) -> matrix { toList(n:0) }
standardAxialVector = (i, n) -> matrix { toList( splice( (i-1:0, 1, n-i:0) ) ) }

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
    algebra.spanningset = {1,2} | apply({2..n}, x -> {1,x});
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

    )
