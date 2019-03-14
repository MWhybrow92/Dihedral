AxialAlgebra = new Type of MutableHashTable
AxialVector  = new Type of Matrix

zeroAxialVector = (n) -> new MutableList from n:0
standardAxialVector = (i, n) -> new MutableList from splice (i-1:0, 1, n-i:0)

JordanTable = n -> hashTable {
    {1,1} => set {1}, {1,0} => set {}, {1,n} => set {n},
    {0,1} => set {}, {0,0} => set {0}, {0,n} => set {n},
    {n,1} => set {n}, {n,0} => set {n}, {n,n} => set {1,0}
}

dihedralAlgebraSetup = method(TypicalValue => AxialAlgebra, Options => { field => QQ, primitive => true } )
dihedralAlgebraSetup(List, HashTable ) := opts -> (evals, tbl) -> (
    n := #evals;
    algebra := new MutableHashTable;
    algebra.evals = evals;
    algebra.tbl = tbl;
    algebra.field = opts.field;
    algebra.primitive = opts.primitive;
    algebra.products = new MutableList from {};
    for i to n do (
        algebra.products#i = new MutableList from {};
        for j to n do algebra.products#i#j = false
        );
    for i to n do algebra.products#i#i = standardAxialVector(i, n);
    algebra.evecs = new MutableHashTable;
    for ev in unique values tbl do algebra.evecs#1 = zeroAxialVector n;
    algebra.spanningset = append({1,2}, pack(mingle(n-1:1,2..n),2));
    )
