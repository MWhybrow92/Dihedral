-- build generic vectors
zeroAxialVector = (n) -> transpose matrix { toList(n:0) }
standardAxialVector = (i, n) -> transpose matrix { toList( splice( (i:0, 1, n-i-1:0) ) ) }

dihedralAlgebraSetup = dihedralOpts >> opts -> (evals, tbl) -> (

    n := #evals;

    -- Set up algebra hash table
    algebra := new MutableHashTable;
    algebra.evals = evals;
    algebra.tbl = tbl;
    algebra.opts = opts;
    if opts.primitive then algebra.coordring = opts.field[]
    else algebra.coordring = opts.field;
    algebra.polynomials = {};
    ev := opts.eigenvalue;
    algebra.span = {0,1} | apply(toList(1..n-1), x -> {0,x});

    -- Add products as list of lists
    algebra.products = new MutableList from {};
    for i to n do (
        algebra.products#i = new MutableList from {};
        for j to n do algebra.products#i#j = false;
        );
    for i to 1 do algebra.products#i#i = ev*sub(standardAxialVector(i, n + 1), algebra.coordring); -- Then add known products
    for i in 1..n-1 do algebra.products#0#i = sub(standardAxialVector(i + 1, n + 1), algebra.coordring);
    for i in 1..n-1 do algebra.products#i#0 = sub(standardAxialVector(i + 1, n + 1), algebra.coordring);

    -- Add first eigenvectors
    algebra.evecs = new MutableHashTable;
    findFirstEigenvectors algebra;

    if algebra.opts.primitive then (
        -- Scale the eigenvector so that x0 = (a0, a1)
        for x in toList(set(algebra.evals) - {ev}) do (
            algebra.evecs#(set {ev}) = sub(1/(ev-x), opts.field)*algebra.evecs#(set {ev});
        );
        quotientOneEigenvectors algebra;
    );

    n = #algebra.span;
    algebra.evecs#(set {ev}) = standardAxialVector(0,n) | algebra.evecs#(set {ev});
    algebra.evecs#(set {ev}) = findBasis algebra.evecs#( set {ev} );

    -- Build the full eigenspaces
    for s in (properSubsets evals )/set do (
        if #(toList s) > 1 then (
            algebra.evecs#s = zeroAxialVector n;
            for ev in (toList s) do (
                algebra.evecs#s = algebra.evecs#s|algebra.evecs#(set {ev});
                );
            algebra.evecs#s = findBasis algebra.evecs#s;
            );
        );
    algebra
    )

properSubsets = s -> select( subsets s, x -> #x > 0 and x != s );

-- Using HRS15 Lemma 5.3
findFirstEigenvectors = algebra -> (
    n := #algebra.evals;
    a0 := sub(standardAxialVector(0, n + 1), algebra.coordring);
    for ev0 in algebra.evals do (
        prod := sub(standardAxialVector(1, n + 1), algebra.coordring);
        for ev1 in toList(set( algebra.evals ) - {ev0}) do (
                prod = axialProduct(a0, prod, algebra.products) - ev1*prod;
            );
        algebra.evecs#(set {ev0}) = prod;
        );
    )
