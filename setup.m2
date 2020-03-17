-- build generic vectors
zeroAxialVector = (n) -> transpose matrix { toList(n:0) }
standardAxialVector = (i, n) -> transpose matrix { toList( splice( (i:0, 1, n-i-1:0) ) ) }

dihedralAlgebraSetup = { field => QQ, primitive => true, form => true, eigenvalue => 1 } >> opts -> (evals, tbl) -> (

    n := #evals;

    -- Set up algebra hash table
    algebra := new MutableHashTable;
    algebra.evals = evals;
    algebra.tbl = tbl;
    algebra.usefulpairs = usefulPairs(evals, tbl);
    for key in keys opts do algebra#key = opts#key;
    algebra.coordring = opts.field;
    algebra.polynomials = {};
    algebra.polys = false;
    ev := algebra.eigenvalue;
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

    if algebra.primitive then (
        -- Scale the eigenvector so that x0 = (a0, a1)
        for x in toList(set(algebra.evals) - {ev}) do (
            algebra.evecs#(set {ev}) = (1/(ev-x))*algebra.evecs#(set {ev});
        );
        quotientOneEigenvector ( algebra, algebra.evecs#(set {ev}), form => opts.form );
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
    a0 := sub(standardAxialVector(0, n + 1), algebra.field);
    for ev0 in algebra.evals do (
        prod := sub(standardAxialVector(1, n + 1), algebra.field);
        for ev1 in toList(set( algebra.evals ) - {ev0}) do (
                prod = axialProduct(a0, prod, algebra.products) - ev1*prod;
            );
        algebra.evecs#(set {ev0}) = prod;
        );
    )

-- Add indeterminates to ring in order to quotient a 1-eigenvector
extendedRing = { form => true } >> opts -> algebra -> (
    n := numgens algebra.coordring - numgens algebra.field;
    if opts.form then return algebra.field[ apply (0..n, i -> "x"|i)]
    else return algebra.field[ apply (0..n, i -> "x"|i) | apply (0..n, i -> "y"|i) ];
    )

-- Special procedure to quotient a 1-eigenvector in the primitive case
quotientOneEigenvector = { form => true } >> opts -> (algebra, v) -> (
    changeRingOfAlgebra(algebra, extendedRing (algebra, form => opts.form) );
    n := #algebra.evals;
    v = v - x0*sub(standardAxialVector(0,n + 1), ring(x0));
    quotientNullspace (algebra, v);
    )

-- Finds useful pairs as defined in expansion algorithm paper
usefulPairs = (evals, tbl) -> (
    pset := properSubsets evals;
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
