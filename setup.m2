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
    algebra.field = opts.field;
    algebra.primitive = opts.primitive;
    algebra.eigenvalue = opts.eigenvalue;
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
    ev := algebra.eigenvalue;
    for i to 1 do algebra.products#i#i = ev*sub(standardAxialVector(i, n + 1), algebra.field);
    for i in 1..n-1 do algebra.products#0#i = sub(standardAxialVector(i + 1, n + 1), algebra.field);
    for i in 1..n-1 do algebra.products#i#0 = sub(standardAxialVector(i + 1, n + 1), algebra.field);
    -- Add first eigenvectors
    algebra.evecs = new MutableHashTable;
    for ev0 in (properSubsets evals)/set do (
        algebra.evecs#ev0 = zeroAxialVector(n + 1);
        );
    evecs := findFirstEigenvectors algebra;
    -- If we assume primitivity then change the field to a polynomial ring
    if algebra.primitive then (
        changeRingOfAlgebra(algebra, algebra.field[symbol x, symbol y]);
        vec := algebra.evecs#(set {ev});
        for ev0 in toList(set(algebra.evals) - {ev}) do vec = (ev-ev0)^(-1)*vec;
        quotientNullspace (algebra, vec - x*sub(standardAxialVector(0,n + 1), ring(x)));
        n = #algebra.span;
        algebra.evecs#(set {ev}) = sub(standardAxialVector(0, n), algebra.field);
        )
    else algebra.evecs#(set {ev}) = algebra.evecs#(set {ev})|standardAxialVector(0, n + 1);
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
        algebra.evecs#s = findBasis algebra.evecs#s;
        );
    --performFlip algebra;
    algebra
    )

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
