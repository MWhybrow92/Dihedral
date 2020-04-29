dihedralOpts = { field => QQ, primitive => true, form => true, eigenvalue => 1 };

load "examples.m2";
load "testFusion.m2";
load "setup.m2";

-- Column reduces a matrices with entries in a ring

colReduce =  M -> ( -- Note - rowSwap is a lot faster than columnSwap, hence the transpose
    if M == 0 then return M;
    r := ring M;
    M = new MutableMatrix from transpose M; -- transpose the matrix
    (m,n) := (numrows M, numcols M);
    i := m - 1; --row of pivot, starting from the bottom
    for j in reverse (0 .. n-1) do ( -- run over the columns of the matrix, starting from the right
    	if i == -1 then break; -- Then we've finished
    	a := position (0..i, l-> M_(l,j) != 0, Reverse => true); -- Find first nonzero entry of jth column from the bottom
        while a =!= null do (
        	c := M_(a,j);
        	rowSwap(M,a,i);
            if c == 1 or isUnit c then break; -- isUnit is expensive, but often c == 1 so check this first
            i = i - 1; -- if c is not a unit then look at the next row
            a = position (0..i, l-> M_(l,j) != 0, Reverse => true);
            );
        if a === null then continue;
        rowMult(M, i, c^(-1)); -- scale the pivot row
    	for k from 0 to m-1 do if M_(k,j) !=0 then rowAdd(M,k,-M_(k,j),i); -- Subtract pivot row from *all* rows of matrix
    	i = i - 1;
	);
    M = transpose (new Matrix from M);
    M = map(r^n, r^m, M);
    return M_{i+1..m-1};
    )

findBasis = mat -> colReduce mingens image mat;

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

-- Finds fusion pairs as defined in expansion algorithm paper
fusionPairs = (evals, tbl) -> (
    pset := properSubsets evals;
    evalpairs := toList((set pset)**(set pset))/toList;
    fusion := {};
    for p in evalpairs do (
        rule := fusionRule(p#0, p#1, tbl);
        if #rule < #evals then (
            sets0 := select(pset, x -> isSubset(p#0, x) and x != p#0);
            sets1 := select(pset, x -> isSubset(p#1, x) and x != p#1);
            rules = apply(sets0, x -> fusionRule(x, p#1, tbl));
            rules = rules | apply(sets1, x -> fusionRule(x, p#0, tbl));
            if not member(rule, rules) then fusion = append(fusion, set(p/set));
            );
        );
    fusion = (unique fusion)/toList;
    return apply(fusion, x -> if #x == 1 then {x#0, x#0} else x);
    )

fusion = {expand => true} >> opts -> algebra -> (
    if opts.expand == true then print "Performing fusion with expansion"
    else print "Performing fusion without expansion";
    algebra.temp = copy algebra.evecs;
    for p in fusionPairs(algebra.evals, algebra.tbl) do (
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
                        prod := colReduce axialProduct(u, v, algebra.products);
                        if prod =!= false then recordEvec(prod, rule, algebra.temp, algebra);
                        );
                    );
                );
            );
        for ev in keys algebra.temp do algebra.evecs#ev = algebra.temp#ev;
        remove(algebra, temp);
    )

recordEvec = (v, rule, evecs, algebra) -> (
    if v == 0 then return;
    if rule === set {} then return quotientNullspace (algebra, v);
    for s in keys evecs do if isSubset(rule, s) then evecs#s = findBasis (evecs#s|v);
    )

expandVector = (vec, k) -> (
    d := numgens source vec;
    return vec || matrix( toList(k:toList(d:0)));
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
                algebra.products#i#j = expandVector(algebra.products#i#j, k);
                );
            );
        );
    for ev in keys algebra.evecs do algebra.evecs#ev = expandVector(algebra.evecs#ev, k);
    if algebra#?temp then (
        for ev in keys algebra.temp do algebra.temp#ev = expandVector(algebra.temp#ev, k);
        );
    if algebra#?nullspace then algebra.nullspace = expandVector(algebra.nullspace, k);
    for i to k - 1 do (
        x := unknowns#i;
        algebra.products#(x#0)#(x#1) = sub(standardAxialVector(n + i, n + k), algebra.coordring);
        algebra.products#(x#1)#(x#0) = algebra.products#(x#0)#(x#1);
        );
    algebra.span = algebra.span | unknowns;
    )

findNewEigenvectors = {expand => true} >> opts -> algebra -> (
    if opts.expand then print "Finding new eigenvectors with expansion"
    else print "Finding new eigenvectors without expansion";
    a := sub(standardAxialVector(0, #algebra.span), algebra.coordring);
    for s in keys algebra.evecs do (
        for i to numgens source algebra.evecs#s - 1 do (
            for t in select(subsets s, x -> x =!= set {}) do (
                if i < numgens source algebra.evecs#s then (
                    u := algebra.evecs#s_{i};
                    for ev in toList t do (
                        if opts.expand then (
                            unknowns := findUnknowns(a, u, algebra.products);
                            if #unknowns != 0 then (
                                expandAlgebra(algebra, unknowns);
                                a = expandVector(a, #unknowns);
                                u = expandVector(u, #unknowns);
                                );
                            );
                        prod = axialProduct(a, u, algebra.products);
                        if prod === false then break;
                        u = prod - ev*u
                        );
                    if prod =!= false then recordEvec(u, s - t, algebra.evecs, algebra);
                    );
                );
            );
        );
    )

-- Add indeterminates to ring in order to quotient a 1-eigenvector
extendedRing = algebra -> (
    n := numgens algebra.coordring;
    if algebra.opts.form then ind :=  apply (0..n, i -> "x"|i)
    else ind = apply (0..(n/2)^ZZ, i -> "y"|i) | apply (0..(n/2)^ZZ, i -> "x"|i);
    return algebra.opts.field[ ind ];
    )

-- Special procedure to quotient a 1-eigenvector in the primitive case
quotientOneEigenvectors = algebra -> (
    ev := algebra.opts.eigenvalue;
    d := numgens image algebra.evecs#( set {ev} );
    for i in reverse (0..d-1) do (
        n := #algebra.span;
        v := algebra.evecs#(set {ev})_{i} - ev*standardAxialVector(0,n);
        k := position(entries v, x -> x#0 != 0, Reverse => true);
        if k === null or not isUnit v_(k, 0) then continue;
        changeRingOfAlgebra(algebra, extendedRing algebra );
        x := last gens algebra.coordring;
        v = algebra.evecs#(set {ev})_{i}-x*sub(standardAxialVector(0,n), algebra.coordring);
        quotientNullspace (algebra, v);
        );
    )

-- If we quotient by a poly of degree 1, we can lose one of the indeterminates
-- of the coord ring
reduceCoordRing = (algebra, I) -> (
        r := (flattenRing( algebra.coordring/I ))#0;
        ind := unique apply (gens r, x -> sub(x, algebra.coordring));
        ind = select(ind, x -> not liftable(x, algebra.opts.field));
        -- If there no indeterminates have been determined then do nothing
        if #ind == numgens algebra.coordring then return;
        -- Otherwise change to ring with reduced number of indeterminates
        r = coefficientRing(algebra.coordring)[ind];
        changeRingOfAlgebra(algebra, r);
    )

quotientNullPolynomials = algebra -> (
    if #algebra.polynomials == 0 then return;
    -- Quotient polys from products, evecs and nullspace
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
    -- TODO Implement and test this
    -- Possibly reduce the number of determinants in coord ring
    -- reduceCoordRing( algebra, I );
    )

findNullPolys = algebra -> (
    -- A bit patchy to catch null polynomials
    v := sub(standardAxialVector(0, #algebra.span), algebra.coordring);
    evals := select(algebra.evals, ev -> ev != algebra.opts.eigenvalue);
    za := findBasis gens intersect(image v, image algebra.evecs#(set evals));
    quotientNullVec(algebra, za);
    )

intersectionPairs = evals -> (
    n := #evals;
    pairs := {};
    for i from 1 to n - 1 do (
        for x in subsets(evals, i) do (
            for j from 0 to i - 1 do (
                for y in subsets(evals, n - (i - j) ) do (
                    if #(set x * set y) == j then (
                        pairs = pairs | {apply(sort {x,y}, set)};
                        );
                    );
                );
            );
        );
    return unique pairs;
    )

findNullVectors = algebra -> (
    pset := keys algebra.evecs;
    while true do (
        n := howManyUnknowns algebra;
        -- intersect distinct eigenspaces
        print "Finding null vectors";
        for ev in intersectionPairs evals do (
            za := colReduce gens intersect(image algebra.evecs#(ev#0), image algebra.evecs#(ev#1));
            recordEvec(za, (ev#0)*(ev#1), algebra.evecs, algebra );
            );
        if howManyUnknowns algebra == 0 then return;
        -- quotient any one-eigenvectors
        if algebra.opts.primitive then quotientOneEigenvectors algebra;
        -- find new evecs
        findNewEigenvectors(algebra, expand => false);
        if member(howManyUnknowns algebra, {0,n}) then return;
        );
    )

changeRingOfAlgebra = (algebra, r) -> (
    algebra.coordring = r;
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
    -- Change the nullspace
    if algebra#?nullspace then algebra.nullspace = sub(algebra.nullspace, r);
    )

reduceSpanningVec = (vec, k) -> (
    if member (vec, {0,1}) then return vec;
    if vec#0 > k and vec#1 > k then return {vec#0 - 1, vec#1 - 1};
    if vec#0 > k then return {vec#0 - 1, vec#1};
    if vec#1 > k then return {vec#0, vec#1 -1};
    vec
    )

quotientNullspace = (algebra, mat)  -> (
    if #algebra.polynomials > 0 then mat = mat % (ideal algebra.polynomials);
    algebra.nullspace = mat;
    d := numgens image algebra.nullspace;
    -- Apply flip to the nullspace vectors
    for i to d - 1 do (
        v := flipVector(algebra.nullspace_{i}, algebra);
        if v =!= false then algebra.nullspace = algebra.nullspace | v;
        );
    d = numgens image algebra.nullspace;
    -- Quotient one vec at a time
    for j in reverse toList(0..d-1) do quotientNullVec(algebra, algebra.nullspace_{j});
    )

polyNullVec = (algebra, vec) -> (
    n := numgens target vec;
    -- The poly is vec_(0,0) + (v_(1,0) + v_(2,0))*x0
    -- This needs to be a lemma that \phi_a0 (a_1) = \phi_a0 (a0a1) = x0
    -- As projection of a0a1 - a1 is zero
    poly := vec_(0,0);
    x0 := (gens algebra.coordring)#0;
    for i in 1..n-1 do poly = poly + vec_(i,0)*x0;
    -- Then quotient this polynomial
    if not algebra.opts.form then polys := {poly, flipPoly(poly, algebra)}
    else polys = {poly};
    polys = flatten entries groebnerBasis ideal (algebra.polynomials | polys);
    if polys != algebra.polynomials then (
        algebra.polynomials = polys;
        quotientNullPolynomials algebra;
        );
    return vec % (ideal algebra.polynomials);
    );

quotientNullVec = (algebra, vec) -> (
    if vec == 0 then return;
    r := algebra.coordring;
    k := last positions(entries vec, x -> x#0 != 0);
    if algebra.opts.primitive and #(set(support vec_(k,0))*set(gens r)) > 0 then ( -- all poly mat
        if k < 3 then vec = polyNullVec (algebra, vec);
        );
    if not isUnit vec_(k,0) then return false;
    vec = vec*vec_(k,0)^(-1);
    n := #algebra.span;
    prod := standardAxialVector(k,n) - vec;
    for i in k+1 .. n-1 do (
        if 1 < i and i < #algebra.span then (
            x := algebra.span#i;
            if member(k,x) then (
                n = #algebra.span;
                if x#0 == k then u := prod
                else u = standardAxialVector(x#0,n);
                if x#1 == k then v := prod
                else v = standardAxialVector(x#1,n);
                newProd := axialProduct(u, v, algebra.products);
                if newProd === false or (newProd != 0 and newProd_(i, 0) == 1) then return false;
                newVec := sub(standardAxialVector(i,n), r) - newProd;
                if quotientNullVec(algebra, newVec) === false then return false;
                );
            );
        );
    n = #algebra.span;
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
        algebra.evecs#ev = findBasis algebra.evecs#ev;
        );
    if algebra#?temp then (
        for ev in keys algebra.temp do (
            algebra.temp#ev = (reduce(algebra.temp#ev, vec, k))^reduction;
            );
        );
    if algebra#?nullspace then (
        algebra.nullspace = (reduce(algebra.nullspace, vec, k))^reduction;
        );
    algebra.span = drop(algebra.span, {k,k});
    n = #algebra.span;
    if any(toList (2..n-1), i -> member(i, algebra.span#i)) then error "here";
    )

reduce = (u, v, k) -> u - v*u^{k}

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
    if n == 1 then return {0};
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
    if f_i =!= null then return sub(standardAxialVector(f_i, n), algebra.coordring);
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
    else im0 =  sub(standardAxialVector(im0, n), algebra.coordring);
    if im0 === false then return false;
    if im1 === null then im1 = imageFlip(x#1, f, algebra)
    else im1 =  sub(standardAxialVector(im1, n), algebra.coordring);
    if im1 === false then return false;
    unknowns := findUnknowns (im0, im1, algebra.products);
    expandAlgebra (algebra, unknowns);
    return axialProduct(im0, im1, algebra.products);
    )

-- Applies polynomial flip to x which can be a polynomial or a vector
flipPoly = (x, algebra) -> (
    r := algebra.coordring;
    k := numgens r - numgens algebra.opts.field;
    k = (k/2)^ZZ;
    for i to (k - 1) do x = sub(x, {r_i => r_(i + k), r_(i + k) => r_i} );
    return x;
    )

-- Applies flip to a vector, changing entries via flipPoly then changing coordinates
flipVector = (vec, algebra) -> (
    -- If we are not assuming a form then the flip switches the indeterminates of the coord ring
    if not algebra.opts.form then vec = flipPoly (vec, algebra);
    -- Now flip the coordinates
    f := findFlip algebra;
    res := sub(zeroAxialVector(#algebra.span), algebra.coordring);
    for i in positions(entries vec, x -> x#0 !=0 ) do (
        im := imageFlip(i, f, algebra);
        if im === false then return false;
        if #algebra.span != numgens target res then (
            res = res || matrix( toList ((#algebra.span - numgens target res):{0}) );
            );
        res = res + im*vec_(i,0);
        );
    res
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
        n := howManyUnknowns algebra;
        findNewEigenvectors algebra;
        findNullVectors algebra;
        print (n, howManyUnknowns algebra);
        if member(howManyUnknowns algebra, {0,n}) then break;
        );
    fusion algebra;
    findNullVectors algebra;
    )

universalDihedralAlgebra = dihedralOpts >> opts -> (evals, tbl) -> (
    algebra := dihedralAlgebraSetup(evals, tbl, opts);
    while howManyUnknowns algebra > 0 do (
        t1 := cpuTime();
        mainLoop algebra;
        print( "Time taken:", cpuTime() - t1 );
        );
    return algebra;
    )

findFactors = polys -> (
    factors := unique apply(toList factor polys#0, x -> x#0);
    factors = select (factors, x -> not isConstant x);
    prod := {};
    for p in toList factors do (
        subpolys := unique apply( polys, x -> x%p );
        subpolys = select( subpolys, x -> x != 0 );
        if #subpolys > 0 then (
            prod = prod | toList((set {p})**(set findFactors( subpolys )));
            )
        else prod = append (prod, {p});
        );
    return apply(prod, x -> flatten toList x);
    )

dihedralAlgebras = dihedralOpts >> opts -> (evals, tbl) -> (
    -- Construct the whole universal algebra
    algebra := universalDihedralAlgebra(evals, tbl, opts);

    -- Might need to go looking for more polynomials
    while true do (
        n := #algebra.polynomials;
        findNullPolys algebra;
        if n == #algebra.polynomials then break;
        );
    -- If still none then return
    if #algebra.polynomials == 0 then (
        print "Warning: could not find dihedral algebras";
        return hashTable{algebras => {algebra}, lambdas => {}};
        );

    -- Change ordering in order to get good gb
    changeRingOfAlgebra (algebra, newRing (algebra.coordring , MonomialOrder => Lex) );
    algebra.polynomials = flatten entries groebnerBasis ideal algebra.polynomials;

    -- Factor polynomials
    factors := findFactors (algebra.polynomials);

    -- Run over each of these roots
    algs := {};
    for p in toList factors do (
        print ("Using factor", p);
        -- Make the new algebra
        newalgebra := new MutableHashTable from {};
        for key in keys algebra do newalgebra#key = algebra#key;
        newalgebra.evecs = copy algebra.evecs;
        newalgebra.products = new MutableList from {};
        for i to #algebra.span - 1 do newalgebra.products#i = copy algebra.products#i;
        -- Use the factor p
        newalgebra.polynomials = toList p;
        quotientNullPolynomials newalgebra;
        findNullVectors newalgebra;
        while howManyUnknowns newalgebra > 0 do mainLoop newalgebra;
        fusion newalgebra;
        findNullVectors newalgebra;
        if #newalgebra.span > 0 then algs = append(algs, newalgebra)
        else factors = delete(p, factors);
        print "Found new algebra";
        );
    return hashTable{algebras => algs, polys => factors};
    )

tauMaps = (algebra, evals, chars) -> (
    n := #algebra.span;
    mat0 := zeroAxialVector n;
    espace := zeroAxialVector n;
    for s in evals do (
        espace = espace | algebra.evecs#(set s);
        );
    espace = espace_{1..n};
    dims := apply(evals, s -> numgens image algebra.evecs#(set s));
    dims = toList apply(0..#dims-1, i -> sum dims_{0..i});
    for i to n - 1 do (
        a := sub(standardAxialVector(i, n), algebra.coordring);
        v := a//espace;
        u = (chars#0)*v^{0..dims#0-1};
        for j from 1 to #chars - 1 do (
            u = u || (chars#j)*v^{dims#(j-1)..dims#j-1};
            );
        mat0 = mat0 | (espace*u);
        );
    mat0 = mat0_{1..n};
    mat1 := new MutableMatrix from mat0;
    f := findFlip algebra;
    for i to n - 1 do (
        for j to n - 1 do (
            im := f_{i,j};
            mat1_(im#0, im#1) = mat0_(i,j);
            );
        );
    return {mat0, matrix mat1};
    )
