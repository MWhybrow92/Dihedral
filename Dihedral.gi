
InstallGlobalFunction( SparseVandermondeMat, function( values, ring )

    local mat, n, i, j;

    n := Size(values);

    mat := SparseZeroMatrix(n, n, ring);

    for i in [1 .. n] do
        for j in [1 .. n] do
            SetEntry(mat, i, j, values[j]^(i-1));
        od;
    od;

    return mat;

end );

InstallGlobalFunction( FindFirstEigenvectors, function(eigenvalues, ring)

    local mat, ech;

    mat := SparseVandermondeMat( eigenvalues, ring );
    ech := EchelonMatTransformationDestructive(mat);

    return ech.coeffs;

end );

InstallGlobalFunction( FindFlip, function(algebra)

    local span, flip, x, im;

    span := Size(algebra.spanningset);
    flip := [2, 1, 3];

    # Extend the flip permutation
    for x in algebra.spanningset{[4 .. span]} do
        im := SortedList(flip{x});
        Add( flip, Position(algebra.spanningset, im) );
    od;

    return flip;

end );

InstallGlobalFunction( DihedralAlgebrasFlip, function(algebra)

    local flip, x, im, i, j, new;

    flip := FindFlip(algebra);

    # Attempt to find new products from flip
    for i in [1 .. Size(algebra.spanningset)] do
        if i <= Size(algebra.spanningset) then
            for j in [1 .. Size(algebra.spanningset)] do
                if j <= Size(algebra.spanningset) then
                    im := flip{[i,j]};
                    if not fail in im then
                        if algebra.products[i, j] <> false then

                            new := DihedralAlgebrasFlipVector(algebra.products[i, j], flip, algebra);
                            flip := FindFlip(algebra);

                            if algebra.products[im[1], im[2]] = false then
                                algebra.products[im[1], im[2]] := new;
                                algebra.products[im[2], im[1]] := new;
                            elif algebra.products[im[1], im[2]] <> new then
                                DihedralAlgebrasRemoveNullVec(new - algebra.products[im[1], im[2]], algebra);
                            fi;

                        fi;
                    fi;
                fi;
            od;
        fi;
    od;

end );

InstallGlobalFunction( DihedralAlgebrasSolvePolynomial, function(poly, algebra)

    local rep, monomials, var, pos, coeff, new, x;

    rep := ExtRepPolynomialRatFun(poly);
    monomials := rep{[1, 3 .. Size(rep) - 1]};

    # If poly contains any multivariate monomials then we can't solve it
    if ForAny(monomials, x -> Size(x) > 2) then
        coeff := rep[Size(rep)];
        if Inverse(coeff)*One(algebra.ring) in algebra.ring then
            poly := poly*Inverse(coeff);
        fi;
        if not poly in algebra.polynomials then
            Add(algebra.polynomials, poly);
        fi;
        return;
    fi;

    # If the poly is linear in either of the indeterminants then we can solve it
    if Size( Filtered(monomials, x -> x[1] = 2) ) = 1 and [2, 1] in monomials then
        var := 2;
        pos := Position(rep, [2,1] );
    elif Size( Filtered(monomials, x -> x[1] = 1) ) = 1 and [1, 1] in monomials then
        var := 1;
        pos := Position(rep, [1,1] );
    else
        coeff := rep[Size(rep)];
        if Inverse(coeff)*One(algebra.ring) in algebra.ring then
            poly := poly*Inverse(coeff);
        fi;
        if not poly in algebra.polynomials then
            Add(algebra.polynomials, poly);
        fi;
        return;
    fi;

    coeff := rep[pos + 1];

    if not Inverse(coeff)*One(algebra.ring) in algebra.ring then
        Error("Cannot solve polynomial");
    fi;

    x := IndeterminatesOfPolynomialRing(algebra.ring);

    new := poly*Inverse(coeff);
    new := x[var] - new;

    # Substitute the new value into products and eigenvectors
    DihedralAlgebrasValue([x[var]], [new], algebra);

    if Size(x) = 1 then
        DihedralAlgebrasChangeRing( algebra, algebra.coefficients );
    elif var = 2 then
        DihedralAlgebrasChangeRing( algebra, PolynomialRing(algebra.coefficients, 1) );
    elif var = 1 then
        DihedralAlgebrasValue( algebra, [x[2]], [x[1]]);
        DihedralAlgebrasChangeRing( algebra, PolynomialRing(algebra.coefficients, 1) );
    fi;

end );

InstallGlobalFunction( DihedralAlgebrasValue, function(indets, vals, algebra)

    local i, j, k, entries, ev;

    for i in [1 .. Size(algebra.products)] do
        for j in [1 .. Size(algebra.products[i])] do
            entries := algebra.products[i,j]!.entries[1];
            for k in [1.. Size(entries)] do
                entries[k] := Value(entries[k], indets, vals );
                entries[k] := entries[k]*One(algebra.ring);
                if entries[k] = Zero(algebra.ring) then
                    Unbind(entries[k]);
                    Remove(algebra.products[i,j]!.indices[1], k);
                fi;
                algebra.products[i,j]!.entries[1] := Compacted(entries);
            od;
        od;
    od;

    for ev in RecNames(algebra.eigenvectors) do
        for i in [1 .. Nrows(algebra.eigenvectors.(ev))] do
            entries := algebra.eigenvectors.(ev)!.entries[i];
            for k in [1 .. Size(entries)] do
                if not entries[k] in algebra.ring then Error(); fi;
                entries[k] := Value(entries[k], indets, vals );
                entries[k] := entries[k]*One(algebra.ring);
                if entries[k] = Zero(algebra.ring) then
                    Unbind(entries[k]);
                    Remove(algebra.eigenvectors.(ev)!.indices[i], k);
                fi;
                algebra.eigenvectors.(ev)!.entries[i] := Compacted(entries);
            od;
        od;
    od;

    algebra.polynomials := List(algebra.polynomials, p -> Value(p, indets, vals ));
    algebra.polynomials := DuplicateFreeList(algebra.polynomials)*One(algebra.ring);

end );

InstallGlobalFunction( DihedralAlgebrasRemoveNullVec, function(null, algebra)

    local i, j, x, prod, reduction, ev, span, n, entry, k, u, v, new;

    if null!.entries[1] = [] then return; fi;

    span := Size( algebra.spanningset );
    n := Size( null!.entries[1] );
    k := null!.indices[1, n];

    entry := null!.entries[1, n];

    if k in [1, 2] then
        if IsConstantRationalFunction(entry) then
            Error("Algebra is one or zero dimensional");
        else
            DihedralAlgebrasSolvePolynomial(entry, algebra);
            return;
        fi;
    fi;

    if Inverse(entry) in algebra.ring then
        null!.entries := null!.entries*Inverse(entry);
    elif n = 1 and not IsConstantRationalFunction(entry) then
        DihedralAlgebrasSolvePolynomial(entry, algebra);
        return;
    else
        Error("Non invertible nullspace vec, what do we do?");
    fi;

    x := algebra.spanningset[ k ];
    prod := CopyMat(-null);

    # Record new product
    if algebra.products[x[1], x[2]] = false then
        SetEntry(prod, 1, k, Zero(algebra.ring));
        algebra.products[x[1], x[2]] := prod;
        algebra.products[x[2], x[1]] := prod;
    elif prod!.indices[1] = [span] then
        algebra.products[x[1], x[2]] := SparseZeroMatrix(1, span, algebra.ring);
        algebra.products[x[2], x[1]] := SparseZeroMatrix(1, span, algebra.ring);
    fi;

    # Correct the spanning set labels
    for i in [ k + 1 .. span ] do
        x := algebra.spanningset[i];
        if k in x then
            if x[1] = k then
                u := prod;
            else
                u := SparseMatrix(1, span, [[ x[1] ]], [[ One(algebra.ring) ]], algebra.ring);
            fi;

            if x[2] = k then
                v := prod;
            else
                v := SparseMatrix(1, span, [[ x[2] ]], [[ One(algebra.ring) ]], algebra.ring);
            fi;

            new := MAJORANA_NaiveProduct(u, v, algebra.products);

            if new = false then Error("Can't find product - what do we do?"); fi;

            new := SparseMatrix(1, span, [[i]], [[One(algebra.ring)]], algebra.ring) - new;

            DihedralAlgebrasRemoveNullVec(new, algebra);
        fi;
    od;

    span := Size(algebra.spanningset);

    for i in [ k + 1 .. span ] do
        # if x[1] > k then OLD VERSION but I think that this is wrong
        if algebra.spanningset[i, 1] > k then
            algebra.spanningset[i, 1] := algebra.spanningset[i, 1] - 1;
        fi;
        if algebra.spanningset[i, 2] > k then
            algebra.spanningset[i, 2] := algebra.spanningset[i, 2] - 1;
        fi;
    od;

    reduction := Difference([1 .. span], [k]);
    Remove(algebra.spanningset, k);

    # Remove the null vector from products and eigenvectors
    null := ReversedEchelonMatDestructive_Ring(null);
    Remove(algebra.products, k);

    for i in [1 .. Size(algebra.products)] do
        Remove(algebra.products[i], k);
        for j in [1 .. Size(algebra.products[i])] do
            if algebra.products[i][j] <> false then
                RemoveMatWithHeads(algebra.products[i][j], null);
                algebra.products[i,j] := CertainColumns(algebra.products[i,j], reduction);
            fi;
        od;
    od;

    for ev in RecNames(algebra.eigenvectors) do
        algebra.eigenvectors.(ev) := RemoveMatWithHeads(algebra.eigenvectors.(ev), null);
        algebra.eigenvectors.(ev) := CertainColumns(algebra.eigenvectors.(ev), reduction);
        algebra.eigenvectors.(ev) := ReversedEchelonMatDestructive_Ring(algebra.eigenvectors.(ev)).vectors;
    od;

    if IsBound(algebra.new) then
        for ev in RecNames(algebra.new) do
            algebra.new.(ev) := RemoveMatWithHeads(algebra.new.(ev), null);
            algebra.new.(ev) := CertainColumns(algebra.new.(ev), reduction);
            algebra.new.(ev) := ReversedEchelonMatDestructive_Ring(algebra.new.(ev)).vectors;
        od;
    fi;

end );

InstallGlobalFunction( DihedralAlgebrasChangeRing, function( algebra, ring )

    local ev, i, j;

    for ev in RecNames(algebra.eigenvectors) do
        algebra.eigenvectors.(ev)!.entries := algebra.eigenvectors.(ev)!.entries*One(ring);
        algebra.eigenvectors.(ev)!.ring := ring;
    od;

    for i in [1..Size(algebra.products)] do
        for j in [1..Size(algebra.products)] do
            if algebra.products[i][j] <> false then
                algebra.products[i][j]!.entries := algebra.products[i][j]!.entries*One(ring);
                algebra.products[i][j]!.ring := ring;
            fi;
        od;
    od;

    algebra.ring := ring;

end );

InstallGlobalFunction( DihedralAlgebrasSetup, function(eigenvalues, fusiontable, ring, primitive)

    local n, algebra, ev, first, i, j, k, sum, null, ind, v, coeffs;

    n := Size(eigenvalues);

    # Set up the algebra record
    algebra := rec( eigenvalues := eigenvalues,
                    fusiontable := fusiontable,
                    coefficients := ring,
                    ring := ring,
                    eigenvectors := rec(),
                    products := NullMat(n + 1, n + 1),
                    polynomials := [],
                    primitive := primitive );

    for i in [1 .. n + 1] do
        for j in [1 .. n + 1] do
            algebra.products[i][j] := false;
        od;
    od;

    # Add known algebra products
    algebra.products[1][1] := SparseMatrix(1, n + 1, [[1]], [[One(ring)]], ring);
    algebra.products[2][2] := SparseMatrix(1, n + 1, [[2]], [[One(ring)]], ring);

    for i in [2 .. n] do
        algebra.products[1][i] := SparseMatrix(1, n + 1, [[i + 1]], [[One(ring)]], ring);
        algebra.products[i][1] := SparseMatrix(1, n + 1, [[i + 1]], [[One(ring)]], ring);
    od;

    # The empty eigenvector record (for axis a_0)
    for ev in Filtered(Union(fusiontable), x -> x <> []) do
        algebra.eigenvectors.(String(ev)) := SparseMatrix(0, n + 1, [], [], ring);
    od;

    # The spanning set at the moment is a_0, a_1, a_0(a_0a_1), a_0(a_0(a_0a_1)) etc.
    algebra.spanningset := Concatenation( [1, 2], Cartesian([1], [2..n]));

    # Find first eigenvectors and adjust indices
    first := FindFirstEigenvectors( eigenvalues, ring );
    first!.indices := List(first!.indices, x -> x + 1);
    first!.ncols := n + 1;

    # Add these eigenvectors to the algebra
    for i in [1 .. Size(eigenvalues)] do
        algebra.eigenvectors.(String([eigenvalues[i]])) := CertainRows(first, [i]);
    od;

    if primitive = true then
        DihedralAlgebrasChangeRing( algebra, PolynomialRing(algebra.ring, 2) );

        ind := IndeterminatesOfPolynomialRing(algebra.ring);

        null := CertainRows( algebra.eigenvectors.(String([1])), [1] );
        null := null - SparseMatrix(1, n + 1, [[1]], [[ind[1]]], algebra.ring);

        DihedralAlgebrasRemoveNullVec(null, algebra);

        # Finish off recording eigenvectors
        algebra.eigenvectors.(String([1])) := SparseMatrix(1, n, [ [1] ], [ [One(algebra.ring)] ], algebra.ring );
    else
        algebra.eigenvectors.(String([1])) := UnionOfRows(algebra.eigenvectors.(String([1])), SparseMatrix(1, n, [ [1] ], [ [One(algebra.ring)] ], algebra.ring ) );
    fi;

    # We might also need to look at direct sums of eigenspaces coming from the fusion table
    for sum in Union(fusiontable) do
        if Size(sum) > 1 then
            for ev in sum do
                algebra.eigenvectors.(String(sum)) := UnionOfRows( algebra.eigenvectors.(String(sum)), algebra.eigenvectors.(String([ev])) );
            od;
        fi;
    od;

    DihedralAlgebrasFlip(algebra);

    return algebra;

end );

InstallGlobalFunction( DihedralAlgebrasExpand, function(algebra)

    local i, j, ev, span;

    span := Size(algebra.spanningset);

    for i in [1 .. span] do
        if IsBound(algebra.products[i]) then
            for j in [Size(algebra.products) + 1 .. span] do
                algebra.products[i, j] := false;
            od;
        else
            algebra.products[i] := List( algebra.spanningset, x -> false );
        fi;
    od;

    for i in [1 .. Size(algebra.products)] do
        for j in [1 .. Size(algebra.products)] do
            if algebra.products[i, j] <> false then
                algebra.products[i, j]!.ncols := span;
            fi;
        od;
    od;

    for ev in RecNames(algebra.eigenvectors) do
        algebra.eigenvectors.(ev)!.ncols := span;
    od;

end );

InstallGlobalFunction( DihedralAlgebrasFlipPolynomial, function(poly, algebra)

    if algebra.ring = algebra.coefficients then return poly; fi;
    if Size(IndeterminatesOfPolynomialRing(algebra.ring)) < 2 then return poly; fi;

    return OnIndeterminates(poly, (1,2));

end );

InstallGlobalFunction( DihedralAlgebrasFlipVector, function(mat, g, algebra)

    local  span, ring, res, i, k, pos, coeff, prod, im;

    span := Size(algebra.spanningset);
    ring := algebra.ring;

    res := SparseMatrix(1, span, [[]], [[]], ring);

    # Loop over the non-zero indices of vec and add their image to res
    for i in [1..Size(mat!.indices[1])] do

        coeff := mat!.entries[1,i];

        if algebra.primitive then
            # If the coefficient is a polynomial in \phi and \phi' then the flip exchanges the two values
            coeff := DihedralAlgebrasFlipPolynomial(coeff, algebra);
        fi;

        # Now find where the spanning set vector is sent to
        k := g[mat!.indices[1, i]];

        if k = fail then
            # If the image of mat!.indices[1, i] gives an algebra product that is already known then use this as a vector
            # Otherwise, add the image to the spanning set
            im := g{algebra.spanningset[mat!.indices[1,i]]};

            if fail in im then Error("Can't find image of spanning set vector under flip"); fi;

            prod := algebra.products[im[1], im[2]];

            if prod <> false then
                res := res + coeff*prod;
            else
                Add(algebra.spanningset, SortedList(im));
                DihedralAlgebrasExpand(algebra);
                span := span + 1;
                res!.ncols := span;
                res := res + coeff*SparseMatrix(1, span, [[Size(algebra.spanningset)]], [[One(ring)]], ring );
            fi;

        else
            res := res + coeff*SparseMatrix(1, span, [[k]], [[One(ring)]], ring );
        fi;
    od;

    return res;

    end );

InstallGlobalFunction( MAJORANA_NaiveSeparateAlgebraProduct, function( u, v, unknowns, products)

    local span, lhs, rhs, i, j, pair, pos, prod;

    span := u!.ncols;

    lhs := SparseMatrix(1, Size(unknowns), [[]], [[]], u!.ring );
    rhs := SparseMatrix(1, span, [[]], [[]], u!.ring);

    for i in [1 .. Size(u!.indices[1])] do
        for j in [1 .. Size(v!.indices[1])] do

            prod := products[u!.indices[1, i]][v!.indices[1,j]];

            if prod <> false then
                rhs := rhs - u!.entries[1, i]*v!.entries[1, j]*prod;
            else
                pair := [u!.indices[1, i], v!.indices[1, j]];
                Sort(pair);

                pos := Position(unknowns,pair);

                if pos = fail then
                    Add(unknowns, pair); pos := Size(unknowns);
                fi;

                AddToEntry(lhs, 1, pos, u!.entries[1, i]*v!.entries[1, j]);
            fi;
        od;
    od;

    return [lhs, rhs];

end );

InstallGlobalFunction( DihedralAlgebrasSolutionProducts, function(system, algebra)

    local i, j, x, prod, pos, elm, nonzero_rows;

    # If the matrix is zero then return
    if ForAll(system.mat!.indices, x -> x = []) then return; fi;

    MAJORANA_SolveSystem(system);

    if ForAll(system.solutions, x -> x = fail) then
        Unbind(system.solutions);
        return;
    fi;

    for i in [1 .. Size(system.solutions)] do
        if system.solutions[i] <> fail then

            x := system.unknowns[i];
            prod := system.solutions[i];

            algebra.products[x[1], x[2]] := prod;
            algebra.products[x[2], x[1]] := prod;

            for j in [1..Nrows(system.vec)] do
                pos := Position(system.mat!.indices[j], i);
                if pos <> fail then
                    elm := system.mat!.entries[j, pos];
                    AddRow(prod!.indices[1], elm*prod!.entries[1], system.vec!.indices, system.vec!.entries);
                fi;
            od;
        fi;
    od;

    # I don't think that this is necessary:

    # system.mat := CertainColumns(system.mat, Positions(system.solutions, fail) );
    # system.unknowns := system.unknowns{ Positions(system.solutions, fail) };

    # Unbind(system.solutions);

    # nonzero_rows := Filtered([1..Nrows(system.mat)], j -> system.mat!.indices[j] <> []);
    # system.mat := CertainRows(system.mat, nonzero_rows);
    # system.vec := CertainRows(system.vec, nonzero_rows);



end );

InstallGlobalFunction( DihedralAlgebrasEigenvectorsUnknowns, function(algebra)

    local span, ring, u, system, v, eqn, ev, pair;

    span := Size(algebra.spanningset);
    ring := algebra.ring;

    u := SparseMatrix(1, span, [[1]], [[One(ring)]], ring);

    system := rec(  mat := SparseMatrix(0, 0, [], [], ring),
                    vec := SparseMatrix(0, span, [], [], ring),
                    unknowns := [] );

    for ev in algebra.eigenvalues do
        for v in algebra.eigenvectors.(String([ev])) do
            eqn := MAJORANA_NaiveSeparateAlgebraProduct(u, v, system.unknowns, algebra.products);
            eqn[2] := eqn[2] + ev*v;

            if Size(eqn[1]!.indices[1]) = 1 then
                pair := system.unknowns[eqn[1]!.indices[1][1]];
                algebra.products[pair[1], pair[2]] := eqn[2]*(1/eqn[1]!.entries[1][1]);
                algebra.products[pair[2], pair[1]] := eqn[2]*(1/eqn[1]!.entries[1][1]);
            elif Size(eqn[1]!.indices[1]) <> 0 then
                system.mat := UnionOfRows(system.mat, eqn[1]);
                system.vec := UnionOfRows(system.vec, eqn[2]);
            fi;
        od;
    od;

    system.mat!.ncols := Size(system.unknowns);

    DihedralAlgebrasSolutionProducts(system, algebra);

    DihedralAlgebrasFlip(algebra);

    return system;

end );

InstallGlobalFunction( DihedralAlgebrasFindNullVecs, function(algebra)

    local span, a, ev, v, null;

    span := Size(algebra.spanningset);

    a := SparseMatrix( 1, span, [[1]], [[One(algebra.ring)]], algebra.ring );

    for ev in algebra.eigenvalues do
        for v in algebra.eigenvectors.(String([ev])) do
            null := MAJORANA_NaiveProduct(a, v, algebra.products);
            if null <> false then
                null := null - ev*v;
                DihedralAlgebrasRemoveNullVec(null, algebra);
            fi;
        od;
    od;

    DihedralAlgebrasFlip(algebra);

end );

InstallGlobalFunction( DihedralAlgebrasFusion, function(algebra, expand)

    local e, i, j, k, evecs_a, evecs_b, unknowns, prod, pos, ev, u, v, sum, x;

    e := Size(algebra.eigenvalues);

    algebra.new := ShallowCopy(algebra.eigenvectors);

    # TODO we could make this for Union(fusiontable) then find union of table entries?
    for i in [1 .. e] do
        evecs_a := algebra.eigenvectors.(String([algebra.eigenvalues[i]]));
        for j in [i .. e] do
            evecs_b := algebra.eigenvectors.(String([algebra.eigenvalues[j]]));

            ev := algebra.fusiontable[i][j];

            for u in evecs_a do
                for v in evecs_b do

                    unknowns := [];
                    prod := MAJORANA_NaiveSeparateAlgebraProduct( u, v, unknowns, algebra.products);

                    if expand = true then
                        for x in unknowns do
                            pos := Position(algebra.spanningset, x);
                            if pos = fail then
                                Add(algebra.spanningset, x);
                                DihedralAlgebrasExpand(algebra);

                                pos := Size(algebra.spanningset);
                                algebra.products[x[1], x[2]] := SparseMatrix(1, pos, [[pos]], [[One(algebra.ring)]], algebra.ring);
                                algebra.products[x[2], x[1]] := SparseMatrix(1, pos, [[pos]], [[One(algebra.ring)]], algebra.ring);
                            fi;

                            AddToEntry(prod[2], 1, pos, -prod[1]!.entries[1][Position(unknowns, x)]);
                        od;

                        unknowns := [];

                        prod[2]!.ncols := Size(algebra.spanningset);
                    fi;

                    if unknowns = [] then
                        if Size(ev) = 0 then
                            DihedralAlgebrasRemoveNullVec(prod[2], algebra);
                        else
                            for sum in Union(algebra.fusiontable) do
                                if IsSubset(sum, ev) then
                                    algebra.new.(String(sum)) :=  DihedralAlgebrasAddEvec( algebra.new.(String(sum)), -prod[2] );
                                fi;
                            od;
                        fi;
                    fi;
                od;
            od;
        od;
    od;

    for ev in RecNames(algebra.new) do
        algebra.new.(ev)!.ncols := Size(algebra.spanningset);
        algebra.eigenvectors.(ev) := CopyMat(EchelonMat_Ring(algebra.new.(ev)).vectors);
    od;

    Unbind(algebra.new);

    DihedralAlgebrasFlip(algebra);

end );

InstallGlobalFunction( DihedralAlgebrasAddEvec, function ( mat, x )

    local coeff;

    if x!.indices[1] = [  ] then
        return mat;
    fi;

    coeff := x!.entries[1, Size( x!.entries[1] )];

    if false and Inverse(coeff) in mat!.ring then
        x!.entries := x!.entries*Inverse(coeff);
    fi;

    if _IsRowOfSparseMatrix( mat, x ) then
        return mat;
    else
        return UnionOfRows( mat, x );
    fi;
    return;
end );


InstallGlobalFunction( DihedralAlgebrasIntersectEigenspaces, function(algebra)

    local span, null, ev, za, v;

    span := Size(algebra.spanningset);

    null := SparseMatrix(0, span, [], [], algebra.ring);

    # Find the intersection of all pairs of known eigenspaces and add to null
    for ev in Combinations( Union(algebra.fusiontable), 2 ) do
        if not [] in ev and Intersection(ev[1], ev[2]) = [] then
            za := SumIntersectionSparseMat( algebra.eigenvectors.(String(ev[1])), algebra.eigenvectors.(String(ev[2])) );
            for v in za[2] do
                null := DihedralAlgebrasAddEvec(null, za[2]);
            od;
        fi;
    od;

    # TODO this should be _ring but it doesn't actually give them in reversed order here
    null := ReversedEchelonMatDestructive_Ring(null).vectors;

    for v in null do
        DihedralAlgebrasRemoveNullVec(v, algebra);
    od;

    DihedralAlgebrasFlip(algebra);

end );

InstallGlobalFunction( DihedralAlgebrasMainLoop, function(algebra)

    local count, span;

    # See if we can find more algebra products without expanding the algebra

    while true do
        count := Sum( List(algebra.products, x -> Size(Positions(x, false))) );
        span := Size(algebra.spanningset);

        DihedralAlgebrasFusion(algebra, false); # This bit might not be necessary
        DihedralAlgebrasIntersectEigenspaces(algebra);
        DihedralAlgebrasEigenvectorsUnknowns(algebra);
        DihedralAlgebrasFindNullVecs(algebra);

        if count = Sum( List(algebra.products, x -> Size(Positions(x, false))) ) and span = Size(algebra.spanningset) then
            return;
        fi;
    od;

end );

InstallGlobalFunction( DihedralAlgebras, function(eigenvalues, fusiontable, ring, primitive)

    local algebra;

    algebra := DihedralAlgebrasSetup(eigenvalues, fusiontable, ring, primitive);
    DihedralAlgebrasMainLoop(algebra);

    while ForAny(algebra.products, x -> false in x) do
        DihedralAlgebrasFusion(algebra, true);
        DihedralAlgebrasMainLoop(algebra);
    od;

    DihedralAlgebrasMainLoop(algebra);

    return algebra;

end );

InstallGlobalFunction( JordanTable, function(nu)

    return [ [ [1], [], [nu] ], [ [], [0], [nu] ], [ [nu], [nu], [1, 0] ] ];

end );
