
SparseVandermondeMat := function( values, ring )

    local mat, n, i, j;

    n := Size(values);

    mat := SparseZeroMatrix(n, n, ring);

    for i in [1 .. n] do
        for j in [1 .. n] do
            SetEntry(mat, i, j, values[j]^(i-1));
        od;
    od;

    return mat;

end;

FindFirstEigenvectors := function(eigenvalues, ring)

    local mat, ech;

    mat := SparseVandermondeMat( eigenvalues, ring );
    ech := EchelonMatTransformationDestructive(mat);

    return ech.coeffs;

end;

DihedralAlgebrasSetup := function(eigenvalues, fusiontable, ring)

    local n, algebra, ev, first, i, j, sum;

    n := Size(eigenvalues);

    # Set up the algebra record
    algebra := rec( eigenvalues := eigenvalues,
                    fusiontable := fusiontable,
                    ring := ring,
                    flip := [2, 1, 3],
                    eigenvectors := rec(),
                    products := NullMat(n + 1, n + 1) );

    for i in [1 .. n + 1] do
        for j in [1 .. n + 1] do
            algebra.products[i][j] := false;
        od;
    od;

    # The empty eigenvector record (for axis a_0)
    for ev in Filtered(Union(fusiontable), x -> x <> []) do
        algebra.eigenvectors.(String(ev)) := SparseMatrix(0, n + 1, [], [], ring);
    od;

    algebra.null := SparseMatrix(0, n + 1, [], [], Rationals);

    # The spanning set at the moment is a_0, a_1, a_0(a_0a_1), a_0(a_0(a_0a_1)) etc.
    algebra.spanningset := Concatenation( [1, 2], Cartesian([1], [2..n]));

    # The semi-automorphism given by exchanging a_0 and a_1
    algebra.flip := [2, 1, 3];

    # Find first eigenvectors and adjust indices
    first := FindFirstEigenvectors( eigenvalues, ring );
    first!.indices := List(first!.indices, x -> x + 1);

    # Add these eigenvectors to the algebra
    for i in [1 .. Size(eigenvalues)] do
        algebra.eigenvectors.(String([eigenvalues[i]])) := CertainRows(first, [i]);
    od;

    algebra.eigenvectors.(String([1])) := UnionOfRows( algebra.eigenvectors.(String([1])), SparseMatrix(1, n + 1, [ [1] ], [ [One(ring)] ], ring) );

    # We might also need to look at direct sums of eigenspaces coming from the fusion table
    for sum in Union(fusiontable) do
        if Size(sum) > 1 then
            for ev in sum do
                algebra.eigenvectors.(String(sum)) := UnionOfRows( algebra.eigenvectors.(String(sum)), algebra.eigenvectors.(String([ev])) );
            od;
        fi;
    od;

    # TODO What about primitivity?

    # Add known algebra products
    algebra.products[1][1] := SparseMatrix(1, n + 1, [[1]], [[One(ring)]], ring);
    algebra.products[2][2] := SparseMatrix(1, n + 1, [[2]], [[One(ring)]], ring);

    for i in [2 .. n] do
        algebra.products[1][i] := SparseMatrix(1, n + 1, [[i + 1]], [[One(ring)]], ring);
        algebra.products[i][1] := SparseMatrix(1, n + 1, [[i + 1]], [[One(ring)]], ring);
    od;

    return algebra;

end;

DihedralAlgebrasConjugateVec := function(mat, g)

    local  res, i, k, pos;

    # If g is the identity on vec then return
    if ForAll(mat!.indices[1], i -> g[i] = i) then return mat; fi;

    res := SparseMatrix(1, Ncols(mat), [[]], [[]], mat!.ring);

    # Loop over the non-zero indices of vec and add their image to res
    for i in [1..Size(mat!.indices[1])] do

        k := g[mat!.indices[1, i]];

        if k = fail then return fail; fi;

        pos := PositionSorted(res!.indices[1], k);

        Add(res!.indices[1], k, pos);
        Add(res!.entries[1], mat!.entries[1, i], pos);
    od;

    return res;

    end;

## This currently works if the ring is the rationals but need to extend to polynomial rings

DihedralAlgebrasFlip := function(algebra)

    local span, flip, x, im, i, j, new;

    span := Size(algebra.spanningset);
    flip := algebra.flip;

    # First extend the flip permutation
    for x in algebra.spanningset{[Size(flip) + 1 .. span]} do
        im := SortedList(flip{x});
        Add( flip, Position(algebra.spanningset, im) );
    od;

    # Attempt to find new products from flip
    for i in [1 .. span] do
        for j in [1 .. span] do
            im := flip{[i,j]};
            if not fail in im then
                if algebra.products[i, j] <> false and algebra.products[im[1], im[2]] = false then
                    new := DihedralAlgebrasConjugateVec(algebra.products[i, j], flip);
                    if new <> fail then
                        algebra.products[im[1], im[2]] := new;
                    fi;
                fi;
            fi;
        od;
    od;

    # TODO This is ugly
    # TODO Do we want to compare the image under flip to the existing prod?

end;

MAJORANA_NaiveSeparateAlgebraProduct := function( u, v, unknowns, products)

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

end;

DihedralAlgebrasEigenvectorsUnknowns := function(algebra)

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
                algebra.products[pair[1], pair[2]] := eqn[2];
                algebra.products[pair[2], pair[1]] := eqn[2];
            elif Size(eqn[1]!.indices[1]) <> 0 then
                system.mat := UnionOfRows(system.mat, eqn[1]);
                system.vec := UnionOfRows(system.vec, eqn[2]);
            fi;
        od;
    od;

    return system;

end;

DihedralAlgebrasFusion := function(algebra)

    local e, new, i, j, k, evecs_a, evecs_b, unknowns, prod, pos, ev, u, v;

    e := Size(algebra.eigenvalues);

    new := ShallowCopy(algebra.eigenvectors);

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

                    for k in [1..Size(unknowns)] do
                        pos := Position(algebra.spanningset, unknowns[k]);
                        if pos = fail then
                            Add(algebra.spanningset, unknowns[k]);
                            pos := Size(algebra.spanningset);
                        fi;

                        AddToEntry(prod[2], 1, pos, -prod[1]!.entries[1][k]);
                    od;

                    # TODO make all rec names lists and add new vectors to all relevant

                    if Size(ev) = 0 then
                        algebra.null := MAJORANA_AddEvec(algebra.null, prod[2]);
                    else
                        new.(String(ev)) := UnionOfRows(new.(String(ev)), -prod[2]);
                    fi;
                od;
            od;
        od;
    od;

    for ev in RecNames(new) do
        new.(ev)!.ncols := Size(algebra.spanningset);
        new.(ev) := ReversedEchelonMatDestructive(new.(ev)).vectors;
    od;

    algebra.eigenvectors := new;

    algebra.null!.ncols := Size(algebra.spanningset);

end;

DihedralAlgebrasIntersectEigenspaces := function(algebra)

    local span, null, ev, za, x, prod, reduction, i, j;

    span := Size(algebra.spanningset);

    null := algebra.null;

    # Find the intersection of all pairs of known eigenspaces and add to null
    for ev in Combinations( Union(algebra.fusiontable), 2 ) do
        if not [] in ev and Intersection(ev[1], ev[2]) = [] then
            za := SumIntersectionSparseMat( algebra.eigenvectors.(String(ev[1])), algebra.eigenvectors.(String(ev[2])) );
            null := UnionOfRows(null, za[2]);
        fi;
    od;

    null := ReversedEchelonMatDestructive(null);

    # Record any new products from the nullspace
    for i in Reversed([1 .. span]) do
        if null.heads[i] <> 0 then

            x := algebra.spanningset[i];
            prod := CertainRows(null.vectors, [null.heads[i]]);

            # Record new product
            if algebra.products[x[1], x[2]] = false then
                SetEntry(prod, 1, i, Zero(algebra.ring));
                algebra.products[x[1], x[2]] := -prod;
                algebra.products[x[2], x[1]] := -prod;
            elif prod!.indices[1] = [i] then
                algebra.products[x[1], x[2]] := SparseZeroMatrix(1, span, algebra.ring);
                algebra.products[x[2], x[1]] := SparseZeroMatrix(1, span, algebra.ring);
            else
                Error("Need to check equality of new product with old");
            fi;
        fi;
    od;

    # Adjust spanning set, algebra products and eigenvectors to remove nullspace quotient
    reduction := Positions(null.heads, 0);

    algebra.spanningset := algebra.spanningset{reduction};

    for i in [1 .. Size(algebra.products)] do
        for j in [1 .. Size(algebra.products)] do
            if algebra.products[i][j] <> false then
                RemoveMatWithHeads(algebra.products[i][j], null);
                algebra.products[i][j] := CertainColumns(algebra.products[i][j], reduction);
            fi;
        od;
    od;

    for ev in RecNames(algebra.eigenvectors) do
        algebra.eigenvectors.(ev) := RemoveMatWithHeads(algebra.eigenvectors.(ev), null);
        algebra.eigenvectors.(ev) := CertainColumns(algebra.eigenvectors.(ev), reduction);
        algebra.eigenvectors.(ev) := ReversedEchelonMatDestructive(algebra.eigenvectors.(ev)).vectors;
    od;

    algebra.null := SparseMatrix(0, Size(algebra.spanningset), [], [], algebra.ring);

end;

DihedralAlgebras := function(eigenvalues, fusiontable, ring)

    local algebra;

    algebra := DihedralAlgebrasSetup(eigenvalues, fusiontable, ring);

    DihedralAlgebrasEigenvectorsUnknowns(algebra);
    DihedralAlgebrasFlip(algebra);
    DihedralAlgebrasFusion(algebra);
    DihedralAlgebrasIntersectEigenspaces(algebra);

    return algebra;

end;

JordanTable := function(nu)

    return [ [ [1], [], [nu] ], [ [], [0], [nu] ], [ [nu], [nu], [1, 0] ] ];

end;
