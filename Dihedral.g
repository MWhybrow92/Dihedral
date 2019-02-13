
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

DihedralAlgebrasRemoveNullspace := function(null, algebra)

    local i, j, x, prod, reduction, ev, span;

    span := Size(algebra.spanningset);
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
                # Error("Need to check equality of new product with old");
                # This should be picked up in remove mat with heads below
            fi;
        fi;
    od;

    # Adjust spanning set, algebra products and eigenvectors to remove nullspace quotient
    reduction := Positions(null.heads, 0);

    if reduction <> [1 .. Size(reduction)] then
        Error("Problem with nullspace vectors");
    fi;

    algebra.spanningset := algebra.spanningset{reduction};

    algebra.products := algebra.products{reduction};

    for i in [1 .. Size(algebra.products)] do
        algebra.products[i] := algebra.products[i]{reduction};
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

DihedralAlgebrasChangeRing := function( algebra, ring )

    local ev, i, j;

    for ev in RecNames(algebra.eigenvectors) do
        algebra.eigenvectors.(ev)!.entries := algebra.eigenvectors.(ev)!.entries*One(ring);
        algebra.eigenvectors.(ev)!.ring := ring;
    od;

    if IsBound(algebra.null) then
        algebra.null!.entries := algebra.null!.entries*One(ring);
        algebra.null!.ring := ring;
    fi;

    for i in [1..Size(algebra.products)] do
        for j in [1..Size(algebra.products)] do
            if algebra.products[i][j] <> false then
                algebra.products[i][j]!.entries := algebra.products[i][j]!.entries*One(ring);
                algebra.products[i][j]!.ring := ring;
            fi;
        od;
    od;

    algebra.ring := ring;

end;

DihedralAlgebrasSetup := function(eigenvalues, fusiontable, ring)

    local n, algebra, ev, first, i, j, k, sum, null, ind, v, coeffs;

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

    algebra.null := SparseMatrix(0, n + 1, [], [], Rationals);

    # The spanning set at the moment is a_0, a_1, a_0(a_0a_1), a_0(a_0(a_0a_1)) etc.
    algebra.spanningset := Concatenation( [1, 2], Cartesian([1], [2..n]));

    # The semi-automorphism given by exchanging a_0 and a_1
    algebra.flip := [2, 1, 3];

    # Find first eigenvectors and adjust indices
    first := FindFirstEigenvectors( eigenvalues, ring );
    first!.indices := List(first!.indices, x -> x + 1);
    first!.ncols := n + 1;

    # Add these eigenvectors to the algebra
    for i in [1 .. Size(eigenvalues)] do
        algebra.eigenvectors.(String([eigenvalues[i]])) := ReversedEchelonMatDestructive(CertainRows(first, [i])).vectors;
    od;

    # Assume primitivity for now
    DihedralAlgebrasChangeRing( algebra, FunctionField(algebra.ring, 2) );

    ind := IndeterminatesOfFunctionField(algebra.ring);
    null := SparseMatrix(0, n + 1, [], [], algebra.ring);

    v := CertainRows( algebra.eigenvectors.(String([1])), [1] );
    v := v - SparseMatrix(1, n + 1, [[1]], [[ind[1]]], algebra.ring);
    null := UnionOfRows(null, v);

    DihedralAlgebrasRemoveNullspace(null, algebra);

    # Finish off recording eigenvectors
    algebra.eigenvectors.(String([1])) := SparseMatrix(1, n, [ [1] ], [ [One(ring)] ], algebra.ring );

    # We might also need to look at direct sums of eigenspaces coming from the fusion table
    for sum in Union(fusiontable) do
        if Size(sum) > 1 then
            for ev in sum do
                algebra.eigenvectors.(String(sum)) := UnionOfRows( algebra.eigenvectors.(String(sum)), algebra.eigenvectors.(String([ev])) );
            od;
        fi;
    od;

    return algebra;

end;

DihedralAlgebrasFlipPolynomial := function(poly)

    local num, den, x, i, j;

    if IsConstantRationalFunction(poly) then return poly; fi;

    num := List(ExtRepNumeratorRatFun(poly), ShallowCopy);
    den := List(ExtRepDenominatorRatFun(poly), ShallowCopy);

    for x in [num, den] do
        for i in [1, 3 .. Size(x) - 1] do
            for j in [1, 3 .. Size(x[i]) - 1] do
                if x[i][j] = 2 then
                    x[i][j] := 1;
                elif x[i][j] = 1 then
                    x[i][j] := 2;
                else
                    Error("Polynomial has too many variables");
                fi;
            od;
        od;
    od;

    return RationalFunctionByExtRep(RationalFunctionsFamily(FamilyObj(1)), num, den);

end;

DihedralAlgebrasFlipVector := function(mat, g, algebra)

    local  span, ring, res, i, k, pos, coeff, prod, im;

    span := Ncols(mat);
    ring := mat!.ring;

    res := SparseMatrix(1, span, [[]], [[]], ring);

    # Loop over the non-zero indices of vec and add their image to res
    for i in [1..Size(mat!.indices[1])] do

        # If the coefficient is a polynomial in \phi and \phi' then the flip exchanges the two values
        coeff := DihedralAlgebrasFlipPolynomial(mat!.entries[1,i]);

        # Now find where the spanning set vector is sent to
        k := g[mat!.indices[1, i]];

        if k = fail then
            # If the image of mat!.indices[1, i] gives an algebra product that is already known then use this as a vector
            # Otherwise, add the image to the spanning set
            im := g{algebra.spanning[mat!.indices[1,i]]};

            if fail in im then Error("Can't find image of spanning set vector under flip"); fi;

            prod := algebra.producs[im[1], im[2]];

            if prod <> false then
                res := res + coeff*prod;
            else
                Add(algebra.spanningset, SortedList(im));
                res := res + coeff*SparseMatrix(1, span, [[Size(algebra.spanningset)]], [[One(ring)]], ring );
            fi;

        else
            res := res + coeff*SparseMatrix(1, span, [[k]], [[One(ring)]], ring );
        fi;
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
                if algebra.products[i, j] <> false then
                    new := DihedralAlgebrasFlipVector(algebra.products[i, j], flip, algebra);
                    if algebra.products[im[1], im[2]] = false then
                        algebra.products[im[1], im[2]] := new;
                        algebra.products[im[2], im[1]] := new;
                    elif algebra.products[im[1], im[2]] <> new then
                        Error("Need to put this product into nullspace");
                    fi;
                fi;
            fi;
        od;
    od;

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

DihedralAlgebrasSolutionProducts := function(system, algebra)

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

    system.mat := CertainColumns(system.mat, Positions(system.solutions, fail) );
    system.unknowns := system.unknowns{ Positions(system.solutions, fail) };

    Unbind(system.solutions);

    nonzero_rows := Filtered([1..Nrows(system.mat)], j -> system.mat!.indices[j] <> []);
    system.mat := CertainRows(system.mat, nonzero_rows);
    system.vec := CertainRows(system.vec, nonzero_rows);

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

    return system;

end;

DihedralAlgebrasFusion := function(algebra, expand)

    local e, new, i, j, k, evecs_a, evecs_b, unknowns, prod, pos, ev, u, v, sum, x;

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

                    if expand = true then
                        for x in unknowns do
                            pos := Position(algebra.spanningset, x);
                            if pos = fail then
                                Add(algebra.spanningset, x);
                                pos := Size(algebra.spanningset);
                                algebra.products[x[1], x[2]] := SparseMatrix(1, pos, [[pos]], [[One(algebra.ring)]], algebra.ring);
                                algebra.products[x[2], x[1]] := SparseMatrix(1, pos, [[pos]], [[One(algebra.ring)]], algebra.ring);
                            fi;

                            AddToEntry(prod[2], 1, pos, -prod[1]!.entries[1][Position(unknowns, x)]);
                        od;

                        unknowns := [];
                    fi;

                    if unknowns = [] then
                        if Size(ev) = 0 then
                            algebra.null := MAJORANA_AddEvec(algebra.null, prod[2]);
                        else
                            for sum in Union(algebra.fusiontable) do
                                if IsSubset(sum, ev) then
                                    new.(String(sum)) := UnionOfRows(new.(String(sum)), -prod[2]);
                                fi;
                            od;
                        fi;
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

    local span, null, ev, za;

    span := Size(algebra.spanningset);

    null := algebra.null;

    # Find the intersection of all pairs of known eigenspaces and add to null
    for ev in Combinations( Union(algebra.fusiontable), 2 ) do
        if not [] in ev and Intersection(ev[1], ev[2]) = [] then
            za := SumIntersectionSparseMat( algebra.eigenvectors.(String(ev[1])), algebra.eigenvectors.(String(ev[2])) );
            null := UnionOfRows(null, za[2]);
        fi;
    od;

    DihedralAlgebrasRemoveNullspace(null, algebra);

end;

DihedralAlgebrasExpand := function(algebra)

    local i, j;

    for i in [1 .. Size(algebra.spanningset)] do
        if IsBound(algebra.products[i]) then
            for j in [Size(algebra.products) + 1 .. Size(algebra.spanningset)] do
                algebra.products[i, j] := false;
            od;
        else
            algebra.products[i] := List( algebra.spanningset, x -> false );
        fi;
    od;

end;

DihedralAlgebrasMainLoop := function(algebra)

    DihedralAlgebrasEigenvectorsUnknowns(algebra);
    DihedralAlgebrasFlip(algebra);
    DihedralAlgebrasFusion(algebra, true);
    DihedralAlgebrasIntersectEigenspaces(algebra);
    DihedralAlgebrasExpand(algebra);

end;

DihedralAlgebras := function(eigenvalues, fusiontable, ring)

    local algebra;

    algebra := DihedralAlgebrasSetup(eigenvalues, fusiontable, ring);

    while ForAny(algebra.products, x -> false in x) do
        DihedralAlgebrasMainLoop(algebra);
    od;

    return algebra;

end;

JordanTable := function(nu)

    return [ [ [1], [], [nu] ], [ [], [0], [nu] ], [ [nu], [nu], [1, 0] ] ];

end;
