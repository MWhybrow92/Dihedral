
testFusion = algebra -> (
    mat := zeroAxialVector (#algebra.span);
    for ev in keys algebra.evecs do algebra.evecs#ev = mingens image algebra.evecs#ev;
    a := standardAxialVector(0, #algebra.span);
    I := sub(ideal algebra.polynomials, algebra.coordring);
    for ev0 in algebra.evals do (
        for ev1 in algebra.evals do (
            for i to numgens source algebra.evecs#(set {ev0}) - 1 do (
                for j to numgens source algebra.evecs#(set {ev1}) - 1 do (
                    u := algebra.evecs#(set {ev0})_{i};
                    v := algebra.evecs#(set {ev1})_{j};
                    prod := axialProduct(u, v, algebra.products);
                    rule = toList(algebra.tbl#{ev0, ev1});
                    for ev in rule do (
                        prod = axialProduct(a, prod, algebra.products) - ev*prod;
                        );
                    prod = prod % I;
                    if prod != 0 then error "fusion";
                    --if prod != 0 then mat = mat | prod;
                    );
                );
            );
        );
    if mat == 0 then return true else return colReduce(mat);
    )

testIntersection = algebra -> (
    mat := zeroAxialVector (#algebra.span);
    for ev0 in keys algebra.evecs do (
        for ev1 in keys algebra.evecs do (
            if ev0*ev1 === set {} then (
                za := colReduce gens intersect(image algebra.evecs#(ev0), image algebra.evecs#(ev1));
                if za != 0 then mat = mat | za;
                );
            );
        );
    if mat == 0 then return true else return colReduce mat;

    )

testEvecs = algebra -> (
    a := sub(standardAxialVector(0, #algebra.span), algebra.field);
    for ev in algebra.evals do (
        for i to numgens source algebra.evecs#(set {ev}) - 1 do (
            u := algebra.evecs#(set {ev})_{i};
            v := axialProduct(a, u, algebra.products);
            if v =!= false and v - ev*u != 0 then "evecs error";
            );
        );
    )

testFlip = {form => true} >> opts -> algebra -> (
    n := #algebra.span;
    for i to n - 1 do (
        u := standardAxialVector(i, n);
        uf := flipVector(u, algebra);
        for j to n - 1 do (
            v := standardAxialVector(j, n);
            vf := flipVector(v, algebra);
            -- Calculate products and compare (uv)^sigma and u^sigma v^sigma
            prod := axialProduct(u, v, algebra.products);
            prodf := axialProduct(uf, vf, algebra.products);
            if prod - flipVector(prodf, algebra) !=0 then "flip error";
            );
        );
    return true;
    )
