
testFusion = algebra -> (
    a := standardAxialVector(0, #algebra.span);
    I := ideal algebra.polynomials;
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
                    );
                );
            );
        );
    )
