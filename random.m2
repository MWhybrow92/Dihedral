
load "Dihedral.m2";
load "examples.m2";

randomPairRational = (x, y) -> (
    n0 := random(x, y);
    n1 := random(x, y);
    d0 := random(x, y);
    d1 := random(x, y);
    return {n0/d0, n1/d1};
    )

results = {};
pairsRational = {};

for i to 3 do (
    pair := randomPairRational(-1024, 1024);
    if pair#0 != pair#1 then (
        print pair;
        evals = {1, 0, pair#0, pair#1};
        tbl = MonsterTable (pair#0, pair#1);
        results = append(results, dihedralAlgebras(evals, tbl));
        pairsRational = append(pairsRational, pair);
        );
    );
