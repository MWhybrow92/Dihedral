recursionLimit = 1000;

load "Dihedral.m2";
load "examples.m2";

-- r = frac(QQ[symbol n]);
-- evals = {1, 0, r_0};
-- tbl = JordanTable r_0;
-- algebra = dihedralAlgebraSetup(evals, tbl, symbol field => r);

tbl = MonsterTable (1/4, 1/32);
evals = {1, 0, 1/4, 1/32};
algebra = dihedralAlgebras (evals, tbl);
