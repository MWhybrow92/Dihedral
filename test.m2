load "Dihedral.m2";
load "examples.m2";
load "testFusion.m2"

evals = {1, 0, 100};
tbl = JordanTable 100;
algebra = universalDihedralAlgebra (evals, tbl, form => false);

if #algebra.span != 3 then error "Jordan";

r = QQ[n, m, p];
I = ideal {n*m - 1, (n - 1)*p - 1};
r = r/I;

n = r_0;
m = r_1;
p = r_2;

evals = {1, 0, n};
tbl = JordanTable n;

algebra = universalDihedralAlgebra (evals, tbl, field => r);

-- This is erroring :(

--evals = {1, 0, 2, 3};
--tbl = MonsterTable(2,3);

--algebra = universalDihedralAlgebra(evals, tbl);

--algebra.span;


-- I'll finish this when I work out what the right answer is!
