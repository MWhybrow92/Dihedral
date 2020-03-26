load "Dihedral.m2";

-- Test Jordan 1/4

evals = {1, 0, 1/4};
tbl = JordanTable (1/4);
algs = dihedralAlgebras (evals, tbl, form => false);

test = apply(algs.algebras, x -> #x.span);
if set test =!= set {2, 3, 1} then error "Jordan 1/4";

test = apply(algs.algebras, x -> testFusion x);
if test != {true, true, true} then error "Jordan 1/4";

algebra = universalDihedralAlgebra (evals, tbl, primitive => false);
testFusion algebra;

-- Test Jordan 1/2

evals = {1, 0, 1/2};
tbl = JordanTable (1/2);

algebra = universalDihedralAlgebra (evals, tbl, form => true);
testFusion algebra;

-- Gives two algebras, only minor repeat
algs = dihedralAlgebras (evals, tbl, form => false);
apply(algs.algebras, x -> testFusion x);

-- This algebra should be one dimensional

evals = {1, 2, 3};
tbl = GenericJordan (2, 3);
algebra = universalDihedralAlgebra (evals, tbl);

if #algebra.span != 1 then error "1-dimensional";

-- Test Monster
evals = {1, 0, 1/4, 1/32};
tbl = MonsterTable( 1/4, 1/32 );
algs = dihedralAlgebras (evals, tbl);

test = apply(algs.algebras, x -> #x.span);
if set test =!= set {3, 5, 6, 8, 5, 4, 1, 2, 3} then error "Monster";

apply(algs.algebras, x -> testFusion x);

-- Test a polynomial ring case

r = QQ[a, b, m, n, p];
I = ideal {m*(a-1)-1,n*(b-1)-1,p*(a-b)-1}
r = r/I;

evals = {1, a, b};
tbl = ThreeEvals (a,b);

-- TODO Kind of working
algs = dihedralAlgebras (evals, tbl, field => r);
