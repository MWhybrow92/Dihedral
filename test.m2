load "Dihedral.m2";
load "examples.m2";
load "testFusion.m2"

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

algebra = universalDihedralAlgebra (evals, tbl, form => false);
testFusion algebra;

-- This algebra should be one dimensional

evals = {1, 2, 3};
tbl = GenericJordan (2, 3);
algebra = universalDihedralAlgebra (evals, tbl);

-- Unfortunately we have to do a little extra work
fusion algebra;
findNullVectors algebra;

if #algebra.span != 1 then error "1-dimensional";

-- Test Monster

evals = {1, 0, 1/4, 1/32};
tbl = MonsterTable( 1/4, 1/32 );
algs = dihedralAlgebras (evals, tbl);

test = apply(algs.algebras, x -> #x.span);
if set test != set {2, 8, 8, 6, 5, 4, 3, 1} then error "Monster";

apply(algs.algebras, x -> testFusion x);
