load "Dihedral.m2";
load "examples.m2";
load "testFusion.m2"

-- Test Jordan 1/4

evals = {1, 0, 1/4};
tbl = JordanTable (1/4);
algebras = dihedralAlgebras (evals, tbl, form => false);

test = apply(algebras#0, x -> testFusion x);
if test != {true, true, true} then error "Jordan 1/4";

test = apply(algebras#0, x -> #x.span);
if set test != set {2, 3, 0} then error "Jordan 1/4";

algebra = universalDihedralAlgebra (evals, tbl, primitive => false);
testFusion algebra;

-- Test Jordan 1/2

evals = {1, 0, 1/2};
tbl = JordanTable (1/2);

algebra = universalDihedralAlgebra (evals, tbl, form => false);
testFusion algebra;

-- Test Monster

evals = {1, 0, 1/4, 1/32};
tbl = MonsterTable( 1/4, 1/32 );
algebra = universalDihedralAlgebra (evals, tbl, form => true);
