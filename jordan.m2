load "Dihedral.m2";
load "examples.m2";

recursionLimit = 1000;

tbl = JordanTable 100;
evals = {1, 0, 100};

algebras = dihedralAlgebras (evals, tbl, primitive => true, form => false);

--testEvecs algebra
--if #algebra.span != 3 then error "Jordan";
--if algebra.products#2#2_(0,0) != -495000 then error "Jordan"
