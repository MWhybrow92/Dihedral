load "Dihedral.m2";
evals = {1, 0, 100};
tbl = JordanTable 100;
algebra = dihedralAlgebraSetup(evals, tbl);
fusion algebra;
findAlgebraProducts algebra;
findNullVectors algebra;
