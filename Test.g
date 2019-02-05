gap> Read("Dihedral.g");
gap> table := [[ [1], [0] ], [ [0], [0] ]];;
gap> eigenvalues := [1, 0];;
gap> algebra := DihedralAlgebras(eigenvalues, table, Rationals);;
gap> Display(algebra);
rec(
  eigenvalues := [ 1, 0 ],
  eigenvectors := rec(
      ("[ 0 ]") := SparseMatrix( 1, 3, [ [ 2, 3 ] ], 
        [ [ -1, 1 ] ], Rationals ),
      ("[ 1 ]") := SparseMatrix( 2, 3, [ [ 3 ], [ 1 ] ], 
        [ [ 1 ], [ 1 ] ], Rationals ) ),
  flip := [ 2, 1, 3 ],
  fusiontable := [ [ [ 1 ], [ 0 ] ], [ [ 0 ], [ 0 ] ] ],
  null := SparseMatrix( 0, 3, [  ], [  ], Rationals ),
  products := 
   [ 
      [ SparseMatrix( 1, 3, [ [ 1 ] ], [ [ 1 ] ], Rationals ), 
          SparseMatrix( 1, 3, [ [ 3 ] ], [ [ 1 ] ], Rationals ), 
          SparseMatrix( 1, 3, [ [ 3 ] ], [ [ 1 ] ], Rationals ) ], 
      [ SparseMatrix( 1, 3, [ [ 3 ] ], [ [ 1 ] ], Rationals ), 
          SparseMatrix( 1, 3, [ [ 2 ] ], [ [ 1 ] ], Rationals ), 
          SparseMatrix( 1, 3, [ [ 3 ] ], [ [ 1 ] ], Rationals ) ], 
      [ SparseMatrix( 1, 3, [ [ 3 ] ], [ [ 1 ] ], Rationals ), 
          SparseMatrix( 1, 3, [ [ 3 ] ], [ [ 1 ] ], Rationals ), 
          SparseMatrix( 1, 3, [ [ 3 ] ], [ [ 1 ] ], Rationals ) ] ],
  ring := Rationals,
  spanningset := [ 1, 2, [ 1, 2 ] ] )
