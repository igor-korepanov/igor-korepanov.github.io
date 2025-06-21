# ABOUT THIS FILE

# This file, if run under GAP, will calculate the invariants for manifold M = RP^2 × RP^3
# For a different M, comment out the two lines beginning with "M :=" and "M_name :=", 
# and uncomment two similar lines corresponding to that M, see below.

# The last command in this file saves the results in a file. 
# Note that the calculations can last days and weeks, so when they are over,
# maybe at night, it certainly makes sense to save the results immediately.
# But maybe you would like to change the location of that file -- then do it now.

# And of course find a more detailed description of the commands below in file "explanations.pdf"


LoadPackage( "PL" );

field := GF(2^16);


rp2 := projectivePlane(2);
rp3 := projectivePlane(3);
rp4 := projectivePlane(4);
s1 := sphereAB(1);
s2 := sphereTriangul(2);
s3 := sphereTriangul(3);

klein_bottle := rec(
 vertices := [ "A", "B", "C", "D" ], 
 faces := [ [ [1,2], [1,2], [1,3], [1,3], [2,4], [3,4], [2,4], [3,4] ],
  [ [1,4,5,6], [1,3,6,7], [2,4,7,8], [2,3,5,8] ] ] );


############################################################

#    M = RP^2 × RP^3

M := PolTriangulate( PolProduct( rp2, rp3 ) );
M_name := "rp2rp3";

############################################################

#    M = S^1 × KB × KB

# M := PolTriangulate( PolProduct( s1, PolProduct( klein_bottle, klein_bottle ) ) );
# M_name := "s1kbkb";

############################################################

#    M = S^1 × KB × RP^2

# M := PolTriangulate( PolProduct( s1, PolProduct( klein_bottle, rp2 ) ) );
# M_name := "s1kbrp2";

############################################################

#   M = S^1 × RP^2 × RP^2

# M := PolTriangulate( PolProduct( PolProduct( s1, rp2 ), rp2 ) );
# M_name := "s1rp2rp2";

############################################################

#   M = S^1 × S^2 × KB

# M := PolTriangulate( PolProduct( s1, PolProduct( s2, klein_bottle ) ) );
# M_name := "s1s2kb";

############################################################

#   M = S^2 × RP^3

M := PolTriangulate( PolProduct( s2, rp3 ) );
M_name := "s2rp3";

############################################################

#    M = S^2 × S^3

# M := PolTriangulate( PolProduct( s2, s3 ) );
# M_name := "s2s3";

############################################################

#    M = S^3 × KB

# M := PolTriangulate( PolProduct( s3, klein_bottle ) );
# M_name := "s3kb";

############################################################

#    M = T^5

# M := PolTriangulate( PolProduct( PolProduct( s1, T2 ), T2 ) );
# M_name := "t5";

############################################################



# COHOMOLOGY BASIS FOR A MANIFOLD OF ANY DIMENSION

# incidence coefficient between (m+1)-simplex number mp1_cell and m-simplex number m_cell
# in a triangulated manifod M
# It is assumed that all the simplex numbers go in the increasing order
ei := function( M, m, mp1_cell, m_cell )
 local m_vertices, mp1_vertices, one_vertex, p;
 if not m_cell in M.faces[m+1][mp1_cell] then return 0;
  else if m>0 then m_vertices := PolBnd( M, [m,m_cell] )[0+1]; else m_vertices := [m_cell]; fi;
       mp1_vertices := PolBnd( M, [m+1,mp1_cell] )[0+1];
       one_vertex := Difference( mp1_vertices, m_vertices )[1];
       p := Position( mp1_vertices, one_vertex );
  return (-1)^p;
 fi;
end;

# coboundary of an (m-1)-simplex; addr=[ mm1=m-1, number ]
coboundary := function( M, addr )
 local m, mm1_cell, listik;
 m := addr[1] + 1;
 mm1_cell := addr[2];
 listik := [1..Length(M.faces[m])];
 return List( listik, m_cell -> ei( M, m-1, m_cell, mm1_cell ) );
end;

# basis in the space of n-cohomologies with coefficients in field in manifold M
basis_cohomology := function( M, field, n )
 local coboundaries, mat, cocycles, f, bas;
 coboundaries := VectorSpace( field, List([1..Length(M.faces[n-1])], nm1_cell -> coboundary(M,[n-1,nm1_cell]) )
                               * One(field) );
 mat := List([1..Length(M.faces[n])], n_cell -> coboundary(M,[n,n_cell]) ) * One(field);
 cocycles := VectorSpace( field, NullspaceMat( mat ) );
 f:= NaturalHomomorphismBySubspace( cocycles, coboundaries );
 bas := Basis(cocycles/coboundaries);
 return List( bas, x -> PreImagesRepresentative( f, x )
   + Random( coboundaries )      # !!!
    );
end;



# ORIENTATION OF THE CELLS OF THE MAXIMAL DIMENSION

PolTriangulatedOrient := function( M )
 local d, mat, stroka, face, around_face, vertices_face, vertices_d_1, vertices_d_2, pos_1, pos_2, sol_mat, f;
 d := Length( M.faces );
 
 mat := NullMat( Length(M.faces[d]), Length(M.faces[d-1]), GF(2) );
 stroka := List( M.faces[d-1], x -> 0*Z(2) );

 for face in [1..Length(M.faces[d-1])] do
  around_face := PositionsProperty( M.faces[d], x -> face in x );
  mat[ around_face[1], face ] := Z(2);
  mat[ around_face[2], face ] := Z(2);
 
  vertices_face := PolBnd( M, [d-1,face] )[1];
  vertices_d_1 := PolBnd( M, [d, around_face[1]] )[1];
  vertices_d_2 := PolBnd( M, [d, around_face[2]] )[1];
  pos_1 := Position( vertices_d_1, Difference( vertices_d_1, vertices_face )[1] );
  pos_2 := Position( vertices_d_2, Difference( vertices_d_2, vertices_face )[1] );
  if IsEvenInt( pos_1 + pos_2 ) then stroka[face] := Z(2); fi;
 od;

 sol_mat := SolutionMat( mat, stroka );
 if sol_mat=fail then return fail;
  else f := function(x) if x=0*Z(2) then return 1; fi;
                        if x=Z(2) then return -1; fi;    end;
  return List( sol_mat, f );
 fi;
end;




# HEPTAGON

kontrol_rangov_3 := [];
all_omega_components_nonzero := true;

# A component of g-vector
evt := function( M, triangle, pentachoron, cocycle )
 local field, polbnd, triangles, tetrahedra, listik, setik, f, 
    w1234, w1235, w1245, w1345, w2345, m, listi, seti, triangle_position;
 field := DefaultField( cocycle );
       if Zero(field) in cocycle then Print("\nzero omega component!\n");
                                   all_omega_components_nonzero := false; fi;
 polbnd := PolBnd( M, [4,pentachoron] );
 triangles := polbnd[2+1];
 if not triangle in triangles then return [0,0,0]*Zero(field); else
  tetrahedra := polbnd[3+1];
  listik := List( tetrahedra, tetrahedron -> PolBnd( M, [3,tetrahedron] )[0+1] );
  setik := Set( listik );
  f := function( i ) return Position( listik, setik[i] ); end;
   w1234 := cocycle[ tetrahedra[ f(1) ] ];
   w1235 := cocycle[ tetrahedra[ f(2) ] ];
   w1245 := cocycle[ tetrahedra[ f(3) ] ];
   w1345 := cocycle[ tetrahedra[ f(4) ] ];
   w2345 := cocycle[ tetrahedra[ f(5) ] ];
  m := [
     [Zero(field),   w1245,          w1234-w1235],
     [Zero(field),   -w1235,         w1235],
     [Zero(field),   w1235-w1245,    -w1234],
     [w2345,         Zero(field),    -w1235],
     [-w2345,        w1245,          w1234],
     [w2345,         -w1235,         Zero(field)],
     [-w1345,        Zero(field),    w1235],
     [w1345,         -w1245,         -w1234],
     [-w1345,        w1235,          Zero(field)],
     [-w2345+w1345,  Zero(field),    Zero(field)]
       ];
       if Rank(m)<3 then Print("\nRank(m)<3 for pentachoron ",pentachoron,"\n");     # !!!
                Add( kontrol_rangov_3, cocycle ); fi;                                # !!!
  listi := List( triangles, t3 -> PolBnd( M, [2,t3] )[0+1] );
  seti := Set( listi );
  triangle_position := Position( seti, PolBnd( M, [2,triangle] )[0+1] );
  return m[ triangle_position ];
 fi;
end;

# the following function is for any dimension
# g-simplex -- that is a triangle for heptagon, while face is a pentachoron
e := function(M, g_simplex, cocycle)
 local n;
 n := (Length(M.faces)+1)/2;
 return( List( [1..Length(M.faces[2*n-2])], face -> evt(M,g_simplex,face,cocycle) ) );
end;

# the following function is also for any manifold dimension: 3, 5, ...
# IF g-simplices have dimension n-1   !
# Now we remove square brackets around the components at each face (pentachoron in case of heptagon)
# the rows correspond to g-simplices, while columns to components on faces
all_e := function( M, cocycle )
 local n, r;
 n := (Length(M.faces)+1)/2;
 r := List( [1..Length(M.faces[n-1])], g_simplex -> Concatenation(e(M,g_simplex,cocycle)) );
 return r;
end;

# the following function is not used below -- as yet!
# it is also for any dimension
# restrictions (linear functionals) in one d-simplex
r_d_simplex := function( M, d_simplex, cocycle )
 local n, all_e_result, k, nomera, on_d_simplex;
 n := (Length(M.faces)+1)/2;
 all_e_result := all_e(M,cocycle);
 k := Length(all_e_result[1]) / Length(M.faces[2*n-2]); # the number of components on a face
 nomera := Concatenation( List( M.faces[2*n-1][d_simplex], i -> [(i-1)*k+1..i*k] ) );
 on_d_simplex := all_e_result{[1..Length(all_e_result)]}{nomera};
 return NullspaceMat(TransposedMat(on_d_simplex));
end;

# the following function is also for any dimension
# and not used below as well!
r_d_simplex_global := function( M, d_simplex, cocycle )
 local n, all_e_result, k, nomera, on_d_simplex, r, field, m, i, j, l;
 n := (Length(M.faces)+1)/2;
 all_e_result := all_e(M,cocycle);
 k := Length(all_e_result[1]) / Length(M.faces[2*n-2]); # the number of components on a face
 nomera := Concatenation( List( M.faces[2*n-1][d_simplex], i -> [(i-1)*k+1..i*k] ) );
 on_d_simplex := all_e_result{[1..Length(all_e_result)]}{nomera};
 r := NullspaceMat(TransposedMat(on_d_simplex));
 field := DefaultField( cocycle );
 m := NullMat(Length(r), Length(all_e_result[1]), field);
 for i in [1..Length(r)] do
  for j in [1..2*n] do
   for l in [-k+1..0] do
    m[i][ k * M.faces[2*n-1][d_simplex][j] + l ] := r[i][k*j+l];
   od;
  od;
 od;
 return m;
end;

kontrol_rangov_9 := [];

colorings := function( M, cocycle )
 local n, all_e_result, k, r_d_s_g, r_all_result;
 n := (Length(M.faces)+1)/2;
 all_e_result := all_e(M,cocycle);
 k := Length(all_e_result[1]) / Length(M.faces[2*n-2]); # the number of components on a face
 r_d_s_g := function( d_simplex )
  local nomera, on_d_simplex, r, field, m, i, j, l;
  nomera := Concatenation( List( M.faces[2*n-1][d_simplex], i -> [(i-1)*k+1..i*k] ) );
  on_d_simplex := all_e_result{[1..Length(all_e_result)]}{nomera};
  r := NullspaceMat(TransposedMat(on_d_simplex));
     if Rank(r) > 9 then Print( "\nRank(r)>9 for d_simplex ",d_simplex,"\n");     # !!!
           Add( kontrol_rangov_9, cocycle ); fi;                                  # !!!
  field := DefaultField( cocycle );
  m := NullMat(Length(r), Length(all_e_result[1]), field);
  for i in [1..Length(r)] do
   for j in [1..2*n] do
    for l in [-k+1..0] do
     m[i][ k * M.faces[2*n-1][d_simplex][j] + l ] := r[i][k*j+l];
    od;
   od;
  od;
  return m;
 end;
 r_all_result := Concatenation( List([1..Length(M.faces[2*n-1])], t -> r_d_s_g(t) ) );
 return rec( g := all_e_result, p := NullspaceMat( TransposedMat( r_all_result ) ) );
end;



# HEPTAGON COCYCLES

# Bilinear symmetric 4-cocycle
# x and y are two colorings in the form of rows with no redundant square brackets
#      that is, they are like the rows in the output of function all_e
gran := function( M, cocycle, pentachoron, x, y )
 local field, polbnd, tetrahedra, listik, setik, f, w1234, w1235, w1245, w1345, w2345, Q, k, nomera;
 field := DefaultField( cocycle );
 polbnd := PolBnd( M, [4,pentachoron] );
 tetrahedra := polbnd[3+1];
  listik := List( tetrahedra, tetrahedron -> PolBnd( M, [3,tetrahedron] )[0+1] );
  setik := Set( listik );
  f := function( i ) return Position( listik, setik[i] ); end;
   w1234 := cocycle[ tetrahedra[ f(1) ] ];
   w1235 := cocycle[ tetrahedra[ f(2) ] ];
   w1245 := cocycle[ tetrahedra[ f(3) ] ];
   w1345 := cocycle[ tetrahedra[ f(4) ] ];
   w2345 := cocycle[ tetrahedra[ f(5) ] ];
 Q := [[1/((w1245-w1235+w1234)*w1345*(w1345-w1245+w1235-w1234)),   Zero(field),  Zero(field)],
       [Zero(field), -(w1235-w1234)/(w1235^2*w1245*(w1245-w1235+w1234)),   -1/(w1235^2*(w1245-w1235+w1234))],
       [Zero(field), -1/(w1235^2*(w1245-w1235+w1234)),   (w1245-w1235)/(w1234*w1235^2*(w1245-w1235+w1234))]];
 k := 3; # ! 3 components on a face
 nomera := [(pentachoron-1)*k+1..pentachoron*k];
 return x{nomera} * Q * y{nomera};
end;

# we can check that a cocycle has been obtaines indeed: zero appears on one d-simplex
# this function is written for any manifold dimension
on_d := function( M, cocycle, d_simplex, x, y )
 local field, n, all_d, vertices_d, faces_d, r, face, vertices_face, i;
 field := DefaultField( cocycle );
 n := (Length(M.faces)+1)/2;
 all_d := PolBnd(M,[2*n-1,d_simplex]);
 vertices_d := all_d[1];
 faces_d := all_d[2*n-1];
 r := Zero(field);
 for face in faces_d do
  vertices_face := PolBnd(M,[2*n-2,face])[1];
  i := Difference( vertices_d, vertices_face )[1];
  r := r+(-1)^Position(vertices_d,i)*gran(M,cocycle,face,x,y);
 od;
 return r;
end;

# characteristic 2
on_d_2 := function( M, cocycle, d_simplex, x, y )
 local field, n, r, all_d, vertices_d, faces_d, pairs_faces, pair, vertices_face_1, vertices_face_2, i, j, 
    face, vertices_face;
 field := DefaultField( cocycle );
 n := (Length(M.faces)+1)/2;
 all_d := PolBnd(M,[2*n-1,d_simplex]);
 vertices_d := all_d[1];
 faces_d := all_d[2*n-1];
 pairs_faces := Combinations(faces_d, 2);
 r := Zero(field);
 for pair in pairs_faces do
  # vertices_face_1 := PolBnd(M,[2*n-2,pair[1]])[1];
  # i := Difference( vertices_d, vertices_face_1 )[1];
  # vertices_face_2 := PolBnd(M,[2*n-2,pair[2]])[1];
  # j := Difference( vertices_d, vertices_face_2 )[1];
  r := r + # (-1)^( Position(vertices_d,i) + Position(vertices_d,j) ) * 
       gran(M,cocycle,pair[1],x,y) * gran(M,cocycle,pair[2],x,y);
 od;
 
 for face in faces_d do
  vertices_face := PolBnd(M,[2*n-2,face])[1];
  i := Difference( vertices_d, vertices_face )[1];
  if IsEvenInt( Position(vertices_d,i) ) then r := r + gran(M,cocycle,face,x,y)^2; fi;
 od;
 
 return r;
end;

# characteristic 3
on_d_3 := function( M, cocycle, d_simplex, x, y )
 local field, n, r, all_d, vertices_d, faces_d, triples_faces, triple, 
  vertices_face_1, vertices_face_2, vertices_face_3, i, j, k;
 field := DefaultField( cocycle );
 n := (Length(M.faces)+1)/2;
 all_d := PolBnd(M,[2*n-1,d_simplex]);
 vertices_d := all_d[1];
 faces_d := all_d[2*n-1];
 triples_faces := Combinations(faces_d, 3);
 r := Zero(field);
 for triple in triples_faces do
  vertices_face_1 := PolBnd(M,[2*n-2,triple[1]])[1];
  i := Difference( vertices_d, vertices_face_1 )[1];
  vertices_face_2 := PolBnd(M,[2*n-2,triple[2]])[1];
  j := Difference( vertices_d, vertices_face_2 )[1];
  vertices_face_3 := PolBnd(M,[2*n-2,triple[3]])[1];
  k := Difference( vertices_d, vertices_face_3 )[1];
  r := r + (-1)^( Position(vertices_d,i) + Position(vertices_d,j) + Position(vertices_d,k) ) * 
       gran(M,cocycle,triple[1],x,y) * gran(M,cocycle,triple[2],x,y) * gran(M,cocycle,triple[3],x,y);
 od;
 return r;
end;



#######################################################################
#######################################################################
#######################################################################



coboundaries := VectorSpace( field, List([1..Length(M.faces[2])], nm1_cell -> coboundary(M,[2,nm1_cell]) )
                               * One(field) );;

bas :=  basis_cohomology( M, GF(2), 3 );;

if Characteristic( field ) = 0  then random_coboundary := Sum( Basis(coboundaries), x -> x*Random([0..135]) );
 else random_coboundary := Random(coboundaries);
fi;

pol_triangulated_orient_M := PolTriangulatedOrient( M );;



itogi_function := function( )
 local itogi_zagotovka, vektor, cocycle, n, colorings_results, V_p, V_g, subset_V_p_V_g, d_V_p, d_V_g, f, u, v, U, V, x, y, basis_p, basis_g, sum, d_simplex, xx, yy, sumsum, sum_sumsum, p_coeff, i, j, A, rank_A;

 itogi_zagotovka := [];

 # The beginning of a long cycle
 for vektor in Cartesian( List( bas, x -> GF(2) ) ) do
  cocycle := vektor * bas + random_coboundary;

  # k := 3;
  n := 3;


  colorings_results := colorings( M, cocycle );
  V_p := VectorSpace( field, colorings_results.p );
  V_g := VectorSpace( field, colorings_results.g );

  subset_V_p_V_g := IsSubset( V_p, V_g );
  d_V_p := Dimension( V_p );
  d_V_g := Dimension( V_g );

  f := NaturalHomomorphismBySubspace( V_p, V_g );
  basis_p := List( Basis( V_p / V_g ), v -> PreImagesRepresentative(f,v) );

  u := List( [1..Length(basis_p)], i -> X(field, Concatenation("u[", String(i), "]") ) );
  v := List( [1..Length(basis_p)], i -> X(field, Concatenation("v[", String(i), "]") ) );

  U := List( [1..Length(Basis(V_g))], i -> X(field, Concatenation("U[", String(i), "]") ) );
  V := List( [1..Length(Basis(V_g))], i -> X(field, Concatenation("V[", String(i), "]") ) );

  x := Sum( [1..Length(basis_p)], i -> u[i]*basis_p[i] );
  y := Sum( [1..Length(basis_p)], i -> v[i]*basis_p[i] );

  basis_g := Basis( V_g );
  # xx := x + Sum( [1..Length(basis_g)], i -> U[i]*basis_g[i] );
  # yy := y + Sum( [1..Length(basis_g)], i -> V[i]*basis_g[i] );


  Length(M.faces[2*n-1]);


  sum := Zero(field);
  if not IsZero(x) then
   if Characteristic(field)=2 then
    for d_simplex in [1..Length(M.faces[2*n-1])] do
     sum := sum + on_d_2( M, cocycle, d_simplex, x, y );
     Print("\n   d\_simplex = ", d_simplex);
    od;
   fi;
   if Characteristic(field)=3 then
    for d_simplex in [1..Length(M.faces[2*n-1])] do
     sum := sum + pol_triangulated_orient_M[ d_simplex ] * on_d_3( M, cocycle, d_simplex, x, x );
     Print("\n   d\_simplex = ", d_simplex);
    od;
   fi;
  fi;

  # The following is just to check that our calculations, most likely, go right
  # For actual calculations, it may make sense to remove from here everything belonging
  # to "sumsum" and "sum_sumsum"
  xx := x + Sum( [1,2,3], j -> U[j]*basis_g[j] );
  yy := y + Sum( [1,2,3], j -> V[j]*basis_g[j] );
  sumsum := Zero(field);
  if Characteristic(field)=2 then
   for d_simplex in [1..Length(M.faces[2*n-1])] do
    sumsum := sumsum + on_d_2( M, cocycle, d_simplex, xx, yy );
    Print("\n   d\_simplex = ", d_simplex);
   od;
  fi;
  if Characteristic(field)=3 then
   for d_simplex in [1..Length(M.faces[2*n-1])] do
    sumsum := sumsum + pol_triangulated_orient_M[ d_simplex ] * on_d_3( M, cocycle, d_simplex, xx, xx );
    Print("\n   d\_simplex = ", d_simplex);
   od;
  fi;

  sum_sumsum := sum = sumsum;



  if Characteristic(field)=2 and not IsZero(x) then
   p_coeff := function( p, var )
    local l;
    l := PolynomialCoefficientsOfPolynomial( p, var );
    if Length(l) = 3 then return l[3]; else return Zero(u[1]); fi;
   end;

   # The following works gor nonzero x and y only
   A := NullMat( Length(u), Length(v), u[1] );
   for i in [1..Length(u)] do
    for j in [1..Length(v)] do
     A[i][j] := p_coeff( p_coeff( sum, u[i] ), v[j] );
    od;
   od;

   rank_A := Rank(A);;
   Print("\n\n     Rank(A) = ", rank_A);
  fi;


  Add( itogi_zagotovka, [ vektor, subset_V_p_V_g, d_V_p, d_V_g, sum_sumsum, sum, rank_A ] );
  Print( "   vektor = ", vektor, "\n" );
 od; # The end of the long cycle!
 return( itogi_zagotovka );
end;

itogi := itogi_function( );

###########################################################

AppendTo( Concatenation("itogi\_", M_name, ".g"),  "itogi_", M_name, " := \n", itogi, "\n;\n\n" );

