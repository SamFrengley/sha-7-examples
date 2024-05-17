AttachSpec("../src/spec");

//////////////////////////////////////////////////
//////////////////////////////////////////////////
// Fetch stored data
P2<x0,x1,x2> := ProjectiveSpace(Rationals(), 2);
table1 := eval Read("../data/table-1.m");
table2 := eval Read("../data/table-2.m");
twists := eval Read("../data/twists.m");


print "**************************************************";
print "          A PROOF OF PROPOSITION 5.2              ";
print "**************************************************\n";
P<x> := PolynomialRing(Rationals());
search_bd := 100;

for eg in table1 cat table2 do
  print "\n==================================================";
  print "The case where C has Weierstrass equation";
  printf "y^2 = %o*(%o)\n", eg[4], P!Polynomial(eg[2]);
  printf "and RM %o\n\n", eg[1][1];
  
  // First define C and E and twists of X(7)
  C := HyperellipticCurve(Polynomial(eg[2]));
  E := EllipticCurve(eg[3]);

  C := QuadraticTwist(C, eg[4]);
  E := QuadraticTwist(E, eg[4]);  // NB: don't strictly need to take the simul quad. twists
                                  //  it's equivalent that it's true without q. tw.
  
  assert exists(this_tws){tw : tw in twists | eg[1] eq tw[1]};
  this_tws := &cat this_tws[2];

  // Compute the j-maps for each twist
  j_maps := [ModuliKleinQuarticTwist(X) : X in this_tws];
  this_tws := [Curve(P2, X) : X in this_tws];

  // Search for rational points
  pts := [[Eltseq(p) : p in PointSearch(X, search_bd)] : X in this_tws];

  // Compute the associated j-invariants
  jj := &cat[[Evaluate(j_maps[i], p) : p in pts[i]] : i in [1..#j_maps]];

  assert jInvariant(E) in jj;
  print "* Up to quadratic twist, E and Jac(C) are congruent";

  // Now prove that they truly are congruent
  d := CorrectQuadraticTwist(C, E);
  assert d eq 1;
  print "* E and Jac(C) are congruent on the nose";
end for;
