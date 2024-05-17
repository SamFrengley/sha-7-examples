declare verbose TalkToMe, 1;

function VeryOptimisedRepresentation(ff)
    K := NumberField(ff[1]);
    gg := [g*LCM([Denominator(c) : c in Coefficients(g)]) : g in ff];
    gg := [g^Matrix(Integers(), 2, 2, [1,0,0,LeadingCoefficient(g)]) div LeadingCoefficient(g) : g in gg];
    aa := &cat[[r[1] : r in Roots(g, K)] : g in gg];
    O := Order(aa : Verify:=false);
    Omax := MaximalOrder(O);
    _, Omax := OptimizedRepresentation(Omax);
    return NumberField(Omax), LLL(Omax);
end function;

function GetX1(j)
  P<t> := PolynomialRing(FieldOfFractions(Parent(j)));
  j_X1 := (t^2 + t + 1)^(3)*(t^6 - 5*t^5 - 10*t^4 + 15*t^3 + 30*t^2 + 11*t + 1)^(3)/((t)^(7)*(t + 1)^(7)*(t^3 - 5*t^2 - 8*t - 1));
  return Numerator(j_X1 - j);
end function;

function GetX0(j)
  P<t> := PolynomialRing(FieldOfFractions(Parent(j)));
  j_X0 := (t^2 + 5*t + 1)^3*(t^2 + 13*t + 49)/t;
  return Numerator(j_X0 - j);
end function;

function GetX1_to_X0(pt_X0)
  P<t> := PolynomialRing(FieldOfFractions(Parent(pt_X0)));
  j_X1_to_X0 := (t^3 - 5*t^2 - 8*t - 1)/(t^2 + t);
  return Numerator(j_X1_to_X0 - pt_X0);
end function;

////////////////////////////////////////////////
// CHECK THAT THE AB SURFACES ARE IRREDUCIBLE //
////////////////////////////////////////////////

// Checks the criterion for a curve C/QQ to have absolutely simple Jacobian
// given on p.158 of Cassels--Flynn. The code below is a lightly modified
// version of code given by Tom Fisher at
// https://www.dpmms.cam.ac.uk/~taf1000/papers/vis7check.m

function MyCount(g,h,p)
  P1 := PolynomialRing(GF(p));
  P2 := PolynomialRing(GF(p^2));
  Cp := HyperellipticCurve([P1!g,P1!h]);
  Cpp := HyperellipticCurve([P2!g,P2!h]);
  return #Cp,#Cpp;
end function;

intrinsic ProvedAbsolutelySimpleJacobian(C::CrvHyp, bd::RngIntElt) -> BoolElt
{
  Returns true if the Jacobian of C is proved absolutely simple by 
  checking conditions on the local behaviour of J at p for good primes
  p less than the bound bd.
}
  P<x> := PolynomialRing(Rationals());
  PP<y> := PolynomialRing(P);
  CC := ReducedMinimalWeierstrassModel(C);
  eqn := Evaluate(Equation(CC),[x,y,1]);
  g := -Coefficient(eqn,0);
  h := Coefficient(eqn,1);
  assert CC eq HyperellipticCurve([g,h]);
  badp := BadPrimes(CC);
  pp := [p : p in [3..bd] | IsPrime(p) and p notin badp];
  ans := false;
  for p in pp do
    n1,n2 := MyCount(g,h,p);
    t := p + 1 - n1;
    n := (1/2)*(n1^2 + n2) - (p+1)*n1 - p;
    flag1 := IsSquare(t^2 - 4*n);
    poly := x^4 - (n/p)*x^3 + ((t^2 - 2*n - 2*p)/p)*x^2 - (n/p)*x + 1;
    flag2 := exists{k : k in [1..12] | GCD(x^k-1,poly) ne 1};
    if (not flag1) and (not flag2) then ans := true; end if;
  end for;
  return ans;
end intrinsic;


////////////////////////////////////////////////////
// CHECK SURJECTIVITY OF GALOIS REP OF ELL. CURVE //
////////////////////////////////////////////////////

// We use [Ser72] Proposition 19.

function NotExceptional(trs, dets)
  // We need to check that there exists u = Tr(s)^2 / det(s) such that
  // u \ne 0,1,2,4 and u^2 - 3*u + 1 \ne 0. This is [Ser72, Prop.19(iii)]
  us := [trs[i]^2/dets[i] : i in [1..#trs]];
  us := [u : u in us | not u in {0,1,2,4}];
  us := [u : u in us | u^2 - 3*u + 1 ne 0];
  return #us gt 0;
end function;


function NotNormaliserNonsplit(trs, dets)
  // Need to find an element such that Tr(s)^2 - 4det(s) (disc of the char
  // poly) is a non-zero square and Tr(s) \ne 0.
  discs := [trs[i]^2 - 4*dets[i] : i in [1..#trs] | trs[i] ne 0];
  flag := exists{d : d in discs | (d ne 0) and IsSquare(d)};
  return flag;
end function;


function NotBorelOrNormaliserSplit(trs, dets)
  // Need to find an element such that Tr(s)^2 - 4det(s) (disc of the char
  // poly) is a non-square and Tr(s) \ne 0.
  discs := [trs[i]^2 - 4*dets[i] : i in [1..#trs] | trs[i] ne 0];
  flag := exists{d : d in discs | (d ne 0) and (not IsSquare(d))};
  return flag;
end function;


intrinsic ProvedSurjectiveModpGaloisRep(E::CrvEll, p::RngIntElt, bd::RngIntElt) -> BoolElt
{
  Given E/K check if E has surjective mod p Galois rep by checking at 
  good primes up to bd. Returning false does not imply that the Galois rep
  is not surjective.
}
  K := BaseField(E);
  O := MaximalOrder(K);

  require not HasComplexMultiplication(E): "Sorry, E has CM";
  require p gt 5 and IsPrime(p): "The integer p should be a prime >= 5";
  
  //check determinant is surjective (so if SL_2(Fp) contained is equal to GL_2(Fp))
  P := PolynomialRing(K);
  phi_p := P!CyclotomicPolynomial(p);
  if not IsIrreducible(phi_p) then
    return false;
  end if;

  // Find good primes with norm up to bd.
  D := Discriminant(E); D := Numerator(D)*Denominator(D);
  ells := [Factorisation(ideal<O | ell>)[1][1] : ell in PrimesInInterval(8, bd)];
  ells := [ell : ell in ells | not (D in ell)];
  
  // Check that we have an element satisfying (i)--(iii) from [Ser72, Prop. 19]
  // First compute p-adic Trace and Determinant of Frobenius at ell

  // Somtimes E has bad reduction -- I'll just pop such primes out, I don't understand
  // the error, but it's ok to use fewer primes of course
  new_ells := [];
  trs := [];
  for ell in ells do
    try
      Append(~trs, TraceOfFrobenius(E, ell));
      Append(~new_ells, ell);
    catch e
      assert 0 eq 0; // catch an error where E is bad at ell ??
    end try;
  end for;
  
  ells := new_ells;
  dets := [#ResidueClassField(ell) : ell in ells];

  // (in)sanity check
  assert #trs eq #dets;
  
  // Then reduce mod p
  trs := [GF(p)!t : t in trs];
  dets := [GF(p)!d : d in dets];
  // Now check that these ell witnesses the surjectivity.
  return NotExceptional(trs, dets) and NotNormaliserNonsplit(trs, dets) and NotBorelOrNormaliserSplit(trs, dets);
end intrinsic;


/////////////////////////////////////////////////////////////////////
// CHECKING THAT THE SAME FIELDS ARE DEFINED BY THE TORSION POINTS //
/////////////////////////////////////////////////////////////////////

intrinsic MakeTorsionFieldProofRationalj(f_C::RngUPolElt, j::FldRatElt) -> Tup
{
  Given C : y^2 = f_C(x) and E defined over QQ, returns a tuple consisting of 
  (1) A basis for the ring of integers O_K of a number field K/QQ of degree 8.
  (2) A list of coefficients of min polys g_1, g_2, g_3 \in O_K[x] for which 
      the roots give a 7-torsion point on the Kummer surface of C.
  (3) The coefficients of a min poly for a root of j_X1 - j(E), where j_X1 is 
      the j-invariant map on the modular curve X_1(7).
}
  vprint TalkToMe, 1: "Analytic Jacobian calculation\n-----------------------------";
  g1,g2,g1_bar,g2_bar := BothPoly24(f_C);

  try
    g := g1; h := g2;
    L := NumberField(g);
    xx := Roots(GetX1(j), L);
    assert #xx ne 0;
  catch e
    g := g1_bar; h := g2_bar;
    L := NumberField(g);
    xx := Roots(GetX1(j), L);
    error if #xx eq 0, "The curves cannot possibly be congruent";
  end try;

  xx := xx[1][1];
  ply := MinimalPolynomial(&+[r[1] : r in Roots(g, L)]);
  ply2 := GetX0(j);

  vprint TalkToMe, 1: "\nComputing requisite polys and roots\n-----------------------------------";
  vprint TalkToMe, 1 : "Computing optimised repn";
  K,OK := VeryOptimisedRepresentation([ply, ply2]);

  vprint TalkToMe, 1 : "Computing all the min polys etc";
  ff := [Coefficients(MinimalPolynomial(OK.i)) : i in [1..8]];
  K := NumberField(Polynomial(ff[2]));
  OK := Order([Roots(Polynomial(x), K)[1][1] : x in ff]);
  
  Embed(K, L, Roots(MinimalPolynomial(K.1), L)[1][1]);

  xi1 := MinimalPolynomial(Roots(g, L)[1][1], OK);
  xi2 := MinimalPolynomial(Roots(h, L)[1][1], OK);
  
  kk := Coefficients(MinimalPolynomial(xx, OK));
  kk := [Eltseq(c) : c in kk];
  
  _<x> := PolynomialRing(L);
  Kum := KummerSurface(Jacobian(HyperellipticCurve(f_C)));
  Kum := BaseChange(Kum, L);
  f := DefiningPolynomial(Kum);
  xi := [Roots(xi1, L), Roots(xi2, L)];
  xi := [[x[1] : x in y] : y in xi];
  
  assert exists(P){[1,x1,x2] : x1 in xi[1], x2 in xi[2] | #Roots(Evaluate(f, [1,x1,x2,x])) ne 0};
  xi3 := Roots(Evaluate(f, P cat [x]));
  assert exists(xi3){x[1] : x in xi3 | 7*Kum!(P cat [x[1]]) eq Kum![0,0,0,1]};
  xi1 := [Eltseq(c) : c in (Coefficients(xi1))];
  xi2 := [Eltseq(c) : c in (Coefficients(xi2))];
  xi3 := [Eltseq(c) : c in (Coefficients(MinimalPolynomial(xi3, OK)))];
 
  return <ff, [xi1, xi2, xi3], kk>;
end intrinsic;


intrinsic CheckTorsionFieldProofRationalj(f_C::RngUPolElt, j::FldRatElt, proof::Tup) -> BoolElt
{
  Checks if a proof (of the form returned by MakeTorsionFieldProofRationalj) is valid. That is,
  prove that E[7]/(pm 1) and Kum[pp] have the same field of definition.
}
  C := HyperellipticCurve(f_C);
  Kum := KummerSurface(Jacobian(C));
  f := DefiningPolynomial(Kum);

  // unpack the fields K and Q(P)
  OK := proof[1];
  K := NumberField(Polynomial(OK[2]));
  OK := Order([Roots(Polynomial(x), K)[1][1] : x in OK]);

  // Check that the degree is maximal
  if Degree(K) ne 8 then
    return false;
  end if;
  
  // unpack the torsion of Jac(C) into min polys of the torsion point coordinates
  tors_J := proof[2];
  tors_J := [[OK!x : x in xi] : xi in tors_J];
  tors_J := [Polynomial(g) : g in tors_J];

  // the field Q(P) for some point P \in Kum[pp]
  L := NumberField(tors_J[3]);
  Kum_L := BaseChange(Kum, L);

  // Check that the degree is maximal (so Q(Kum[pp]) = L)
  if Degree(L) ne 3 then
    return false;
  end if;

  // unpack the torsion of Jac(C)
  xi := [[r[1] : r in Roots(t, L)] : t in tors_J];
  all_pts := {Kum_L![1,xi1,xi2,xi3] : xi1 in xi[1], xi2 in xi[2], xi3 in xi[3] | Evaluate(f, [1,xi1,xi2,xi3]) eq 0};
  flag := exists(P){P : P in all_pts | 7*P eq Kum_L![0,0,0,1]};
  
  //check that L is the field for pp-tors on Kum.
  if not flag then
    return false;
  end if;

  // unpack the torsion of E
  tors_E := proof[3];
  tors_E := Polynomial([OK!x : x in tors_E]);

  // Check that the degree is maximal (so Q(E[7]/(pm 1)) = L also)
  if not IsIrreducible(PolynomialRing(K)!tors_E) then
    return false;
  end if;
  
  tors_E := Roots(tors_E, L)[1][1];

  //check that L is the field for pp-tors on E/{\pm 1}
  if not Evaluate(GetX1(j), tors_E) eq 0 then
    return false;
  end if;

  return true;
end intrinsic;


///////////////////////////
// VARIANTS OF THE ABOVE //
///////////////////////////

intrinsic MakeTorsionFieldProofRationalj(C::CrvHyp, j::FldRatElt) -> Tup
{
  Given C : y^2 = f_C(x) and E defined over QQ, returns a tuple consisting of 
  (1) A basis for the ring of integers O_K of a number field K/QQ of degree 8.
  (2) A list of coefficients of min polys g_1, g_2, g_3 \in O_K[x] for which 
      the roots give a 7-torsion point on the Kummer surface of C.
  (3) The coefficients of a min poly for a root of j_X1 - j(E), where j_X1 is 
      the j-invariant map on the modular curve X_1(7).
}
  f,g := HyperellipticPolynomials(C);
  error if g ne 0, "The curve C must be of the form y^2 = f(x)";
  return MakeTorsionFieldProofRationalj(f, j);
end intrinsic;

intrinsic MakeTorsionFieldProofRationalj(C::CrvHyp, E::CrvEll) -> Tup
{
  Given C : y^2 = f_C(x) and E defined over QQ, returns a tuple consisting of 
  (1) A basis for the ring of integers O_K of a number field K/QQ of degree 8.
  (2) A list of coefficients of min polys g_1, g_2, g_3 \in O_K[x] for which 
      the roots give a 7-torsion point on the Kummer surface of C.
  (3) The coefficients of a min poly for a root of j_X1 - j(E), where j_X1 is 
      the j-invariant map on the modular curve X_1(7).
}
  f,g := HyperellipticPolynomials(C);
  error if g ne 0, "The curve C must be of the form y^2 = f(x)";
  return MakeTorsionFieldProofRationalj(f, jInvariant(E));
end intrinsic;

intrinsic CheckTorsionFieldProof(C::CrvHyp, j::FldRatElt, proof::Tup) -> BoolElt
{
  Checks if a proof (of the form returned by MakeTorsionFieldProofRationalj) is valid. That is,
  prove that E[7]/+-1 and Kum[pp] have the same field of definition.
}
  f,g := HyperellipticPolynomials(C);
  error if g ne 0, "The curve C must be of the form y^2 = f(x)";
  return CheckTorsionFieldProof(f, j, proof);
end intrinsic;

intrinsic CheckTorsionFieldProof(C::CrvHyp, E::CrvEll, proof::Tup) -> BoolElt
{
  Checks if a proof (of the form returned by MakeTorsionFieldProofRationalj) is valid. That is,
  prove that E[7]/+-1 and Kum[pp] have the same field of definition.
}
  f,g := HyperellipticPolynomials(C);
  error if g ne 0, "The curve C must be of the form y^2 = f(x)";
  return CheckTorsionFieldProof(f, jInvariant(E), proof);
end intrinsic;


/////////////////////////////////////////////////////////////////////
// CHECKING THAT THE SAME FIELDS ARE DEFINED BY THE TORSION POINTS //
// BUT THIS TIME FOR E/F AND WHERE F/Q IS SOME EXTENSION           //
/////////////////////////////////////////////////////////////////////

// Note the code to generate the proof is very similar. 

intrinsic MakeTorsionFieldProof(f_C::RngUPolElt, j::FldNumElt : proof:=<>) -> Tup
{
  Given C : y^2 = f_C(x) and E defined over QQ, returns a tuple consisting of 
  (1) A basis for the ring of integers O_K of a number field K/QQ of degree 8.
  (2) A list of coefficients of min polys g_1, g_2, g_3 \in O_K[x] for which 
      the roots give a 7-torsion point on the Kummer surface of C.
  (3) The coefficients of a min poly for a root of j_X1 - j(E), where j_X1 is 
      the j-invariant map on the modular curve X_1(7).
}
  FF := Parent(j);
  ext_ply := DefiningPolynomial(FF);
  
  if #proof eq 0 then
    vprint TalkToMe, 1: "Analytic Jacobian calculation\n-----------------------------";
    g1,g2,g1_bar,g2_bar := BothPoly24(f_C);
    
    try
      g := g1; h := g2;
      
      L := NumberField(g);
      ply := MinimalPolynomial(&+[r[1] : r in Roots(g, L)]);
      ply2 := MinimalPolynomial(&+[r[1] : r in Roots(h, L)]);

      vprint TalkToMe, 1 : "Computing optimised repn";
      K,OK := VeryOptimisedRepresentation([ply, ply2]);
      vprint TalkToMe, 1 : "Computing all the min polys etc";
      ff := [Coefficients(MinimalPolynomial(OK.i)) : i in [1..8]];
      K := NumberField(Polynomial(ff[2]));
      OK := Order([Roots(Polynomial(x), K)[1][1] : x in ff]);

      KF := ext<K | ext_ply>;  
      Embed(FF, KF, KF.1);
      
      xx := Roots(GetX0(j), KF);
      assert #xx ne 0;
      
    catch e
      g := g1_bar; h := g2_bar;
      L := NumberField(g);
      ply := MinimalPolynomial(&+[r[1] : r in Roots(g, L)]);
      ply2 := MinimalPolynomial(&+[r[1] : r in Roots(h, L)]);

      vprint TalkToMe, 1 : "Computing optimised repn";
      K,OK := VeryOptimisedRepresentation([ply, ply2]);
      vprint TalkToMe, 1 : "Computing all the min polys etc";
      ff := [Coefficients(MinimalPolynomial(OK.i)) : i in [1..8]];
      K := NumberField(Polynomial(ff[2]));
      OK := Order([Roots(Polynomial(x), K)[1][1] : x in ff]);

      KF := ext<K | ext_ply>;
      Embed(FF, KF, KF.1);
      
      xx := Roots(GetX0(j), KF);
      error if #xx eq 0, "The curves cannot possibly be congruent";
    end try;
    
    Embed(K, L, Roots(MinimalPolynomial(K.1), L)[1][1]);
    xi1 := MinimalPolynomial(Roots(g, L)[1][1], OK);
    xi2 := MinimalPolynomial(Roots(h, L)[1][1], OK);

  else //unpack data given to us
    OK := proof[1];
    K := NumberField(Polynomial(OK[2]));
    OK := Order([Roots(Polynomial(x), K)[1][1] : x in OK]);

    xi1 := proof[2][1]; xi1 := Polynomial(xi1);
    xi2 := proof[2][2]; xi1 := Polynomial(xi2);

    // the field Q(P) for some point P \in Kum[pp]
    L := NumberField(xi1);
    Embed(K, L, Roots(MinimalPolynomial(K.1), L)[1][1]);

    KF := ext<K | ext_ply>;
    Embed(FF, KF, KF.1);
    
    xx := Roots(GetX0(j), KF);
    error if #xx eq 0, "The curves are not congruent with data given";
  end if;
    
  _<x> := PolynomialRing(L);
  Kum := KummerSurface(Jacobian(HyperellipticCurve(f_C)));
  Kum := BaseChange(Kum, L);
  f := DefiningPolynomial(Kum);
  xi := [Roots(xi1, L), Roots(xi2, L)];
  xi := [[x[1] : x in y] : y in xi];
  
  assert exists(P){[1,x1,x2] : x1 in xi[1], x2 in xi[2] | #Roots(Evaluate(f, [1,x1,x2,x])) ne 0};
  xi3 := Roots(Evaluate(f, P cat [x]));
  assert exists(xi3){x[1] : x in xi3 | 7*Kum!(P cat [x[1]]) eq Kum![0,0,0,1]};
  xi1 := [Eltseq(c) : c in (Coefficients(xi1))];
  xi2 := [Eltseq(c) : c in (Coefficients(xi2))];
  xi3 := [Eltseq(c) : c in (Coefficients(MinimalPolynomial(xi3, OK)))];

  // Point of X_0(7) -> X(1) above j in K.F
  elt_0 := MinimalPolynomial(xx[1][1], K);
  
  LF := ext<L | ext_ply>;
  elt_0 := Roots(elt_0, LF)[1][1];
  kk := Roots(GetX1_to_X0(elt_0), LF)[1][1];
  kk := Eltseq(kk); // coefficients live in L, now
  kk := [MinimalPolynomial(k, OK) : k in kk]; // min polys over O_K
  kk := [[Eltseq(c) : c in Coefficients(k)] : k in kk];
  
  return <ff, [xi1, xi2, xi3], kk>;
end intrinsic;


/////////////////////////////////////////////////////
// CHECKING ISOMORPHISM OF CURVES X AND X_J[pp](7) //
/////////////////////////////////////////////////////

function HasOneSubfield(K)
  if Type(K) cmpeq FldRat then
    return true;
  elif #Subfields(K) eq 1 then
    return true;
  else
    return false;
  end if;
end function;
    

function FindGoodj(F, jj : max:=100, avoid:=0)
  _<x> := PolynomialRing(Rationals());
  found := false; count := 0;
  while (not found) and (count lt max) do
    u,v := Explode([Random([-10,10]) : i in [1,2]]);
    FF := NumberField(Factorisation(Evaluate(F, [x,u,v]))[1][1]);
    j := Evaluate(jj, [FF.1, u, v]);
    pt := [FF.1,u,v];
    if not j in [0,1728] then
      if HasOneSubfield(FF) then
        Ej := EllipticCurveWithjInvariant(j);
        flag := ProvedSurjectiveModpGaloisRep(Ej, 7, 100);
        if flag then
          if (avoid eq 0) then
            found := true;
          else //check different fields
            if not IsSquare(Discriminant(FF)*Discriminant(Parent(avoid))) then
              found := true;
            end if;
          end if;
        end if;
      end if;
    end if;
    count +:= 1;
  end while;
  return j, [MinimalPolynomial(a) : a in pt];
end function;


function FindHalfGoodj(F, jj : max:=100, avoid:=0)
  _<x> := PolynomialRing(Rationals());
  found := false; count := 0;
  while (not found) and (count lt max) do
    u,v := Explode([Random([-10,10]) : i in [1,2]]);
    FF := NumberField(Factorisation(Evaluate(F, [x,u,v]))[1][1]);
    j := Evaluate(jj, [FF.1, u, v]);
    pt := [FF.1,u,v];
    if not j in [0,1728] then
      found := true;
    end if;
    count +:= 1;
  end while;
  return j, [MinimalPolynomial(a) : a in pt];
end function;



intrinsic MakeHalfProof(f_C::RngUPolElt, X::CrvPln) -> Tup
{
  Returns the data giving a ffp-torsion point on Kum(J) such that we expect
  X to be a twist by J[ffp] or the anti-symplectic version.
}
  F := DefiningPolynomial(X);
  jj := ModuliKleinQuarticTwist(F);
  j1 := FindHalfGoodj(F, jj);
  if Type(j1) cmpeq FldRatElt then
    proof := MakeTorsionFieldProofRationalj(f_C, j1);
  else
    proof := MakeTorsionFieldProof(f_C, j1);
  end if;
  return <proof[1], proof[2]>;
end intrinsic;


intrinsic MakeProofOfIsom(f_C::RngUPolElt, X::CrvPln) -> Tup, Tup
{}
  F := DefiningPolynomial(X);
  jj := ModuliKleinQuarticTwist(F);
  j1 := FindGoodj(F, jj);
  j2 := FindGoodj(F, jj : avoid:=j1);
  proof1 := MakeTorsionFieldProof(f_C, j1);
  proof2 := MakeTorsionFieldProof(f_C, j2 : proof:=proof1);
  return proof1, proof2;
end intrinsic;


