AttachSpec("../src/spec");

// The j-invariant of the modular curve X_1(7)
function GetX1(j)
  P<t> := PolynomialRing(FieldOfFractions(Parent(j)));
  j_X1 := (t^2 + t + 1)^(3)*(t^6 - 5*t^5 - 10*t^4
           + 15*t^3 + 30*t^2 + 11*t + 1)^(3)/((t)^(7)*(t
           + 1)^(7)*(t^3 - 5*t^2 - 8*t - 1));
  return Numerator(j_X1 - j);
end function;

// The j-invariant of the modular curve X_0(7)
function GetX0(j)
  P<t> := PolynomialRing(FieldOfFractions(Parent(j)));
  j_X0 := (t^2 + 5*t + 1)^3*(t^2 + 13*t + 49)/t;
  return Numerator(j_X0 - j);
end function;

// The forgetful map X_1(7) ->  X_0(7)
function GetX1_to_X0(pt_X0)
  P<t> := PolynomialRing(FieldOfFractions(Parent(pt_X0)));
  j_X1_to_X0 := (t^3 - 5*t^2 - 8*t - 1)/(t^2 + t);
  return Numerator(j_X1_to_X0 - pt_X0);
end function;


//////////////////////////////////////////////////
//////////////////////////////////////////////////
// Fetch stored data
_<xx> := PolynomialRing(Rationals());
P2<x0,x1,x2> := ProjectiveSpace(Rationals(), 2);
curves := eval Read("../data/genus-2-curves.m");
proofs := eval Read("../data/proofs.m");
twists := eval Read("../data/twists.m");

pt_search_bd := 500;
rand_pt_bd := 5;

print "**************************************************";
print "          A PROOF OF PROPOSITION 4.4              ";
print "**************************************************\n";

print "Warning: In the case when there is no point defined";
print "  over Q the following code can take some time. \n";
print "Note: We have precomputed the field extensions K[pp]";
print "  to speed this file up. However, in the `MakeProofs.m`";
print "  file we provide some intrinsics which can cook up";
print "  a proof for you if you need.\n\n";

for tw in [tw : tw in twists | #tw[2] ne 0] do
  moduli := tw[1];
  assert exists(prfs){prf : prf in proofs | prf[1] eq moduli};
  assert exists(curve){curve : curve in curves | curve[1] eq moduli};
  
  // unpack genus 2 curve
  C := HyperellipticCurve(Polynomial(curve[3]));
  Kum := KummerSurface(Jacobian(C));
  f := DefiningPolynomial(Kum);

  print "\n==================================================";
  print "Considering the genus 2 curve with\n";
  printf "** RM %o \n", moduli[1];
  if curve[4] ne "" then
    printf "** LMFDB label %o\n", curve[4];
  end if;
  if moduli[1] eq 8 then
    printf "** [A,P,Q] = %o \n\n", moduli[2];
  else
    printf "** [g,h] = %o \n\n", moduli[2];
  end if;
  
  for ii in [1..#tw[2]] do

    if ii eq 1 then 
      print "Case pp\n-------";
    elif ii eq 2 then
      print "\nCase \\bar{pp}\n-------------";
    end if;
    
    Xpm := tw[2][ii];
    proof := prfs[2][ii];
    
    // unpack the fields K and L
    OK := proof[1];
    K := NumberField(Polynomial(OK[2]));
    OK := Order([Roots(Polynomial(x), K)[1][1] : x in OK]);
    
    // unpack the torsion of Jac(C) into min polys of the torsion point coordinates
    tors_J := proof[2];
    tors_J := [[OK!x : x in xi] : xi in tors_J];
    tors_J := [Polynomial(g) : g in tors_J];

    // the field Q(Kum[p])
    L := NumberField(tors_J[3]);
    Kum_L := BaseChange(Kum, L);

    // unpack the torsion of Jac(C)
    xi := [[r[1] : r in Roots(t, L)] : t in tors_J];
    assert exists(P){Kum_L![1,xi1,xi2,xi3] : xi1 in xi[1], xi2 in xi[2], xi3 in xi[3] | Evaluate(f, [1,xi1,xi2,xi3]) eq 0};

    // prove that P is 7-torsion point
    assert 7*P eq Kum_L![0,0,0,1];
    print "* The recorded data defines a 7-torsion point";
    
    // We have now set up the field, complete the proof
    for XX in Xpm do
      
      // Check that XX is a twist of X(7)
      assert DixmierOhnoInvariants(XX : normalize:=true) eq DixmierOhnoInvariants(x0^3*x1 + x1^3*x2 + x2^3*x0 : normalize:=true);
      print "\n* X is a twist of X(7)";
      
      X := Curve(P2, XX);
      pts := PointSearch(X, pt_search_bd);

      // cases with a point
      if #pts gt 0 then
        P := pts[1];
        print "* Found a rational point on X";
        
        j := Evaluate(ModuliKleinQuarticTwist(XX), Eltseq(P));
        assert not j in [0,1728];
        print "      + The point corresponds to E/Q with j \\neq 0, 1728";
        assert ProvedSurjectiveModpGaloisRep(EllipticCurveWithjInvariant(j), 7, 1000);
        print "   - The point corresponds to E/Q with surjective rho_7";
        
        assert exists(r_0){r_0[1] : r_0 in Roots(GetX0(j), K)};
        assert exists(r_1){r_1[1] : r_1 in Roots(GetX1_to_X0(r_0), L)};
        // the following is by construction anyway
        // assert Evaluate(GetX1(j), r_1) eq 0;
        print "   - The field Q(x(P)) is correct";
        
      else
        print "\n* Didn't find rational points on X, work over two fields";

        found1 := false; found2 := false;

        LL := [];
        yz := [];
        
        while not found1 do
          y1,z1 := Explode([Random(-rand_pt_bd,rand_pt_bd) : jj in [1..2]]);
          f_1 := Evaluate(XX, [xx,y1,z1]); f_1 := Factorisation(f_1)[1][1];
          L_1 := NumberField(f_1);
          if not Type(L_1) cmpeq FldRat then // otherwise sometimes throws error
            if #Subfields(L_1) eq 1 then
              found1 := true;
              printf "   - Found field L_1";
              Append(~LL, L_1);
              Append(~yz, [y1,z1]);
            end if;
          end if;
        end while;

        while not found2 do
          y2,z2 := Explode([Random(-rand_pt_bd,rand_pt_bd) : jj in [1..2]]);
          f_2 := Evaluate(XX, [xx,y2,z2]); f_2 := Factorisation(f_2)[1][1];
          L_2 := NumberField(f_2);
          if not Type(L_2) cmpeq FldRat then // otherwise sometimes throws error
            if #Subfields(L_2) eq 1 then
              if not IsSquare(Discriminant(L_1)*Discriminant(L_2)) then
                found2 := true;
                print " and field L_2";
                Append(~LL, L_2);
                Append(~yz, [y2,z2]);
              end if;
            end if;
          end if;
        end while;

        assert not IsSquare(Discriminant(L_1)*Discriminant(L_2));
        print "      + L_1 and L_2 are non-isomorphic";
        assert #Subfields(L_1) eq 1; assert #Subfields(L_2) eq 1;
        print "      + Fields have only Q as a subfield";

        for jj in [1..2] do
          printf "   - Working with field L_%o\n", jj;
          pt := [LL[jj].1, yz[jj][1], yz[jj][2]];
          assert Evaluate(XX, pt) eq 0; // check it's a point
          j := Evaluate(ModuliKleinQuarticTwist(XX), pt);
          assert not j in [0,1728];
          printf "      + The point corresponds to E/L_%o with j \\neq 0, 1728\n", jj;
          assert ProvedSurjectiveModpGaloisRep(EllipticCurveWithjInvariant(j), 7, 1000);
          printf "      + The point corresponds to E/L_%o with surjective rho_7\n", jj;
          
          K_Ljj := ext<K | DefiningPolynomial(LL[jj])>;
          L_Ljj := ext<L | DefiningPolynomial(LL[jj])>;
          Embed(LL[jj], K_Ljj, K_Ljj.1);
          Embed(K_Ljj, L_Ljj, L_Ljj.1);
          assert exists(r_0){r_0[1] : r_0 in Roots(GetX0(j), K_Ljj)};
          assert exists(r_1){r_1[1] : r_1 in Roots(GetX1_to_X0(r_0), L_Ljj)};
          // the following is by construction anyway
          // assert Evaluate(GetX1(j), r_1) eq 0;
          printf "      + The field L_%o(x(P)) is correct\n", jj;
        end for;

      end if;
    end for;
    
  end for;

  print "\nCombining case(s) completes the proof for this curve";
end for;
