/**************************************************
***************************************************
****    CODE TO APPROXIMATE THE TORSION        ****
***************************************************
**************************************************/

declare verbose TalkToMe, 1;

function NormCase(A, gg, min_plys, pm)
  // Input the analytic Jacobian
  CC<i> := BaseRing(A);
  O := ext<Integers() | min_plys[2]>;
  _, eta := NormEquation(O, 7);
  
  if pm eq 1 then
    a,b := Explode(Eltseq(eta[1]));
    M := a*gg[1] + b*gg[2];
  elif pm eq -1 then
    a,b := Explode(Eltseq(eta[2]));
    M := a*gg[1] + b*gg[2];    
  end if;

  assert Determinant(M) eq 49;
  P := BigPeriodMatrix(A); 

  alpha := Submatrix(P*Matrix(CC,M),1,1,2,2)*Submatrix(P,1,1,2,2)^-1 ;
  alpha := Matrix(CC,2,2,[Round(Real(x)) : x in Eltseq(alpha)]); //RM should be /QQ

  p := ColumnSubmatrixRange(P, 1, 1);
  p := alpha^(-1)*p; //An RM torsion point

  vprint TalkToMe, 1: "Computing min polys";
  pp := FromAnalyticJacobian(p,A); 
  xpx := pp[1][1] + pp[2][1];
  xx := pp[1][1] * pp[2][1];
  ply := MinimalPolynomial(xpx, 24);
  ply2 := MinimalPolynomial(xx, 24);

  return ply,ply2; 
end function;


function NonNormCase(A, gg, min_plys, pm)
  // Input the analytic Jacobian
  CC<i> := BaseRing(A);
  O := ext<Integers() | min_plys[2]>;
  assert IsMaximal(O);
  eta := Generators(Factorisation(ideal<O|7>)[1][1])[2];
  eta_conj := [r[1] : r in Roots(MinimalPolynomial(eta), O) | r[1] ne eta][1];
  
  if pm eq 1 then
    a,b := Explode(Eltseq(eta));
    M := a*gg[1] + b*gg[2];
  elif pm eq -1 then
    a,b := Explode(Eltseq(eta_conj));
    M := a*gg[1] + b*gg[2];    
  end if;

  assert (Determinant(M) mod 49) eq 0;
  _, n_mul := IsSquare(Determinant(M) div 49);
  
  P := BigPeriodMatrix(A); 

  alpha := Submatrix(P*Matrix(CC,M),1,1,2,2)*Submatrix(P,1,1,2,2)^-1;
  alpha := Matrix(CC,2,2,[Round(Real(x)) : x in Eltseq(alpha)]); //RM should be /QQ

  p := ColumnSubmatrixRange(P, 1, 1);
  p := alpha^(-1)*p; //An RM torsion point

  n_mul := Submatrix(P*Matrix(CC,n_mul*gg[1]),1,1,2,2)*Submatrix(P,1,1,2,2)^-1;
  p := n_mul*p;
  
  vprint TalkToMe, 1: "Computing min polys";
  pp := FromAnalyticJacobian(p,A); 
  xpx := pp[1][1] + pp[2][1];
  xx := pp[1][1] * pp[2][1];
  ply := MinimalPolynomial(xpx, 24);
  ply2 := MinimalPolynomial(xx, 24);

  return ply,ply2; 
end function;


intrinsic Poly24(f::RngUPolElt : pm:=1, prec:=1200) -> RngUPolElt, RngUPolElt
{
  If C : y^2 = f(x) compute (complex approximation to) the polynomials g_1, g_2 
  which vanish on the frak_p Torsion on the Kummer surface (with CF embedding). Jac(C)
  needs RM by an order where 7 splits. 
}
    CC<i> := ComplexField(prec);
    _<xc> := PolynomialRing(CC);
    C := HyperellipticCurve(f);
    fc := Evaluate(f, xc);

    vprintf TalkToMe, 1: "Analytic Jacobian calculation with prec=%o\n", prec;
    A := AnalyticJacobian(fc);
    E := EndomorphismRing(A); assert IsCommutative(E);
    gg := [g : g in Generators(E)];
    min_plys := [MinimalPolynomial(g) : g in gg];
    if not Degree(min_plys[1]) eq 1 then
      gg := [gg[2], gg[1]]; //id then RM
      min_plys := [MinimalPolynomial(g) : g in gg];
    end if;

    vprint TalkToMe, 1: "Computing endomorphisms";
    O := ext<Integers() | min_plys[2]>;
    flag := NormEquation(O, 7);

    if flag then
      return NormCase(A, gg, min_plys, pm);
    else
      return NonNormCase(A, gg, min_plys, pm);
    end if;
end intrinsic;


intrinsic BothPoly24(f::RngUPolElt : prec:=1200) -> RngUPolElt, RngUPolElt, RngUPolElt, RngUPolElt
{
  If C : y^2 = f(x) compute (complex approximation to) the polynomials g_1, g_2 
  which vanish on the frak_p Torsion on the Kummer surface (with CF embedding). Jac(C)
  needs RM by an order where 7 splits. 
}
    CC<i> := ComplexField(prec);
    _<xc> := PolynomialRing(CC);
    C := HyperellipticCurve(f);
    fc := Evaluate(f, xc);

    vprintf TalkToMe, 1: "Analytic Jacobian calculation with prec=%o\n", prec;
    A := AnalyticJacobian(fc);
    E := EndomorphismRing(A); assert IsCommutative(E);
    gg := [g : g in Generators(E)];
    min_plys := [MinimalPolynomial(g) : g in gg];
    if not Degree(min_plys[1]) eq 1 then
      gg := [gg[2], gg[1]]; //id then RM
      min_plys := [MinimalPolynomial(g) : g in gg];
    end if;

    vprint TalkToMe, 1: "Computing endomorphisms";
    O := ext<Integers() | min_plys[2]>;
    flag := NormEquation(O, 7);

    if flag then
      try
        g1, g2 := NormCase(A, gg, min_plys, 1);
      catch e
        vprint TalkToMe, 1: "Failed for one sign";
        g1 := 0; g2 := 0;
      end try;
      try
        g1_bar, g2_bar := NormCase(A, gg, min_plys, -1);
      catch e
        vprint TalkToMe, 1: "Failed for one sign";
        g1_bar := 0; g2_bar := 0;
      end try;
    else     
      try
        g1, g2 := NonNormCase(A, gg, min_plys, 1);
      catch e
        vprint TalkToMe, 1: "Failed for one sign";
        g1 := 0; g2 := 0;
      end try;
      try
        g1_bar, g2_bar := NonNormCase(A, gg, min_plys, -1);
      catch e
        vprint TalkToMe, 1: "Failed for one sign";
        g1_bar := 0; g2_bar := 0;
      end try;
    end if;

    return g1, g2, g1_bar, g2_bar;
end intrinsic;


