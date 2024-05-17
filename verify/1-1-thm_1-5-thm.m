AttachSpec("../src/spec");

print "**************************************************";
print "              PROOF OF THEOREM 1.1                ";
print "**************************************************\n";

table1 := eval Read("../data/table-1.m");

for eg in table1 do
  print "\n==================================================";
  print "Considering the genus 2 curve with";
  printf "** RM %o \n", eg[1][1];
  if eg[1][1] eq 8 then
    printf "** [A,P,Q] = %o \n", eg[1][2];
  else
    printf "** [g,h] = %o \n", eg[1][2];
  end if;
  printf "** N_J = (%o)^2\n", eg[5];
  printf "** N_E = %o\n\n", eg[6];  

  C := HyperellipticCurve(eg[2]);
  E := EllipticCurve(eg[3]);
  C := QuadraticTwist(C, eg[4]);
  J := Jacobian(C);
  E := QuadraticTwist(E, eg[4]);

  assert ProvedAbsolutelySimpleJacobian(C, 500);
  print "- Proved J is abs. simple";
  
  assert Rank(E) eq 2;
  print "- The rank of E is 2";
  assert RankBounds(J) eq 0;
  print "- The rank of J is 0";

  assert GCD(Integers()!Discriminant(E), 7) eq 1;
  print "- E has good reduction at 7";
  assert GCD(Integers()!Discriminant(C), 7) eq 1;
  print "- C has good reduction at 7";
  
  assert GCD(#TorsionSubgroup(E), 7) eq 1;
  print "- E[7] is trivial";
  assert GCD(#TorsionSubgroup(J), 7) eq 1;
  print "- J[7] is trivial";

  assert GCD(&*TamagawaNumbers(E), 7) eq 1;
  print "- Tamagawa numbers of E are prime to 7";

  print "- Checking Tamagawa numbers of J";
  print "------------------------------";
  print "Warnings are thrown by Regular model";
  fail_p := [];
  for p in BadPrimes(C) do
    try
      X := RegularModel(C, p);
      geom_order := #ComponentGroup(X);
      assert GCD(geom_order, 7) eq 1;
    catch e
      Append(~fail_p, p);
    end try;
  end for;
  assert (not 2 in fail_p) or
         (
           (eg[1] eq <8, [-10,1,-5]>) and
           eg[5] eq 3200
         );
  print "------------------------------";
  printf "   + We failed to compute the regular model at %o\n", fail_p;
  print "   + Note that 2 is not here (except at the case treated in the";
  print "     appendix to [KS23]. For the failed odd primes we can use";
  print "     Liu's genus2reduction in SageMath.\n";
end for;



print "\n**************************************************";
print "              PROOF OF THEOREM 1.5                ";
print "**************************************************\n";
table2 := eval Read("../data/table-2.m");

for eg in table2 do
  print "\n==================================================";
  print "Considering the genus 2 curve with";
  printf "** RM %o \n", eg[1][1];
  if eg[1][1] eq 8 then
    printf "** [A,P,Q] = %o \n", eg[1][2];
  else
    printf "** [g,h] = %o \n", eg[1][2];
  end if;
  printf "** N_J = (%o)^2\n", eg[5];
  printf "** N_E = %o\n\n", eg[6];  

  C := HyperellipticCurve(eg[2]);
  E := EllipticCurve(eg[3]);  
  C := QuadraticTwist(C, eg[4]);
  J := Jacobian(C);
  E := QuadraticTwist(E, eg[4]);

  assert Rank(E) eq 2;
  print "- The rank of E is 2";
  assert RankBounds(J) eq 0;
  print "- The rank of J is 0";

  assert GCD(Integers()!Discriminant(E), 7) eq 1;
  print "- E has good reduction at 7";
  assert GCD(Integers()!Discriminant(C), 7) eq 1;
  print "- C has good reduction at 7";
  
  assert GCD(#TorsionSubgroup(E), 7) eq 1;
  print "- E[7] is trivial";
  assert GCD(#TorsionSubgroup(J), 7) eq 1;
  print "- J[7] is trivial";

  assert GCD(&*TamagawaNumbers(E), 7) eq 1;
  print "- Tamagawa numbers of E are prime to 7";

  print "- Checking Tamagawa numbers of J";
  print "------------------------------";
  print "Warnings are thrown by Regular model";
  fail_p := [];
  for p in BadPrimes(C) do
    try
      X := RegularModel(C, p);
      geom_order := #ComponentGroup(X);
      assert GCD(geom_order, 7) eq 1;
    catch e
      Append(~fail_p, p);
    end try;
  end for;
  assert (not 2 in fail_p) or
         (
           (eg[1] eq <8, [-10,1,-5]>) and
           eg[5] eq 3200
         );
  print "------------------------------";
  printf "   + We failed to compute the regular model at %o\n", fail_p;
  print "   + Note that 2 is not here (except at the case treated in the";
  print "     appendix to [KS23]. For the failed odd primes we can use";
  print "     Liu's genus2reduction in SageMath.\n";
end for;
