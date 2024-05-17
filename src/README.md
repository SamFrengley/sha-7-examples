This directory contains code which implements the algorithms described in Section 3. The most notable intrinsic supplied here is `KleinQuarticTwists` which is implemented in `ComputeTwist.m`. There is a verbosity flag `TalkToMe` which, if set to `1`, outputs some information about the operations performed.

## `ComputeTwist.m`

This file contains code which implements the "main algorithm" described in Section 3.2. The main functionality provided is:
  - `KleinQuarticTwists`: This takes as input a genus 2 curve $C/\mathbb{Q}$ whose Jacobian has RM by an order in which $7$ splits. It outputs four twists of the Klein quartic (or fewer if an error results during the computation) parametrising elliptic curves (conjecturally) congruent to $J$.  Input choices are as follows:
    - `f` a Weierstrass polynomial for $C$.
    - `C` a Hyperelliptic curve.
    - `APQ` a triple of Bending's parameters for genus 2 curves with RM 8.
    - Optional argument `max_tries:=4` : This optional argument controls how many times we try running the algorithm again (from step 5 in the paper) if some unknown error occurs (which could be down to our random choices behaving badly somehow).

The following helper functions can be quite useful:
  - `ModuliKleinQuarticTwists`: This is quite a general intrinsic which should work for any twist of $X(7)$ and is simply a direct implementation of Lemma 2.4  (cf. [[Fis14](https://doi.org/10.1112/S1461157014000059), Section 4.1]).
  - `CorrectQuadraticTwist`: On input a $C/\mathbb{Q}$ and $E/\mathbb{Q}$ which are known to be congruent up to a quadratic twist, this finds the twist (by checking traces of Frobenius modulo a bunch of primes, and testing those twists supported on bad primes).
  - `CongruencesFromTwists`: This combines the above, given a bunch of twists of $X(7)$ which parametrise congruences with $E$ it point-searches up to some bound and then returns the corresponding elliptic curves (with the correct quadratic twist).

### Usage examples
  A first example, using the genus 2 curve [385641.a.385641.1](https://www.lmfdb.org/Genus2Curve/Q/385641/a/385641/1) from the LMFDB. This takes about 15 minutes seconds for us, though most of the time is spent on the `AnalyticJacobian` calculation[^1] with precision `1200`.
  ```
  AttachSpec("spec");
  SetVerbose("TalkToMe", 1);  
  // The genus 2 curve 385641.a.385641.1 from the LMFDB
  
  C := HyperellipticCurve(Polynomial([ 1, -12, 36, 6, -72, -48, -7 ])); 
  time tw,_ := KleinQuarticTwists(C); // the second output just tells you about failures
  ```

  A more involved example with a curve with RM by $D = 92$[^2]. This takes about 25 minutes for us (again the bulk of the time is spent on `AnalyticJacobian`).
  ```
  AttachSpec("spec");
  SetVerbose("TalkToMe", 1);  
  
  C := HyperellipticCurve(Polynomial([ -43341960, 111351000, -48151679, -8086290, 3757093, 574020, 2916 ])); 
  time tw,_ := KleinQuarticTwists(C);
  ```

  Now finally, the same RM 8 example again, but this time using the numerically stable approach from (see below). This takes about 5 minutes for us (most time was spent on Hilbert 90 and on resultants to compute the division polynomials).
  ```
  AttachSpec("spec");
  SetVerbose("TalkToMe", 1);  
  // The genus 2 curve 385641.a.385641.1 from the LMFDB has Bending parameters [16, 3/4, 5]

  APQ := [16, 3/4, 5];
  f := Genus2Curve(APQ);
  C1 := HyperellipticCurve(f);
  C2 := HyperellipticCurve(Polynomial([ 1, -12, 36, 6, -72, -48, -7 ])); 

  assert G2Invariants(C1) eq G2Invariants(C2);
  
  time tw,_ := KleinQuarticTwists(APQ);
  ```
    
## `TorsPolys.m`

Here we implement functions used which compute "7-division polynomials" for the Kummer surface of a genus 2 Jacobian with RM by an order in which 7 splits. Output is not guarenteed to be correct.

The main approach is using the `AnalyticJacobian` machinery in Magma (see [the documentation](https://magma.maths.usyd.edu.au/magma/handbook/text/1571)). These division polynomials have degree $(7^2 - 1)/2 = 24$ and the intrinsics are named `Poly24` and `BothPoly24` (depending if you want to only compute for one choice of prime dividing $7$ or both).

It is often here where numerical instability results in errors. By default the precision is set to the maximum of `1200` (often leading to very slow run-times). If the coefficients of your Weierstrass polynomial are very small, you can call it with `800` or so with dramatic speed-up.

  ### Numerically stable approach for RM 8

  On a side note, when $D = 8$, we give here a much better method for computing the division polynomial (this is the content of `ExplicitRM8.m`). This relies on Bending's parametrisation of genus 2 curves with RM 8 [Ben98, [Ben99](https://doi.org/10.48550/arXiv.math/9911273)] and we have (in effect) hard-coded the output of Nicholls' equations for Richelot isogenies on Kummer surfaces [[Nic18](https://ora.ox.ac.uk/objects/uuid:04cef70a-2ab9-44c2-8bbe-ca2ac33bfe41)] [[GitHub](https://github.com/cgnicholls/phd-code.git)]. The main intrinsic being `Poly24Alg` which gives the division polynomials on the Cassels--Flynn model for the Kummer surface of the genus 2 curve returned by `Genus2Curve` (both take in Bending's parameters $A,P,Q$ -- one could use the [[EK14](https://doi-org.ezp.lib.cam.ac.uk/10.2140/ant.2014.8.2297)] + [[CFM24](https://doi.org/10.48550/arXiv.2403.03191)] = [[GitHub](https://github.com/SamFrengley/genus-2-RM.git)] parameters if you wished.

  
## `hilb90.m`

In this helper-file we implement Algorithm 3.1. Note however that our code is tailored very specifically to our situation (it requries some specific input of "nice bases" for rings of integers of fields $\mathbb{Q} \subset K \subset L$ and everything in sight is some type of $q$-adic approximation).
   
## Known issues and workarounds

Since the main intrinsics rely on analytic approximations, if the coefficients of $C$ are too large numerical instability causes failures. In particular, one is advised to choose a minimised and reduced model for $C$ -- try running `MinRedBinaryForm` on the Weierstrass polynomial in Magma before invoking the code.

Our implementation breaks if $J[\mathfrak{p}]$ is a reducible Galois module (it can even be annoying ot find the polynomials defining a torsion point, since they factor over $\mathbb{Q}$). In this case one expects to obtain a diagonal twist of $X(7)$, and possibly there is an easier way.

[^1]: This raises an interesting question. Is there a better way of computing $\mathfrak{p}$-division polynomials on Kummer surfaces.
[^2]: This example worked for me, however maybe there is some random behaviour "under the hood" which causes it to fail for you. If so, please contact me so that I can change the example. Thanks :)
