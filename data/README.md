The file `genus-2-curves.m` records a number of curves of genus 2. Data in this file are tuples of the form `< < D , gh >, N, c_i, label >` where
  - `D` is the discriminant of the order which $J$ has multiplication by,
  - `gh` is a pair of coordinates specifying a point on Elkies--Kumar's model for the Humbert surface with the conventions of Cowan--Frengley--Martin (see the [GitHub](https://github.com/SamFrengley/genus-2-RM/tree/5b4695fd7f4e5c4cf2bdac4dbb9a7e23ee550ac4/models/RM_invs)) (in the case when $D = 8$ we use Bending's parameters $A,P,Q$)
  - `N` is the square-root of the conductor of $J$,
  - `c_i` are the coefficients of a degree 6 polynomial $f(x)$ so that $C : y^2 = f(x)$,
  - `label` is the LMFDB label of $C$ (if it appears there).
  
The file `twists.m` records the Klein quartic twists associated to the curves contained in `genus-2-curves.m`. In some cases an error occurred and the final string contains our best guess at the failure reason.

The files `table-1.m` and `table-2.m` are electronic forms of Tables 1 and 2 from the paper. Each entry in the list is of the form `< < D, gh >, c_i, a_i, d, N, M >` here
  - `< D, gh >` is as in `genus-2-curves.m`,
  - `c_i` are the coefficients of a degree 6 polynomial $f(x)$,
  - `a_i` are the $a$-invariants of an elliptic curve $F/\mathbb{Q}$,
  - `d` is a (square-free) integer so that $C : y^2 = d f(x)$ and $E$ is the quadratic twist $F^d/\mathbb{Q}$,
  - `N` is the square-root of the conductor of $J$,
  - `M` is the conductor of $E$.

The file `proof.m` contains data which can be used to verify the claims in Proposition 4.4. This is unpacked in `verify/4-4-prop.m`, see there for details.

Finally the two files `genus-2-curves_big-list.m` and `twists_big-list.m` record similar data to `genus-2-curves.m` and `twists.m` except that in these cases we DO NOT INCLUDE A PROOF that the twist is correct. These include those curves with $N_J \leq (500000)^2$. Any particular case can probably be verified using the `MakeProofOfIsom` intrinsic in `src/MakeProofs.m`.