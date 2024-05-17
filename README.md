This is the GitHub repository containing code related to the paper [*Explicit 7-torsion in the Tate-Shafarevich groups of genus 2 Jacobians*](https://arxiv.org) by Sam Frengley [arXiv:??](https://arxiv.org).

Most of the code in this repository is written in [Magma](http://magma.maths.usyd.edu.au/magma/), some verifications are performed in [SageMath](https://www.sagemath.org). We have tested on Magma version 2.27-8.

## The intrinsics in `src`
The main algorithms described in the paper are implemented in the files in the directory `src`. In particular, the user should be aware of the intrinsic `KleinQuarticTwists` which takes as input a degree 6 polynomial defining a genus 2 curve with RM by $\mathcal{O}_D$ in which 7 splits and outputs four twists of the Klein quartic which are conjecturally the ones associated to this curve.

## Data
The `data` directory includes (for example) the results of Theorem 1.1 and 1.2. We include several examples of twists of the Klein quartic associated to genus 2 curves.

## Verifications
The `verify` directory provides proofs of claims made in the paper. Namely, we provide code to prove:
- Theorems 1.1 and 1.5,
- Proposition 4.4, and
- Proposition 5.2.