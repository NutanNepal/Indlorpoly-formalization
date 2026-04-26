import IndLorPoly.Basic
import IndLorPoly.Operator
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Derivation

open MvPolynomial

namespace IndLorPoly

variable {m n : ℕ}

/--
A polynomial $f \in \mathbb{R}[x_1, \dots, x_n]$ is Lorentzian if it satisfies the conditions from [BH20]:
1. Homogeneous of degree d with non-negative coefficients.
2. The support is M-convex.
3. For any derivative $\partial^\alpha f$ of degree 2, its Hessian has exactly one positive eigenvalue.

Since formalizing M-convexity and eigenvalues of the Hessian requires deep results from 
convex geometry and linear algebra, we set this up as an opaque predicate for now.
This allows us to state the main theorems and work on the combinatorial structure first.
-/
opaque IsLorentzian : MvPolynomial (Fin n) ℝ → Prop

/--
A polynomial is a realizable volume polynomial over a field (here specialized to $\mathbb{R}$)
in the sense of [GHMSW2025].
-/
opaque IsRealizableVolumePolynomial : MvPolynomial (Fin n) ℝ → Prop

/--
Theorem 1.2 states that the symbol of the operator $\mathcal{I}_{\mathcal{S}}$ is a 
realizable volume polynomial.
We introduce the property that the linear operator preserves Lorentzian and volume polynomials.
-/
def PreservesLorentzian (T : (MvPolynomial (Fin m) ℝ) →ₗ[ℝ] (MvPolynomial (Fin n) ℝ)) : Prop :=
  ∀ f, IsLorentzian f → IsLorentzian (T f)

def PreservesVolume (T : (MvPolynomial (Fin m) ℝ) →ₗ[ℝ] (MvPolynomial (Fin n) ℝ)) : Prop :=
  ∀ f, IsRealizableVolumePolynomial f → IsRealizableVolumePolynomial (T f)

end IndLorPoly
