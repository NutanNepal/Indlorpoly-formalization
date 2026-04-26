import IndLorPoly.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Nat.Factorial.Basic

open Polynomial MvPolynomial
open Classical

namespace IndLorPoly

variable {m n : ℕ}
variable (S : Fin n → Finset (Fin m))

/--
The factorial of a multidegree vector $\alpha$.
$\alpha! = \prod_{i} (\alpha_i)!$
-/
noncomputable def vecFact {k : ℕ} (α : Fin k → ℕ) : ℝ :=
  ∏ i, (Nat.factorial (α i) : ℝ)

/--
The set of all $\beta$ such that $\alpha \overset{\mathcal{S}}{\longleftrightarrow} \beta$.
Since $\sum \beta_j = \sum \alpha_i$, each $\beta_j$ is bounded by $N = \sum \alpha_i$.
This allows us to construct the finite set of valid $\beta$ vectors.
-/
noncomputable def matchingBetas (α : Fin m → ℕ) : Finset (Fin n → ℕ) :=
  let N := ∑ i, α i
  -- All vectors where each component is bounded by N
  let boundedBetas := Fintype.piFinset (fun _ : Fin n ↦ Finset.Iic N)
  boundedBetas.filter (fun β ↦ SMatching S α β)

/--
The action of the inducing operator $\mathcal{I}_{\mathcal{S}}$ on a single monomial $x^\alpha$.
According to the paper:
$\mathcal{I}_{\mathcal{S}} \left( \frac{x^\alpha}{\alpha!} \right) = \sum_{\beta : \alpha \leftrightarrow \beta} \frac{y^\beta}{\beta!}$

Therefore:
$\mathcal{I}_{\mathcal{S}}(x^\alpha) = \sum_{\beta : \alpha \leftrightarrow \beta} \frac{\alpha!}{\beta!} y^\beta$
-/
noncomputable def IS_monomial (α : Fin m → ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ β ∈ matchingBetas S α,
    MvPolynomial.C (vecFact α / vecFact β) * ∏ j, X j ^ β j

/--
The inducing operator $\mathcal{I}_{\mathcal{S}}$ extended linearly to the entire polynomial ring.
(This is defined by linearly extending `IS_monomial` on the monomial basis)
-/
noncomputable def IS_Operator (S : Fin n → Finset (Fin m)) : (MvPolynomial (Fin m) ℝ) →ₗ[ℝ] (MvPolynomial (Fin n) ℝ) :=
  sorry

end IndLorPoly
