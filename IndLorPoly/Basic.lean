import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

open Polynomial MvPolynomial
open Classical

namespace IndLorPoly

/-
We fix positive integers `m` and `n`.
In the paper, `[m] = {1, ..., m}` and `[n] = {1, ..., n}`.
In Lean, we model these using `Fin m` and `Fin n`.
-/
variable {m n : ℕ}

/-
`S` is a finite sequence of subsets of `[m]`, indexed by `[n]`.
We model this as a function from `Fin n` to `Finset (Fin m)`.
-/
variable (S : Fin n → Finset (Fin m))

/-
For a subset $T \subseteq [n]$, we consider a matching statistic $C_T(\mathcal{S})$,
which is the number of sets $B \subseteq [m]$ such that there is a bijection $f : T \to B$
with $f(t) \in S_t$ for all $t \in T$.

We first define what it means for a set `B` to admit an `S`-matching from `T`.
-/
def AdmitsSMatching (T : Finset (Fin n)) (B : Finset (Fin m)) : Prop :=
  ∃ f : T ≃ B, ∀ (t : T), (f t : Fin m) ∈ S t

/--
$C_T(\mathcal{S})$ is the number of such subsets $B$.
-/
noncomputable def CT (T : Finset (Fin n)) : ℕ :=
  -- We use `noncomputable` because counting the number of subsets
  -- satisfying a propositional existence statement requires classical logic.
  Nat.card { B : Finset (Fin m) // AdmitsSMatching S T B }

/--
The $\mathcal{S}$-matching condition for non-negative vectors $\alpha \in \mathbb{Z}_{\ge 0}^m$
and $\beta \in \mathbb{Z}_{\ge 0}^n$.

We say $\alpha \overset{\mathcal{S}}{\longleftrightarrow} \beta$ if there exists a weighting
$W : [m] \times [n] \to \mathbb{Z}_{\ge 0}$ such that:
1. $W_{i,j} > 0 \implies i \in S_j$ (it is a weighting of the edges of $\Gamma_{\mathcal{S}}$).
2. The row sums of $W$ equal $\alpha$.
3. The column sums of $W$ equal $\beta$.
-/
def SMatching (α : Fin m → ℕ) (β : Fin n → ℕ) : Prop :=
  ∃ W : Matrix (Fin m) (Fin n) ℕ,
    (∀ i j, W i j > 0 → i ∈ S j) ∧
    (∀ i, (∑ j, W i j) = α i) ∧
    (∀ j, (∑ i, W i j) = β j)

/--
A fundamental property of $\mathcal{S}$-matchings: if $\alpha \overset{\mathcal{S}}{\longleftrightarrow} \beta$,
then the sum of the components of $\alpha$ equals the sum of the components of $\beta$.
This corresponds to the total number of edges in the matching bipartite graph.
-/
lemma SMatching_sum_eq {α : Fin m → ℕ} {β : Fin n → ℕ} (h : SMatching S α β) :
    ∑ i, α i = ∑ j, β j := by
  rcases h with ⟨W, _, hα, hβ⟩
  -- ∑_i α_i = ∑_i ∑_j W_{i,j}
  have h1 : ∑ i, α i = ∑ i, ∑ j, W i j := Finset.sum_congr rfl (fun i _ ↦ (hα i).symm)
  -- ∑_j β_j = ∑_j ∑_i W_{i,j}
  have h2 : ∑ j, β j = ∑ j, ∑ i, W i j := Finset.sum_congr rfl (fun j _ ↦ (hβ j).symm)
  -- By exchanging the order of summation, they are equal.
  rw [h1, h2, Finset.sum_comm]

/--
The generating function $f_{\mathcal{S}, r} = \sum_{T \in \binom{[n]}{r}} C_T(\mathcal{S}) y^T$.
We model this using `MvPolynomial (Fin n) ℝ`.
-/
noncomputable def f_S_r (r : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ T ∈ Finset.univ.filter (fun T' : Finset (Fin n) ↦ T'.card = r),
    MvPolynomial.C (CT S T : ℝ) * ∏ t ∈ T, MvPolynomial.X t

end IndLorPoly
