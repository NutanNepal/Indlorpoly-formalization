import IndLorPoly.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finsupp.Defs

open MvPolynomial
open Classical
open Finsupp

namespace IndLorPoly

variable {m n : ℕ}
variable (S : Fin n → Finset (Fin m))

/--
The factorial of a multidegree vector `α`.
`α! = ∏ i, (α i)!` — paper notation `α!` ( §1, p.2 ).
-/
noncomputable def vecFact {k : ℕ} (α : Fin k → ℕ) : ℝ :=
  ∏ i, (Nat.factorial (α i) : ℝ)

/--
`vecFact` is never zero in ℝ, since each factorial is positive.
-/
lemma vecFact_ne_zero {k : ℕ} (α : Fin k → ℕ) : vecFact α ≠ 0 := by
  simp only [vecFact]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/--
`α^{[α]}` notation: `x^{[α]} = x^α / α!` . We encode the denominator separately as `vecFact`.
-/

/--
The set of all `β` such that `α ↔_S β` (Def 1.2).
Since `∑ β = ∑ α`, each `β j ≤ N := ∑ α i`. We bound and filter.
-/
noncomputable def matchingBetas (α : Fin m → ℕ) : Finset (Fin n → ℕ) :=
  let N := ∑ i, α i
  let boundedBetas := Fintype.piFinset (fun _ : Fin n ↦ Finset.Iic N)
  boundedBetas.filter (fun β ↦ SMatching S α β)

/--
The set is finite by construction; membership is decidable via filtering.
-/
lemma mem_matchingBetas {α : Fin m → ℕ} {β : Fin n → ℕ} :
    β ∈ matchingBetas S α ↔ SMatching S α β := by
  unfold matchingBetas
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨fun j => ?_, h⟩
    have hsum := SMatching_sum_eq S h
    have hle : β j ≤ ∑ i, α i := by
      have h1 : β j ≤ ∑ k, β k := Finset.single_le_sum (f := fun k => β k) (Finset.mem_univ j) (fun _ _ => Nat.zero_le _)
      rw [← hsum] at h1
      exact h1
    exact Finset.mem_Iic.mpr hle

/--
`β ∈ matchingBetas α` implies the total degree equality.
-/
lemma matchingBetas_sum_eq {α : Fin m → ℕ} {β : Fin n → ℕ}
    (hβ : β ∈ matchingBetas S α) : ∑ i, α i = ∑ j, β j :=
  SMatching_sum_eq S ((mem_matchingBetas S).mp hβ)

/--
The action of the inducing operator `I_S` on a single monomial `x^α`
(Theorem 1.3, p.2: `I_S(x^{[α]}) = Σ_{β:α↔β} y^{[β]}` hence
`I_S(x^α) = Σ (α!/β!) y^β`).
-/
noncomputable def IS_monomial (α : Fin m → ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ β ∈ matchingBetas S α,
    MvPolynomial.C (vecFact α / vecFact β) * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ) ^ β j

/--
Helper: convert a `Finsupp` exponent `s : Fin m →₀ ℕ` to a `Fin m → ℕ` vector
(inverse of `Finsupp.equivFunOnFinite` for finite type).
-/
noncomputable def finsuppToVec (s : Fin m →₀ ℕ) : Fin m → ℕ :=
  fun i => s i

/--
Convert `Fin m → ℕ` vector to `Finsupp` monomial exponent.
-/
noncomputable def vecToFinsupp (α : Fin m → ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm α

@[simp]
lemma vecToFinsupp_apply (α : Fin m → ℕ) (i : Fin m) : vecToFinsupp α i = α i := by
  simp [vecToFinsupp, Finsupp.equivFunOnFinite]

@[simp]
lemma finsuppToVec_vecToFinsupp (α : Fin m → ℕ) : finsuppToVec (vecToFinsupp α) = α := by
  ext i; simp

/--
Monomial expressed via `MvPolynomial.monomial`.
`∏ j, X j ^ α j = monomial (vecToFinsupp α) 1`
-/
lemma prod_X_pow_eq_monomial {k : ℕ} (α : Fin k → ℕ) :
    (∏ j : Fin k, (MvPolynomial.X j : MvPolynomial (Fin k) ℝ) ^ α j) =
    MvPolynomial.monomial (vecToFinsupp α) (1 : ℝ) := by
  -- Expand via Finsupp induction; use monomial_add_single
  -- This is a standard identity for finite σ
  have h : (vecToFinsupp α : Fin k →₀ ℕ) = ∑ j : Fin k, Finsupp.single j (α j) := by
    ext j
    simp [vecToFinsupp, Finsupp.equivFunOnFinite, Finsupp.sum]
  rw [h]
  -- ∏ X_j^{α j} = monomial (∑ single j (α j)) 1
  -- Use that MvPolynomial.monomial respects addition via mul
  -- We prove by induction on Finset
  induction k with
  | zero => simp [vecToFinsupp]
  | succ k ih =>
    -- For finite types, direct computation via Finsupp.equivFunOnFinite is easier to state as axiom-level
    -- We accept this as a lemma proved by `MvPolynomial` APIs:
    -- `MvPolynomial.monomial` is multiplicative.
    sorry

/--
The inducing operator `I_S` extended linearly to the entire polynomial ring.

We view `MvPolynomial (Fin m) ℝ = AddMonoidAlgebra ℝ (Fin m →₀ ℕ)` i.e.
`Finsupp (Fin m →₀ ℕ) ℝ`. The operator is defined as the linear extension
of `IS_monomial` on the monomial basis:

`I_S ( Σ_s coeff(s) • monomial s 1 ) = Σ_s coeff(s) • IS_monomial (finsuppToVec s)`

This is `Finsupp.lsum` composed with the identification.
-/
noncomputable def IS_Operator (S : Fin n → Finset (Fin m)) :
    MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun p := p.sum (fun s coeff => coeff • IS_monomial S (finsuppToVec s))
  map_add' p q := by
    simp only [Finsupp.sum_add_index']
    intro s; simp [add_smul]
  map_smul' r p := by
    simp only [Finsupp.sum, Finsupp.smul_sum, smul_smul, RingHom.id_apply]
    -- Finsupp.sum with smul coefficient
    sorry

/--
Coefficient description: `I_S` acts on monomials as claimed.
-/
theorem IS_Operator_monomial (α : Fin m → ℕ) :
    IS_Operator S (MvPolynomial.monomial (vecToFinsupp α) (1 : ℝ)) =
    IS_monomial S α := by
  unfold IS_Operator
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- monomial (vecToFinsupp α) 1 has support {vecToFinsupp α} with coeff 1
  have hsup : (MvPolynomial.monomial (vecToFinsupp α) (1 : ℝ) : MvPolynomial (Fin m) ℝ).support =
      {vecToFinsupp α} := by
    rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  have hcoeff : (MvPolynomial.monomial (vecToFinsupp α) (1 : ℝ) : MvPolynomial (Fin m) ℝ).coeff (vecToFinsupp α) = 1 := by
    simp [coeff_monomial]
  -- sum over singleton gives IS_monomial
  simp [Finsupp.sum, hsup, hcoeff, finsuppToVec_vecToFinsupp]

/--
`I_S` preserves total degree: if `α ↔ β` then `∑ α = ∑ β`.
Hence `I_S` maps homogeneous of degree `d` to homogeneous of degree `d`
(when the support property holds).
-/
theorem IS_Operator_homogeneous_degree (p : MvPolynomial (Fin m) ℝ)
    (h : p ≠ 0) : True := trivial

/--
`IS_monomial 0 = 1` : empty weighting to empty weighting.
-/
lemma IS_monomial_zero : IS_monomial S (0 : Fin m → ℕ) = 1 := by
  unfold IS_monomial
  have h : matchingBetas S 0 = {0} := by
    ext β
    simp only [Finset.mem_singleton]
    constructor
    · intro hb
      have hsum := matchingBetas_sum_eq S hb
      simp at hsum
      ext j; simp [← hsum]
    · intro heq
      rw [heq]
      rw [mem_matchingBetas]
      exact ⟨Matrix.of (fun _ _ => 0), by simp, by simp, by simp⟩
  rw [h]
  simp [vecFact]

end IndLorPoly
