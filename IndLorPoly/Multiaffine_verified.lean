/-
Induced Lorentzian and Volume Polynomials (Eur--Nepal--Qin, arXiv 2605.05319).
Section 1: the multi-affine part computation behind Theorem 1.1.

The paper's deduction of Theorem 1.1 from Theorem 1.3 is:

  `f_{S,r}` is the multi-affine part of `I_S(∑_{B ∈ binom([m],r)} x_B)`.

This file proves the coefficient-level content of that sentence, sorry-free:

* `matchingBetas_mem`  -- membership in `matchingBetas S α` is `SMatching S α β`;
* `coeff_IS_monomial_ind` -- on square-free monomials the inducing operator has
  *unit* coefficients: the coefficient of `y^T` in `I_S(y^B)` is `1` if `B` admits an
  `S`-matching from `T`, and `0` otherwise (this is where the bridge theorem
  `smatching_ind_iff` is used);
* `coeff_elemSymm_IS` -- the coefficient of `y^T` in `I_S(∑_{|B| = r} x_B)` is
  `C_T(S)`, i.e. the multi-affine part of `I_S(e_r)` is exactly `f_{S,r}`.
-/
import IndLorPoly.Basic_verified
import IndLorPoly.Matching_verified
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

open Classical MvPolynomial

namespace IndLorPoly

variable {m n : ℕ}
variable {S : Fin n → Finset (Fin m)}

/-! ### Functions versus finitely supported functions -/

/-- Regard a function `Fin k → ℕ` as a finitely supported function (multidegree). -/
noncomputable def toF {k : ℕ} (f : Fin k → ℕ) : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm f

lemma toF_apply {k : ℕ} (f : Fin k → ℕ) (i : Fin k) : toF f i = f i := rfl

lemma toF_injective {k : ℕ} : Function.Injective (toF : (Fin k → ℕ) → Fin k →₀ ℕ) :=
  fun _ _ h => Finsupp.equivFunOnFinite.symm.injective h

@[simp]
lemma toF_support {k : ℕ} (f : Fin k → ℕ) : (toF f).support = Finset.univ.filter (fun i => f i ≠ 0) := by
  ext i
  simp [Finsupp.mem_support_iff, toF_apply]

/-- A product of powers of the variables is a single monomial. -/
lemma prod_X_pow_eq_monomial {k : ℕ} (β : Fin k → ℕ) (R : Type*) [CommSemiring R] :
    (∏ j : Fin k, (MvPolynomial.X j : MvPolynomial (Fin k) R) ^ β j)
      = monomial (toF β) 1 := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial (s := toF β)]
  refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
  intro i _ hi
  have h0 : β i = 0 := by
    by_contra hc
    exact hi (by rw [toF_support]; simp [hc])
  rw [h0, pow_zero]

/-! ### The bundle `matchingBetas` -/

/-- The factorial `α!` of a multidegree, as a real number. -/
noncomputable def vecFact {k : ℕ} (α : Fin k → ℕ) : ℝ := ∏ i, (Nat.factorial (α i) : ℝ)

/-- All `β` with `α ↔_S β`.  Finiteness: `SMatching_sum_eq` forces `β_j ≤ ∑ α_i`. -/
noncomputable def matchingBetas (S : Fin n → Finset (Fin m)) (α : Fin m → ℕ) :
    Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Iic (∑ i, α i))).filter (fun β => SMatching S α β)

/-- **Membership in `matchingBetas`.** -/
theorem matchingBetas_mem {α : Fin m → ℕ} {β : Fin n → ℕ} :
    β ∈ matchingBetas S α ↔ SMatching S α β := by
  unfold matchingBetas
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨fun j => ?_, h⟩
    have hsum := SMatching_sum_eq (S := S) h
    have hle : β j ≤ ∑ j, β j :=
      Finset.single_le_sum (f := β) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    exact Finset.mem_Iic.mpr (le_trans hle (le_of_eq hsum.symm))

/-- The factorial of an indicator vector is `1`. -/
lemma vecFact_ind (B : Finset (Fin m)) : vecFact (ind B) = 1 := by
  unfold vecFact
  rw [Finset.prod_eq_one]
  intro i _
  rw [ind]
  split <;> simp

/-! ### The inducing operator on monomials -/

/-- The action of `I_S` on `x^α`, in the normalisation of the paper. -/
noncomputable def IS_monomial (S : Fin n → Finset (Fin m)) (α : Fin m → ℕ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ β ∈ matchingBetas S α, MvPolynomial.C (vecFact α / vecFact β) * ∏ j, X j ^ (β j)

/-- The coefficient of a square-free monomial in a monomial `y^β`. -/
lemma coeff_prod_X_pow {k : ℕ} (β : Fin k → ℕ) (δ : Fin k → ℕ) :
    ((∏ j, X j ^ (β j)) : MvPolynomial (Fin k) ℝ).coeff (toF δ)
      = if β = δ then 1 else 0 := by
  rw [show ((∏ j, X j ^ (β j)) : MvPolynomial (Fin k) ℝ) = monomial (toF β) 1 from
    prod_X_pow_eq_monomial β ℝ, MvPolynomial.coeff_monomial]
  by_cases h : β = δ
  · simp [h]
  · rw [if_neg, if_neg h]
    intro hc
    exact h (toF_injective hc)

/-- **Unit coefficients on square-free monomials.**  The coefficient of `y^T` in the
`I_S`-image of the square-free monomial `x^B` is `1` exactly when `B` admits an
`S`-matching from `T`, and `0` otherwise.  In particular the coefficient does *not*
record the number of bijections `μ` (cf. the remark after Theorem 1.1). -/
theorem coeff_IS_monomial_ind (B : Finset (Fin m)) (T : Finset (Fin n)) :
    (IS_monomial S (ind B)).coeff (toF (ind (m := n) T))
      = if SMatching S (ind B) (ind T) then 1 else 0 := by
  unfold IS_monomial
  rw [MvPolynomial.coeff_sum]
  have hterm : ∀ β ∈ matchingBetas S (ind B),
      (MvPolynomial.C (vecFact (ind B) / vecFact β) * ∏ j, X j ^ (β j)).coeff (toF (ind (m := n) T))
      = if β = ind T then (vecFact (ind B) / vecFact β) else 0 := by
    intro β _
    rw [MvPolynomial.coeff_C_mul, coeff_prod_X_pow]
    split <;> simp
  rw [Finset.sum_congr rfl hterm]
  by_cases h : ind T ∈ matchingBetas S (ind B)
  · rw [Finset.sum_eq_single (ind (m := n) T)]
    · rw [if_pos rfl, vecFact_ind, vecFact_ind, div_one, if_pos]
      exact matchingBetas_mem.mp h
    · intro β _ hβ
      rw [if_neg hβ]
    · intro hnot; exact absurd h hnot
  · rw [if_neg (fun hc => h (matchingBetas_mem.mpr hc))]
    refine Finset.sum_eq_zero (fun β hβ => ?_)
    rw [if_neg]
    intro hc
    exact h (hc ▸ hβ)

/-! ### The multi-affine part of `I_S(e_r)` -/

/-- `C_T(S)` is the number of `B` of size `|T|` admitting an `S`-matching from `T`.
(An `S`-matching forces `|B| = |T|`, and `B ⊆ [m]` bounds `|B|` by `m`.) -/
theorem CT_eq_card_filter (T : Finset (Fin n)) :
    CT S T
      = ((Finset.univ.powersetCard T.card).filter (fun B => AdmitsSMatching S T B)).card := by
  unfold IndLorPoly.CT
  congr 1
  ext B
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
    Finset.subset_univ]
  constructor
  · rintro h
    refine ⟨?_, h⟩
    obtain ⟨μ, -⟩ := h
    have hc := Fintype.card_congr μ.symm
    simpa only [Fintype.card_coe] using hc
  · rintro ⟨-, h⟩
    exact h

/-! ### The multi-affine part of `I_S(e_r)` -/

/-- The elementary symmetric polynomial `e_r = ∑_{|B| = r} x_B` (written with the
`Finset`-indexed monomials `x_B = ∏_{i ∈ B} x_i`). -/
noncomputable def elemSymm (r : ℕ) : MvPolynomial (Fin m) ℝ :=
  ∑ B ∈ Finset.univ.powersetCard r, ∏ i ∈ B, (MvPolynomial.X i : MvPolynomial (Fin m) ℝ)

/-- **The multi-affine part of `I_S(e_r)` is `f_{S,r}`**, in coefficient form: the
coefficient of `y^T` in `I_S(∑_{|B|=r} x_B)` is `C_T(S)`.

Together with `IndLorPoly.Theorems` this is the content of the reduction of
Theorem 1.1 to Theorem 1.3 stated in the proof of Theorem 1.1. -/
theorem coeff_elemSymm_IS (r : ℕ) {T : Finset (Fin n)} (hT : T.card = r) :
    (∑ B ∈ Finset.univ.powersetCard r, IS_monomial S (ind B)).coeff (toF (ind (m := n) T)) = (CT S T : ℝ) := by
  rw [MvPolynomial.coeff_sum]
  have h : ∀ B ∈ Finset.univ.powersetCard r,
      (IS_monomial S (ind B)).coeff (toF (ind (m := n) T))
        = if AdmitsSMatching S T B then (1 : ℝ) else 0 := by
    intro B _
    rw [coeff_IS_monomial_ind, smatching_ind_iff]
  rw [Finset.sum_congr rfl h]
  rw [Finset.sum_boole]
  have hct : CT S T
      = ((Finset.univ.powersetCard r).filter (fun B => AdmitsSMatching S T B)).card := by
    rw [CT_eq_card_filter, hT]
  rw [hct]


/-! ### Vanishing of `C_T` and the coefficients of `f_{S,r}` -/

/-- `C_T(S) = 0` when `|T| > m`, since no subset of `[m]` has that many elements. -/
theorem CT_eq_zero_of_lt {T : Finset (Fin n)} (h : m < T.card) : CT S T = 0 := by
  have hfilter : (Finset.univ.powersetCard T.card).filter (fun B => AdmitsSMatching S T B)
      = ∅ := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨hcard, μ, -⟩
      have h2 : B.card ≤ m := by simpa using Finset.card_le_univ B
      exfalso
      omega
    · intro hB
      simp at hB
  rw [CT_eq_card_filter, hfilter, Finset.card_empty]

/-- A product of variables over a set `T'` is the monomial `x_{T'}`. -/
lemma prod_X_eq_prod_pow_ind {k : ℕ} (T' : Finset (Fin k)) :
    (∏ t ∈ T', (MvPolynomial.X t : MvPolynomial (Fin k) ℝ)) = ∏ j, X j ^ (ind T' j) := by
  rw [← Finset.prod_subset (Finset.subset_univ T')
    (fun j _ hj => by rw [ind_of_not_mem hj, pow_zero])]
  exact Finset.prod_congr rfl (fun t ht => by rw [ind_of_mem ht, pow_one])

/-- The coefficient of a multi-affine monomial in `x_{T'}`, i.e. `y_T` is a coefficient
`1` of `y_{T'}` exactly when `T = T'`. -/
lemma coeff_finset_prod_X {k : ℕ} (T T' : Finset (Fin k)) :
    ((∏ t ∈ T', (MvPolynomial.X t : MvPolynomial (Fin k) ℝ))).coeff (toF (ind T)) = if T' = T then 1 else 0 := by
  rw [prod_X_eq_prod_pow_ind T', coeff_prod_X_pow]
  by_cases h : T' = T
  · simp [h]
  · rw [if_neg, if_neg h]
    intro hc
    exact h (ind_inj (toF_injective (congrArg toF hc)))

/-- **The coefficients of `f_{S,r}`.**  The polynomial `f_{S,r}` of Theorem 1.1 is the
multi-affine polynomial whose coefficient at `y^T` is `C_T(S)` when `|T| = r` and `0`
otherwise.  This is the "easy" half of the identity
`f_{S,r} = multi-affine part of I_S(e_r)`; the substantive half is
`coeff_elemSymm_IS`. -/
theorem f_S_r_coeff (r : ℕ) (T : Finset (Fin n)) :
    (fSR S r).coeff (toF (ind T))
      = if T.card = r then (CT S T : ℝ) else 0 := by
  unfold fSR
  rw [MvPolynomial.coeff_sum]
  have hterm : ∀ T' ∈ Finset.univ.filter (fun T' : Finset (Fin n) => T'.card = r),
      (MvPolynomial.C (CT S T' : ℝ) * ∏ t ∈ T', X t).coeff (toF (ind T)) = if T' = T then (CT S T : ℝ) else 0 := by
    intro T' _
    rw [MvPolynomial.coeff_C_mul, coeff_finset_prod_X]
    by_cases h : T' = T <;> simp [h]
  rw [Finset.sum_congr rfl hterm]
  by_cases hT : T ∈ Finset.univ.filter (fun T' : Finset (Fin n) => T'.card = r)
  · rw [Finset.sum_eq_single T]
    · rw [if_pos rfl]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      rw [if_pos hT]
    · intro b _ hb
      rw [if_neg hb]
    · intro hb; exact absurd hT hb
  · rw [Finset.sum_eq_zero]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      rw [if_neg hT]
    · intro b hb
      rw [if_neg]
      intro h
      exact hT (h ▸ hb)

end IndLorPoly
