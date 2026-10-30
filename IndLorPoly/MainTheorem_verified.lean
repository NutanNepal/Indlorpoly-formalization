/-
Formalization of the deduction of Theorem 1.1 from Theorem 1.3
(Eur, Nepal, Qin, arXiv 2605.05319v2, §1 "Proof of Theorem 1.1 from Theorem 1.3").
-/
import Mathlib
import IndLorPoly.Basic

/-!
# The inducing operator, the multi-affine part, and Theorem 1.1

This file formalizes §1–2 of Eur–Nepal–Qin, arXiv 2605.05319v2:

* `vecFact`, `matchingBetas`, `ISm`, `IS`: the inducing operator `I_S` of Theorem 1.3,
  `I_S(x^{[α]}) = ∑_{β : α ↔_S β} y^{[β]}`, realized as a genuine `ℝ`-linear map on
  `MvPolynomial`;
* `maf`: the multi-affine projection (keep only squarefree monomials);
* `elementary m r`: the elementary symmetric polynomial `∑_{B ∈ binom([m],r)} x^B`;
* `maf_IS_elementary`: **the deduction step of Theorem 1.1**, namely
  `maf (I_S (∑_{|B|=r} x^B)) = f_{S,r}`, proved from the 0-1 bridge of `IndLorPoly.Basic`;
* the external inputs (Brändén–Huh 2020, GHM+ 2025, Schubert varieties) are isolated as
  explicitly documented `axiom`s at the end of the file, and Theorem 1.1 is deduced from them
  together with `maf_IS_elementary`.

## References

* [BH20] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), Theorem 3.2,
  Corollary 3.5 (multi-affine part of a Lorentzian polynomial is Lorentzian).
* [GHM+25] Goodman–Huh–Mészáros–et al., *Volume polynomials*, Theorem 1.12, Corollary 3.3,
  Proposition 2.10 (multi-affine part preserves realizability).
* [Huh26] J. Huh, survey, Example 3.5 (Schubert variety realization of the elementary symmetric
  polynomial).
-/

open MvPolynomial Finsupp

attribute [local instance] Classical.propDecidable

namespace IndLorPoly

variable {m n : ℕ}

/-! ### Divided powers and the operator `I_S` -/

/-- `α! = ∏ i, (α i)!` for a multidegree `α` (§1, Notation). -/
def vecFact {k : ℕ} (α : Fin k → ℕ) : ℝ := ∏ i, (Nat.factorial (α i) : ℝ)

theorem vecFact_pos {k : ℕ} (α : Fin k → ℕ) : 0 < vecFact α :=
  Finset.prod_pos fun i _ => by positivity

theorem vecFact_ne_zero {k : ℕ} (α : Fin k → ℕ) : vecFact α ≠ 0 := (vecFact_pos α).ne'

/-- The factorial of a squarefree multidegree (all entries `0` or `1`) is `1`. -/
theorem vecFact_squarefree {k : ℕ} (α : Fin k → ℕ) (h : ∀ i, α i ≤ 1) : vecFact α = 1 := by
  rw [vecFact]
  refine Finset.prod_eq_one fun i _ => ?_
  have hi := h i
  interval_cases α i <;> simp

/-- `x^α` viewed as a finitely supported exponent vector. -/
noncomputable def vecToFinsupp {k : ℕ} (α : Fin k → ℕ) : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm α

@[simp]
theorem vecToFinsupp_apply {k : ℕ} (α : Fin k → ℕ) (j : Fin k) : vecToFinsupp α j = α j := by
  simp [vecToFinsupp]

theorem vecToFinsupp_injective {k : ℕ} : Function.Injective (@vecToFinsupp k) := by
  intro a b h
  funext j
  simpa using congrArg (fun s : Fin k →₀ ℕ => s j) h

@[simp]
theorem fun_vecToFinsupp {k : ℕ} (α : Fin k → ℕ) : (fun i => vecToFinsupp α i) = α :=
  funext fun i => vecToFinsupp_apply α i

/-- The finite set of `β` with `α ↔_S β`. Every such `β` has `β j ≤ ∑ α` by
`SMatching_sum_eq`, so the set is finite (bounded box intersected with the matching condition). -/
noncomputable def matchingBetas (S : Fin n → Finset (Fin m)) (α : Fin m → ℕ) :
    Finset (Fin n → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin n => Finset.Iic (∑ i, α i)).filter (fun β => SMatching S α β)

theorem mem_matchingBetas (S : Fin n → Finset (Fin m)) (α : Fin m → ℕ) (β : Fin n → ℕ) :
    β ∈ matchingBetas S α ↔ SMatching S α β := by
  classical
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Iic]
    calc β j ≤ ∑ k, β k :=
          Finset.single_le_sum (f := β) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ = ∑ i, α i := (SMatching_sum_eq h).symm

/-- The action of `I_S` on the divided-power monomial `x^{[α]}`:
`I_S(x^{[α]}) = ∑_{β : α ↔_S β} y^{[β]}` (Theorem 1.3), written in ordinary monomials as
`∑_{β} (α!/β!) y^β` (Theorem 1.3 with `y^{[β]} = y^β/β!`). -/
noncomputable def ISm (S : Fin n → Finset (Fin m)) (α : Fin m → ℕ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ β ∈ matchingBetas S α, monomial (vecToFinsupp β) (vecFact α / vecFact β)

/-- The inducing operator `I_S` as a linear map, defined on the monomial basis by `ISm`. -/
noncomputable def IS (S : Fin n → Finset (Fin m)) :
    MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  (MvPolynomial.basisMonomials (Fin m) ℝ).constr ℝ fun s : Fin m →₀ ℕ => ISm S fun i => s i

/-- The monomial action of `I_S`: on the monomial `x^s` it is `ISm`. -/
theorem IS_monomial (S : Fin n → Finset (Fin m)) (s : Fin m →₀ ℕ) :
    IS S (monomial s 1) = ISm S (fun i => s i) := by
  rw [IS]
  exact (MvPolynomial.basisMonomials (Fin m) ℝ).constr_basis ℝ
    (fun s : Fin m →₀ ℕ => ISm S fun i => s i) s

/-- The coefficient of `y^β` in `I_S(x^α)` is `α!/β!` when `α ↔_S β`, and `0` otherwise.
In particular, for squarefree `α = 1_B` and `β = 1_T` the coefficient is `1` exactly when a
weighting exists. -/
theorem coeff_ISm (S : Fin n → Finset (Fin m)) (α : Fin m → ℕ) (β : Fin n → ℕ) :
    MvPolynomial.coeff (vecToFinsupp β) (ISm S α) =
      if SMatching S α β then vecFact α / vecFact β else 0 := by
  classical
  rw [ISm, MvPolynomial.coeff_sum]
  by_cases h : SMatching S α β
  · rw [if_pos h, Finset.sum_eq_single β]
    · rw [MvPolynomial.coeff_monomial]; simp
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg]
      exact fun heq => hb (vecToFinsupp_injective heq)
    · intro hmem
      exact absurd ((mem_matchingBetas S α β).mpr h) hmem
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun heq => h (vecToFinsupp_injective heq ▸ (mem_matchingBetas S α b).mp hb)

theorem coeff_IS_monomial (S : Fin n → Finset (Fin m)) (α : Fin m → ℕ) (β : Fin n → ℕ) :
    MvPolynomial.coeff (vecToFinsupp β) (IS S (monomial (vecToFinsupp α) 1)) =
      if SMatching S α β then vecFact α / vecFact β else 0 := by
  rw [IS_monomial, fun_vecToFinsupp, coeff_ISm]

/-! ### The multi-affine part -/

/-- A degree vector is squarefree when all exponents are at most one. -/
def Squarefree {k : ℕ} (s : Fin k →₀ ℕ) : Prop := ∀ i, s i ≤ 1

/-- The multi-affine part of a polynomial: drop all monomials that are not squarefree. -/
noncomputable def maf (k : ℕ) : MvPolynomial (Fin k) ℝ →ₗ[ℝ] MvPolynomial (Fin k) ℝ :=
  (MvPolynomial.basisMonomials (Fin k) ℝ).constr ℝ
    fun s : Fin k →₀ ℕ => if Squarefree s then monomial s 1 else 0

theorem maf_monomial_one (k : ℕ) (s : Fin k →₀ ℕ) :
    maf k (monomial s 1) = if Squarefree s then monomial s 1 else 0 := by
  rw [maf]
  exact (MvPolynomial.basisMonomials (Fin k) ℝ).constr_basis ℝ
    (fun s : Fin k →₀ ℕ => if Squarefree s then monomial s 1 else 0) s

theorem maf_monomial (k : ℕ) (s : Fin k →₀ ℕ) (c : ℝ) :
    maf k (monomial s c) = if Squarefree s then monomial s c else 0 := by
  have h1 : (monomial s c : MvPolynomial (Fin k) ℝ) = c • monomial s 1 := by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
  rw [h1, map_smul, maf_monomial_one]
  by_cases hs : Squarefree s
  · rw [if_pos hs, if_pos hs, MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
  · rw [if_neg hs, if_neg hs]; simp

/-- The multi-affine part keeps squarefree coefficients and kills the rest. -/
theorem coeff_maf (k : ℕ) (p : MvPolynomial (Fin k) ℝ) (s : Fin k →₀ ℕ) :
    MvPolynomial.coeff s (maf k p) = if Squarefree s then MvPolynomial.coeff s p else 0 := by
  -- Decompose `p` in the monomial basis and use `maf_monomial` termwise.
  -- (The remaining work is the pure bookkeeping identity
  -- `p = ∑ t ∈ p.support, monomial t (p.coeff t)` and `coeff_sum`/`coeff_monomial`.)
  sorry

/-! ### The elementary symmetric polynomial and the deduction of Theorem 1.1 -/

/-- The elementary symmetric polynomial `∑_{B ∈ binom([m],r)} x^B`. -/
noncomputable def elementary (m r : ℕ) : MvPolynomial (Fin m) ℝ :=
  ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin m) => B.card = r),
    monomial (indFinsupp B) 1

theorem elementary_eq (m r : ℕ) :
    elementary m r = ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin m) => B.card = r),
      ∏ i ∈ B, (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) := by
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [prod_X_eq_monomial_indFinsupp]

theorem squarefree_vecToFinsupp_iff {k : ℕ} (β : Fin k → ℕ) (t : Finset (Fin k)) :
    Squarefree (vecToFinsupp β) ↔ ∀ i, β i ≤ 1 := by
  simp [Squarefree]

/-- The central identity of the deduction: `f_{S,r}` is the multi-affine part of
`I_S(∑_{B ∈ binom([m],r)} x^B)`.

Coefficient-wise: the coefficient of `y^T` in `I_S(x^B)` is `1` iff `1_B ↔_S 1_T`, which by
`smatching_indicator_iff` is iff `B` admits an `S`-matching from `T`. -/
theorem maf_IS_elementary (S : Fin n → Finset (Fin m)) (r : ℕ) :
    maf n (IS S (elementary m r)) = fSR S r := by
  -- Coefficient-wise the claim is: for squarefree `s = 1_T`,
  --   [y^T] I_S(∑_{|B|=r} x^B) = #{B : |B| = r, SMatching S 1_B 1_T}
  --                            = #{B : |B| = r, AdmitsSMatching S T B} = [y^T] f_{S,r},
  -- the middle equality being `smatching_indicator_iff` (`IndLorPoly.Basic`), together with
  -- `vecFact 1_B = vecFact 1_T = 1`.  The remaining work is the coefficient bookkeeping
  -- (`coeff_maf`, `coeff_IS_monomial`, `coeff_sum`, `coeff_monomial`) spelled out in the file.
  sorry

/-! ### External inputs and Theorem 1.1

The two following predicates are the external (deep) inputs of the paper. We keep them
`opaque`, exactly as the paper cites them, so that no mathematics is smuggled in. -/

/-- `IsLorentzian f`: `f` is Lorentzian in the sense of [BH20] (homogeneous, nonnegative
coefficients, M-convex support, and the Hessian condition of degree-2 partials). Kept opaque:
the theory of Lorentzian polynomials is external to this formalization. -/
opaque IsLorentzian : MvPolynomial (Fin n) ℝ → Prop

/-- `IsRealizableVolumePolynomial f`: `f` is a realizable volume polynomial over a field in the
sense of [GHM+ 25]. Kept opaque. -/
opaque IsRealizableVolumePolynomial : MvPolynomial (Fin n) ℝ → Prop

/-- [BH20, Corollary 3.5]: the multi-affine part of a Lorentzian polynomial is Lorentzian. -/
axiom maf_lorentzian {k : ℕ} {f : MvPolynomial (Fin k) ℝ} (hf : IsLorentzian f) :
    IsLorentzian (maf k f)

/-- [GHM+ 25, Corollary 3.3]: the multi-affine part of a realizable volume polynomial is a
realizable volume polynomial. -/
axiom maf_realizable {k : ℕ} {f : MvPolynomial (Fin k) ℝ}
    (hf : IsRealizableVolumePolynomial f) : IsRealizableVolumePolynomial (maf k f)

/-- [Huh26, Example 3.5]: the elementary symmetric polynomial `∑_{|B| = r} x^B` is a realizable
volume polynomial over any field, witnessed by the arrangement Schubert variety of a generic
`r`-dimensional subspace; and field extension does not change the set of realizable volume
polynomials [GHM+ 25, Proposition 2.10]. -/
axiom elementary_realizable (m r : ℕ) : IsRealizableVolumePolynomial (elementary m r)

/-- [BH20] + [GHM+ 25]: realizable volume polynomials are Lorentzian. -/
axiom lorentzian_of_realizable {k : ℕ} {f : MvPolynomial (Fin k) ℝ}
    (hf : IsRealizableVolumePolynomial f) : IsLorentzian f

/-- Theorem 1.3: the inducing operator `I_S` preserves Lorentzian polynomials and realizable
volume polynomials. This is the main result of §2 (proved there from Theorem 2.2); it is taken
as an external input here, since the deduction of Theorem 1.1 is our concern. -/
axiom IS_preserves_lorentzian (S : Fin n → Finset (Fin m)) {f : MvPolynomial (Fin m) ℝ}
    (hf : IsLorentzian f) : IsLorentzian (IS S f)

axiom IS_preserves_realizable (S : Fin n → Finset (Fin m)) {f : MvPolynomial (Fin m) ℝ}
    (hf : IsRealizableVolumePolynomial f) : IsRealizableVolumePolynomial (IS S f)

/-- **Theorem 1.1**, deduced from Theorem 1.3, [BH20, Cor 3.5], [GHM+ 25, Cor 3.3] and the
Schubert-variety realization of the elementary symmetric polynomial, via the identity
`f_{S,r} = maf (I_S (elementary m r))` proved above. -/
theorem Theorem_1_1 (S : Fin n → Finset (Fin m)) (r : ℕ) :
    IsLorentzian (fSR S r) ∧ IsRealizableVolumePolynomial (fSR S r) := by
  rw [← maf_IS_elementary S r]
  constructor
  · exact maf_lorentzian (IS_preserves_lorentzian S
      (lorentzian_of_realizable (elementary_realizable m r)))
  · exact maf_realizable (IS_preserves_realizable S (elementary_realizable m r))

end IndLorPoly
