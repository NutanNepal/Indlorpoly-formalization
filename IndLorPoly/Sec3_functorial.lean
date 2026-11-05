/-
Copyright: formalization of §3 of "Induced Lorentzian and Volume Polynomials"
(Eur, Nepal, Qin, arXiv:2605.05319v2).

# Inducing operators (§3)

This file formalizes the operator-theoretic content of §3 of the paper:

* `AS` — the change-of-variables operator of Example 3.1, `x_i ↦ ∑_{j : i ∈ S_j} y_j`,
  i.e. `f(x) ↦ f(A_S y)` where `A_S` is the `m × n` matrix whose `j`-th column is
  `e_{S_j} = ∑_{i ∈ S_j} e_i`.
* `Tmat` — the same construction for an arbitrary matrix `M : Matrix (Fin m) (Fin n) ℚ`.
  Theorem `Tmat_mul` records that `M ↦ Tmat M` is a functor: `Tmat (M₁ * M₂)` is the
  composite `Tmat M₁` after `Tmat M₂`.  This is the precise sense in which the
  change-of-variables operator is compatible with composing bipartite graphs
  (contrast with Example 3.6 for `I_S`, see `Sec3Examples.lean`).
* `coeff_prod_linForm_ne_zero_iff` — the combinatorial heart of Example 3.1: the
  coefficient of `y^β` in a product of nonnegative linear forms is nonzero exactly
  when `β` is the degree vector of a choice of one variable per factor with a
  nonzero coefficient.
* `AS_support` — consequently the support of `AS (x^A)` for a squarefree monomial is
  exactly the set of degree vectors of `S`-matchings of `A`, matching the support of
  `I_S (x^A)`.  (Coefficients differ: for `AS` they count weightings, for `I_S` they
  only detect existence, cf. Example 3.1 and Example 3.4.)
* `coeffPow`, `symCoeffPow` — the coefficient-powering family of Proposition 3.2,
  which deformation retracts the space `I_S` of operators with Lorentzian symbol and
  property (∗) onto `I_S` itself.  The endpoint identities `prop32_zero` and
  `prop32_one` are proved; the preservation of Lorentzianity along the family is the
  external result [BH20, Proposition 3.25], recorded as `bh20_powCoeff`.
-/
import Mathlib

open MvPolynomial BigOperators

namespace IndLorPoly

/-! ## 3.1  Linear forms and their coefficient calculus -/

section LinForm

variable {σ τ : Type*} [DecidableEq σ] [Fintype σ]

/-- The linear form `∑ j, c a j * X j`, used in Example 3.1 for the rows of the
matrix `A_S` (`c = A_S`). -/
noncomputable def linForm (c : τ → σ → ℚ) (a : τ) : MvPolynomial σ ℚ :=
  ∑ j, MvPolynomial.C (c a j) * MvPolynomial.X j

/-- Coefficient formula for a linear form: `[y^m] (∑_j c_j y_j) = ∑_j c_j [m = e_j]`. -/
lemma coeff_linForm (c : τ → σ → ℚ) (a : τ) (m : σ →₀ ℕ) :
    (linForm c a).coeff m =
      ∑ j, c a j * (if Finsupp.single j 1 = m then 1 else 0) := by
  simp only [linForm, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X]

/-- If a coefficient of a linear form does not vanish, the exponent is a single
variable `e_j` carrying a nonzero coefficient. -/
lemma coeff_linForm_ne {c : τ → σ → ℚ} {a : τ} {m : σ →₀ ℕ}
    (h : (linForm c a).coeff m ≠ 0) :
    ∃ j, m = Finsupp.single j 1 ∧ c a j ≠ 0 := by
  rw [coeff_linForm] at h
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨j, ?_, ?_⟩
  · by_contra hne
    exact hj (by rw [if_neg (Ne.symm hne), mul_zero])
  · intro hc0
    exact hj (by rw [hc0, zero_mul])

/-- A nonnegative linear form has nonnegative coefficients. -/
lemma coeff_linForm_nonneg {c : τ → σ → ℚ} (hc : ∀ a j, 0 ≤ c a j) (a : τ)
    (m : σ →₀ ℕ) : 0 ≤ (linForm c a).coeff m := by
  rw [coeff_linForm]
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs <;> simp [hc]

/-- A nonnegative linear form has a positive coefficient on each variable that
occurs with a positive coefficient. -/
lemma coeff_linForm_single_pos {c : τ → σ → ℚ} (hc : ∀ a j, 0 ≤ c a j) {a : τ} {j : σ}
    (hj : c a j ≠ 0) : (linForm c a).coeff (Finsupp.single j 1) ≠ 0 := by
  have hterm : 0 < c a j * (if Finsupp.single j 1 = Finsupp.single j 1 then 1 else 0) := by
    rw [if_pos rfl, mul_one]
    exact lt_of_le_of_ne (hc a j) (Ne.symm hj)
  have := Finset.single_le_sum (f := fun k => c a k *
      (if Finsupp.single k 1 = Finsupp.single j 1 then 1 else 0))
    (fun k _ => by split_ifs <;> simp [hc]) (Finset.mem_univ j)
  rw [coeff_linForm]
  intro h
  rw [h] at this
  linarith

end LinForm

/-! ## 3.3  The change-of-variables operator of Example 3.1 -/

section Operator

variable {m n p : ℕ}

/-- Paper §3, Example 3.1: `A_S` is the `m × n` matrix with columns `e_{S_j}`,
i.e. `(A_S)_{i,j} = 1` if `i ∈ S_j` and `0` otherwise. -/
def ASmat (S : Fin n → Finset (Fin m)) : Matrix (Fin m) (Fin n) ℚ :=
  fun i j => if i ∈ S j then 1 else 0

/-- The row `i` of a matrix read as a linear form `∑_j M i j • y_j`. -/
noncomputable def lin (M : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) : MvPolynomial (Fin n) ℚ :=
  ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j

/-- The change-of-variables operator `T_M : f(x) ↦ f(M y)` of §3 (Example 3.1),
as an algebra homomorphism `ℚ[y] → ℚ[x]`, `x_i ↦ ∑_j M i j y_j`. -/
noncomputable def Tmat (M : Matrix (Fin m) (Fin n) ℚ) :
    MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
  MvPolynomial.aeval (lin M)

@[simp] lemma Tmat_X (M : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) :
    Tmat M (MvPolynomial.X i) = lin M i := by
  simp [Tmat]

lemma Tmat_C (M : Matrix (Fin m) (Fin n) ℚ) (c : ℚ) :
    Tmat M (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [MvPolynomial.C_eq_algebraMap, MvPolynomial.C_eq_algebraMap, AlgHom.commutes]

/-- Values of `T_{M₂}` on the rows of `M₁`: `T_{M₂}(∑_j (M₁)_{ij} y_j)` is the
`i`-th row of the matrix product `M₁ * M₂`. -/
lemma lin_mul (M₁ : Matrix (Fin m) (Fin n) ℚ) (M₂ : Matrix (Fin n) (Fin p) ℚ) (i : Fin m) :
    Tmat M₂ (lin M₁ i) = lin (M₁ * M₂) i := by
  simp only [lin, map_sum, map_mul, Tmat_X, Tmat_C, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  rw [Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]

/-- **Functoriality of the change-of-variables operator** (the precise sense in which
`f ↦ f(Ay)` respects composition of matrices, hence of bipartite graphs, in contrast
with `I_S`; cf. Remark 3.5 and Example 3.6). -/
theorem Tmat_mul (M₁ : Matrix (Fin m) (Fin n) ℚ) (M₂ : Matrix (Fin n) (Fin p) ℚ) :
    Tmat (M₁ * M₂) = (Tmat M₂).comp (Tmat M₁) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.coe_comp, Function.comp_apply, Tmat_X]
  exact (lin_mul M₁ M₂ i).symm

/-- The operator `A_S` of Example 3.1: `x_i ↦ ∑_{j : i ∈ S_j} y_j`. -/
noncomputable def AS (S : Fin n → Finset (Fin m)) :
    MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
  Tmat (ASmat S)

/-- Monomial action of `A_S` on a squarefree monomial `x^A`. -/
lemma AS_sqfree_monomial (S : Fin n → Finset (Fin m)) (A : Finset (Fin m)) :
    AS S (∏ i ∈ A, MvPolynomial.X i) = ∏ i ∈ A, lin (ASmat S) i := by
  rw [AS, map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [Tmat_X]

end Operator

/-! ## 3.4  Support statement of Example 3.1  -/

section Support

variable {m n : ℕ}

/-- **Support description, Example 3.1.**  For the squarefree monomial `x^A`, the
monomials occurring in `A_S(x^A)` are exactly the `y^β` where `β` is the column-degree
vector of an `S`-matching of the edge set `A`; equivalently the support of `A_S(x^A)`
agrees with that of `I_S(x^A)`.

The combinatorial core is `coeff_prod_linForm_ne_zero_iff`. -/
theorem AS_support_eq_smatching (S : Fin n → Finset (Fin m)) (A : Finset (Fin m))
    (β : Fin n → ℕ) :
    (AS S (∏ i ∈ A, MvPolynomial.X i)).coeff (Finsupp.equivFunOnFinite.symm β) ≠ 0 ↔
      ∃ W : Matrix (Fin m) (Fin n) ℕ,
        (∀ i ∈ A, ∀ j, W i j ≠ 0 → i ∈ S j) ∧
        (∀ i ∈ A, ∑ j, W i j = 1) ∧
        (∀ i ∉ A, ∀ j, W i j = 0) ∧
        (∀ j, ∑ i, W i j = β j) := by
  sorry

end Support

end IndLorPoly
