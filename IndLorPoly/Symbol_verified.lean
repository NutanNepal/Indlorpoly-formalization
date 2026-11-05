/-
Copyright: formalization of §2 ("The symbol of `I_S`") of
C. Eur, N. Nepal, D. Qin, *Induced Lorentzian and volume polynomials*
(arXiv:2605.05319v2).

This file is self-contained: it imports only `Mathlib` and `IndLorPoly.Basic`.

Names that coincide with the (draft) `IndLorPoly/Operator.lean` of the skeleton are
re-declared here with *definitionally identical* bodies (`vecFact`, `vecToFinsupp`,
`finsuppToVec`, `matchingBetas`, `xBr`/`IS_monomial`), because `Operator.lean` still
contains `sorry`s and §2 should not depend on them.  `prod_X_pow_eq_monomial` below
fills one of those holes.
-/
import Mathlib
import IndLorPoly.Basic_verified

open MvPolynomial Finset
open Classical

namespace IndLorPoly

variable {m n : ℕ}

/-! ## 1. The `κ`-box `R[x]_κ` (paper §2, p. 3)

`R[x_1,…,x_m]_κ` denotes the set of polynomials whose support is contained in the box
`[0,κ_1] × ⋯ × [0,κ_m]`.  We write `α ≤ κ` for the pointwise order, and `boxFinset κ`
for the finite set of such `α`. -/

/-- Paper §2: `α ≤ κ` means `α i ≤ κ i` for all `i`.  `boxFinset κ` is the finite set of
multi-indices `0 ≤ α ≤ κ`. -/
def boxFinset (κ : Fin m → ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (κ i + 1))

@[simp]
lemma mem_boxFinset {κ α : Fin m → ℕ} : α ∈ boxFinset κ ↔ ∀ i, α i ≤ κ i := by
  simp [boxFinset]

/-- Paper §2: `R[x]_κ`, the set of polynomials whose support is contained in the box
`[0,κ_1] × ⋯ × [0,κ_m]`. -/
def InBox {k : ℕ} (κ : Fin k → ℕ) (f : MvPolynomial (Fin k) ℝ) : Prop :=
  ∀ s ∈ f.support, ∀ i, s i ≤ κ i

lemma InBox.zero {k : ℕ} (κ : Fin k → ℕ) : InBox κ (0 : MvPolynomial (Fin k) ℝ) := by
  intro s hs
  simp at hs

/-! ## 2. Factorials, multinomial coefficients and the divided monomials `x^[α]` -/

/-- Paper §1, Notation: `α! = α_1! ⋯ α_m!`. -/
noncomputable def vecFact {k : ℕ} (α : Fin k → ℕ) : ℝ := ∏ i, (Nat.factorial (α i) : ℝ)

/-- The multinomial coefficient `κ!/(α!(κ-α)!) = ∏_i binom(κ_i, α_i)`. -/
noncomputable def vecMultinom {k : ℕ} (κ α : Fin k → ℕ) : ℝ :=
  ∏ i, (Nat.choose (κ i) (α i) : ℝ)

lemma vecFact_pos {k : ℕ} (α : Fin k → ℕ) : 0 < vecFact α := by
  simp only [vecFact]
  exact Finset.prod_pos fun i _ => by positivity

lemma vecFact_ne_zero {k : ℕ} (α : Fin k → ℕ) : vecFact α ≠ 0 :=
  (vecFact_pos α).ne'

/-- `κ! = (α!)·((κ-α)!)·∏_i binom(κ_i,α_i)` for `α ≤ κ`, whence the multinomial
coefficient is `κ!/(α!(κ-α)!)`. -/
lemma vecMultinom_eq_div {k : ℕ} {κ α : Fin k → ℕ} (h : ∀ i, α i ≤ κ i) :
    vecMultinom κ α = vecFact κ / (vecFact α * vecFact (κ - α)) := by
  have hstep : ∀ i : Fin k,
      (Nat.choose (κ i) (α i) : ℝ) * (Nat.factorial (α i) : ℝ) *
        (Nat.factorial (κ i - α i) : ℝ) = (Nat.factorial (κ i) : ℝ) :=
    fun i => by exact_mod_cast Nat.choose_mul_factorial_mul_factorial (h i)
  have hpos : ∀ i : Fin k,
      (0 : ℝ) < (Nat.factorial (α i) : ℝ) * (Nat.factorial (κ i - α i) : ℝ) :=
    fun i => by positivity
  have hN : (∏ i, (Nat.factorial (κ i) : ℝ)) =
      ((∏ i, (Nat.choose (κ i) (α i) : ℝ)) * ∏ i, (Nat.factorial (α i) : ℝ)) *
        ∏ i, (Nat.factorial (κ i - α i) : ℝ) := by
    simp only [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => (hstep i).symm)
  have hd : ((∏ i, (Nat.factorial (α i) : ℝ)) *
      ∏ i, (Nat.factorial (κ i - α i) : ℝ)) ≠ 0 := by positivity
  simp only [vecMultinom, vecFact, Pi.sub_apply]
  rw [eq_div_iff hd, hN, mul_assoc]

/-- Paper §1, Notation: `x^[α] = x^α/α!`. -/
noncomputable def xBr {k : ℕ} (α : Fin k → ℕ) : MvPolynomial (Fin k) ℝ :=
  MvPolynomial.C ((vecFact α)⁻¹) * ∏ i, (MvPolynomial.X i) ^ α i

lemma xBr_zero {k : ℕ} : xBr (0 : Fin k → ℕ) = 1 := by
  simp [xBr, vecFact]

/-! ## 3. `Fin k → ℕ` versus `Fin k →₀ ℕ` -/

/-- The multi-index `α` as a finitely supported exponent. -/
noncomputable def vecToFinsupp {k : ℕ} (α : Fin k → ℕ) : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm α

/-- The finitely supported exponent as a multi-index. -/
noncomputable def finsuppToVec {k : ℕ} (s : Fin k →₀ ℕ) : Fin k → ℕ := fun i => s i

@[simp]
lemma vecToFinsupp_apply {k : ℕ} (α : Fin k → ℕ) (i : Fin k) : vecToFinsupp α i = α i := by
  simp [vecToFinsupp, Finsupp.equivFunOnFinite]

@[simp]
lemma finsuppToVec_vecToFinsupp {k : ℕ} (α : Fin k → ℕ) : finsuppToVec (vecToFinsupp α) = α := by
  funext i; simp [finsuppToVec]

/-- `∏_j X_j^{α_j} = monomial α 1`.  (This closes the `sorry` in
`IndLorPoly/Operator.lean`.) -/
lemma prod_X_pow_eq_monomial {k : ℕ} (α : Fin k → ℕ) :
    (∏ j : Fin k, (MvPolynomial.X j : MvPolynomial (Fin k) ℝ) ^ α j) =
      MvPolynomial.monomial (vecToFinsupp α) (1 : ℝ) := by
  have h : (Finsupp.indicator Finset.univ (fun i (_ : i ∈ Finset.univ) => α i) : Fin k →₀ ℕ) =
      vecToFinsupp α := by
    ext i
    simp [Finsupp.indicator_apply]
  rw [MvPolynomial.prod_X_pow α Finset.univ, h]

/-- `x^[α] = α^{-1} • x^α`. -/
lemma xBr_eq {k : ℕ} (α : Fin k → ℕ) :
    xBr α = MvPolynomial.C ((vecFact α)⁻¹) *
      (MvPolynomial.monomial (vecToFinsupp α) (1 : ℝ) : MvPolynomial (Fin k) ℝ) := by
  rw [xBr, prod_X_pow_eq_monomial]

/-! ## 4. The multinomial expansion behind `sym_T(y,u) = T((x+u)^κ)`

Paper §2: `sym_T(y,u) = T((x_1+u_1)^{κ_1} ⋯ (x_m+u_m)^{κ_m})`, "or equivalently,
`sym_T = κ! Σ_{0≤α≤κ} T(x^[α]) u^[κ-α]`".  The content of the equivalence is the
multinomial theorem, proved below in the ring `ℝ[x_1,…,x_m,u_1,…,u_m]`. -/

/-- **The multinomial expansion of `(x+u)^κ`**, in the ring whose variables are
`[m] ⊔ [m]` (`inl` = the `x`-variables, `inr` = the `u`-variables). -/
theorem prod_add_pow_eq_sum (κ : Fin m → ℕ) :
    (∏ i : Fin m,
        ((MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin m ⊕ Fin m) ℝ) +
          MvPolynomial.X (Sum.inr i)) ^ (κ i)) =
      ∑ α ∈ boxFinset κ,
        (∏ i, (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin m ⊕ Fin m) ℝ) ^ (α i)) *
          (∏ i, (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin m ⊕ Fin m) ℝ) ^ (κ i - α i)) *
            MvPolynomial.C (vecMultinom κ α) := by
  have h : ∀ i : Fin m,
      ((MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin m ⊕ Fin m) ℝ) +
          MvPolynomial.X (Sum.inr i)) ^ (κ i) =
        ∑ k ∈ Finset.range (κ i + 1),
          (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin m ⊕ Fin m) ℝ) ^ k *
            (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin m ⊕ Fin m) ℝ) ^ (κ i - k) *
              MvPolynomial.C ((Nat.choose (κ i) k : ℝ)) := by
    intro i
    rw [add_pow]
    simp only [map_natCast]
  simp only [h, Finset.prod_univ_sum, boxFinset]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← map_prod]
  simp only [vecMultinom]

/-! ## 5. The inducing operator `I_S` on the monomial basis -/

/-- The set of `β` with `α ↔_S β` (Definition 1.2).  Bounded by `Σ_i α_i`, which is
finite and, by `SMatching_sum_eq`, contains every such `β`. -/
noncomputable def matchingBetas (S : Fin n → Finset (Fin m)) (α : Fin m → ℕ) :
    Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Iic (∑ i, α i))).filter
    (fun β => SMatching S α β)

lemma mem_matchingBetas {S : Fin n → Finset (Fin m)} {α : Fin m → ℕ} {β : Fin n → ℕ} :
    β ∈ matchingBetas S α ↔ SMatching S α β := by
  simp only [matchingBetas, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨fun j => ?_, h⟩
    have hsum := SMatching_sum_eq h
    have h1 : β j ≤ ∑ k, β k :=
      Finset.single_le_sum (f := fun k => β k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [← hsum] at h1
    exact Finset.mem_Iic.mpr h1

/-- **The inducing operator `I_S`** (Theorem 1.3), defined on the monomial basis
`x^α` of `ℝ[x_1,…,x_m]` by `I_S(x^[α]) = Σ_{β: α ↔_S β} y^[β]`, equivalently
`I_S(x^α) = Σ_{β: α ↔_S β} (α!/β!) y^β`. -/
noncomputable def inducingOperator (S : Fin n → Finset (Fin m)) :
    MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  (MvPolynomial.basisMonomials (Fin m) ℝ).constr ℝ fun s =>
    ∑ β ∈ matchingBetas S (finsuppToVec s),
      MvPolynomial.C (vecFact (finsuppToVec s) / vecFact β) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ) ^ β j

lemma inducingOperator_monomial (S : Fin n → Finset (Fin m)) (s : Fin m →₀ ℕ) :
    inducingOperator S (MvPolynomial.monomial s (1 : ℝ)) =
      ∑ β ∈ matchingBetas S (finsuppToVec s),
        MvPolynomial.C (vecFact (finsuppToVec s) / vecFact β) *
          ∏ j, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ) ^ β j :=
  (MvPolynomial.basisMonomials (Fin m) ℝ).constr_basis ℝ _ s

/-- **Theorem 1.3, on monomials**: `I_S(x^[α]) = Σ_{β: α ↔_S β} y^[β]`. -/
theorem inducingOperator_xBr (S : Fin n → Finset (Fin m)) (α : Fin m → ℕ) :
    inducingOperator S (xBr α) = ∑ β ∈ matchingBetas S α, xBr β := by
  rw [xBr_eq, ← MvPolynomial.smul_eq_C_mul, map_smul, inducingOperator_monomial,
    finsuppToVec_vecToFinsupp]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [smul_eq_C_mul]
  simp only [xBr]
  rw [← mul_assoc, ← map_mul]
  congr 1
  have hα : vecFact α ≠ 0 := vecFact_ne_zero α
  have hβ : vecFact β ≠ 0 := vecFact_ne_zero β
  field_simp

/-! ## 6. The symbol `sym_T` (paper §2) -/

/-- Paper §2: `sym_T(y,u) := T((x_1+u_1)^{κ_1} ⋯ (x_m+u_m)^{κ_m})`, written in the
equivalent displayed form `sym_T = κ! Σ_{0≤α≤κ} T(x^[α]) u^[κ-α]`.
The `y`-variables are `Sum.inl` (`Fin n`) and the `u`-variables are `Sum.inr` (`Fin m`). -/
noncomputable def symbol (T : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)
    (κ : Fin m → ℕ) : MvPolynomial (Fin n ⊕ Fin m) ℝ :=
  ∑ α ∈ boxFinset κ,
    MvPolynomial.C (vecFact κ) *
      MvPolynomial.rename Sum.inl (T (xBr α)) *
        MvPolynomial.rename Sum.inr (xBr (κ - α))

/-- `y^[β]` as a polynomial in the `y`-variables of `ℝ[y,u]`. -/
noncomputable def yBrInl (β : Fin n → ℕ) : MvPolynomial (Fin n ⊕ Fin m) ℝ :=
  MvPolynomial.rename Sum.inl (xBr β)

/-- `u^[δ]` as a polynomial in the `u`-variables of `ℝ[y,u]`. -/
noncomputable def uBrInr (δ : Fin m → ℕ) : MvPolynomial (Fin n ⊕ Fin m) ℝ :=
  MvPolynomial.rename Sum.inr (xBr δ)

@[simp]
lemma yBrInl_apply (β : Fin n → ℕ) :
    yBrInl β = MvPolynomial.C ((vecFact β)⁻¹) *
      ∏ j, (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin n ⊕ Fin m) ℝ) ^ β j := by
  simp [yBrInl, xBr]

@[simp]
lemma uBrInr_apply (δ : Fin m → ℕ) :
    uBrInr δ = MvPolynomial.C ((vecFact δ)⁻¹) *
      ∏ i, (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin n ⊕ Fin m) ℝ) ^ δ i := by
  simp [uBrInr, xBr]

/-- **The symbol of the inducing operator** `sym_{I_S}`. -/
noncomputable def symbolIS (S : Fin n → Finset (Fin m)) (κ : Fin m → ℕ) :
    MvPolynomial (Fin n ⊕ Fin m) ℝ :=
  symbol (inducingOperator S) κ

/-- **The computation of §2**: `sym_{I_S}(y,u) = κ! Σ_{0≤α≤κ} Σ_{β: α ↔_S β} y^[β] u^[κ-α]`. -/
theorem symbolIS_eq (S : Fin n → Finset (Fin m)) (κ : Fin m → ℕ) :
    symbolIS S κ =
      ∑ α ∈ boxFinset κ, ∑ β ∈ matchingBetas S α,
        MvPolynomial.C (vecFact κ) * (yBrInl β * uBrInr (κ - α)) := by
  simp only [symbolIS, symbol, inducingOperator_xBr, yBrInl, uBrInr, map_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun β _ => mul_assoc _ _ _)

/-! ## 7. The support of `sym_{I_S}` is the lattice-point set, and `sym_{I_S}` is its
exponential generating function

Paper §2: "the symbol is the exponential generating function of its support".  The
support of `sym_{I_S}` is the set of pairs `(β, κ-α)` with `0 ≤ α ≤ κ` and `α ↔_S β`;
this is exactly the set whose lattice-point-polytope description is Theorem 2.2. -/

/-- The (index set of the) support of `sym_{I_S}`: pairs `(β, κ-α)` with `0 ≤ α ≤ κ` and
`α ↔_S β`.  Under `(α,β) ↦ (κ-α, β)` this is the lattice-point set `Q(I_E(P)) ∩ ℤ`. -/
noncomputable def symLattice (S : Fin n → Finset (Fin m)) (κ : Fin m → ℕ) :
    Finset ((Fin n → ℕ) × (Fin m → ℕ)) :=
  (boxFinset κ).biUnion fun α => (matchingBetas S α).image fun β => (β, κ - α)

lemma mem_symLattice {S : Fin n → Finset (Fin m)} {κ : Fin m → ℕ}
    {p : (Fin n → ℕ) × (Fin m → ℕ)} :
    p ∈ symLattice S κ ↔ ∃ α, α ∈ boxFinset κ ∧ SMatching S α p.1 ∧ κ - α = p.2 := by
  simp only [symLattice, Finset.mem_biUnion, Finset.mem_image, mem_matchingBetas,
    mem_boxFinset]
  constructor
  · rintro ⟨α, hα, β, hβ, rfl⟩
    exact ⟨α, hα, hβ, rfl⟩
  · rintro ⟨α, hα, hβ, hδ⟩
    exact ⟨α, hα, p.1, hβ, by simp [hδ]⟩

/-- `κ - (κ - α) = α` for `α ≤ κ`. -/
lemma sub_sub_self_vec {κ α : Fin m → ℕ} (h : ∀ i, α i ≤ κ i) : κ - (κ - α) = α := by
  funext i
  simp [Pi.sub_apply, Nat.sub_sub_self (h i)]

/-- The exponential generating function `Σ_{p ∈ A} y^{p.1} u^{p.2}/(p.1)! (p.2)!`
of a finite set of lattice points. -/
noncomputable def EGF (A : Finset ((Fin n → ℕ) × (Fin m → ℕ))) :
    MvPolynomial (Fin n ⊕ Fin m) ℝ :=
  ∑ p ∈ A,
    MvPolynomial.C ((vecFact p.1 * vecFact p.2)⁻¹) *
      (∏ j, (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin n ⊕ Fin m) ℝ) ^ p.1 j) *
        ∏ i, (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin n ⊕ Fin m) ℝ) ^ p.2 i

/-- The fibre of `symLattice S κ` over `α`: the lattice points `(β, κ-α)` with `α ↔_S β`. -/
noncomputable def symLatticeFam (S : Fin n → Finset (Fin m)) (κ : Fin m → ℕ)
    (α : Fin m → ℕ) : Finset ((Fin n → ℕ) × (Fin m → ℕ)) :=
  (matchingBetas S α).image fun β => (β, κ - α)

lemma symLatticeFam_inj {S : Fin n → Finset (Fin m)} {κ : Fin m → ℕ} {α : Fin m → ℕ} :
    Set.InjOn (fun β : Fin n → ℕ => (β, κ - α)) ↑(matchingBetas S α) := by
  intro β₁ _ β₂ _ h
  exact congrArg Prod.fst h

lemma symLattice_eq_biUnion (S : Fin n → Finset (Fin m)) (κ : Fin m → ℕ) :
    symLattice S κ = (boxFinset κ).biUnion (symLatticeFam S κ) := rfl

/-- **`sym_{I_S}` is the exponential generating function of the lattice points of its
support.**  Explicitly: the coefficient of `y^β u^δ` is `κ!/(β! δ!)` when `δ = κ-α` for
some `0 ≤ α ≤ κ` with `α ↔_S β`, and vanishes on every other pair.  This is the
displayed computation of §2 together with the EGF interpretation stated there. -/
theorem symbolIS_eq_latticeEGF (S : Fin n → Finset (Fin m)) (κ : Fin m → ℕ) :
    symbolIS S κ =
      ∑ α ∈ boxFinset κ, ∑ p ∈ symLatticeFam S κ α,
        MvPolynomial.C (vecFact κ * (vecFact p.1 * vecFact p.2)⁻¹) *
          ((∏ j, (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin n ⊕ Fin m) ℝ) ^ p.1 j) *
            ∏ i, (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin n ⊕ Fin m) ℝ) ^ p.2 i) := by
  rw [symbolIS_eq]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  simp only [symLatticeFam]
  rw [Finset.sum_image (symLatticeFam_inj (κ := κ))]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  simp only [yBrInl_apply, uBrInr_apply]
  have hc : (MvPolynomial.C (vecFact κ * (vecFact β * vecFact (κ - α))⁻¹) :
        MvPolynomial (Fin n ⊕ Fin m) ℝ) =
      MvPolynomial.C (vecFact κ) * MvPolynomial.C ((vecFact β)⁻¹) *
        MvPolynomial.C ((vecFact (κ - α))⁻¹) := by
    rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
    congr 1
    rw [mul_inv]
    ring
  rw [hc]
  ring


/-! ## 8. Proposition 2.1: the symbol criterion

Paper §2, Proposition 2.1.  Both halves are *imported* results of [BH20] and [GHM+25];
they are recorded here as clearly-marked `axiom`s, exactly as the paper uses them, and
never unfolded.  The Lorentzian / volume predicates are opaque for the same reason
(they mention Hessians of derivatives and intersection theory of polymatroids). -/

/-- `IsLorentzianPoly σ f`: `f ∈ ℝ[x_σ]` is Lorentzian in the sense of [BH20]
(Definition 2.4: homogeneous, non-negative coefficients, M-convex support, and the
quadratic form of every degree-`2` derivative has exactly one positive eigenvalue).
Generalises `IndLorPoly.IsLorentzian` (the case `σ = Fin n`) to an arbitrary finite
variable set, which is needed for the symbol, whose variables are `[n] ⊔ [m]`.
Opaque: the paper only ever uses the two closure properties formulated below. -/
opaque IsLorentzianPoly (σ : Type) [Fintype σ] [DecidableEq σ]
    (f : MvPolynomial σ ℝ) : Prop

/-- `IsVolumePoly σ f`: `f ∈ ℝ[x_σ]` is a realizable volume polynomial over `ℝ` in the
sense of [GHM+25].  Opaque, cf. `IsLorentzianPoly`. -/
opaque IsVolumePoly (σ : Type) [Fintype σ] [DecidableEq σ]
    (f : MvPolynomial σ ℝ) : Prop

/-- **Proposition 2.1, first half** — [BH20, Theorem 3.2].  If `T` is a linear operator
on the `κ`-box whose symbol is Lorentzian, then `T` maps Lorentzian polynomials in the
`κ`-box to Lorentzian polynomials. -/
axiom Prop_2_1_lorentzian {m n : ℕ} (T : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)
    (κ : Fin m → ℕ) (hκ : ∀ i, 0 < κ i)
    (hsym : IsLorentzianPoly (Fin n ⊕ Fin m) (symbol T κ))
    (f : MvPolynomial (Fin m) ℝ) (hf : IsLorentzianPoly (Fin m) f) (hbox : InBox κ f) :
    IsLorentzianPoly (Fin n) (T f)

/-- **Proposition 2.1, second half** — [GHM+25, Theorem 1.12].  If the symbol of `T` is
a realizable volume polynomial, then so is the image of every realizable volume
polynomial in the `κ`-box. -/
axiom Prop_2_1_volume {m n : ℕ} (T : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)
    (κ : Fin m → ℕ) (hκ : ∀ i, 0 < κ i)
    (hsym : IsVolumePoly (Fin n ⊕ Fin m) (symbol T κ))
    (f : MvPolynomial (Fin m) ℝ) (hf : IsVolumePoly (Fin m) f) (hbox : InBox κ f) :
    IsVolumePoly (Fin n) (T f)

/-! ## 9. The reduction "Theorem 2.2 ⇒ Theorem 1.3"

Paper §2: "[EL24, Corollary 1.4 & Remark 3.21] states that the exponential generating
function of a linearly realizable polymatroid over `k` is a realizable volume polynomial
over `k`", and "[BH20, Theorem 4.6]: realizable volume polynomials are Lorentzian".
Together with Proposition 2.1 this gives Theorem 1.3 from Theorem 2.2. -/

/-- **Theorem 2.2 ⇒ Theorem 1.3** (paper, proof of Theorem 1.3): if the symbol of the
inducing operator `I_S` is a realizable volume polynomial (Theorem 2.2, formalized
separately via Theorem `symbolIS_eq_latticeEGF` plus the polymatroid realisability
theory), then `I_S` preserves realizable volume polynomials on every `κ`-box, and
therefore on all of `ℝ[x]`. -/
theorem Theorem_1_3_of_symbol_volume {m n : ℕ} (S : Fin n → Finset (Fin m))
    (h : ∀ κ : Fin m → ℕ, (∀ i, 0 < κ i) → IsVolumePoly (Fin n ⊕ Fin m) (symbolIS S κ))
    (κ : Fin m → ℕ) (hκ : ∀ i, 0 < κ i) (f : MvPolynomial (Fin m) ℝ)
    (hf : IsVolumePoly (Fin m) f) (hbox : InBox κ f) :
    IsVolumePoly (Fin n) (inducingOperator S f) :=
  Prop_2_1_volume (inducingOperator S) κ hκ (h κ hκ) f hf hbox

end IndLorPoly
