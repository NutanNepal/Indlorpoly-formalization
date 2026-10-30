/-
Formalization of §1 of "Induced Lorentzian and Volume Polynomials"
(Eur, Nepal, Qin, arXiv 2605.05319v2).
-/
import Mathlib

/-!
# §1 of *Induced Lorentzian and Volume Polynomials*: S-matchings and the matching statistic

This file formalizes the combinatorial definitions of §1 of Eur–Nepal–Qin
(arXiv 2605.05319v2):

* `AdmitsSMatching S T B` : there is a bijection `T → B` sending `t` into `S t`;
* `CT S T` : the matching statistic `C_T(S)`, the number of such `B`;
* `SMatching S α β` : Definition 1.2, an `S`-matching of degree vectors `α` and `β`
  (an edge weighting of the bipartite graph `Γ_S` with those row/column sums);
* `SMatching_sum_eq` : degree bookkeeping, `∑ α = ∑ β`;
* `fSR S r` : the polynomial `f_{S,r} = ∑_{T ∈ binom([n],r)} C_T(S) y^T` of Theorem 1.1.

The main new content here is `smatching_indicator_iff`: for *squarefree* degree vectors
`α = 1_B`, `β = 1_T` an `S`-matching exists **iff** the set `B` admits an `S`-matching from
`T`. This is exactly what identifies the multi-affine part of `I_S(∑_{|B|=r} x^B)` with
`f_{S,r}` (see `IndLorPoly.Main`), i.e. the deduction of Theorem 1.1 from Theorem 1.3.
-/

open MvPolynomial Finsupp

namespace IndLorPoly

variable {m n : ℕ}

/-! ### The matching statistic of §1 -/

/-- There is a bijection `μ : T → B` such that `μ t ∈ S t` for all `t ∈ T`.

This is the relation inside the definition `C_T(S) = |{B ⊆ [m] : ∃ μ, ...}|` of §1. -/
def AdmitsSMatching (S : Fin n → Finset (Fin m)) (T : Finset (Fin n))
    (B : Finset (Fin m)) : Prop :=
  ∃ μ : ↥T ≃ ↥B, ∀ t : ↥T, (μ t : Fin m) ∈ S (t : Fin n)

/-- The matching statistic `C_T(S)` of §1: the number of `B ⊆ [m]` admitting an
`S`-matching from `T`. -/
noncomputable def CT (S : Fin n → Finset (Fin m)) (T : Finset (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter fun B : Finset (Fin m) => AdmitsSMatching S T B).card

/-- Definition 1.2: `α ↔_S β` holds when the bipartite graph `Γ_S` on `[m] ⊔ [n]`
(edges `i--j` iff `i ∈ S_j`) admits a nonnegative integer edge weighting `W` whose
row sums are `α` and whose column sums are `β`. -/
def SMatching (S : Fin n → Finset (Fin m)) (α : Fin m → ℕ) (β : Fin n → ℕ) : Prop :=
  ∃ W : Matrix (Fin m) (Fin n) ℕ,
    (∀ i j, W i j > 0 → i ∈ S j) ∧
    (∀ i, (∑ j, W i j) = α i) ∧
    (∀ j, (∑ i, W i j) = β j)

/-- Degree bookkeeping for `S`-matchings: row and column sums of the same matrix agree. -/
theorem SMatching_sum_eq {S : Fin n → Finset (Fin m)} {α : Fin m → ℕ} {β : Fin n → ℕ}
    (h : SMatching S α β) : ∑ i, α i = ∑ j, β j := by
  obtain ⟨W, _, hα, hβ⟩ := h
  have h1 : ∑ i, α i = ∑ i, ∑ j, W i j := Finset.sum_congr rfl fun i _ => (hα i).symm
  have h2 : ∑ j, β j = ∑ j, ∑ i, W i j := Finset.sum_congr rfl fun j _ => (hβ j).symm
  rw [h1, h2, Finset.sum_comm]

/-- The polynomial `f_{S,r} = ∑_{T ∈ binom([n],r)} C_T(S) y^T` of Theorem 1.1. -/
noncomputable def fSR (S : Fin n → Finset (Fin m)) (r : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => T.card = r),
    MvPolynomial.C (CT S T : ℝ) * ∏ t ∈ T, MvPolynomial.X t

/-! ### Indicator vectors of finite sets

The squarefree degree vectors `1_B` of §1, written as finitely supported functions. -/

/-- The indicator vector `1_B ∈ ℤ_{≥0}^m` of a finite set `B`. -/
noncomputable def indFinsupp {k : ℕ} (B : Finset (Fin k)) : Fin k →₀ ℕ :=
  Finsupp.indicator B (fun _ _ => 1)

@[simp]
theorem indFinsupp_apply {k : ℕ} (B : Finset (Fin k)) (i : Fin k) :
    indFinsupp B i = if i ∈ B then 1 else 0 := by
  rw [indFinsupp, Finsupp.indicator_apply]
  split <;> simp_all

theorem indFinsupp_le_one {k : ℕ} (B : Finset (Fin k)) (i : Fin k) : indFinsupp B i ≤ 1 := by
  rw [indFinsupp_apply]; split <;> simp

@[simp]
theorem support_indFinsupp {k : ℕ} (B : Finset (Fin k)) : (indFinsupp B).support = B := by
  ext i
  rw [Finsupp.mem_support_iff, indFinsupp_apply]
  split <;> simp_all

theorem indFinsupp_eq_iff {k : ℕ} {B B' : Finset (Fin k)} :
    indFinsupp B = indFinsupp B' ↔ B = B' := by
  constructor
  · intro h
    rw [← support_indFinsupp B, ← support_indFinsupp B', h]
  · rintro rfl; rfl

theorem sum_indFinsupp {k : ℕ} (B : Finset (Fin k)) : ∑ i, indFinsupp B i = B.card := by
  simp [indFinsupp_apply, Finset.sum_ite_mem]

/-- The monomial `y^T` for a finite set `T`. -/
theorem prod_X_eq_monomial_indFinsupp {k : ℕ} (T : Finset (Fin k)) :
    (∏ t ∈ T, (MvPolynomial.X t : MvPolynomial (Fin k) ℝ)) = monomial (indFinsupp T) 1 := by
  have h := MvPolynomial.prod_X_pow (R := ℝ) (fun _ : Fin k => 1) T
  simpa [indFinsupp] using h

/-! ### Elementary 0-1 counting lemmas -/

theorem sum_ge_of_two {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) {i j : ι}
    (hij : i ≠ j) : f i + f j ≤ ∑ k, f k := by
  have h2 := Finset.add_sum_erase (Finset.univ : Finset ι) f (Finset.mem_univ j)
  have h3 : f i ≤ ∑ x ∈ (Finset.univ : Finset ι).erase j, f x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  omega

/-- A finite sum of natural numbers with a single possibly-nonzero term. -/
theorem sum_eq_single_univ {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) (i : ι)
    (h : ∀ j, j ≠ i → f j = 0) : ∑ j, f j = f i := by
  have := Finset.sum_eq_single (s := (Finset.univ : Finset ι)) (f := f) i
    (fun j _ hj => h j hj) (by simp)
  simpa using this

/-- If a sum of natural numbers is `1`, some summand is `1`. -/
theorem exists_eq_one_of_sum_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ℕ}
    (h : ∑ i, f i = 1) : ∃ i, f i = 1 := by
  have hne : ∃ i, f i ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : ∑ i, f i = 0 := Finset.sum_eq_zero fun i _ => hc i
    omega
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, ?_⟩
  have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- A sum of natural numbers equals `1` iff there is a term equal to `1` and all other terms
vanish. -/
theorem sum_eq_one_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ℕ} :
    ∑ i, f i = 1 ↔ ∃ i, f i = 1 ∧ ∀ j, j ≠ i → f j = 0 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_one_of_sum_eq_one h
    refine ⟨i, hi, fun j hj => ?_⟩
    by_contra hne
    have hpos : 1 ≤ f j := Nat.one_le_iff_ne_zero.mpr hne
    have hge := sum_ge_of_two f (Ne.symm hj)
    omega
  · rintro ⟨i, hi, hzero⟩
    rw [Finset.sum_eq_single i]
    · exact hi
    · intro j _ hj; exact hzero j hj
    · simp

/-- **The 0-1 bridge.** For squarefree degree vectors `α = 1_B` and `β = 1_T`, an
`S`-matching exists if and only if the set `B` admits an `S`-matching from `T`.

This is the key combinatorial input for deducing Theorem 1.1 from Theorem 1.3: it says that
the coefficient of `y^T` in `I_S(x^B)` (with `T` squarefree) is `1` precisely when `B` is
counted by `C_T(S)`. -/
theorem smatching_indicator_iff (S : Fin n → Finset (Fin m)) (B : Finset (Fin m))
    (T : Finset (Fin n)) :
    SMatching S (fun i => indFinsupp B i) (fun j => indFinsupp T j) ↔
      AdmitsSMatching S T B := by
  classical
  constructor
  · rintro ⟨W, hsupp, hrow, hcol⟩
    -- every column in `T` has an entry equal to `1`
    have hex : ∀ j ∈ T, ∃ i, W i j = 1 := by
      intro j hj
      have h1 : ∑ i, W i j = 1 := by
        simp [hcol j, indFinsupp_apply, hj]
      exact exists_eq_one_of_sum_eq_one h1
    choose g hg using fun (j : Fin n) (hj : j ∈ T) => hex j hj
    -- `g` lands in `B`
    have hgB : ∀ j (hj : j ∈ T), g j hj ∈ B := by
      intro j hj
      by_contra hmem
      have hrow0 : ∑ jj, W (g j hj) jj = 0 := by
        simp [hrow (g j hj), indFinsupp_apply, hmem]
      have hle : W (g j hj) j ≤ ∑ jj, W (g j hj) jj :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      rw [hrow0] at hle
      have := hg j hj
      omega
    -- `g` is injective on `T`
    have hginj : ∀ j (hj : j ∈ T) (j' : Fin n) (hj' : j' ∈ T), g j hj = g j' hj' → j = j' := by
      intro j hj j' hj' heq
      by_contra hne
      have h1 : W (g j hj) j = 1 := hg j hj
      have h2 : W (g j' hj') j' = 1 := hg j' hj'
      rw [heq] at h1
      have hrowle : W (g j' hj') j + W (g j' hj') j' ≤ ∑ jj, W (g j' hj') jj :=
        sum_ge_of_two _ hne
      simp only [hrow (g j' hj'), indFinsupp_apply] at hrowle
      split_ifs at hrowle <;> omega
    -- cardinalities agree
    have hcard : B.card = T.card := by
      have h1 : B.card = ∑ i, ∑ j, W i j := by
        rw [← sum_indFinsupp B]
        exact Finset.sum_congr rfl fun i _ => (hrow i).symm
      have h2 : T.card = ∑ j, ∑ i, W i j := by
        rw [← sum_indFinsupp T]
        exact Finset.sum_congr rfl fun j _ => (hcol j).symm
      rw [h1, h2, Finset.sum_comm]
    -- assemble the bijection
    let φ : ↥T → ↥B := fun t => ⟨g t.1 t.2, hgB t.1 t.2⟩
    have hφinj : Function.Injective φ := by
      intro t t' h
      have h' := congrArg Subtype.val h
      simp only [φ] at h'
      exact Subtype.ext (hginj t.1 t.2 t'.1 t'.2 h')
    have hφcard : Fintype.card ↥T = Fintype.card ↥B := by
      simp only [Fintype.card_coe]
      omega
    have hφbij : Function.Bijective φ :=
      (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφinj, hφcard⟩
    refine ⟨Equiv.ofBijective φ hφbij, fun t => ?_⟩
    have hpos : W (g t.1 t.2) (t.1) > 0 := by
      rw [hg t.1 t.2]; norm_num
    have hmem := hsupp (g t.1 t.2) (t.1) hpos
    simpa only [φ, Equiv.ofBijective_apply] using hmem
  · rintro ⟨μ, hμ⟩
    -- the permutation matrix of `μ`
    set W : Matrix (Fin m) (Fin n) ℕ := fun i j =>
      if ∃ t : ↥T, (t : Fin n) = j ∧ (μ t : Fin m) = i then 1 else 0 with hW
    have hWpos : ∀ i j, W i j > 0 → i ∈ S j := by
      intro i j hij
      have hij' : (if ∃ t : ↥T, (t : Fin n) = j ∧ (μ t : Fin m) = i then (1 : ℕ) else 0) > 0 := by
        simpa [hW] using hij
      split_ifs at hij' with h
      · obtain ⟨t, rfl, rfl⟩ := h
        exact hμ t
      · omega
    have hWrow : ∀ i, ∑ j, W i j = indFinsupp B i := by
      intro i
      rw [indFinsupp_apply]
      by_cases hi : i ∈ B
      · obtain ⟨t0, ht0⟩ : ∃ t0 : ↥T, (μ t0 : Fin m) = i :=
          ⟨μ.symm ⟨i, hi⟩, by simp⟩
        rw [if_pos hi]
        have hvan : ∀ j : Fin n, j ≠ (t0 : Fin n) → W i j = 0 := by
          intro j hj
          have hne : ¬ ∃ t : ↥T, (t : Fin n) = j ∧ (μ t : Fin m) = i := by
            rintro ⟨t, ht, hti⟩
            have h1 : t = t0 := by
              apply μ.injective
              exact Subtype.ext (by rw [ht0, hti])
            rw [h1] at ht
            exact hj ht.symm
          rw [hW]
          simp only [hne, if_false]
        rw [sum_eq_single_univ (fun j => W i j) (t0 : Fin n) hvan]
        have hex0 : ∃ t : ↥T, (t : Fin n) = (t0 : Fin n) ∧ (μ t : Fin m) = i := ⟨t0, rfl, ht0⟩
        simp only [hW]
        exact if_pos hex0
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun j _ => ?_
        have hne : ¬ ∃ t : ↥T, (t : Fin n) = j ∧ (μ t : Fin m) = i := by
          rintro ⟨t, -, hti⟩
          have hmem : (μ t : Fin m) ∈ B := (μ t).2
          rw [hti] at hmem
          exact hi hmem
        rw [hW]
        simp only [hne, if_false]
    have hWcol : ∀ j, ∑ i, W i j = indFinsupp T j := by
      intro j
      rw [indFinsupp_apply]
      by_cases hj : j ∈ T
      · rw [if_pos hj]
        have hvan : ∀ i : Fin m, i ≠ ((μ ⟨j, hj⟩ : ↥B) : Fin m) → W i j = 0 := by
          intro i hi
          have hne : ¬ ∃ t : ↥T, (t : Fin n) = j ∧ (μ t : Fin m) = i := by
            rintro ⟨t, ht, hti⟩
            have h1 : t = ⟨j, hj⟩ := Subtype.ext ht
            rw [h1] at hti
            exact hi hti.symm
          rw [hW]
          simp only [hne, if_false]
        rw [sum_eq_single_univ (fun i => W i j) ((μ ⟨j, hj⟩ : ↥B) : Fin m) hvan]
        have hex0 : ∃ t : ↥T, (t : Fin n) = j ∧ (μ t : Fin m) = ((μ ⟨j, hj⟩ : ↥B) : Fin m) :=
          ⟨⟨j, hj⟩, rfl, rfl⟩
        simp only [hW]
        exact if_pos hex0
      · rw [if_neg hj]
        refine Finset.sum_eq_zero fun i _ => ?_
        have hne : ¬ ∃ t : ↥T, (t : Fin n) = j ∧ (μ t : Fin m) = i := by
          rintro ⟨t, ht, -⟩
          exact hj (ht ▸ t.2)
        rw [hW]
        simp only [hne, if_false]
    exact ⟨W, hWpos, hWrow, hWcol⟩

end IndLorPoly
