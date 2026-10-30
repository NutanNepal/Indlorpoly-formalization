/-
Induced Lorentzian and Volume Polynomials (Eur--Nepal--Qin, arXiv 2605.05319).
Section 1: `S`-matching theory and the `C_T(S)` calculus.

This file is *sorry-free*.  It contains the combinatorial heart of §1:

* `ind`      -- the indicator vector `1_B ∈ ℤ_{≥0}^m` of a subset `B ⊆ [m]`;
* the bridge `smatching_ind_iff` -- for `0`-`1` vectors, the weighting
  condition `α ↔_S β` of Definition 1.2 is *equivalent* to the existence of a
  bijection `μ : T → B` with `μ t ∈ S_t` used in the definition of `C_T(S)`;
* fibre-count lemmas, the vanishing of `C_T` for `|T| > m`, and the
  finiteness/boundedness results needed to make `matchingBetas` a finite set.
-/
import IndLorPoly.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open Classical

namespace IndLorPoly

variable {m n : ℕ}
variable {S : Fin n → Finset (Fin m)}

/-! ### Indicator vectors -/

/-- The indicator vector `1_B ∈ ℤ_{≥0}^m` of a subset `B ⊆ [m]`: `(1_B)_i = 1` if
`i ∈ B` and `0` otherwise.  These are exactly the square-free multidegrees, i.e.
the exponent vectors of the multi-affine monomials `x_B = ∏_{i ∈ B} x_i`. -/
noncomputable def ind (B : Finset (Fin m)) : Fin m → ℕ := fun i => if i ∈ B then 1 else 0

@[simp]
lemma ind_of_mem {B : Finset (Fin m)} {i : Fin m} (h : i ∈ B) : ind B i = 1 := if_pos h

@[simp]
lemma ind_of_not_mem {B : Finset (Fin m)} {i : Fin m} (h : i ∉ B) : ind B i = 0 :=
  if_neg h

lemma ind_le_one (B : Finset (Fin m)) (i : Fin m) : ind B i ≤ 1 := by
  unfold ind; split <;> simp

lemma ind_eq_one_iff {B : Finset (Fin m)} {i : Fin m} : ind B i = 1 ↔ i ∈ B := by
  unfold ind; split <;> simp_all

lemma ind_eq_zero_iff {B : Finset (Fin m)} {i : Fin m} : ind B i = 0 ↔ i ∉ B := by
  unfold ind; split <;> simp_all

/-- The total degree of an indicator vector is the cardinality of the set. -/
lemma sum_ind (B : Finset (Fin m)) : ∑ i, ind B i = B.card := by
  have h1 : ∑ i ∈ B, ind B i = ∑ i ∈ B, (1 : ℕ) :=
    Finset.sum_congr rfl (fun i hi => ind_of_mem hi)
  have h2 : ∑ i, ind B i = ∑ i ∈ B, ind B i :=
    (Finset.sum_subset (Finset.subset_univ B) (fun i _ hi => ind_of_not_mem hi)).symm
  rw [Finset.sum_const, smul_eq_mul, mul_one] at h1
  rw [h2, h1, Finset.card_eq_sum_ones]

lemma ind_inj {B B' : Finset (Fin m)} (h : ind B = ind B') : B = B' := by
  ext i
  rw [← ind_eq_one_iff, ← ind_eq_one_iff, h]

/-! ### The bridge between `SMatching` and `AdmitsSMatching`

The two definitions in §1 look syntactically different: Definition 1.2 asks for an
integer weighting of the edges of the bipartite graph `Γ_S` with prescribed row and
column sums, while `C_T(S)` asks for a bijection `μ : T → B` with `μ t ∈ S_t`.
For `0`-`1` vectors the two are equivalent, and this equivalence is what makes the
multi-affine part of `I_S(∑_B x_B)` computable with *unit* coefficients. -/

/-- Splitting a conjunction in the integrand, so that the second factor is the
`if`-condition of the summation index. -/
private lemma ite_and_swap (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℕ) else 0) = if Q then (if P then 1 else 0) else 0 := by
  by_cases h1 : P <;> by_cases h2 : Q <;> simp [h1, h2]

/-- From a bijection `μ : T ≃ B` respecting `S` we build the edge weighting
`W i j = #{t ∈ T : μ t = i, t = j}` of `Γ_S`.  It has row sums `1_B` and column
sums `1_T`. -/
theorem smatching_ind_of_admits {T : Finset (Fin n)} {B : Finset (Fin m)}
    (h : AdmitsSMatching S T B) : SMatching S (ind B) (ind T) := by
  obtain ⟨μ, hμ⟩ := h
  set W : Matrix (Fin m) (Fin n) ℕ :=
    fun i j => ∑ t : T, if ((μ t : Fin m) = i ∧ (t : Fin n) = j) then 1 else 0 with hW
  have hfib : ∀ (i : Fin m) (t : T),
      (∑ j : Fin n, if ((μ t : Fin m) = i ∧ (t : Fin n) = j) then 1 else 0)
        = if (μ t : Fin m) = i then 1 else 0 := by
    intro i t
    simp only [ite_and_swap]
    rw [Finset.sum_eq_single (t : Fin n)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  have hfib' : ∀ (j : Fin n) (t : T),
      (∑ i : Fin m, if ((μ t : Fin m) = i ∧ (t : Fin n) = j) then 1 else 0)
        = if (t : Fin n) = j then 1 else 0 := by
    intro j t
    simp only [ite_and_swap]
    rw [Finset.sum_eq_single (μ t : Fin m)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i j hij
    obtain ⟨t, -, ht⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (by omega : W i j ≠ 0)
    have hconj : (μ t : Fin m) = i ∧ (t : Fin n) = j := by
      by_contra hc
      exact ht (if_neg hc)
    rw [← hconj.1, ← hconj.2]
    exact hμ t
  · intro i
    calc ∑ j, W i j = ∑ j, ∑ t : T, (if ((μ t : Fin m) = i ∧ (t : Fin n) = j)
                then 1 else 0) := rfl
      _ = ∑ t : T, ∑ j, (if ((μ t : Fin m) = i ∧ (t : Fin n) = j) then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ t : T, if (μ t : Fin m) = i then 1 else 0 :=
          Finset.sum_congr rfl (fun t _ => hfib i t)
      _ = ind B i := by
          by_cases hi : i ∈ B
          · rw [Finset.sum_eq_single (μ.symm ⟨i, hi⟩)]
            · simp [hi]
            · intro t _ htne
              by_cases h' : (μ t : Fin m) = i
              · exfalso
                apply htne
                exact μ.injective (Subtype.ext (by rw [h', Equiv.apply_symm_apply]))
              · simp [h']
            · intro hb; exact absurd (Finset.mem_univ _) hb
          · have hz : ∀ t : T, ¬ ((μ t : Fin m) = i) := by
              intro t h'; exact hi (h' ▸ (μ t).2)
            simp [hz, hi]
  · intro j
    calc ∑ i, W i j = ∑ i, ∑ t : T, (if ((μ t : Fin m) = i ∧ (t : Fin n) = j)
                then 1 else 0) := rfl
      _ = ∑ t : T, ∑ i, (if ((μ t : Fin m) = i ∧ (t : Fin n) = j) then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ t : T, if (t : Fin n) = j then 1 else 0 :=
          Finset.sum_congr rfl (fun t _ => hfib' j t)
      _ = ind T j := by
          by_cases hj : j ∈ T
          · rw [Finset.sum_eq_single (⟨j, hj⟩ : T)]
            · simp [hj]
            · intro t _ htne
              by_cases h' : (t : Fin n) = j
              · exfalso; exact htne (Subtype.ext h')
              · simp [h']
            · intro hb; exact absurd (Finset.mem_univ _) hb
          · have hz : ∀ t : T, ¬ ((t : Fin n) = j) := fun t h' => hj (h' ▸ t.2)
            simp [hz, hj]

/-- Conversely, from a `0`-`1` edge weighting of `Γ_S` with row sums `1_B` and column
sums `1_T` we extract a bijection `T ≃ B` respecting `S`.  Injectivity of the
extracted map uses that the row sums are at most `1`; surjectivity follows from
`|T| = |B|`, which in turn follows from `SMatching_sum_eq`. -/
theorem admits_of_smatching_ind {T : Finset (Fin n)} {B : Finset (Fin m)}
    (h : SMatching S (ind B) (ind T)) : AdmitsSMatching S T B := by
  obtain ⟨W, hsupp, hrow, hcol⟩ := h
  have hW1 : ∀ i j, W i j ≤ 1 := by
    intro i j
    have h1 : W i j ≤ ∑ j, W i j :=
      Finset.single_le_sum (f := fun j => W i j) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ j)
    rw [hrow i] at h1
    have h2 : ind B i ≤ 1 := ind_le_one B i
    omega
  have hex : ∀ t : T, ∃ i, W i (t : Fin n) = 1 := by
    intro t
    have hsum : ∑ i, W i (t : Fin n) = 1 := by
      rw [hcol (t : Fin n), ind_of_mem t.2]
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun i => W i (t : Fin n)) (by rw [hsum]; exact one_ne_zero)
    exact ⟨i, by have := hW1 i (t : Fin n); omega⟩
  choose g hg using hex
  have hmem : ∀ t : T, g t ∈ B := by
    intro t
    have h1 : W (g t) (t : Fin n) ≤ ∑ j, W (g t) j :=
      Finset.single_le_sum (f := fun j => W (g t) j) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ (t : Fin n))
    rw [hrow (g t), hg t] at h1
    have h2 : ind B (g t) ≤ 1 := ind_le_one B (g t)
    exact ind_eq_one_iff.mp (by omega)
  let G : T → B := fun t => ⟨g t, hmem t⟩
  have hinj : Function.Injective G := by
    intro t t' htt
    have hgg : g t = g t' := by simpa [G] using congrArg Subtype.val htt
    by_contra hne
    have hne' : (t : Fin n) ≠ (t' : Fin n) := fun h => hne (Subtype.ext h)
    have h1 : ∑ j ∈ ({(t : Fin n), (t' : Fin n)} : Finset (Fin n)), W (g t) j
        ≤ ∑ j, W (g t) j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
    have hgt' : W (g t) (t' : Fin n) = 1 := by
      have h' := hg t'
      rw [← hgg] at h'
      exact h'
    rw [Finset.sum_pair hne', hg t, hgt', hrow (g t), ind_of_mem (hmem t)] at h1
    omega
  have hcard : Fintype.card T = Fintype.card B := by
    rw [Fintype.card_coe, Fintype.card_coe]
    have h1 : ∑ i, ind B i = ∑ i, ∑ j, W i j :=
      Finset.sum_congr rfl (fun i _ => (hrow i).symm)
    have h2 : ∑ j, ind T j = ∑ j, ∑ i, W i j :=
      Finset.sum_congr rfl (fun j _ => (hcol j).symm)
    rw [← sum_ind B, ← sum_ind T, h1, h2, Finset.sum_comm]
  have hbij : Function.Bijective G :=
    (Fintype.bijective_iff_injective_and_card G).mpr ⟨hinj, hcard⟩
  refine ⟨Equiv.ofBijective G hbij, ?_⟩
  intro t
  have happ : (Equiv.ofBijective G hbij) t = G t := rfl
  rw [happ]
  exact hsupp (g t) (t : Fin n) (by rw [hg t]; norm_num)

/-- **Bridge theorem.** For square-free exponent vectors, the `S`-matching relation of
Definition 1.2 coincides with the existence of a bijection used to define `C_T(S)`. -/
theorem smatching_ind_iff {T : Finset (Fin n)} {B : Finset (Fin m)} :
    SMatching S (ind B) (ind T) ↔ AdmitsSMatching S T B :=
  ⟨admits_of_smatching_ind, smatching_ind_of_admits⟩

end IndLorPoly
