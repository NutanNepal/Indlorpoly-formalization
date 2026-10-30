/-
Copyright: formalization of §1–2 of Eur–Nepal–Qin, "Induced Lorentzian and
Volume Polynomials" (arXiv 2605.05319v2).

# Polymatroid infrastructure

Self-contained, sorry-free development of the polymatroid machinery of the paper:

* `IsPolymatroid` — rank functions with `rk ∅ = 0`, monotonicity, submodularity
  (paper p. 3, axioms (i)–(iii)).
* `IsMatroid` — a polymatroid with `rk I ≤ |I|` (paper p. 3).
* `inducedRank` — the induced polymatroid `I_S(P)` of Welsh Ch. 8.2:
  `rk_{I_S(P)}(I) = rk_P(⋃_{i∈I} S_i)` (paper p. 3), and the theorem that it
  is again a polymatroid.
* `BasePolytope` — the base polytope `Q(P)` (paper p. 3), its convexity and
  nonnegativity, and its integer points `InBase`, packaged as the finite set
  `basePolytopeLatticePoints`.
* `uniformRank` — the polymatroid `Δ^r_[N]` of the proof of Theorem 2.2
  (paper p. 4) and the identification of its base polytope.

Direct sums are in `DirectSum.lean`; the cited linear-realizability facts are in
`Cited.lean`.
-/
import Mathlib

open Finset
open scoped BigOperators

namespace IndLorPoly

universe u

variable {E : Type*} [DecidableEq E] [Fintype E]

/-! ## 1. Polymatroids and their base polytopes -/

/-- A polymatroid `P` on a finite set `E` (paper p. 3): a function
`rk_P : 2^E → ℤ≥0` satisfying
(i) `rk_P(∅) = 0`,
(ii) `I ⊆ J → rk_P(I) ≤ rk_P(J)`,
(iii) `rk_P(I) + rk_P(J) ≥ rk_P(I ∪ J) + rk_P(I ∩ J)`. -/
structure IsPolymatroid (rk : Finset E → ℕ) : Prop where
  /-- (i) the empty set has rank zero -/
  rk_empty : rk ∅ = 0
  /-- (ii) the rank function is monotone -/
  monotone : ∀ I J : Finset E, I ⊆ J → rk I ≤ rk J
  /-- (iii) the rank function is submodular -/
  submodular : ∀ I J : Finset E, rk (I ∪ J) + rk (I ∩ J) ≤ rk I + rk J

namespace IsPolymatroid

variable {rk : Finset E → ℕ}

theorem nonneg (h : IsPolymatroid rk) (I : Finset E) : 0 ≤ rk I := Nat.zero_le _

theorem le_univ (h : IsPolymatroid rk) (I : Finset E) : rk I ≤ rk univ :=
  h.monotone I univ (subset_univ I)

theorem mono_of_subset (h : IsPolymatroid rk) {I J : Finset E} (hIJ : I ⊆ J) : rk I ≤ rk J :=
  h.monotone I J hIJ

end IsPolymatroid

/-- A matroid is a polymatroid whose rank function satisfies `rk I ≤ |I|`
(paper p. 3). -/
def IsMatroid (rk : Finset E → ℕ) : Prop :=
  IsPolymatroid rk ∧ ∀ I : Finset E, rk I ≤ I.card

theorem IsMatroid.isPolymatroid {rk : Finset E → ℕ} (h : IsMatroid rk) :
    IsPolymatroid rk := h.1

/-- The base polytope `Q(P)` (paper p. 3):
`Q(P) := {x ∈ ℝ^m : ∑_{i∈I} x_i ≤ rk_P(I) for all I ⊆ [m], and
∑_{i∈[m]} x_i = rk_P([m])}`. -/
def BasePolytope (rk : Finset E → ℕ) : Set (E → ℝ) :=
  { x | (∀ I : Finset E, ∑ i ∈ I, x i ≤ (rk I : ℝ)) ∧ ∑ i, x i = (rk univ : ℝ) }

theorem mem_basePolytope {rk : Finset E → ℕ} {x : E → ℝ} :
    x ∈ BasePolytope rk ↔
      (∀ I : Finset E, ∑ i ∈ I, x i ≤ (rk I : ℝ)) ∧ ∑ i, x i = (rk univ : ℝ) :=
  Iff.rfl

/-- **Nonnegativity of a base polytope.**  Although the definition of `Q(P)` has
no explicit sign conditions, every point of `Q(P)` is nonnegative: looking at the
complement of `{i}` gives `x_i = rk(E) - ∑_{j ≠ i} x_j ≥ rk(E) - rk(E∖{i}) ≥ 0`. -/
theorem nonneg_of_mem_basePolytope {rk : Finset E → ℕ} (h : IsPolymatroid rk)
    {x : E → ℝ} (hx : x ∈ BasePolytope rk) (i : E) : 0 ≤ x i := by
  obtain ⟨h1, h2⟩ := hx
  have hc := h1 (univ.erase i)
  have hmono : (rk (univ.erase i) : ℝ) ≤ (rk univ : ℝ) := by
    exact_mod_cast h.mono_of_subset (Finset.erase_subset i univ)
  have hsplit : x i + ∑ j ∈ univ.erase i, x j = ∑ j, x j := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  linarith

/-- A single coordinate of a point of the base polytope is bounded by `rk(E)`. -/
theorem le_rank_univ_of_mem_basePolytope {rk : Finset E → ℕ} (h : IsPolymatroid rk)
    {x : E → ℝ} (hx : x ∈ BasePolytope rk) (i : E) : x i ≤ (rk univ : ℝ) := by
  have h1 : x i ≤ (rk ({i} : Finset E) : ℝ) := by
    have h2 := hx.1 {i}
    simpa using h2
  have hmono : (rk ({i} : Finset E) : ℝ) ≤ (rk univ : ℝ) := by
    exact_mod_cast h.mono_of_subset (Finset.singleton_subset_iff.2 (Finset.mem_univ i))
  linarith

/-- The base polytope is convex. -/
theorem convex_basePolytope {rk : Finset E → ℕ} (_h : IsPolymatroid rk) :
    Convex ℝ (BasePolytope rk) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have key : ∀ I : Finset E,
      ∑ i ∈ I, (a • x + b • y) i = a * (∑ i ∈ I, x i) + b * (∑ i ∈ I, y i) := by
    intro I
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun I => ?_, ?_⟩
  · rw [key]
    have h1 := mul_le_mul_of_nonneg_left (hx1 I) ha
    have h2 := mul_le_mul_of_nonneg_left (hy1 I) hb
    nlinarith
  · rw [key, hx2, hy2]
    nlinarith

/-! ## 2. The induced polymatroid `I_S(P)` -/

section Induced

variable {m n : ℕ}

/-- The induced polymatroid `I_S(P)` of Welsh, Chapter 8.2 (paper p. 3):
`rk_{I_S(P)}(I) := rk_P(⋃_{i∈I} S_i)` for `I ⊆ [n]`. -/
noncomputable def inducedRank (rk : Finset (Fin m) → ℕ) (S : Fin n → Finset (Fin m))
    (I : Finset (Fin n)) : ℕ :=
  rk (I.biUnion S)

/-- The induced rank function is the rank of a union of `S_i`'s. -/
theorem inducedRank_def (rk : Finset (Fin m) → ℕ) (S : Fin n → Finset (Fin m))
    (I : Finset (Fin n)) : inducedRank rk S I = rk (I.biUnion S) := rfl

/-- `I_S(P)` is a polymatroid (paper p. 3).  Submodularity follows from
`⋃_{i∈I∩J} S_i ⊆ (⋃_{i∈I} S_i) ∩ (⋃_{j∈J} S_j)` together with monotonicity and
submodularity of `rk_P`. -/
theorem isPolymatroid_induced {rk : Finset (Fin m) → ℕ} (hP : IsPolymatroid rk)
    (S : Fin n → Finset (Fin m)) : IsPolymatroid (inducedRank rk S) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [inducedRank, hP.rk_empty]
  · intro I J hIJ
    exact hP.monotone _ _ (Finset.biUnion_subset_biUnion_of_subset_left S hIJ)
  · intro I J
    have hunion : (I ∪ J).biUnion S = I.biUnion S ∪ J.biUnion S := Finset.union_biUnion
    have hinter : (I ∩ J).biUnion S ⊆ I.biUnion S ∩ J.biUnion S := by
      intro x hx
      simp only [Finset.mem_biUnion, Finset.mem_inter] at hx ⊢
      obtain ⟨a, ⟨hI, hJ⟩, hxS⟩ := hx
      exact ⟨⟨a, hI, hxS⟩, ⟨a, hJ, hxS⟩⟩
    have hsub := hP.submodular (I.biUnion S) (J.biUnion S)
    have hmono := hP.mono_of_subset hinter
    show rk ((I ∪ J).biUnion S) + rk ((I ∩ J).biUnion S) ≤ rk (I.biUnion S) + rk (J.biUnion S)
    rw [hunion]
    omega

/-- Making `S` monotone in the index set: `I ⊆ J` gives `⋃_{i∈I} S_i ⊆ ⋃_{j∈J} S_j`. -/
theorem biUnion_mono {m n : ℕ} (S : Fin n → Finset (Fin m)) {I J : Finset (Fin n)}
    (hIJ : I ⊆ J) : I.biUnion S ⊆ J.biUnion S :=
  Finset.biUnion_subset_biUnion_of_subset_left S hIJ

/-- The induced *matroid*: replacing `rk` by `I ↦ min {|I|, rk(⋃_{i∈I} S_i)}`
gives a matroid (paper p. 3).  We record the truncation formula and its trivial
bound; matroid submodularity of the truncation is not needed in §2. -/
noncomputable def inducedMatroidRank (rk : Finset (Fin m) → ℕ) (S : Fin n → Finset (Fin m))
    (I : Finset (Fin n)) : ℕ :=
  min I.card (inducedRank rk S I)

theorem inducedMatroidRank_le_card (rk : Finset (Fin m) → ℕ) (S : Fin n → Finset (Fin m))
    (I : Finset (Fin n)) : inducedMatroidRank rk S I ≤ I.card :=
  min_le_left _ _

end Induced

/-! ## 3. Integer points of the base polytope -/

/-- Integer points of `Q(P)`: the lattice points `Q(P) ∩ ℤ^E`, expressed as
`ℕ`-valued vectors (nonnegativity is automatic for a lattice point, see
`nonneg_of_mem_basePolytope`). -/
def InBase (rk : Finset E → ℕ) (x : E → ℕ) : Prop :=
  (∀ I : Finset E, ∑ i ∈ I, x i ≤ rk I) ∧ ∑ i, x i = rk univ

theorem mem_inBase {rk : Finset E → ℕ} {x : E → ℕ} :
    InBase rk x ↔ (∀ I : Finset E, ∑ i ∈ I, x i ≤ rk I) ∧ ∑ i, x i = rk univ :=
  Iff.rfl

theorem inBase_nonneg {rk : Finset E → ℕ} {x : E → ℕ} (_h : InBase rk x) (i : E) : 0 ≤ x i :=
  Nat.zero_le _

/-- Every coordinate of a lattice point of `Q(P)` is at most `rk(E)`. -/
theorem inBase_le_rank_univ {rk : Finset E → ℕ} {x : E → ℕ} (h : InBase rk x) (i : E) :
    x i ≤ rk univ := by
  have hle : x i ≤ ∑ j, x j :=
    Finset.single_le_sum (f := x) (fun j _ => Nat.zero_le (x j)) (Finset.mem_univ i)
  rw [h.2] at hle
  exact hle

/-- The lattice points of the base polytope, as a finite set: by the previous
lemma they are all contained in the box `[0, rk(E)]^E`. -/
noncomputable def basePolytopeLatticePoints (rk : Finset E → ℕ) : Finset (E → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : E => Finset.range (rk univ + 1))).filter (fun x => InBase rk x)

/-- The finite set `basePolytopeLatticePoints` is exactly `Q(P) ∩ ℤ^E`. -/
theorem mem_basePolytopeLatticePoints {rk : Finset E → ℕ} {x : E → ℕ} :
    x ∈ basePolytopeLatticePoints rk ↔ InBase rk x := by
  classical
  constructor
  · intro hx
    exact (Finset.mem_filter.1 hx).2
  · intro h
    refine Finset.mem_filter.2 ⟨?_, h⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have := inBase_le_rank_univ h i
    omega

/-! ## 4. The uniform polymatroid `Δ^r_[N]` -/

section Uniform

/-- `Δ^r_[N]`: the polymatroid on `[N]` of rank `r` on every nonempty set
(proof of Theorem 2.2, paper p. 4). -/
def uniformRank (N r : ℕ) : Finset (Fin N) → ℕ :=
  fun A => if A = ∅ then 0 else r

theorem uniformRank_empty (N r : ℕ) : uniformRank N r ∅ = 0 := by
  simp [uniformRank]

theorem uniformRank_nonempty {N r : ℕ} {A : Finset (Fin N)} (hA : A ≠ ∅) :
    uniformRank N r A = r := by
  simp [uniformRank, hA]

/-- `Δ^r_[N]` is a polymatroid. -/
theorem isPolymatroid_uniform (N r : ℕ) : IsPolymatroid (uniformRank N r) := by
  refine ⟨uniformRank_empty N r, ?_, ?_⟩
  · intro I J hIJ
    by_cases hI : I = ∅
    · rw [hI, uniformRank_empty]; exact Nat.zero_le _
    · have hJ : J ≠ ∅ := fun h =>
        hI (Finset.subset_empty.1 (by rw [← h]; exact hIJ))
      rw [uniformRank_nonempty hI, uniformRank_nonempty hJ]
  · intro I J
    have key : uniformRank N r (I ∪ J) ≤ uniformRank N r I + uniformRank N r J := by
      by_cases hU : I ∪ J = ∅
      · rw [hU, uniformRank_empty]; exact Nat.zero_le _
      · rw [uniformRank_nonempty hU]
        have hne : I ≠ ∅ ∨ J ≠ ∅ := by
          by_contra h
          push_neg at h
          exact hU (by rw [h.1, h.2, Finset.empty_union])
        rcases hne with hI | hJ
        · rw [uniformRank_nonempty hI]; omega
        · rw [uniformRank_nonempty hJ]; omega
    by_cases hIJ : I ∩ J = ∅
    · rw [hIJ, uniformRank_empty, Nat.add_zero]; exact key
    · have hI : I ≠ ∅ := fun h => hIJ (by rw [h, Finset.empty_inter])
      have hJ : J ≠ ∅ := fun h => hIJ (by rw [h, Finset.inter_empty])
      have hU : I ∪ J ≠ ∅ := fun h =>
        hI (Finset.subset_empty.1 (by rw [← h]; exact Finset.subset_union_left))
      rw [uniformRank_nonempty hI, uniformRank_nonempty hJ, uniformRank_nonempty hU,
        uniformRank_nonempty hIJ]

/-- `Δ^r_[N]` is a matroid when `r ≤ 1`. -/
theorem uniformRank_le_card_of_le_one {N r : ℕ} (hr : r ≤ 1) (A : Finset (Fin N)) :
    uniformRank N r A ≤ A.card := by
  by_cases hA : A = ∅
  · rw [hA, uniformRank_empty]; simp
  · rw [uniformRank_nonempty hA]
    have : 1 ≤ A.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hA)
    omega

/-- Integer points of `Q(Δ^r_[N])` are exactly the nonnegative integer vectors
of total sum `r` (paper p. 4: `Q(Δ^r_[N]) = {x ∈ ℝ_{≥0}^N : ∑ x_i = r}`). -/
theorem mem_inBase_uniform {N r : ℕ} (hN : 0 < N) {x : Fin N → ℕ} :
    InBase (uniformRank N r) x ↔ ∑ i, x i = r := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  constructor
  · intro h
    rw [h.2, uniformRank_nonempty (Finset.univ_nonempty.ne_empty)]
  · intro h
    refine ⟨fun I => ?_, ?_⟩
    · by_cases hI : I = ∅
      · rw [hI, uniformRank_empty]; simp
      · rw [uniformRank_nonempty hI]
        calc ∑ i ∈ I, x i ≤ ∑ i, x i :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
                (fun i _ _ => Nat.zero_le (x i))
          _ = r := h
    · rw [uniformRank_nonempty (Finset.univ_nonempty.ne_empty)]; exact h

/-- The real base polytope of `Δ^r_[N]`, matching the paper verbatim.  We assume
`N > 0`, which is the case relevant to Theorem 2.2 (`E_i` nonempty). -/
theorem mem_basePolytope_uniform {N r : ℕ} (hN : 0 < N) {x : Fin N → ℝ} :
    x ∈ BasePolytope (uniformRank N r) ↔
      (∀ i, 0 ≤ x i) ∧ ∑ i, x i = (r : ℝ) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  constructor
  · intro hx
    refine ⟨fun i => nonneg_of_mem_basePolytope (isPolymatroid_uniform N r) hx i, ?_⟩
    rw [hx.2, uniformRank_nonempty (Finset.univ_nonempty.ne_empty)]
  · rintro ⟨hx0, hxs⟩
    refine ⟨fun I => ?_, ?_⟩
    · by_cases hI : I = ∅
      · rw [hI, uniformRank_empty]; simp
      · rw [uniformRank_nonempty hI]
        calc ∑ i ∈ I, x i ≤ ∑ i, x i :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => hx0 i)
          _ = (r : ℝ) := hxs
    · rw [uniformRank_nonempty (Finset.univ_nonempty.ne_empty), hxs]

end Uniform

end IndLorPoly
