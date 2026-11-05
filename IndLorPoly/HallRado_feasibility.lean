/-
Feasibility layer for §2 of "Induced Lorentzian and Volume Polynomials"
(Eur-Nepal-Qin), swarm direction d8.

Contents
* `IsPolyRank` : the rank-function axioms (monotone + submodular) of a polymatroid.
* `InBase` : lattice points of the base polytope `Q(P)` of a polymatroid.
* `inducedRank` : the induced polymatroid `rk_{I_ℰ(P)}(J) = rk_P(⋃_{j ∈ J} ℰ_j)`.
* `EMatching` / `AdmitsEMatching` : the `ℰ`-matching of Proposition 2.3, i.e. an
  `ℕ`-valued matrix on the incidence relation of `ℰ` with row sums `γ` and column
  sums `δ`.
* `inBase_induced_of_admits` : the (<=) half of Proposition 2.3, proved here.
* `mcdiarmid` : the (=>) half of Proposition 2.3, cited from [McD75, Theorem 2].
* `inBase_induced_iff` : Proposition 2.3 in the form used in Theorem 2.2.
* `deltaRank` : the polymatroid `Δ^r_[N]` of the proof of Theorem 2.2, with
  `inBase_deltaRank_iff` identifying its base polytope as the "box" polytope
  `{x ∈ R>=0^[N] : sum x_i = r}`.
-/
import Mathlib

open Finset
open scoped BigOperators

namespace IndLorPoly.HallRado

section RankFunction

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A rank function of a polymatroid on a finite ground set `E`: normalised at `∅`,
monotone and submodular ([Wel76]; §1 of the paper). -/
structure IsPolyRank (rk : Finset E → ℕ) : Prop where
  /-- `rk ∅ = 0` -/
  empty : rk ∅ = 0
  /-- monotonicity -/
  mono : ∀ A B : Finset E, A ⊆ B → rk A ≤ rk B
  /-- submodularity -/
  submod : ∀ A B : Finset E, rk (A ∪ B) + rk (A ∩ B) ≤ rk A + rk B

/-- `γ` is a lattice point of the base polytope
`Q(P) = {x ∈ R>=0^E : x(A) <= rk(A) for all A, x(E) = rk(E)}`
of the polymatroid with rank function `rk`.  The carrier `γ : E → ℕ` already encodes
nonnegativity and integrality. -/
def InBase (rk : Finset E → ℕ) (γ : E → ℕ) : Prop :=
  (∀ A : Finset E, ∑ e ∈ A, γ e ≤ rk A) ∧ (∑ e, γ e = rk univ)

/-- The induced polymatroid `I_ℰ(P)` of §1/§2: `rk_{I_ℰ(P)}(J) = rk_P(⋃_{j ∈ J} ℰ_j)`. -/
def inducedRank {L : Type*} [DecidableEq L] (rk : Finset E → ℕ) (ℰ : L → Finset E)
    (J : Finset L) : ℕ :=
  rk (J.biUnion ℰ)

end RankFunction

section EMatching

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {L : Type*} [Fintype L] [DecidableEq L]

/-- An `ℰ`-matching of the pair `(γ, δ)` (Proposition 2.3): a nonnegative integer weight
`w e j` carried by the incidence relation `e ∈ ℰ j`, with row sums `γ e` and column sums
`δ j`. -/
def EMatching (ℰ : L → Finset E) (γ : E → ℕ) (δ : L → ℕ) (w : E → L → ℕ) : Prop :=
  (∀ e j, w e j ≠ 0 → e ∈ ℰ j) ∧ (∀ e, ∑ j, w e j = γ e) ∧ (∀ j, ∑ e, w e j = δ j)

/-- The pair `(γ, δ)` admits an `ℰ`-matching. -/
def AdmitsEMatching (ℰ : L → Finset E) (γ : E → ℕ) (δ : L → ℕ) : Prop :=
  ∃ w : E → L → ℕ, EMatching ℰ γ δ w

variable {ℰ : L → Finset E} {γ : E → ℕ} {δ : L → ℕ} {w : E → L → ℕ}

/-- For fixed `e`, the mass that an `ℰ`-matching charges to `e` through the columns `j ∈ J`
is at most `γ e`, and vanishes unless `e ∈ ⋃_{j ∈ J} ℰ_j`. -/
theorem sum_col_le (hw : EMatching ℰ γ δ w) (J : Finset L) (e : E) :
    ∑ j ∈ J, w e j ≤ if e ∈ J.biUnion ℰ then γ e else 0 := by
  by_cases he : e ∈ J.biUnion ℰ
  · rw [if_pos he]
    have hle : ∑ j ∈ J, w e j ≤ ∑ j : L, w e j :=
      sum_le_sum_of_subset_of_nonneg (subset_univ J) (fun _ _ _ => Nat.zero_le _)
    calc ∑ j ∈ J, w e j ≤ ∑ j : L, w e j := hle
      _ = γ e := hw.2.1 e
  · rw [if_neg he]
    refine le_of_eq (sum_eq_zero fun j hj => ?_)
    by_contra h
    exact he (mem_biUnion.mpr ⟨j, hj, hw.1 e j h⟩)

/-- The column sums over `J` of an `ℰ`-matching are carried by `⋃_{j ∈ J} ℰ_j`. -/
theorem sum_col_eq_sum_biUnion (hw : EMatching ℰ γ δ w) (J : Finset L) :
    ∑ e, ∑ j ∈ J, w e j = ∑ e ∈ J.biUnion ℰ, ∑ j ∈ J, w e j := by
  refine (sum_subset (subset_univ _) ?_).symm
  intro e _ he
  refine sum_eq_zero fun j hj => ?_
  by_contra h
  exact he (mem_biUnion.mpr ⟨j, hj, hw.1 e j h⟩)

/-- **(Proposition 2.3, forward-easy direction)**: if `γ` is a lattice point of `Q(P)` and
the pair `(γ, δ)` admits an `ℰ`-matching, then `δ` is a lattice point of the base polytope
of the induced polymatroid `I_ℰ(P)`.

The hypothesis `hcover : ⋃_j ℰ_j = E` is the one used in the proof of Theorem 2.2, where
the `ℰ_v` are the sets of edges of `Γ_S` incident to a vertex `v` and hence cover all
edges. -/
theorem inBase_induced_of_admits (hcover : (univ : Finset L).biUnion ℰ = univ)
    (hw : EMatching ℰ γ δ w) (hγ : InBase rk γ) : InBase (inducedRank rk ℰ) δ := by
  refine ⟨fun J => ?_, ?_⟩
  · have h1 : ∑ j ∈ J, δ j = ∑ e, ∑ j ∈ J, w e j := by
      calc ∑ j ∈ J, δ j = ∑ j ∈ J, ∑ e, w e j := sum_congr rfl fun j _ => (hw.2.2 j).symm
        _ = ∑ e, ∑ j ∈ J, w e j := sum_comm
    have h2 : ∑ e, ∑ j ∈ J, w e j ≤ ∑ e ∈ J.biUnion ℰ, γ e := by
      rw [sum_col_eq_sum_biUnion hw J]
      refine sum_le_sum fun e _ => ?_
      rw [← hw.2.1 e]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ J) (fun _ _ _ => Nat.zero_le _)
    rw [h1]
    exact le_trans h2 (hγ.1 _)
  · have h1 : ∑ j, δ j = ∑ e, γ e := by
      calc ∑ j, δ j = ∑ j, ∑ e, w e j := sum_congr rfl fun j _ => (hw.2.2 j).symm
        _ = ∑ e, ∑ j, w e j := sum_comm
        _ = ∑ e, γ e := sum_congr rfl fun e _ => hw.2.1 e
    rw [h1, hγ.2]
    simp only [inducedRank, hcover]

/-- **(Proposition 2.3, other direction)** - [McD75, Theorem 2] (McDiarmid, *Rado's theorem
for polymatroids*).  If `δ` is a lattice point of the base polytope of the induced
polymatroid `I_ℰ(P)`, it is obtained from a lattice point `γ` of `Q(P)` by an
`ℰ`-matching.

This is the single imported combinatorial input of Theorem 2.2 (a max-flow /
total-unimodularity statement). -/
axiom mcdiarmid {rk : Finset E → ℕ} (h : IsPolyRank rk) (ℰ : L → Finset E) (δ : L → ℕ)
    (hδ : InBase (inducedRank rk ℰ) δ) : ∃ γ : E → ℕ, InBase rk γ ∧ AdmitsEMatching ℰ γ δ

/-- **Proposition 2.3**, in the form used in the proof of Theorem 2.2: `δ ∈ Q(I_ℰ(P)) ∩ Z^l`
iff `δ` is the column-sum vector of an `ℰ`-matching of some lattice point `γ ∈ Q(P) ∩ Z^E`. -/
theorem inBase_induced_iff {rk : Finset E → ℕ} (h : IsPolyRank rk) (ℰ : L → Finset E)
    (hcover : (univ : Finset L).biUnion ℰ = univ) (δ : L → ℕ) :
    InBase (inducedRank rk ℰ) δ ↔ ∃ γ : E → ℕ, InBase rk γ ∧ AdmitsEMatching ℰ γ δ := by
  constructor
  · exact mcdiarmid h ℰ δ
  · rintro ⟨γ, hγ, w, hw⟩
    exact inBase_induced_of_admits hcover hw hγ

end EMatching

section Delta

/-- The polymatroid `Δ^r_[N]` of the proof of Theorem 2.2: rank `r` on every nonempty
subset of `[N]`, and `0` on the empty set.  Its base polytope is
`{x ∈ R>=0^[N] : sum_i x_i = r}`. -/
def deltaRank (N r : ℕ) : Finset (Fin N) → ℕ := fun A => if A = ∅ then 0 else r

/-- `Δ^r_[N]` is a polymatroid: monotone and submodular. -/
theorem deltaRank_isPolyRank (N r : ℕ) : IsPolyRank (deltaRank N r) := by
  refine ⟨by simp [deltaRank], ?_, ?_⟩
  · intro A B hAB
    by_cases hA : A = ∅
    · simp [deltaRank, hA]
    · have hB : B ≠ ∅ := fun hh => hA (subset_empty.mp (hh ▸ hAB))
      simp [deltaRank, hA, hB]
  · intro A B
    by_cases hAB : A ∪ B = ∅
    · obtain ⟨hA, hB⟩ := Finset.union_eq_empty.mp hAB
      simp [deltaRank, hA, hB]
    · by_cases hI : A ∩ B = ∅
      · have hne : A ≠ ∅ ∨ B ≠ ∅ := by
          by_contra hc
          simp only [not_or, not_not] at hc
          exact hAB (by rw [hc.1, hc.2, Finset.empty_union])
        rcases hne with hA | hB
        · simp [deltaRank, hAB, hI, hA]
        · simp [deltaRank, hAB, hI, hB]
      · have hA : A ≠ ∅ := fun hh => hI (by rw [hh, Finset.empty_inter])
        have hB : B ≠ ∅ := fun hh => hI (by rw [hh, Finset.inter_empty])
        simp [deltaRank, hAB, hI, hA, hB]

/-- The base polytope of `Δ^r_[N]` is the box polytope: for `N > 0`, an integer vector is a
lattice point of `Q(Δ^r_[N])` iff its coordinates sum to `r` (and then automatically
`0 <= γ_i <= r`). -/
theorem inBase_deltaRank_iff (N r : ℕ) (hN : 0 < N) (γ : Fin N → ℕ) :
    InBase (deltaRank N r) γ ↔ ∑ e, γ e = r := by
  have huniv : (Finset.univ : Finset (Fin N)) ≠ ∅ := by
    intro hh
    have h0 : (⟨0, hN⟩ : Fin N) ∈ (Finset.univ : Finset (Fin N)) := mem_univ _
    rw [hh] at h0
    simpa using h0
  have hrk : deltaRank N r univ = r := by
    simp only [deltaRank]
    exact if_neg huniv
  constructor
  · intro h
    have h2 := h.2
    rw [hrk] at h2
    exact h2
  · intro h
    refine ⟨fun A => ?_, by rw [hrk]; exact h⟩
    simp only [deltaRank]
    by_cases hA : A = ∅
    · subst hA
      simp
    · rw [if_neg hA, ← h]
      exact sum_le_sum_of_subset_of_nonneg (f := γ) (subset_univ A)
        (fun _ _ _ => Nat.zero_le _)

end Delta

end HallRado
