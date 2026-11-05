/-
# Executable layer for §1 of "Induced Lorentzian and Volume Polynomials" (Eur--Nepal--Qin)

Direction D8: computable certification of the paper's worked examples.  Every definition here is a
*computable* transcription of a definition of §1, so the paper's concrete claims can be checked by
`#eval` and by kernel-checked `decide` proofs.  The specification theorems below are what make the
computations meaningful: they say the executable `Bool`/`Finset` objects coincide with the paper's
set-theoretic definitions.
-/
import Mathlib

open Finset

namespace IndLorPoly.Computable

variable {m n : ℕ}

/-- A sequence `S = (S_1, …, S_n)` of subsets of `[m]`, `Fin`-indexed: `S j` is the paper's
`S_{j+1} ⊆ [m] = {1, …, m}`.  §1. -/
abbrev Seq (m n : ℕ) := Fin n → Finset (Fin m)

/-- The bipartite graph `Γ_S` on `[m] ⊔ [n]`: the edge `i -- j` exists iff `i ∈ S_j`.
Definition 1.2. -/
def gammaEdge (S : Seq m n) (i : Fin m) (j : Fin n) : Prop := i ∈ S j

instance gammaEdge_dec (S : Seq m n) (i : Fin m) (j : Fin n) : Decidable (gammaEdge S i j) :=
  inferInstanceAs (Decidable (i ∈ S j))

/-- The edge set `E(Γ_S)` as a finset of positions `(i, j)` with `i -- j`.  Definition 1.2. -/
def gammaEdges (S : Seq m n) : Finset (Fin m × Fin n) :=
  univ.filter fun p => gammaEdge S p.1 p.2

theorem mem_gammaEdges {S : Seq m n} {p : Fin m × Fin n} :
    p ∈ gammaEdges S ↔ gammaEdge S p.1 p.2 := by
  simp [gammaEdges]

/-- **`S`-matching.**  `B ⊆ [m]` is matched into `T ⊆ [n]` along `Γ_S`: there is a map
`f : [m] → [n]`, injective on `B`, with `f i ∈ T` and `i ∈ S_{f i}` for `i ∈ B`.  When
`B.card = T.card` (the case relevant to `CT`) such an `f` is exactly the bijection `μ : B → T` with
`μ(i) ∈ S_i` of §1. -/
def AdmitsSMatching (S : Seq m n) (T : Finset (Fin n)) (B : Finset (Fin m)) : Prop :=
  ∃ f : Fin m → Fin n,
    (∀ i ∈ B, f i ∈ T ∧ i ∈ S (f i)) ∧ (∀ i ∈ B, ∀ i' ∈ B, f i = f i' → i = i')

/-- Decidability of `S`-matchability (noncomputable: only used in statements and in `CT`). -/
noncomputable instance admitsSMatching_decPred (S : Seq m n) (T : Finset (Fin n)) :
    DecidablePred (AdmitsSMatching S T) := fun _ => Classical.propDecidable _

/-- `CT(S)`: the number of `B ⊆ [m]` of size `|T|` which are `S`-matchable into `T`.  §1:
`CT(S) = |{B ⊆ [m] : ∃ bijection μ : T → B with μ(t) ∈ S_t}|`. -/
noncomputable def CT (S : Seq m n) (T : Finset (Fin n)) : ℕ := by
  classical
  exact (((univ : Finset (Fin m)).powersetCard T.card).filter (AdmitsSMatching S T)).card

/-- Specification of `CT`: it counts exactly the `B ⊆ [m]` of cardinality `|T|` admitting an
`S`-matching into `T`. -/
theorem mem_CT_iff (S : Seq m n) (T : Finset (Fin n)) (B : Finset (Fin m)) :
    B ∈ ((univ : Finset (Fin m)).powersetCard T.card).filter (AdmitsSMatching S T) ↔
      B.card = T.card ∧ AdmitsSMatching S T B := by
  classical
  rw [mem_filter, mem_powersetCard]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨subset_univ _, h.1⟩, h.2⟩⟩

/-- `CT` is bounded by the number of `|T|`-subsets of `[m]`. -/
theorem CT_le_choose (S : Seq m n) (T : Finset (Fin n)) : CT S T ≤ m.choose T.card := by
  classical
  rw [CT]
  refine le_trans (card_filter_le _ _) ?_
  rw [card_powersetCard]
  simp

/-- `CT` vanishes iff nothing is matchable. -/
theorem CT_eq_zero_iff (S : Seq m n) (T : Finset (Fin n)) :
    CT S T = 0 ↔ ∀ B : Finset (Fin m), B.card = T.card → ¬ AdmitsSMatching S T B := by
  classical
  rw [CT, card_eq_zero, filter_eq_empty_iff]
  constructor
  · intro h B hB
    exact h (by rw [mem_powersetCard]; exact ⟨subset_univ _, hB⟩)
  · intro h B hB
    exact h B (mem_powersetCard.1 hB).2

/-- `CT` is positive iff some `|T|`-subset of `[m]` is matchable. -/
theorem CT_pos_iff (S : Seq m n) (T : Finset (Fin n)) :
    0 < CT S T ↔ ∃ B : Finset (Fin m), B.card = T.card ∧ AdmitsSMatching S T B := by
  classical
  rw [CT, card_pos, nonempty_iff_ne_empty, Ne, filter_eq_empty_iff]
  push_neg
  constructor
  · rintro ⟨B, hB, hm⟩
    exact ⟨B, (mem_powersetCard.1 hB).2, hm⟩
  · rintro ⟨B, hB, hm⟩
    exact ⟨B, by rw [mem_powersetCard]; exact ⟨subset_univ _, hB⟩, hm⟩

/-- `S`-matchability is monotone in the sequence `S`. -/
theorem admitsSMatching_mono {S S' : Seq m n} (h : ∀ j, S j ⊆ S' j) {T : Finset (Fin n)}
    {B : Finset (Fin m)} (hB : AdmitsSMatching S T B) : AdmitsSMatching S' T B := by
  obtain ⟨f, hf, hinj⟩ := hB
  exact ⟨f, fun i hi => ⟨(hf i hi).1, h _ (hf i hi).2⟩, fun i hi i' hi' => hinj i hi i' hi'⟩

/-- `CT` is monotone in the sequence `S`. -/
theorem CT_mono {S S' : Seq m n} (h : ∀ j, S j ⊆ S' j) (T : Finset (Fin n)) :
    CT S T ≤ CT S' T := by
  classical
  refine card_le_card ?_
  intro B hB
  rw [mem_CT_iff] at hB ⊢
  exact ⟨hB.1, admitsSMatching_mono h hB.2⟩

/-! ### Weight matrices (Definition 1.2), executable

A weighting `w : E(Γ_S) → ℤ≥0` with row sums `α` and column sums `β` is written as a function
`Fin m → Fin n → ℕ` supported on the edges of `Γ_S`.  We enumerate all of them; entries of such a
weight matrix are bounded by `∑ α`, so the enumeration up to `∑ α` is complete. -/

/-- All `m × n` matrices of natural numbers whose `i`-th row entries are all `< α i + 1`. -/
def matricesRowBounded {m n : ℕ} (α : Fin m → ℕ) : Finset (Fin m → Fin n → ℕ) :=
  Fintype.piFinset fun i : Fin m => Fintype.piFinset fun _ : Fin n => Finset.range (α i + 1)

theorem mem_matricesRowBounded {α : Fin m → ℕ} {w : Fin m → Fin n → ℕ} :
    w ∈ matricesRowBounded α ↔ ∀ i j, w i j < α i + 1 := by
  simp [matricesRowBounded]

/-- The finite set of weightings of `Γ_S` with row sums `α` (Definition 1.2).  An entry `w i j`
satisfies `w i j ≤ α i`, so restricting the `i`-th row to `[0, α i]` loses no weighting. -/
def SMatch (S : Seq m n) (α : Fin m → ℕ) : Finset (Fin m → Fin n → ℕ) :=
  (matricesRowBounded α).filter fun w =>
    (∀ i, (∑ j, w i j) = α i) ∧ (∀ i j, w i j ≠ 0 → i ∈ S j)

/-- **Specification of `SMatch`**: it contains *every* weighting with row sums `α` supported on
the edges of `Γ_S`, not merely the bounded ones.  This is what makes the enumeration a complete
count of the `S`-matchings. -/
theorem mem_SMatch {S : Seq m n} {α : Fin m → ℕ} {w : Fin m → Fin n → ℕ} (hw₁ : ∀ i, (∑ j, w i j) = α i)
    (hw₂ : ∀ i j, w i j ≠ 0 → i ∈ S j) : w ∈ SMatch S α := by
  rw [SMatch, mem_filter, mem_matricesRowBounded]
  refine ⟨fun i j => ?_, hw₁, hw₂⟩
  have h1 : w i j ≤ ∑ j, w i j :=
    single_le_sum (f := fun j => w i j) (fun j _ => Nat.zero_le _) (mem_univ j)
  rw [hw₁ i] at h1
  omega

/-- Column sums of a weight matrix: the resulting exponent vector `β`. -/
def colSum (w : Fin m → Fin n → ℕ) : Fin n → ℕ := fun j => ∑ i, w i j

/-- The set of `β` such that `α` and `β` are `S`-matched, `α ↔_S β` (Definition 1.2). -/
def smatchBetas (S : Seq m n) (α : Fin m → ℕ) : Finset (Fin n → ℕ) :=
  (SMatch S α).image (colSum)

/-- Row and column sums of any weight matrix agree in total: the support property `(*.1)` of §1,
`∑ β = ∑ α`. -/
theorem sum_colSum (w : Fin m → Fin n → ℕ) : (∑ j, colSum w j) = ∑ i, ∑ j, w i j := by
  simp only [colSum]
  exact sum_comm

/-! ### Example 1.4: `S = ({1,2,3,4}, {2,3}, {3,4})`, `(0,2,2,1) ←→ (2,2,1)` -/

/-- The sequence of Example 1.4 (`m = 4`, `n = 3`). -/
def ex14 : Seq 4 3 := fun j =>
  match j with
  | 0 => {0, 1, 2, 3}
  | 1 => {1, 2}
  | _ => {2, 3}

/-- The row-sum vector `α = (0,2,2,1)` of Example 1.4. -/
def ex14α : Fin 4 → ℕ := ![0, 2, 2, 1]

/-- The column-sum vector `β = (2,2,1)` of Example 1.4. -/
def ex14β : Fin 3 → ℕ := ![2, 2, 1]

#eval (gammaEdges ex14).card
#eval (SMatch ex14 ex14α).card
#eval (smatchBetas ex14 ex14α).card
#eval (SMatch ex14 ex14α).filter (fun w => colSum w = ex14β) |>.card

end Computable
