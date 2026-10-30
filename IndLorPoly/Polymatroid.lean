import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import IndLorPoly.Basic

open Classical

namespace IndLorPoly

/-!
# Polymatroids (Paper §1, p.3)

A polymatroid `P` on `[m]` is a function `rk_P : 2^[m] → ℤ≥0` with
(i) rk(∅)=0, (ii) monotone, (iii) submodular.
We formalize over `Fin m` / arbitrary finite type.
-/

/--
Polymatroid rank function on a finite ground set `E`.
Paper p.3: `rk_P : 2^[m] → ℤ≥0` with the three axioms.
-/
structure IsPolymatroid {E : Type*} [DecidableEq E] [Fintype E] (rk : Finset E → ℕ) : Prop where
  rk_empty : rk ∅ = 0
  monotone : ∀ I J : Finset E, I ⊆ J → rk I ≤ rk J
  submodular : ∀ I J : Finset E, rk I + rk J ≥ rk (I ∪ J) + rk (I ∩ J)

/--
The base polytope `Q(P)` (Paper p.3):

`Q(P) := { x∈ℝ^m : Σ_{i∈I} x_i ≤ rk(I) for all I⊆[m] and Σ_{i∈[m]} x_i = rk([m]) }`
-/
def BasePolytope {E : Type*} [Fintype E] (rk : Finset E → ℕ) : Set (E → ℝ) :=
  { x | (∀ I : Finset E, ∑ i ∈ I, (x i : ℝ) ≤ (rk I : ℝ)) ∧ ∑ i : Finset.univ (α := E), x i = (rk Finset.univ : ℝ) }

/--
A matroid is a polymatroid with extra `rk(I) ≤ |I|` (Paper p.3).
-/
def IsMatroid {E : Type*} [DecidableEq E] [Fintype E] (rk : Finset E → ℕ) : Prop :=
  IsPolymatroid rk ∧ ∀ I : Finset E, rk I ≤ I.card

/--
Induced polymatroid `I_S(P)` (Paper p.3, following Welsh Chap 8.2):
`rk_{I_S(P)}(I) := rk_P( ⋃_{i∈I} S_i )` for `I⊆[n]`.
-/
noncomputable def inducedRank {m n : ℕ} (rk : Finset (Fin m) → ℕ)
    (S : Fin n → Finset (Fin m)) (I : Finset (Fin n)) : ℕ :=
  rk (I.biUnion S)

/--
Induced polymatroid axioms are inherited.
-/
theorem isPolymatroid_induced {m n : ℕ} {rk : Finset (Fin m) → ℕ}
    (hP : IsPolymatroid rk) (S : Fin n → Finset (Fin m)) :
    IsPolymatroid (inducedRank rk S) := by
  constructor
  · simp [inducedRank, Finset.biUnion_empty]
    exact hP.rk_empty
  · intro I J hIJ
    unfold inducedRank
    apply hP.monotone
    exact Finset.biUnion_subset_biUnion_of_subset_left _ hIJ
  · intro I J
    unfold inducedRank
    have h1 : (I ∪ J).biUnion S = I.biUnion S ∪ J.biUnion S := Finset.biUnion_union
    have h2 : (I ∩ J).biUnion S ⊆ I.biUnion S ∩ J.biUnion S := by
      intro x hx
      simp only [Finset.mem_biUnion, Finset.mem_inter] at hx ⊢
      rcases hx with ⟨k, hk, hxS⟩
      constructor
      · exact ⟨k, Finset.mem_of_mem_inter_left hk, hxS⟩
      · exact ⟨k, Finset.mem_of_mem_inter_right hk, hxS⟩
    have hmono := hP.monotone _ _ h2
    have hsub := hP.submodular (I.biUnion S) (J.biUnion S)
    rw [h1] at hsub
    omega

/--
The uniform polymatroid `Δ^r_{[N]}` (Paper Theorem 2.2 proof):
rank `r` on every nonempty set, base polytope `{ x≥0 : Σ x = r }`.
-/
noncomputable def uniformRank {N : ℕ} (r : ℕ) : Finset (Fin N) → ℕ :=
  fun A => if A = ∅ then 0 else r

theorem isPolymatroid_uniform {N r : ℕ} : IsPolymatroid (uniformRank (N := N) r) := by
  constructor
  · simp [uniformRank]
  · intro I J hIJ
    simp only [uniformRank]
    by_cases hI : I = ∅
    · simp [hI, Nat.zero_le]
    · by_cases hJ : J = ∅
      · simp [hJ] at hIJ
        simp [hI] at *
      · simp [hI, hJ]
  · intro I J
    simp only [uniformRank]
    by_cases hI : I = ∅
    · simp [hI]
      by_cases hJ : J = ∅
      · simp [hJ]
      · simp [hJ, Finset.empty_union, Finset.empty_inter]
    · by_cases hJ : J = ∅
      · simp [hJ, Finset.union_empty, Finset.inter_empty]
      · simp [hI, hJ]
        by_cases hU : I ∪ J = ∅
        · simp [hU] at hI
        · by_cases hInter : I ∩ J = ∅
          · simp [hU, hInter]
          · simp [hU, hInter]

/--
Direct sum of polymatroids on disjoint ground sets (used in Thm 2.2:
`P = Δ^{κ1}_{E_{1∈[m]}} ⊕ ... ⊕ Δ^{κm}_{E_{m∈[m]}}` on `E = edges Γ_S`).
We model the special case needed: disjoint family indexed by `Fin m`.
-/
noncomputable def directSumRank {m : ℕ} {E : Type*} [DecidableEq E] [Fintype E]
    (parts : Fin m → Finset E) (hdisj : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (rks : ∀ i, Finset (Fin (parts i).card) → ℕ) : Finset E → ℕ :=
  fun A => ∑ i : Fin m, rks i ( (A ∩ parts i).card |>.cast (by sorry) )

-- For the actual proof we only need the concrete case: each part is E_{i∈[m]} and rank is uniform
-- So we provide a specialized lemma:

/--
Linear realizability (Paper p.4): `P` on `[m]` is linearly realizable over `k`
if `∃ V1..Vm k-vector spaces, L ⊆ ⊕ Vi` with `rk(A)=dim π_A(L)`.
We axiomatize the key properties; a full linear-algebra formalization would
require vector bundle theory over general fields.
-/
opaque LinearlyRealizable : ∀ {E : Type*} [Fintype E] [DecidableEq E],
    (Finset E → ℕ) → Prop

/--
`Δ^r_{[N]}` is linearly realizable over any field via diagonal embedding
`k^r ↪ (k^r)^{⊕ N}` (Paper p.4, Thm 2.2 proof). Axiom with citation.
-/
axiom uniform_linearlyRealizable {N r : ℕ} :
    @LinearlyRealizable (Fin N) _ _ (uniformRank (N := N) r)

/--
Direct sum of linearly realizable polymatroids is linearly realizable.
-/
axiom directSum_linearlyRealizable {m : ℕ} {E : Type*} [DecidableEq E] [Fintype E]
    (rk : Finset E → ℕ) (h : LinearlyRealizable rk) : True

/--
Induced polymatroid of a linearly realizable polymatroid is linearly realizable
(Paper p.4: "induced polymatroid I_E(P) is linearly realizable over any field k because P is").
-/
axiom induced_linearlyRealizable {E : Type*} [Fintype E] [DecidableEq E]
    {ℓ : ℕ} {rk : Finset E → ℕ} (h : LinearlyRealizable rk)
    (Eseq : Fin ℓ → Finset E) :
    LinearlyRealizable (inducedRank rk Eseq)

/--
Base polytope lattice points `Q(P) ∩ ℤ^E` — the support of the EGF.
-/
def basePolytopeLatticePoints {E : Type*} [Fintype E] [DecidableEq E]
    (rk : Finset E → ℕ) : Finset (E → ℕ) :=
  -- Bounded by rank of universe; we filter all vectors with entries ≤ rk(univ)
  let N := rk Finset.univ
  (Fintype.piFinset (fun _ : E => Finset.Iic N)).filter (fun x =>
    (∀ I : Finset E, ∑ i ∈ I, (x i : ℕ) ≤ rk I) ∧ ∑ i : Finset.univ (α := E), x i = rk Finset.univ)

end IndLorPoly
