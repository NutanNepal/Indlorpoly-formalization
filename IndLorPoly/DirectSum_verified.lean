/-
Copyright: formalization of §1–2 of Eur–Nepal–Qin, "Induced Lorentzian and
Volume Polynomials" (arXiv 2605.05319v2).

# Direct sums of polymatroids and the factorisation `Q(P₁ ⊕ P₂) = Q(P₁) × Q(P₂)`

The proof of Theorem 2.2 (paper p. 4) runs the following step:

> Let `P` be the polymatroid on `E` defined as the direct sum
> `Δ^{κ_1}_{E_1} ⊕ ⋯ ⊕ Δ^{κ_m}_{E_m}`. […] Since `P` is the direct sum of the
> `Δ^{κ_i}_{E_i}`, we have `Q(P) = ∏_{i∈[m]} Q(Δ^{κ_i}_{E_i})`, and thus
> `(w_e + w'_e)_{e∈E} ∈ Q(P)` if and only if `∑_{e ∈ E_{i∈[m]}} (w_e + w'_e) = κ_i`
> for every `i ∈ [m]`.

We formalize direct sums of two polymatroids on a disjoint union `E₁ ⊕ E₂` of
ground sets (iterating gives the general case):

* `sumRank rk₁ rk₂` — the rank function of `P₁ ⊕ P₂`;
* `isPolymatroid_sumRank` — `P₁ ⊕ P₂` is a polymatroid;
* `mem_inBase_sumRank` — **the factorisation of the base polytope**: a lattice
  point of `Q(P₁ ⊕ P₂)` is exactly a pair of lattice points of `Q(P₁)`, `Q(P₂)`;
* `card_basePolytopeLatticePoints_sumRank` — consequently the numbers of lattice
  points multiply, which is what makes the exponential generating function of
  §2 multiplicative over a direct sum.
-/
import IndLorPoly.Polymatroid_verified

open Finset
open scoped BigOperators

namespace IndLorPoly

variable {E₁ E₂ : Type*} [DecidableEq E₁] [Fintype E₁] [DecidableEq E₂] [Fintype E₂]

/-! ## Splitting a finite set of a disjoint union -/

/-- The `E₁`-part of a finite set of `E₁ ⊕ E₂`. -/
def inlPart (A : Finset (E₁ ⊕ E₂)) : Finset E₁ :=
  univ.filter (fun a => Sum.inl a ∈ A)

/-- The `E₂`-part of a finite set of `E₁ ⊕ E₂`. -/
def inrPart (A : Finset (E₁ ⊕ E₂)) : Finset E₂ :=
  univ.filter (fun b => Sum.inr b ∈ A)

theorem mem_inlPart {A : Finset (E₁ ⊕ E₂)} {a : E₁} : a ∈ inlPart A ↔ Sum.inl a ∈ A := by
  simp [inlPart]

theorem mem_inrPart {A : Finset (E₁ ⊕ E₂)} {b : E₂} : b ∈ inrPart A ↔ Sum.inr b ∈ A := by
  simp [inrPart]

@[simp] theorem inlPart_empty : inlPart (∅ : Finset (E₁ ⊕ E₂)) = ∅ := by
  ext a; simp [mem_inlPart]

@[simp] theorem inrPart_empty : inrPart (∅ : Finset (E₁ ⊕ E₂)) = ∅ := by
  ext b; simp [mem_inrPart]

@[simp] theorem inlPart_univ : inlPart (univ : Finset (E₁ ⊕ E₂)) = univ := by
  ext a; simp [mem_inlPart]

@[simp] theorem inrPart_univ : inrPart (univ : Finset (E₁ ⊕ E₂)) = univ := by
  ext b; simp [mem_inrPart]

theorem inlPart_union (A B : Finset (E₁ ⊕ E₂)) :
    inlPart (A ∪ B) = inlPart A ∪ inlPart B := by
  ext a; simp [mem_inlPart]

theorem inrPart_union (A B : Finset (E₁ ⊕ E₂)) :
    inrPart (A ∪ B) = inrPart A ∪ inrPart B := by
  ext b; simp [mem_inrPart]

theorem inlPart_inter (A B : Finset (E₁ ⊕ E₂)) :
    inlPart (A ∩ B) = inlPart A ∩ inlPart B := by
  ext a; simp [mem_inlPart]

theorem inrPart_inter (A B : Finset (E₁ ⊕ E₂)) :
    inrPart (A ∩ B) = inrPart A ∩ inrPart B := by
  ext b; simp [mem_inrPart]

theorem inlPart_mono {A B : Finset (E₁ ⊕ E₂)} (h : A ⊆ B) : inlPart A ⊆ inlPart B := by
  intro a ha; rw [mem_inlPart] at *; exact h ha

theorem inrPart_mono {A B : Finset (E₁ ⊕ E₂)} (h : A ⊆ B) : inrPart A ⊆ inrPart B := by
  intro b hb; rw [mem_inrPart] at *; exact h hb

@[simp] theorem inlPart_image_inl (I : Finset E₁) :
    inlPart (I.image (Sum.inl : E₁ → E₁ ⊕ E₂)) = I := by
  ext a; simp [mem_inlPart]

@[simp] theorem inrPart_image_inl (I : Finset E₁) :
    inrPart (I.image (Sum.inl : E₁ → E₁ ⊕ E₂)) = ∅ := by
  ext b; simp [mem_inrPart]

@[simp] theorem inlPart_image_inr (J : Finset E₂) :
    inlPart (J.image (Sum.inr : E₂ → E₁ ⊕ E₂)) = ∅ := by
  ext a; simp [mem_inlPart]

@[simp] theorem inrPart_image_inr (J : Finset E₂) :
    inrPart (J.image (Sum.inr : E₂ → E₁ ⊕ E₂)) = J := by
  ext b; simp [mem_inrPart]

/-- A sum over a finite set of a disjoint union splits into the sums over its
two parts. -/
theorem sum_split {M : Type*} [AddCommMonoid M] (x : E₁ ⊕ E₂ → M)
    (A : Finset (E₁ ⊕ E₂)) :
    ∑ s ∈ A, x s = ∑ a ∈ inlPart A, x (Sum.inl a) + ∑ b ∈ inrPart A, x (Sum.inr b) := by
  classical
  have h₁ : ∑ s ∈ A, x s = ∑ s ∈ (univ : Finset (E₁ ⊕ E₂)), if s ∈ A then x s else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h₁, Fintype.sum_sum_type]
  congr 1
  · rw [inlPart, ← Finset.sum_filter (s := (univ : Finset E₁))
      (p := fun a => Sum.inl a ∈ A) (f := fun a => x (Sum.inl a))]
  · rw [inrPart, ← Finset.sum_filter (s := (univ : Finset E₂))
      (p := fun b => Sum.inr b ∈ A) (f := fun b => x (Sum.inr b))]

/-! ## The direct sum of two polymatroids -/

/-- The direct sum `P₁ ⊕ P₂` of two polymatroids, on the disjoint union of their
ground sets: `rk(A) := rk₁(A ∩ E₁) + rk₂(A ∩ E₂)`. -/
noncomputable def sumRank (rk₁ : Finset E₁ → ℕ) (rk₂ : Finset E₂ → ℕ) :
    Finset (E₁ ⊕ E₂) → ℕ :=
  fun A => rk₁ (inlPart A) + rk₂ (inrPart A)

theorem sumRank_def (rk₁ : Finset E₁ → ℕ) (rk₂ : Finset E₂ → ℕ)
    (A : Finset (E₁ ⊕ E₂)) : sumRank rk₁ rk₂ A = rk₁ (inlPart A) + rk₂ (inrPart A) := rfl

/-- A direct sum of polymatroids is a polymatroid. -/
theorem isPolymatroid_sumRank {rk₁ : Finset E₁ → ℕ} {rk₂ : Finset E₂ → ℕ}
    (h₁ : IsPolymatroid rk₁) (h₂ : IsPolymatroid rk₂) :
    IsPolymatroid (sumRank rk₁ rk₂) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sumRank, h₁.rk_empty, h₂.rk_empty]
  · intro I J hIJ
    simp only [sumRank]
    have a := h₁.mono_of_subset (inlPart_mono hIJ)
    have b := h₂.mono_of_subset (inrPart_mono hIJ)
    omega
  · intro I J
    simp only [sumRank, inlPart_union, inrPart_union, inlPart_inter, inrPart_inter]
    have a := h₁.submodular (inlPart I) (inlPart J)
    have b := h₂.submodular (inrPart I) (inrPart J)
    omega

/-- **Base polytope of a direct sum** (paper p. 4).  A lattice point of
`Q(P₁ ⊕ P₂)` is exactly a pair of lattice points of `Q(P₁)` and `Q(P₂)`. -/
theorem mem_inBase_sumRank {rk₁ : Finset E₁ → ℕ} {rk₂ : Finset E₂ → ℕ}
    (h₁ : IsPolymatroid rk₁) (h₂ : IsPolymatroid rk₂) (x : E₁ ⊕ E₂ → ℕ) :
    InBase (sumRank rk₁ rk₂) x ↔
      InBase rk₁ (fun a => x (Sum.inl a)) ∧ InBase rk₂ (fun b => x (Sum.inr b)) := by
  classical
  constructor
  · intro hx
    have hx₁ : ∀ I : Finset E₁, ∑ a ∈ I, x (Sum.inl a) ≤ rk₁ I := by
      intro I
      have hc := hx.1 (I.image (Sum.inl : E₁ → E₁ ⊕ E₂))
      rw [sumRank_def, inlPart_image_inl, inrPart_image_inl, h₂.rk_empty, Nat.add_zero] at hc
      rwa [Finset.sum_image (fun a _ b _ h => Sum.inl.inj h)] at hc
    have hx₂ : ∀ J : Finset E₂, ∑ b ∈ J, x (Sum.inr b) ≤ rk₂ J := by
      intro J
      have hc := hx.1 (J.image (Sum.inr : E₂ → E₁ ⊕ E₂))
      rw [sumRank_def, inlPart_image_inr, inrPart_image_inr, h₁.rk_empty, Nat.zero_add] at hc
      rwa [Finset.sum_image (fun a _ b _ h => Sum.inr.inj h)] at hc
    have htot : ∑ i, x i = rk₁ univ + rk₂ univ := by
      have h2 := hx.2
      rwa [sumRank_def, inlPart_univ, inrPart_univ] at h2
    have hs := sum_split x univ
    rw [inlPart_univ, inrPart_univ] at hs
    have p := hx₁ univ
    have q := hx₂ univ
    have total_split : (∑ a, x (Sum.inl a)) + (∑ b, x (Sum.inr b)) = rk₁ univ + rk₂ univ := by
      rw [← hs, htot]
    have hA : ∑ a, x (Sum.inl a) = rk₁ univ := by omega
    have hB : ∑ b, x (Sum.inr b) = rk₂ univ := by omega
    exact ⟨⟨hx₁, hA⟩, ⟨hx₂, hB⟩⟩
  · rintro ⟨⟨hx₁, hx₁'⟩, ⟨hx₂, hx₂'⟩⟩
    refine ⟨fun I => ?_, ?_⟩
    · rw [sumRank_def, sum_split x I]
      exact Nat.add_le_add (hx₁ (inlPart I)) (hx₂ (inrPart I))
    · rw [sum_split x univ, sumRank_def]
      simp only [inlPart_univ, inrPart_univ]
      rw [hx₁', hx₂']

/-! ## Multiplicativity of the lattice-point count -/

/-- The map `(x₁, x₂) ↦ (Sum.rec x₁ x₂)` gluing two vectors into one. -/
def glueFun : ((E₁ → ℕ) × (E₂ → ℕ)) → (E₁ ⊕ E₂ → ℕ) :=
  fun p => Sum.rec p.1 p.2

theorem glueFun_injective : Function.Injective (glueFun : ((E₁ → ℕ) × (E₂ → ℕ)) → _) := by
  intro p q hpq
  have h1 : p.1 = q.1 := funext fun a => congrFun hpq (Sum.inl a)
  have h2 : p.2 = q.2 := funext fun b => congrFun hpq (Sum.inr b)
  exact Prod.ext h1 h2

theorem glueFun_apply_inl (p : (E₁ → ℕ) × (E₂ → ℕ)) (a : E₁) :
    glueFun p (Sum.inl a) = p.1 a := rfl

theorem glueFun_apply_inr (p : (E₁ → ℕ) × (E₂ → ℕ)) (b : E₂) :
    glueFun p (Sum.inr b) = p.2 b := rfl

theorem glueFun_surj_on_glue (y : E₁ ⊕ E₂ → ℕ) :
    glueFun ((fun a => y (Sum.inl a)), (fun b => y (Sum.inr b))) = y := by
  funext s
  cases s <;> rfl

/-- The lattice points of the base polytope of a direct sum are the (glued)
pairs of lattice points of the two summands. -/
theorem basePolytopeLatticePoints_sumRank {rk₁ : Finset E₁ → ℕ} {rk₂ : Finset E₂ → ℕ}
    (h₁ : IsPolymatroid rk₁) (h₂ : IsPolymatroid rk₂) :
    ((basePolytopeLatticePoints rk₁).product (basePolytopeLatticePoints rk₂)).image
        (glueFun : ((E₁ → ℕ) × (E₂ → ℕ)) → (E₁ ⊕ E₂ → ℕ))
      = basePolytopeLatticePoints (sumRank rk₁ rk₂) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨⟨x₁, x₂⟩, hp, hgy⟩ := Finset.mem_image.1 hy
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_product.1 hp
    rw [mem_basePolytopeLatticePoints] at hx₁ hx₂
    have hx₁' : InBase rk₁ (fun a => glueFun (x₁, x₂) (Sum.inl a)) := hx₁
    have hx₂' : InBase rk₂ (fun b => glueFun (x₁, x₂) (Sum.inr b)) := hx₂
    rw [← hgy, mem_basePolytopeLatticePoints]
    exact (mem_inBase_sumRank h₁ h₂ (glueFun (x₁, x₂))).2 ⟨hx₁', hx₂'⟩
  · intro hy
    rw [mem_basePolytopeLatticePoints] at hy
    obtain ⟨hx₁, hx₂⟩ := (mem_inBase_sumRank h₁ h₂ y).1 hy
    refine Finset.mem_image.2 ⟨((fun a => y (Sum.inl a)), (fun b => y (Sum.inr b))), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨?_, ?_⟩
      · rw [mem_basePolytopeLatticePoints]; exact hx₁
      · rw [mem_basePolytopeLatticePoints]; exact hx₂
    · exact glueFun_surj_on_glue y

/-- **Multiplicativity of lattice-point counts under a direct sum**: the direct
sum step of the proof of Theorem 2.2 (paper p. 4), in counting form. -/
theorem card_basePolytopeLatticePoints_sumRank {rk₁ : Finset E₁ → ℕ} {rk₂ : Finset E₂ → ℕ}
    (h₁ : IsPolymatroid rk₁) (h₂ : IsPolymatroid rk₂) :
    (basePolytopeLatticePoints (sumRank rk₁ rk₂)).card =
      (basePolytopeLatticePoints rk₁).card * (basePolytopeLatticePoints rk₂).card := by
  rw [← basePolytopeLatticePoints_sumRank h₁ h₂,
    Finset.card_image_of_injective _ glueFun_injective]
  exact Finset.card_product _ _

end IndLorPoly
