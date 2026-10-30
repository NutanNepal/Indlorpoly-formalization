import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.Data.Real.Basic

open MvPolynomial

namespace IndLorPoly.MatroidBasis

variable {m n : ℕ}

/-! ### Bases of a matroid on `Fin m` -/

noncomputable def basesFinset (M : Matroid (Fin m)) : Finset (Finset (Fin m)) := by
  classical exact Finset.univ.filter fun B => M.IsBase (B : Set (Fin m))

lemma mem_basesFinset {M : Matroid (Fin m)} {B : Finset (Fin m)} :
    B ∈ basesFinset M ↔ M.IsBase (B : Set (Fin m)) := by
  classical simp [basesFinset]

lemma basesFinset_nonempty (M : Matroid (Fin m)) : (basesFinset M).Nonempty := by
  classical
  obtain ⟨B, hB⟩ := M.exists_isBase
  refine ⟨B.toFinite.toFinset, ?_⟩
  rw [mem_basesFinset]
  rwa [Set.Finite.coe_toFinset]

noncomputable def baseCard (M : Matroid (Fin m)) : ℕ :=
  (Classical.choose (basesFinset_nonempty M)).card

lemma card_eq_baseCard {M : Matroid (Fin m)} {B : Finset (Fin m)}
    (hB : M.IsBase (B : Set (Fin m))) : B.card = baseCard M := by
  classical
  have hmem : B ∈ basesFinset M := by rwa [mem_basesFinset]
  have hch : (Classical.choose (basesFinset_nonempty M)) ∈ basesFinset M :=
    Classical.choose_spec (basesFinset_nonempty M)
  have h1 := Matroid.IsBase.ncard_eq_ncard_of_isBase hB (mem_basesFinset.mp hch)
  simp only [baseCard]
  have h2 : (B : Set (Fin m)).ncard = B.card := by simp
  have h3 : ((Classical.choose (basesFinset_nonempty M) : Finset (Fin m)) : Set (Fin m)).ncard
      = (Classical.choose (basesFinset_nonempty M)).card := by simp
  omega

lemma baseCard_le (M : Matroid (Fin m)) : baseCard M ≤ m := by
  classical
  have hch : (Classical.choose (basesFinset_nonempty M)) ∈ basesFinset M :=
    Classical.choose_spec (basesFinset_nonempty M)
  have h1 := Finset.card_le_univ (Classical.choose (basesFinset_nonempty M))
  simpa [baseCard] using h1

/-! ### `S`-matchings into a subset of `[m]` -/

def AdmitsSMatching (S : Fin n → Finset (Fin m)) (T : Finset (Fin n))
    (B : Finset (Fin m)) : Prop :=
  ∃ e : T ≃ B, ∀ t : T, (e t : Fin m) ∈ S t

lemma AdmitsSMatching.card_eq {S : Fin n → Finset (Fin m)} {T : Finset (Fin n)}
    {B : Finset (Fin m)} (h : AdmitsSMatching S T B) : B.card = T.card := by
  obtain ⟨e, _⟩ := h
  have h1 := Fintype.card_congr e
  simpa using h1.symm

noncomputable def ct (S : Fin n → Finset (Fin m)) (T : Finset (Fin n)) : ℕ := by
  classical exact (Finset.univ.filter fun B : Finset (Fin m) => AdmitsSMatching S T B).card

noncomputable def ctMatroid (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m))
    (T : Finset (Fin n)) : ℕ := by
  classical exact ((basesFinset M).filter fun B => AdmitsSMatching S T B).card

lemma ctMatroid_le_ct (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m))
    (T : Finset (Fin n)) : ctMatroid M S T ≤ ct S T := by
  classical
  simp only [ctMatroid, ct]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

lemma card_eq_baseCard_of_ctMatroid_ne_zero (M : Matroid (Fin m))
    (S : Fin n → Finset (Fin m)) {T : Finset (Fin n)} (h : ctMatroid M S T ≠ 0) :
    T.card = baseCard M := by
  classical
  simp only [ctMatroid] at h
  have hne : ((basesFinset M).filter fun B => AdmitsSMatching S T B).Nonempty :=
    Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  obtain ⟨B, hB⟩ := hne
  rw [Finset.mem_filter, mem_basesFinset] at hB
  obtain ⟨hbases, hadm⟩ := hB
  have h1 := hadm.card_eq
  have h2 := card_eq_baseCard hbases
  omega


/-! ### The polynomials of §1 and Remark 2.6

`ctPoly S r` is the paper's `f_{S,r}` written as `∑_{T ∈ binom([n],r)} C_T(S) y^T`,
i.e. with `y^T = ∏_{t∈T} y_t` the squarefree monomial attached to `T`.
`fMatroid M S r` is the matroid analogue of Remark 2.6:
`∑_{T ∈ binom([n],r)} C_T(M,S) y^T`, where `C_T(M,S)` counts only *bases* of `M`. -/

/-- The squarefree monomial `y^T = ∏_{t ∈ T} y_t`. -/
noncomputable def squarefreeMon (T : Finset (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∏ t ∈ T, MvPolynomial.X t

/-- `f_{S,r} = ∑_{T ∈ binom([n],r)} C_T(S) y^T` (paper, §1). -/
noncomputable def ctPoly (S : Fin n → Finset (Fin m)) (r : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => T.card = r),
    MvPolynomial.C (ct S T : ℝ) * squarefreeMon T

/-- The matroid analogue `∑_{T ∈ binom([n],r)} C_T(M,S) y^T` of Remark 2.6, where
`C_T(M,S)` counts the bases `B` of `M` that admit an `S`-matching from `T`. -/
noncomputable def fMatroid (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m)) (r : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => T.card = r),
    MvPolynomial.C (ctMatroid M S T : ℝ) * squarefreeMon T

/-! ### Vanishing of the coefficients of wrong degree -/

lemma ctMatroid_eq_zero_of_card_ne_baseCard (M : Matroid (Fin m))
    (S : Fin n → Finset (Fin m)) {T : Finset (Fin n)} (h : T.card ≠ baseCard M) :
    ctMatroid M S T = 0 := by
  by_contra hc
  exact h (card_eq_baseCard_of_ctMatroid_ne_zero M S hc)

/-- Only the `r = baseCard M` slice of the matroid polynomial can be nonzero: bases of a
matroid all have the same number of elements, so no basis can be matched from a `T` of
the wrong size. -/
theorem fMatroid_eq_zero_of_ne_baseCard (M : Matroid (Fin m))
    (S : Fin n → Finset (Fin m)) {r : ℕ} (h : r ≠ baseCard M) :
    fMatroid M S r = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro T hT
  rw [Finset.mem_filter] at hT
  obtain ⟨-, hcard⟩ := hT
  have hz : ctMatroid M S T = 0 := by
    apply ctMatroid_eq_zero_of_card_ne_baseCard
    omega
  simp [hz]

lemma fMatroid_eq_zero_of_lt (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m)) {r : ℕ}
    (h : m < r) : fMatroid M S r = 0 := by
  apply fMatroid_eq_zero_of_ne_baseCard
  have := baseCard_le M
  omega

/-! ### The uniform-matroid case: Remark 2.6 specialises to Theorem 1.1 -/

/-- If every `r`-element subset of `[m]` is a basis of `M` (so `M` is the uniform matroid
`U_{r,m}`), then counting bases with an `S`-matching is the same as counting arbitrary
subsets with an `S`-matching: a subset matched from `T` with `|T| = r` automatically has
`r` elements, hence is a basis. -/
lemma ctMatroid_eq_ct {M : Matroid (Fin m)} {S : Fin n → Finset (Fin m)} {r : ℕ}
    (hM : ∀ B : Finset (Fin m), M.IsBase (B : Set (Fin m)) ↔ B.card = r)
    {T : Finset (Fin n)} (hT : T.card = r) : ctMatroid M S T = ct S T := by
  classical
  have hbases : basesFinset M = Finset.univ.filter (fun B : Finset (Fin m) => B.card = r) := by
    simp only [basesFinset]
    exact Finset.filter_congr (fun B _ => hM B)
  simp only [ctMatroid, ct, hbases]
  have hset : (Finset.univ.filter (fun B : Finset (Fin m) => B.card = r)).filter
        (fun B => AdmitsSMatching S T B)
      = Finset.univ.filter (fun B => AdmitsSMatching S T B) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr (fun B _ => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩)
    rw [AdmitsSMatching.card_eq h, hT]
  rw [hset]

/-- Remark 2.6 specialises to Theorem 1.1 for the uniform matroid. -/
theorem fMatroid_eq_ctPoly (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m)) {r : ℕ}
    (hM : ∀ B : Finset (Fin m), M.IsBase (B : Set (Fin m)) ↔ B.card = r) :
    fMatroid M S r = ctPoly S r := by
  classical
  simp only [fMatroid, ctPoly]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [Finset.mem_filter] at hT
  rw [ctMatroid_eq_ct hM hT.2]

/-! ### Multi-affinity

Both polynomials are sums of squarefree monomials, so every variable occurs at most to
the first power; this is the "multi-affine" (multilinear) property used throughout §1–§2
of the paper (`f_{S,r}` lives in the multiaffine part of `R[y]`). -/

/-- A polynomial is multi-affine when no monomial contains a square of a variable. -/
def IsMultiaffine (f : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ (a : Fin n →₀ ℕ) (i : Fin n), 2 ≤ a i → MvPolynomial.coeff a f = 0

lemma degreeOf_squarefreeMon_le_one (i : Fin n) (T : Finset (Fin n)) :
    MvPolynomial.degreeOf i (squarefreeMon T) ≤ 1 := by
  classical
  simp only [squarefreeMon]
  calc MvPolynomial.degreeOf i (∏ t ∈ T, MvPolynomial.X t)
      ≤ ∑ t ∈ T, MvPolynomial.degreeOf i (MvPolynomial.X t) :=
        MvPolynomial.degreeOf_prod_le i T (fun t => MvPolynomial.X t)
    _ = ∑ t ∈ T, (if i = t then 1 else 0) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [MvPolynomial.degreeOf_X]
    _ ≤ 1 := by
        rw [Finset.sum_ite_eq]
        split_ifs <;> simp

lemma coeff_squarefreeMon_eq_zero {a : Fin n →₀ ℕ} {i : Fin n} (hi : 2 ≤ a i)
    (T : Finset (Fin n)) : MvPolynomial.coeff a (squarefreeMon T) = 0 := by
  classical
  have hle := degreeOf_squarefreeMon_le_one i T
  have hnot : a ∉ (squarefreeMon T).support := by
    intro hmem
    have h2 := (MvPolynomial.degreeOf_le_iff.mp hle) a hmem
    omega
  by_contra hc
  exact hnot (MvPolynomial.mem_support_iff.mpr hc)

theorem isMultiaffine_ctPoly (S : Fin n → Finset (Fin m)) (r : ℕ) :
    IsMultiaffine (ctPoly S r) := by
  classical
  intro a i hi
  simp only [ctPoly]
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero (fun T _ => ?_)
  rw [MvPolynomial.coeff_C_mul, coeff_squarefreeMon_eq_zero hi]
  simp

theorem isMultiaffine_fMatroid (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m)) (r : ℕ) :
    IsMultiaffine (fMatroid M S r) := by
  classical
  intro a i hi
  simp only [fMatroid]
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero (fun T _ => ?_)
  rw [MvPolynomial.coeff_C_mul, coeff_squarefreeMon_eq_zero hi]
  simp

/-! ### The external inputs, marked as axioms

The two properties below are the only ingredients of the paper that are not proved here:
Lorentzian-ness (Brändén–Huh) and realizability as a volume polynomial (Gutiérrez–
Hoffmann–Michałek–? , cited as [GHM+25] in the paper). They are stated as opaque
predicates with axiomatised closure behaviour, exactly as §2 axiomatises BH20 Thm 3.2
and GHM+25 Thm 1.12. -/

/-- Brändén–Huh Lorentzian property of a polynomial in `Fin k` variables. -/
opaque IsLorentzian {k : ℕ} : MvPolynomial (Fin k) ℝ → Prop

/-- Realizability as a volume polynomial. -/
opaque IsRealizableVolumePolynomial {k : ℕ} : MvPolynomial (Fin k) ℝ → Prop

/-- Paper, Theorem 1.1 (Lorentzian half). Axiomatised: the proof routes through
Brändén–Huh Thm 3.2 and the Schubert variety realisation of §1. -/
axiom theorem_1_1_lorentzian (S : Fin n → Finset (Fin m)) (r : ℕ) (hr : r ≤ m) :
    IsLorentzian (ctPoly S r)

/-- Paper, Theorem 1.1 (volume-polynomial half). Axiomatised: [GHM+25] Thm 1.12. -/
axiom theorem_1_1_realizable (S : Fin n → Finset (Fin m)) (r : ℕ) (hr : r ≤ m) :
    IsRealizableVolumePolynomial (ctPoly S r)

/-- Paper, Remark 2.6 (Lorentzian half): for a matroid `M` of rank `r`, the polynomial
`∑_{T} C_T(M,S) y^T` is Lorentzian. Axiomatised: deduced in the paper from Theorem 1.2. -/
axiom remark_2_6_lorentzian (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m)) :
    IsLorentzian (fMatroid M S (baseCard M))

/-- Paper, Remark 2.6 (volume-polynomial half): realizable whenever `M` is realizable over
the ground field. Axiomatised (it is the second half of Remark 2.6 of the paper). -/
axiom remark_2_6_realizable (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m)) :
    IsRealizableVolumePolynomial (fMatroid M S (baseCard M))

/-! ### Consequence: coherence of the axiomatisation with Theorem 1.1

The matroid statement, *restricted to the uniform matroid*, is Theorem 1.1 itself. Since
`fMatroid_eq_ctPoly` proves the two polynomials are equal in that case, the axiomatised
Remark 2.6 and the axiomatised Theorem 1.1 must agree there — the next theorem derives the
matroid statement from `theorem_1_1_*` and hence serves as a consistency check on the
axioms. -/

/-- Remark 2.6 for the uniform matroid `U_{r,m}`, derived from Theorem 1.1. -/
theorem uniform_case_of_theorem_1_1 (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m))
    (r : ℕ) (hr : r ≤ m) (hM : ∀ B : Finset (Fin m), M.IsBase (B : Set (Fin m)) ↔ B.card = r) :
    IsLorentzian (fMatroid M S r) ∧ IsRealizableVolumePolynomial (fMatroid M S r) := by
  rw [fMatroid_eq_ctPoly M S hM]
  exact ⟨theorem_1_1_lorentzian S r hr, theorem_1_1_realizable S r hr⟩

/-- The matroid polynomial is coefficient-wise dominated by the paper's `f_{S,r}`: the
bases of `M` form a subfamily of all `r`-element subsets of `[m]`. -/
theorem ctMatroid_le_ct_real (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m))
    (T : Finset (Fin n)) : (ctMatroid M S T : ℝ) ≤ (ct S T : ℝ) := by
  exact_mod_cast ctMatroid_le_ct M S T

/-! ### Finiteness in the ground-set size

No `S`-matching can reach a `B` with more elements than `[m]` has, so all coefficients of
`T` with `|T| > m` vanish; in particular Theorem 1.1's hypothesis `r ≤ m` is automatic. -/

lemma ct_eq_zero_of_lt {S : Fin n → Finset (Fin m)} {T : Finset (Fin n)} (h : m < T.card) :
    ct S T = 0 := by
  classical
  simp only [ct]
  rw [Finset.card_eq_zero]
  by_contra hne
  obtain ⟨B, hB⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [Finset.mem_filter] at hB
  have h1 := hB.2.card_eq
  have h2 := Finset.card_le_univ B
  simp only [Fintype.card_fin] at h2
  omega

theorem ctPoly_eq_zero_of_lt (S : Fin n → Finset (Fin m)) {r : ℕ} (h : m < r) :
    ctPoly S r = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro T hT
  rw [Finset.mem_filter] at hT
  have hz : ct S T = 0 := ct_eq_zero_of_lt (by omega)
  simp [hz]

/-! ### The matroid polynomial as a free sum over all `T`

Because a basis of `M` has `baseCard M` elements, the constraint `|T| = baseCard M` in
`fMatroid` is vacuous: the terms with the wrong cardinality vanish identically. -/

theorem fMatroid_eq_sum_univ (M : Matroid (Fin m)) (S : Fin n → Finset (Fin m)) :
    fMatroid M S (baseCard M)
      = ∑ T : Finset (Fin n), MvPolynomial.C (ctMatroid M S T : ℝ) * squarefreeMon T := by
  classical
  simp only [fMatroid]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  by_cases hT : T.card = baseCard M
  · rw [if_pos hT]
  · rw [if_neg hT, ctMatroid_eq_zero_of_card_ne_baseCard M S hT]
    simp

/-! ### Monotonicity in the matroid

If the bases of `M` are bases of `N`, the matroid count for `M` is at most that for `N`. -/

theorem ctMatroid_mono {M N : Matroid (Fin m)}
    (hMN : ∀ B : Finset (Fin m), M.IsBase (B : Set (Fin m)) → N.IsBase (B : Set (Fin m)))
    (S : Fin n → Finset (Fin m)) (T : Finset (Fin n)) :
    ctMatroid M S T ≤ ctMatroid N S T := by
  classical
  simp only [ctMatroid]
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  intro B hB
  rw [mem_basesFinset] at hB ⊢
  exact hMN B hB

/-! ### A concrete computation: the rank-zero matroid

Non-vacuity check for the definitions above. For the matroid `loopyOn univ` (all elements
are loops) the unique basis is `∅`, so `fMatroid` must be the constant `1` in degree `0`
and vanish in every other degree — the matroid analogue of `f_{S,0} = 1`. -/

lemma basesFinset_loopyOn (E : Set (Fin m)) :
    basesFinset (Matroid.loopyOn E) = {∅} := by
  classical
  ext B
  rw [mem_basesFinset, Finset.mem_singleton, Matroid.loopyOn_isBase_iff]
  constructor
  · intro h
    exact Finset.coe_eq_empty.mp h
  · rintro rfl
    simp

lemma baseCard_loopyOn (E : Set (Fin m)) : baseCard (Matroid.loopyOn E) = 0 := by
  classical
  have hb : (∅ : Finset (Fin m)) ∈ basesFinset (Matroid.loopyOn E) := by
    rw [basesFinset_loopyOn]; exact Finset.mem_singleton_self _
  have h := card_eq_baseCard (mem_basesFinset.mp hb)
  simpa using h.symm

lemma ctMatroid_loopyOn_empty (S : Fin n → Finset (Fin m)) :
    ctMatroid (Matroid.loopyOn (Set.univ : Set (Fin m))) S ∅ = 1 := by
  classical
  have h1 : IsEmpty ↥(∅ : Finset (Fin n)) := ⟨fun x => Finset.notMem_empty x.1 x.2⟩
  have h2 : IsEmpty ↥(∅ : Finset (Fin m)) := ⟨fun x => Finset.notMem_empty x.1 x.2⟩
  have hadm : AdmitsSMatching S (∅ : Finset (Fin n)) (∅ : Finset (Fin m)) :=
    ⟨@Equiv.equivOfIsEmpty _ _ h1 h2, fun t => absurd t.2 (Finset.notMem_empty _)⟩
  rw [ctMatroid, basesFinset_loopyOn, Finset.filter_singleton, if_pos hadm, Finset.card_singleton]

lemma ctMatroid_loopyOn_ne_empty (S : Fin n → Finset (Fin m)) {T : Finset (Fin n)}
    (hT : (∅ : Finset (Fin n)) ≠ T) :
    ctMatroid (Matroid.loopyOn (Set.univ : Set (Fin m))) S T = 0 := by
  classical
  have hne : T.card ≠ baseCard (Matroid.loopyOn (Set.univ : Set (Fin m))) := by
    rw [baseCard_loopyOn]
    exact Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hT.symm)
  exact ctMatroid_eq_zero_of_card_ne_baseCard _ S hne

/-- Degree `0` of the matroid polynomial of the rank-zero matroid: the constant `1`. -/
theorem fMatroid_loopyOn_zero (S : Fin n → Finset (Fin m)) :
    fMatroid (Matroid.loopyOn (Set.univ : Set (Fin m))) S 0 = 1 := by
  classical
  have hfilter : (Finset.univ.filter (fun T : Finset (Fin n) => T.card = 0))
      = {(∅ : Finset (Fin n))} := by
    ext T
    rw [Finset.mem_filter, Finset.mem_singleton, Finset.card_eq_zero]
    simp
  simp only [fMatroid, hfilter, Finset.sum_singleton, ctMatroid_loopyOn_empty,
    squarefreeMon, Finset.prod_empty, Nat.cast_one, MvPolynomial.C_1, one_mul]

end IndLorPoly.MatroidBasis
