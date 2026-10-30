import IndLorPoly.Basic
import IndLorPoly.Operator
import IndLorPoly.Polymatroid
import IndLorPoly.Symbol
import IndLorPoly.HallRado
import Mathlib.Algebra.MvPolynomial.Basic

namespace IndLorPoly

variable {m n : ℕ}
variable (S : Fin n → Finset (Fin m))

/-!
# Theorem 2.2 — the symbol is a realizable volume polynomial (Paper §2, p.4-5)

`sym_{I_S}` is the exponential generating function of lattice points of the
base polytope of a polymatroid on `[m]⊔[n]` linearly realizable over any field.

Construction (paper proof):
- `N`, `Δ^r_{[N]}` via diagonal embedding `k^r ↪ (k^r)^{⊕N}` (updated v2 paper)
- `E = edges Γ_S`, `E_v = edges incident to v`, `P = ⊕_{i∈[m]} Δ^{κ_i}_{E_{i∈[m]}}` on `E`
- `𝓔 = (E_v)_{v∈[m]⊔[n]}`, induced polymatroid `I_𝓔(P)` on `[m]⊔[n]`
- Claim: `(α,β)` with `0≤α≤κ` admits `S`-matching ↔ `(κ-α,β) ∈ Q(I_𝓔(P))`
- Via Prop 2.3, reduce to existence of `γ∈Q(P)` admitting `𝓔`-matching to `(κ-α,β)`,
  viewed as double weighting `w: E→ℤ^2_{≥0}` with three bullets.
- Since `Q(P)=∏ Q(Δ)`, condition is `Σ_{e∈E_{i∈[m]}} (w_e+w'_e)=κ_i`.
- The `w` ↔ `w'` correspondence gives the equivalence.
- Linear realizability propagates: `P` realizable (diag embedding) ⇒ `I_𝓔(P)` realizable
  via induced construction (Remark after Thm 2.2 definition: image of `L` under `V^{[m]}→⊕ V_{S_i}`).
- Then `[EL24, Cor 1.4]` gives symbol is realizable volume polynomial.

We formalize the scaffolding; the deep step `[EL24]` remains an axiom.
-/

/--
The concrete polymatroid `P` on `E = edges Γ_S` as direct sum of `Δ^{κ_i}`.
In Lean we represent `E` as `Fin m × Fin n` filtered, and `P` via uniform ranks.
-/
noncomputable def symbolPolymatroidRank (κ : Fin m → ℕ) :
    Finset (Fin m × Fin n) → ℕ :=
  fun A => ∑ i : Fin m, if (A ∩ (GammaEdges S).filter (fun e => e.1 = i)) = ∅ then 0 else κ i
  -- Simplified: rank of A in P is Σ_i min(κ_i, |A ∩ E_{i∈[m]}|) for uniform Δ
  -- For the actual Δ^r, rank(A)= if A=∅ then 0 else r, so direct sum gives Σ.

/--
Theorem 2.2 statement (paper p.4, updated v2 diagonal embedding).
The symbol is the EGF of a linearly realizable polymatroid.
-/
theorem theorem_2_2 (κ : Fin m → ℕ) :
    ∃ (rk : Finset (Fin m ⊕ Fin n) → ℕ),
      IsPolymatroid rk ∧
      LinearlyRealizable rk ∧
      (∀ α β, α ∈ kappaBox κ → (SMatching S α β ↔
        -- (κ-α, β) as element of Sum.inl/inr corresponds to being in Q(I_E(P))
        -- We state membership in the induced rank: base polytope condition
        True -- placeholder for ` (κ-α,β) ∈ Q(inducedRank ... ) `
      )) ∧
      -- And the symbol's support is exactly those (κ-α,β)
      (symIS S κ).support =
        (Finset.univ : Finset (Fin m ⊕ Fin n →₀ ℕ)).filter (fun _ => True) -- placeholder
      := by
  -- Construction as in paper
  -- P is linearly realizable over any field by diagonal embedding
  -- I_E(P) is then linearly realizable (axiom induced_linearlyRealizable)
  -- The equivalence uses Hall-Rado (Prop 2.3) and the double-weighting argument
  sorry

/--
Corollary: the symbol is a realizable volume polynomial over any field.
Paper: "This theorem implies Theorem 1.3" via `[EL24, Cor 1.4 & Remark 3.21]`
which states EGF of linearly realizable polymatroid is realizable volume polynomial.
-/
axiom el24_cor_1_4 {E : Type*} [Fintype E] [DecidableEq E]
    (rk : Finset E → ℕ) (hReal : LinearlyRealizable rk) :
    IsRealizableVolumePolynomial (egfOf rk) -- placeholder type

-- To state it for our case, we use the opaque from Lorentzian.lean:
-- We axiomatize that Theorem 2.2 implies the symbol is volume:

/--
`sym_{I_S}` is a realizable volume polynomial (axiom packaging Theorem 2.2 + EL24).
-/
axiom symIS_isVolume (κ : Fin m → ℕ) :
    IsRealizableVolumePolynomial (symIS S κ)

/--
And therefore Lorentzian ( [BH20, Thm 4.6]: realizable volume ⇒ Lorentzian ).
-/
axiom volume_implies_lorentzian {k : ℕ} (p : MvPolynomial (Fin k) ℝ)
    (h : IsRealizableVolumePolynomial p) : IsLorentzian p

theorem symIS_isLorentzian (κ : Fin m → ℕ) :
    IsLorentzian (symIS S κ) :=
  volume_implies_lorentzian _ (symIS_isVolume S κ)

/--
The double-weighting equivalence (core combinatorial lemma, p.5).
We isolate it for clarity.
-/
theorem doubleWeighting_equiv (κ α : Fin m → ℕ) (β : Fin n → ℕ)
    (hα : ∀ i, α i ≤ κ i) :
    SMatching S α β ↔
    ∃ w w' : Fin m × Fin n → ℕ,
      DoubleWeighting S κ α β w w' ∧
      (∀ i : Fin m, ∑ e ∈ incidentEdges S (Sum.inl i), (w e + w' e) = κ i) := by
  constructor
  · intro hMatch
    -- Forward: given w' witnessing α↔β, extend w to satisfy Σ_{E_{i}} w = κ-α
    -- Choose any nonnegative vector with the required sums (possible because κ-α ≥0)
    rcases hMatch with ⟨W, hsupp, hrow, hcol⟩
    let w' : Fin m × Fin n → ℕ := fun p => W p.1 p.2
    -- Need to construct w: distribute κ_i - α_i arbitrarily over edges in E_{i}
    -- e.g. put all on first edge incident to i, or zero if no edges (but then α_i=0)
    sorry
  · intro ⟨w, w', hDouble, hSum⟩
    -- Backward: projection to w' witnesses α↔β
    -- Need to show w' has row sums α and column sums β, using hSum and DoubleWeighting
    -- Row sums: Σ_{E_{i}} w'_e = Σ_{E_{i}}(w+w') - Σ_{E_{i}} w = κ_i - (κ_i - α_i) = α_i
    -- Column sums already in hDouble
    sorry

end IndLorPoly
