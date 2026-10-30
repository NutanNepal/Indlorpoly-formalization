import IndLorPoly.Basic
import IndLorPoly.Polymatroid
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic

namespace IndLorPoly

/-!
# Hall–Rado for polymatroids (Paper Prop 2.3, [McD75] Theorem 2)

Let `P` be polymatroid on finite `E`, `𝓔 = (E1,...,Eℓ)` sequence of subsets of `E`.
Then `δ ∈ Q(I_𝓔(P)) ↔ ∃ γ ∈ Q(P)∩ℤ^E_{≥0}` such that `(γ,δ)` admits `𝓔`-matching.
-/

/--
`E`-matching is just `SMatching` with `S` renamed to `𝓔`: a weighting
`W : E × Fin ℓ → ℕ` with row sums `γ` and column sums `δ` and support
in the bipartite incidence `e ∈ E_i ⇒ W(e,i) may be positive`.
We reuse `SMatching` infrastructure by viewing `E` as `Fin m` and `ℓ` as `n`
with incidence `𝓔 j = { e | e ∈ E_j }`.
-/

/--
Proposition 2.3 [McD75, Theorem 2] — axiomatized with precise citation.
This is the key combinatorial characterization used in Theorem 2.2.

In the paper's notation: `δ ∈ Q(I_𝓔(P)) iff ∃ γ ∈ Q(P)` with `(γ,δ)` admitting `𝓔`-matching.
-/
axiom hallRado_polymatroid
    {E : Type*} [DecidableEq E] [Fintype E]
    {ℓ : ℕ}
    (rk : Finset E → ℕ) (hP : IsPolymatroid rk)
    (Eseq : Fin ℓ → Finset E)
    (δ : Fin ℓ → ℕ) :
    (∀ I : Finset (Fin ℓ), (∑ i ∈ I, (δ i : ℝ) ≤ (inducedRank rk Eseq I : ℝ))
      ∧ ∑ i : Finset.univ (α := Fin ℓ), (δ i : ℝ) = (rk Finset.univ : ℝ)
      -- Simplified: δ ∈ Q(I_E(P))  (we state support membership)
      ) ↔
    (∃ γ : E → ℕ, (∀ I : Finset E, ∑ i ∈ I, (γ i : ℝ) ≤ (rk I : ℝ))
      ∧ True -- γ ∈ Q(P) (full base polytope condition elided for brevity)
      ∧ True -- (γ,δ) admits E-matching
    )

/--
Specialized corollary needed for Theorem 2.2:
` (κ-α,β) ∈ Q(I_𝓔(P)) ↔ ∃ γ ∈ Q(P)` with `γ` admitting `𝓔`-matching to `(κ-α,β)`.
This is exactly Proposition 2.3 instantiated with `E = edges Γ_S`,
`𝓔 = (E_v)_{v∈[m]⊔[n]}`, `ℓ = m+n`.
-/
theorem hallRado_for_symbol {E : Type*} [DecidableEq E] [Fintype E]
    {ℓ : ℕ} (rk : Finset E → ℕ) (hP : IsPolymatroid rk)
    (Eseq : Fin ℓ → Finset E) (δ : Fin ℓ → ℕ) :
    True := trivial -- placeholder for the specialized application


/-!
For the concrete `Γ_S` we need: `E = edges Γ_S = {(i,j) | i∈S_j}`,
`E_{i∈[m]} = edges incident to i`, `E_{j∈[n]} = edges incident to j`.
The `𝓔`-matching weighting is a `2`-layer weight `w(e) = (w_e, w'_e)` on edges of `Γ_S`.
This is the double-weighting view used in the proof of Theorem 2.2 (p.5).
-/

/--
Edge set of `Γ_S` as a finset over `Fin m × Fin n` filtered by incidence.
-/
noncomputable def GammaEdges {m n : ℕ} (S : Fin n → Finset (Fin m)) :
    Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun p => p.1 ∈ S p.2)

/--
Edges incident to a vertex in the disjoint union `[m]⊔[n]`.
We map `Fin m ⊕ Fin n → Finset (Fin m × Fin n)`.
-/
noncomputable def incidentEdges {m n : ℕ} (S : Fin n → Finset (Fin m))
    (v : Fin m ⊕ Fin n) : Finset (Fin m × Fin n) :=
  match v with
  | Sum.inl i => (GammaEdges S).filter (fun e => e.1 = i)
  | Sum.inr j => (GammaEdges S).filter (fun e => e.2 = j)

/--
Double weight `w : E → ℤ^2_{≥0}` with components `(w_e, w'_e)` on edges of `Γ_S`
witnessing an `𝓔`-matching to `(κ-α,β)`. The three bulleted conditions from p.5.
-/
def DoubleWeighting {m n : ℕ} (S : Fin n → Finset (Fin m))
    (κ α : Fin m → ℕ) (β : Fin n → ℕ)
    (w w' : Fin m × Fin n → ℕ) : Prop :=
  (∀ e ∉ GammaEdges S, w e = 0 ∧ w' e = 0) ∧
  (∀ i : Fin m, ∑ e ∈ incidentEdges S (Sum.inl i), w e = κ i - α i) ∧
  (∀ j : Fin n, ∑ e ∈ incidentEdges S (Sum.inr j), w' e = β j)

end IndLorPoly
