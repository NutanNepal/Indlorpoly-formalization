/-
Copyright: formalization of §1–2 of Eur–Nepal–Qin, "Induced Lorentzian and
Volume Polynomials" (arXiv 2605.05319v2).

# Cited external facts about linear realizability

Paper p. 4: a polymatroid `P` on `[m]` is *linearly realizable* over a field `k`
if there are `k`-vector spaces `V_1, …, V_m` and a subspace
`L ⊆ V_{[m]} = ⨁_{i∈[m]} V_i` such that

  `rk_P(A) = dim(image of L under the projection π_A : V_{[m]} → V_A)`
  for all `A ⊆ [m]`, where `V_A := ⨁_{j∈A} V_j`.

The linear algebra behind this predicate (dimension counts of images of a fixed
subspace under varying projections) is developed nowhere in §1–3 of the paper
and is orthogonal to the combinatorial content we formalize.  Following the
instruction to axiomatize external deep results rather than reprove them, we
introduce the predicate `LinearlyRealizable` as an `opaque` constant and record
the four facts the paper *cites* about it.  Every one of them is marked
`AXIOM (cited)` with its place in the paper.

Remark (point of honesty): `isPolymatroid_of_linearlyRealizable` is *provable*
from `Submodule.finrank_sup_add_finrank_inf_eq`; we leave it as a citation
because the dimension bookkeeping is not part of this file's assignment.
-/
import Polymatroid
import DirectSum

open Finset
open scoped BigOperators

namespace IndLorPoly

/-- Linearly realizability of a polymatroid over a field `k` (paper p. 4).
Declared `opaque`: we never unfold it, only use the cited facts below. -/
opaque LinearlyRealizable : ∀ {E : Type*} [Fintype E] [DecidableEq E], (Finset E → ℕ) → Prop

/-- AXIOM (cited, paper p. 4): "It is straightforward to verify" that a linearly
realizable polymatroid is a polymatroid. -/
axiom isPolymatroid_of_linearlyRealizable {E : Type*} [Fintype E] [DecidableEq E]
    {rk : Finset E → ℕ} (h : LinearlyRealizable rk) : IsPolymatroid rk

/-- AXIOM (cited, paper p. 4): `Δ^r_[N]` is linearly realizable over any field,
by the diagonal embedding of `k^r` in `(k^r)^{⊕[N]}`. -/
axiom uniform_linearlyRealizable (N r : ℕ) : LinearlyRealizable (uniformRank N r)

/-- AXIOM (cited, paper p. 4): the induced polymatroid `I_S(P)` of a linearly
realizable polymatroid is linearly realizable over the same field, as the image
of `L` under `V_{[m]} → V_{S_1} ⊕ ⋯ ⊕ V_{S_n}`. -/
axiom induced_linearlyRealizable {m n : ℕ} {rk : Finset (Fin m) → ℕ}
    (h : LinearlyRealizable rk) (S : Fin n → Finset (Fin m)) :
    LinearlyRealizable (inducedRank rk S)

/-- AXIOM (cited, paper p. 4): a direct sum of linearly realizable polymatroids
is linearly realizable (immediate from the definition). -/
axiom sumRank_linearlyRealizable {E₁ E₂ : Type*} [Fintype E₁] [DecidableEq E₁]
    [Fintype E₂] [DecidableEq E₂] {rk₁ : Finset E₁ → ℕ} {rk₂ : Finset E₂ → ℕ}
    (h₁ : LinearlyRealizable rk₁) (h₂ : LinearlyRealizable rk₂) :
    LinearlyRealizable (sumRank rk₁ rk₂)

end IndLorPoly
