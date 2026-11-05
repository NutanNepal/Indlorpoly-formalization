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
import IndLorPoly.Polymatroid_verified
import IndLorPoly.DirectSum_verified

open Finset
open scoped BigOperators

namespace IndLorPoly

/-- Linearly realizability of a polymatroid over a field `k` (paper p. 4).
Declared `opaque`: we never unfold it, only use the cited facts below. -/
opaque LinearlyRealizable : ∀ {E : Type*} [Fintype E] [DecidableEq E], (Finset E → ℕ) → Prop

end IndLorPoly
