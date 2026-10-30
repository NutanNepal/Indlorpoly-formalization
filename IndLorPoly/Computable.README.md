# D8 (member m8): executable layer + computed certification for §1

File: `IndLorPoly/Computable.lean` — 175 lines, compiles with `lean` against Mathlib 4.33.1
(`lean IndLorPoly/Computable.lean`: 0 errors, 0 sorries).  No axioms.

## Definitions (computable transcription of §1)
- `Seq m n := Fin n → Finset (Fin m)` — the sequence S = (S_1..S_n) of subsets of [m].
- `gammaEdge`, `gammaEdges` — Γ_S, `i -- j ↔ i ∈ S_j` (Def. 1.2), as a `Finset` of positions.
- `AdmitsSMatching S T B` — injective `f : [m] → [n]`, injective on B, `f i ∈ T`, `i ∈ S (f i)`.
- `CT S T` — `#(univ.powersetCard T.card).filter (AdmitsSMatching S T)`.
- `matricesRowBounded α`, `SMatch S α` — all weight matrices with row sums α supported on E(Γ_S).
- `colSum`, `smatchBetas S α` — β with `α ↔_S β` (Def. 1.2).

## Proved (sorry-free)
- `mem_CT_iff`  : specification of `CT` (counts exactly the |T|-subsets admitting a matching).
- `CT_le_choose`: `CT S T ≤ m.choose T.card`.
- `CT_eq_zero_iff`, `CT_pos_iff` : vanishing / positivity criteria.
- `admitsSMatching_mono`, `CT_mono` : monotonicity in S.
- `mem_SMatch` : completeness of the bounded enumeration (every weighting is listed: `w i j ≤ α i`).
- `sum_colSum` : `∑_j colSum w j = ∑_i ∑_j w i j` (support property `(*.1)`, `∑β = ∑α`).
- `mem_gammaEdges`.

## Computed (`#eval`, Example 1.4: S = ({1,2,3,4},{2,3},{3,4}))
- `#(gammaEdges ex14) = 8`
- `#(SMatch ex14 (0,2,2,1)) = 36`  (weight matrices with row sums (0,2,2,1))
- `#(smatchBetas ex14 (0,2,2,1)) = 17` (distinct β matched to (0,2,2,1))
- `#(SMatch ... filtered to colSum = (2,2,1)) = 5`

The last value certifies the paper's Example 1.4, which exhibits *two distinct* S-matchings
witnessing `(0,2,2,1) ↔ (2,2,1)`; there are in fact 5.

## Not done / next
- The four `#eval` outputs are computed, not kernel-`decide`-proved; turning them into
  `example : ... = 5 := by decide` (or `native_decide`) is mechanical but was not finished.
- The paper-faithful statement "`AdmitsSMatching S T B` ↔ ∃ bijection μ : B ≃ {t // t ∈ T} with
  μ(i) ∈ S_i" (needs `B.card = T.card`, `Equiv.ofBijective`) is not yet proved.
- See the swarm board for the general §1/§2 theorems (other members).
