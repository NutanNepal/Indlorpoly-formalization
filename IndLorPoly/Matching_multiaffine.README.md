# m3 / direction d1 — `S`-matching theory and the `C_T(S)` calculus (paper §1)

Two drop-in files for the repo (same module layout as `IndLorPoly/*.lean`),
**both sorry-free and axiom-free** (they only import `IndLorPoly.Basic`
and Mathlib):

* `IndLorPoly/Matching.lean`  — §1 combinatorics
* `IndLorPoly/Multiaffine.lean` — §1 coefficient calculus / proof of Thm 1.1's reduction

Build (from a checkout of the repo, after copying both files into `IndLorPoly/`):
`lake build` or `lean IndLorPoly/Multiaffine.lean` with `LEAN_PATH` set.

## What is proved

### `Matching.lean`
* `ind : Finset (Fin m) → Fin m → ℕ` — indicator vector `1_B`, with
  `ind_of_mem`, `ind_le_one`, `ind_eq_one_iff`, `ind_eq_zero_iff`,
  `sum_ind : ∑ i, ind B i = B.card`, `ind_inj`.
* **`smatching_ind_iff`** (the central combinatorial identity of §1):
  for `T ⊆ [n]`, `B ⊆ [m]`,
  `SMatching S (ind B) (ind T) ↔ AdmitsSMatching S T B`.
  So Definition 1.2 (`α ↔_S β`, an `ℤ_{≥0}`-weighting of `E(Γ_S)` with row sums
  `α` and column sums `β`) *coincides*, on square-free vectors, with the
  bijection-existence condition in the definition of `C_T(S)`.
  * `smatching_ind_of_admits`: from a bijection build the weighting
    `W i j = #{t : μ t = i, t = j}` (row sums `1_B`, column sums `1_T`, support in
    `Γ_S`) — the fibre sums are computed with `Finset.sum_comm`/`sum_eq_single`.
  * `admits_of_smatching_ind`: from a `0`-`1` weighting extract the bijection.
    Row sums `≤ 1` give injectivity of `t ↦ (unique i with W i t = 1)`; surjectivity
    comes from `|T| = |B|`, itself a double count (`∑∑ W = |B| = |T|`).

### `Multiaffine.lean`
* `toF : (Fin k → ℕ) → (Fin k →₀ ℕ)` (`Finsupp.equivFunOnFinite`), `toF_injective`,
  `prod_X_pow_eq_monomial : ∏ j, X j ^ β j = monomial (toF β) 1`.
* `vecFact`, `matchingBetas` (same definitions as `Operator.lean`; they are repeated
  here so that this file is self-contained and sorry-free — delete them once
  `Operator.lean`'s `IS_Operator` is filled in), `IS_monomial`.
* `matchingBetas_mem : β ∈ matchingBetas S α ↔ SMatching S α β`
  (finiteness: `SMatching_sum_eq` bounds every `β_j` by `∑ α_i`).
* `vecFact_ind : (1_B)! = 1`.
* **`coeff_IS_monomial_ind`** — *unit coefficients on square-free monomials*:
  `coeff (y^T) (I_S (x^B)) = if SMatching S (1_B) (1_T) then 1 else 0`.
  This is why `C_T(S)` counts *subsets* `B` and never the number of bijections.
* `CT_eq_card_filter : C_T(S) = #{(B ∈ binom([m],|T|) : B admits an S-matching from T)}`.
* **`coeff_elemSymm_IS`** — the multi-affine part of `I_S(e_r)`:
  for `|T| = r`,
  `coeff (y^T) (∑_{B ∈ binom([m],r)} I_S(x_B)) = C_T(S)`.
  This is exactly the paper's sentence "`f_{S,r}` is the multi-affine part of
  `I_S(∑_{B ∈ binom([m],r)} x_B)`", at the level of coefficients.
* `CT_eq_zero_of_lt : m < |T| → C_T(S) = 0`.
* `f_S_r_coeff : coeff (y^T) (f_{S,r}) = if |T| = r then C_T(S) else 0` — the
  matching coefficient computation for the other side.
* `prod_X_eq_prod_pow_ind`, `coeff_finset_prod_X` — monomial bookkeeping.

## What remains (not in these files)
* The literal polynomial identity `f_{S,r} = multiAffinePart (I_S(e_r))` still needs
  (a) the `multiaffinePart` operator on `MvPolynomial` and the fact that it kills
  non-square-free monomials, and (b) `I_S` as a linear map (`IS_Operator`, direction
  D3).  Both coefficient halves are done above.
* Everything Lorentzian / volume-polynomial (external: BH20, GHM+25) is untouched,
  as instructed; Theorem 1.1 then follows from Theorem 1.3 + `coeff_elemSymm_IS`
  + multi-affine-part preservation, both cited as axioms.
