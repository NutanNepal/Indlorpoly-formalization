# Matroid basis version of the inducing operator (paper Remark 2.6)

Direction: **Remark 2.6 (matroid basis version)**, built on Mathlib's `Matroid` API.

File: `IndLorPoly/MatroidBasis.lean` (399 lines, namespace `IndLorPoly.MatroidBasis`).
Self-contained: imports only Mathlib, no dependency on the repo's `IndLorPoly.*` files.
To integrate, drop the file into `IndLorPoly/` and add `import IndLorPoly.MatroidBasis`
to `IndLorPoly.lean`.

## Verified

```
$ lean IndLorPoly/MatroidBasis.lean
$ echo $?
0
```
No `sorry`, no warnings. Axiom audit (`.scratch/audit.lean`):

* `isMultiaffine_fMatroid`, `fMatroid_eq_sum_univ`, `fMatroid_loopyOn_zero`,
  `card_eq_baseCard_of_ctMatroid_ne_zero`:
  `[propext, Classical.choice, Quot.sound]` — no extra axioms.
* `uniform_case_of_theorem_1_1`:
  `[propext, Classical.choice, Quot.sound, theorem_1_1_lorentzian, theorem_1_1_realizable]`
  — exactly the two marked paper axioms (Theorem 1.1 itself).

## Content and paper correspondence

| Lean | Paper |
|---|---|
| `basesFinset M`, `mem_basesFinset` | bases of `M` as a `Finset (Finset (Fin m))` (paper §1, "matroid on `[m]`") |
| `baseCard M`, `card_eq_baseCard` | `rank M`: all bases have the same cardinality (Mathlib `Matroid.IsBase.ncard_eq_ncard_of_isBase`) |
| `baseCard_le` | `rank M ≤ m` |
| `AdmitsSMatching S T B`, `AdmitsSMatching.card_eq` | "there is a bijection `μ : T → B` with `μ(t) ∈ S_t`" (§1) |
| `ct S T` | `C_T(S)` (§1) |
| `ctMatroid M S T` | `C_T(M,S)` of Remark 2.6: only bases of `M` are counted |
| `ctMatroid_le_ct` | bases are a subfamily of all subsets |
| `card_eq_baseCard_of_ctMatroid_ne_zero` | a matched basis has `|T| = rank M` |
| `squarefreeMon T`, `ctPoly S r` | `y^T = ∏_{t∈T} y_t` and `f_{S,r} = Σ_{T∈binom([n],r)} C_T(S) y^T` |
| `fMatroid M S r` | `Σ_{T∈binom([n],r)} C_T(M,S) y^T` (Remark 2.6) |
| `fMatroid_eq_zero_of_ne_baseCard`, `fMatroid_eq_zero_of_lt` | the polynomial lives in degree `rank M` only; `r > m` gives `0` |
| `ctPoly_eq_zero_of_lt`, `ct_eq_zero_of_lt` | Theorem 1.1's hypothesis `r ≤ m` is automatic |
| `ctMatroid_eq_ct`, `fMatroid_eq_ctPoly` | for the uniform matroid `U_{r,m}` Remark 2.6 *is* Theorem 1.1 |
| `IsMultiaffine`, `degreeOf_squarefreeMon_le_one`, `coeff_squarefreeMon_eq_zero`, `isMultiaffine_ctPoly`, `isMultiaffine_fMatroid` | both polynomials are multi-affine: no variable occurs squared |
| `fMatroid_eq_sum_univ` | the constraint `|T| = rank M` is vacuous, so the matroid polynomial is a free sum over all `T` |
| `ctMatroid_mono` | monotonicity for `M` whose bases are bases of `N` |
| `basesFinset_loopyOn`, `baseCard_loopyOn`, `ctMatroid_loopyOn_empty`, `fMatroid_loopyOn_zero` | worked example: the rank-zero matroid gives `f_{S,0}`-analogue `= 1` |

## Axiomatised (marked, with citations)

`IsLorentzian` and `IsRealizableVolumePolynomial` are `opaque` predicates, mirroring
`IndLorPoly/Lorentzian.lean`. Four axioms, all of them paper citations:

1. `theorem_1_1_lorentzian` — Theorem 1.1, Lorentzian half (Brändén–Huh Thm 3.2 + the
   Schubert-variety argument of §1).
2. `theorem_1_1_realizable` — Theorem 1.1, volume-polynomial half ([GHM+25] Thm 1.12).
3. `remark_2_6_lorentzian` — Remark 2.6, Lorentzian half (deduced in the paper from
   Theorem 1.2).
4. `remark_2_6_realizable` — Remark 2.6, volume-polynomial half.

`uniform_case_of_theorem_1_1` shows the matroid axioms are consistent with axioms 1–2:
restricted to the uniform matroid, the matroid statement is *proved* from Theorem 1.1
rather than assumed.

## Remaining work

* Realizability in Remark 2.6 is stated for a field of the same characteristic as a
  realization of `M`; the current axiom records only the Lorentzian- and
  `ℝ`-realizability halves.
* `Nat.card`-vs-`Finset.card` bookkeeping is done with `Finset` counters; the abstract
  `IndLorPoly.CT` of `Basic.lean` is `Nat.card`-based. The two agree, but the bridge lemma
  between `IndLorPoly.CT S T` and `ct S T` is not in this file (it needs `Basic.lean`,
  which lives outside this directory and is still being edited).
* The `r`-restricted variant (Remark 2.4 of the `.tex` draft) is not covered.
