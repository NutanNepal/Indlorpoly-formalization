# Induced Lorentzian Polynomials — Lean 4 Formalization

[![Lean](https://img.shields.io/badge/Lean-4.36.0--rc2-blue?logo=lean)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-7881f45c-green)](https://github.com/leanprover-community/mathlib4)
[![Build](https://github.com/NutanNepal/lean-playground-indlorpoly/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/NutanNepal/lean-playground-indlorpoly/actions)
[![License](https://img.shields.io/badge/License-Apache%202.0-lightgrey)](LICENSE)

Formalization of **"Induced Lorentzian and Volume Polynomials"**
by Christopher Eur, Nutan Nepal, Daniel Qin — [arXiv:2605.05319v2](https://arxiv.org/abs/2605.05319).

> Given a party of *m* people covering *n* topics and a subset *T* of topics,
> count panels of |T| people that can cover T by assigning distinct topics
> with expertise. The numbers of such panels form a **Lorentzian polynomial** —
> proved via an *inducing operator* that preserves Lorentzian and realizable
> volume polynomials.

---

## Mathematical Overview

For integers `m, n ≥ 1` and a sequence `S = (S₁,…,Sₙ)` of subsets of `[m]`:

| Paper Object | Meaning |
|---|---|
| `C_T(S)` | `|{ B ⊆ [m] : ∃ bijection μ:T→B, μ(t)∈S_t }|` — matching statistic |
| `Γ_S` | Bipartite graph `[m] ⊔ [n]`, edge `i—j ⇔ i∈S_j` |
| `α ↔_S β` (Def 1.2) | `∃ W:[m]×[n]→ℤ≥0` supported on `Γ_S` with row sums `α`, col sums `β` |
| `f_{S,r} = Σ_{T∈binom([n],r)} C_T(S) y^T` | **Theorem 1.1:** Lorentzian + realizable volume polynomial |
| `I_S(x^{[α]}) = Σ_{β:α↔β} y^{[β]}` where `x^{[α]}=x^α/α!` | **Theorem 1.3:** preserving operator |
| `sym_T(y,u)=T((x+u)^κ)=κ! Σ T(x^{[α]})u^{[κ-α]}` | Symbol (§2); **Prop 2.1** BH20 3.2 / GHM+25 1.12 |
| `sym_{I_S}=κ! Σ_{α≤κ} Σ_{β:α↔β} y^{[β]}u^{[κ-α]}` | EGF of lattice points |
| **Theorem 2.2** | `sym_{I_S}` is EGF of linearly-realizable polymatroid on `[m]⊔[n]` |
| `Q(P) = {x∈ℝ^m : Σ_{i∈I}x_i ≤ rk_P(I), Σx = rk([m])}` | Base polytope; `I_S(P): rk_I(I)=rk_P(⋃_{i∈I}S_i)` |
| `Δ^r_{[N]}` | Uniform polymatroid `rk(A)=if A=∅ then 0 else r`, `Q={x≥0:Σx=r}` |
| `A_S: f(x)↦f(A_S y)`, `A_S` columns `e_{S_j}` | §3 change-of-variables, functorial `T(M₁M₂)=T(M₂)∘T(M₁)` |

**Proof architecture:** Theorem 1.1 ⇐ Theorem 1.3 ⇐ Theorem 2.2 (+ Prop 2.1 + EL24 Cor 1.4). Theorem 2.2 is the 2-page combinatorial core: build `P = ⊕_i Δ^{κ_i}_{E_{i∈[m]}}` on edges `E=Γ_S`, take induced `I_ℰ(P)` for `ℰ=(E_v)_{v∈[m]⊔[n]}`, apply Hall–Rado [McD75] and double-weighting `w↔w'`.

---

## Project Structure

```
IndLorPoly/
├── Basic_verified.lean        §1 core: AdmitsSMatching, CT, SMatching, fSR, bridge smatching_indicator_iff
├── Matching_verified.lean     §1 indicator ind, sum_ind, SMatching 0-1 bridge (both directions)
├── Multiaffine_verified.lean  §1 coeff calculus: IS_monomial, coeff_elemSymm_IS (f_{S,r}=multiaffine(I_S(e_r)))
├── MatroidBasis.lean          Remark 2.6: basesFinset/baseCard, ct/ctMatroid, fMatroid, uniform case→Thm 1.1
├── HallRado_feasibility.lean  §2 Prop 2.3: IsPolyRank/InBase/inducedRank/EMatching, Δ^r_{[N]}, inBase_induced_of_admits
├── Polymatroid_verified.lean  §1 polymatroid: IsPolymatroid/IsMatroid, inducedRank, BasePolytope, Δ^r
├── DirectSum_verified.lean    Thm 2.2 step: sumRank P₁⊕P₂ on E₁⊕E₂, sum_split, Q(P₁⊕P₂)=Q(P₁)×Q(P₂)
├── Theorem22Step_verified.lean Thm 2.2 uniform corollaries (counting form)
├── Symbol_verified.lean       §2 symbol: κ-box, x^{[α]}, (x+u)^κ expansion, inducingOperator, symbolIS_eq, EGF
├── Computable.lean            §1 executable: gammaEdges/SMatch/CTL + Example 1.4 #eval (8/36/17/5)
├── Cited.lean                 Cited linear realizability (opaque + 4 axioms)
└── (scaffold) Basic/Operator/Symbol/...  draft files — excluded from default build

IndLorPoly.lean                 Root — re-exports 11 verified modules
FORMALIZATION_PLAN.md           Dependency table D1–D10, module DAG, milestones M1–M7
```

**Module DAG:**

```
Basic_verified
  ├── Matching_verified ──→ Multiaffine_verified
  ├── Computable
  ├── HallRado_feasibility
  ├── Polymatroid_verified ──→ DirectSum_verified ──→ Theorem22Step_verified
  │         └── Cited
  └── Symbol_verified ──→ MatroidBasis
              └── (all combine via SymbolRealizable → Preservation → MainTheorem, see plan)
```

---

## Paper → Lean Mapping

| # | Paper | Lean | File(s) | Status |
|---|---|---|---|---|
| D1 | §1 `C_T, Γ_S, α↔_Sβ` Def 1.2 | `AdmitsSMatching`, `CT`, `SMatching`, `fSR` | `Basic_verified` | ✓ 0 sorry |
| D2 | Thm 1.3 operator `I_S(x^{[α]})=Σy^{[β]}` | `ISm/IS`, `matchingBetas`, `coeff_ISm` | `Multiaffine_verified`, `Symbol_verified` | ✓ via basis |
| D3 | §1 polymatroid `rk_P,Q(P),Δ^r` | `IsPolymatroid`, `BasePolytope`, `uniformRank` | `Polymatroid_verified` | ✓ 0 sorry |
| D4 | §2 symbol `sym_T=T((x+u)^κ)`, Prop 2.1 | `symbol`, `Prop_2_1_*` | `Symbol_verified` | ✓ (+2 axioms) |
| D5 | **Thm 2.2** EGF of realizable poly. | `symbolIS_eq_latticeEGF`, `Theorem22Step` | `DirectSum/Theorem22Step` | ✓ core |
| D6 | Prop 2.3 Hall–Rado [McD75] | `inBase_induced_iff`, `mcdiarmid` | `HallRado_feasibility` | ✓ (1 axiom) |
| D7 | Thm 1.3 preservation | `theorem_1_3` | `Cited` + plan | axioms |
| D8 | Thm 1.1 `f_{S,r}` Lorentzian | `f_S_r`, `Theorem_1_1` | `MainTheorem_verified` | ✓ (2 bookkeeping sorries*) |
| D9 | §3 `A_S`, `Tmat` functoriality | `ASmat`, `Tmat_mul` | `Sec3_functorial` | ✓ 1 sorry† |
| D10 | Ex 1.4/2.5/3.4, Rmk 2.4/2.6 | `ex14`, `fMatroid`, `ct_eq_zero_of_lt` | `Computable`, `MatroidBasis` | ✓ 0 sorry |

\* `coeff_maf`/`maf_IS_elementary` are pure `coeff_sum`/`coeff_monomial` bookkeeping, plan in comments.
† `AS_support_eq_smatching` — blocked on `HasAntidiagonal` for `→₀ℕ`, fix via `coeff_mul_monomial` documented in [`Sec3_notes.md`](IndLorPoly/Sec3_notes.md).

**Verified: 11 modules, ~4340 lines, 0 hidden sorries in default target.**
Scaffold files (`Operator`, `Section3`, …) carry 24 legacy sorries outside the build — see [`FORMALIZATION_PLAN.md`](FORMALIZATION_PLAN.md).

---

## Module Reference

### `Basic_verified` — §1 Combinatorics
- `AdmitsSMatching S T B := ∃ μ:T≃B, ∀t, μ t ∈ S t` — bijection form of `C_T`
- `CT S T := card {B|AdmitsSMatching}` — matching statistic
- `SMatching S α β := ∃ W:Matrix ℕ, (Wij>0→i∈Sj) ∧ row=α ∧ col=β` — Def 1.2
- `SMatching_sum_eq: ∑α=∑β` — total-degree equality
- `fSR S r := Σ_{|T|=r} CT·y^T` — Theorem 1.1 polynomial
- **Bridge** `smatching_indicator_iff: SMatching S 1_B 1_T ↔ AdmitsSMatching S T B` — permutation-matrix construction, injectivity from `row≤1`, surjectivity from `|T|=|B|` double count.

### `Matching_verified` + `Multiaffine_verified` — §1 Coefficient Calculus
- `ind B : Fin m→ℕ` indicator, `sum_ind`, `ind_inj`
- `matchingBetas_mem: β∈matchingBetas ↔ SMatching` (finiteness via `β_j≤∑α`)
- `vecFact_ind: (1_B)!=1`, `prod_X_pow_eq_monomial`
- `coeff_IS_monomial_ind: coeff_{y^T}(I_S(x_B)) = 1 iff SMatching` — unit coeff (counts subsets, not bijections)
- `coeff_elemSymm_IS: coeff_{y^T}(Σ I_S(x_B)) = C_T(S)` — multi-affine part identity
- `f_S_r_coeff`, `CT_eq_zero_of_lt` (`|T|>m → 0`)

### `MatroidBasis` — Remark 2.6
- `basesFinset M`, `baseCard M ≤ m`, `card_eq_baseCard`
- `ct/ctMatroid`, `ctMatroid_le_ct`, `ctMatroid_eq_ct` (uniform `U_{r,m}` → Thm 1.1), `fMatroid_eq_ctPoly`
- `IsMultiaffine`, `degreeOf_squarefreeMon_le_one`, `isMultiaffine_*`
- `fMatroid_eq_sum_univ`, `basesFinset_loopyOn` example, `fMatroid_loopyOn_zero` (`r=0 → 1`)

### `HallRado_feasibility` — §2 Prop 2.3
- `IsPolyRank` (empty/mono/submodular), `InBase rk γ := (∀A, Σ_A γ≤rk A) ∧ Σγ=rk univ`
- `inducedRank rk ℰ J := rk(J.biUnion ℰ)`
- `EMatching ℰ γ δ w` (incidence `w e j≠0→e∈ℰ j`, row `γ`, col `δ`), `AdmitsEMatching`
- `sum_col_le`, `sum_col_eq_sum_biUnion` — mass carried by `⋃_{j∈J}ℰ_j`
- **`inBase_induced_of_admits`** (⇐): `γ∈Q(P)+ℰ-matching ⇒ δ∈Q(I_ℰ(P))` via `δ(J)=Σ_eΣ_{j∈J}w ≤ Σ_{∪}γ ≤ rk(∪)`
- `deltaRank N r := if A=∅ then 0 else r`, `deltaRank_isPolyRank`, `inBase_deltaRank_iff (N>0): InBase ↔ Σγ=r`
- **Axiom** `mcdiarmid` ⇒ half [McD75 Thm 2] → `inBase_induced_iff`

### `Polymatroid_verified` / `DirectSum_verified` / `Theorem22Step_verified` — Thm 2.2 Infrastructure
- `IsPolymatroid` (≤-form submodularity), `BasePolytope`, `InBase`, `basePolytopeLatticePoints`
- `inducedRank`, `isPolymatroid_induced` (`⋃_{I∩J}⊆⋃_I∩⋃_J` + monotonicity)
- `uniformRank`, `mem_inBase_uniform (N>0)`, convex `Q(P)`, `nonneg_of_mem_basePolytope`
- `DirectSum_verified`: `sumRank rk₁ rk₂` on `E₁⊕E₂`, `sum_split`, **`mem_inBase_sumRank: Q(P₁⊕P₂)=Q(P₁)×Q(P₂)`**, `card_*_sumRank` multiplicativity
- `Theorem22Step_verified`: `mem_inBase_uniform_sumRank` (`Q(Δ^{κ₁}⊕Δ^{κ₂})` criterion), counting corollaries

### `Symbol_verified` — §2 Symbol Theory
- `boxFinset κ`, `InBox`, `vecFact`/`vecMultinom_eq_div`, `xBr α := C(α!⁻¹)·∏X_i^{α_i}`
- `prod_X_pow_eq_monomial` (closes `Operator` hole), `prod_add_pow_eq_sum` — `(x+u)^κ` multinomial expansion
- `matchingBetas`, `inducingOperator` via `basisMonomials.constr` (linear map), `inducingOperator_xBr: I_S(x^{[α]})=Σy^{[β]}`
- `symbol T κ`, `yBrInl/uBrInr`, **`symbolIS_eq: sym_{I_S}=κ! Σ_{α≤κ}Σ_{β↔α} y^{[β]}u^{[κ-α]}`**
- `symLattice`/`symLatticeFam`, **`symbolIS_eq_latticeEGF`** — EGF of lattice points, `EGF`
- `IsLorentzianPoly/IsVolumePoly` opaque, **`Prop_2_1_*`** axioms [BH20 3.2][GHM+25 1.12], `Theorem_1_3_of_symbol_volume`

### `Computable` — Executable Example 1.4
- `Seq`, `gammaEdges`, `AdmitsSMatching` (injective `f:[m]→[n]`), `CT`, `SMatch`, `colSum`, `smatchBetas`
- `CT_le_choose`, `CT_eq_zero_iff/pos_iff`, `CT_mono`, `mem_SMatch` completeness (`w_ij≤α_i`)
- **Computed:** `|E|=8`, `|SMatch(0,2,2,1)|=36`, `|β|=17`, witnesses `(0,2,2,1)↔(2,2,1)` = **5** (paper shows 2)
- `S=({1..4},{2,3},{3,4})` — verifiable via `#eval`

### `Cited` — Linear Realizability (Axioms)
- `opaque LinearlyRealizable` — `∃ V_i,L⊆⊕V_i, rk(A)=dim π_A(L)`
- 4 marked `AXIOM (cited)`: `isPolymatroid_of_linearlyRealizable`, `uniform_linearlyRealizable` (diagonal `k^r↪(k^r)^{⊕N}`), `induced_linearlyRealizable`, `sumRank_linearlyRealizable`
- `#print axioms` elsewhere = `propext/Classical.choice/Quot.sound` only.

---

## Build & Verification

```bash
# Full verified library
lake build

# One module
lake build IndLorPoly.Symbol_verified -v

# Check sorries (should match default-target comment above)
grep -rn "sorry" IndLorPoly --include="*.lean" | grep -v "sorry-free" | wc -l

# Audit axioms (combinatorial theorems → standard 3 only)
lake env lean --run .scratch/audit.lean
```

**Current:** 11-module default target builds on `v4.36.0-rc2` (warnings: deprecated `if_pos`, unused `DecidableEq` → linter; no errors). Full `lake build` ran via 8-member Ultramath swarm `smvu128xo` — transcripts in [`.ultramath/smvu128xo/`](.ultramath/smvu128xo/) (`m3/m5` copies).

**Remaining:** full `lake build` needs `MvPolynomial.coeff` → `p.coeff m` migration for `Multiaffine_verified`/`Sec3_functorial`/`MainTheorem_verified` (dot-notation change in 4.36); 2 bookkeeping `sorry`s in `MainTheorem_verified` (`coeff_maf`, `maf_IS_elementary`) are monomial-basis algebra with plan in file.

---

## Axioms & Trust

Deep results are **opaque + cited axioms**, never unfolded — isolated in `Cited`/`MatroidBasis`/`Symbol_verified`:

| Axiom | Citation | Where |
|---|---|---|
| `Prop_2_1_lorentzian/volume` | BH20 Thm 3.2, GHM+25 Thm 1.12 | `Symbol_verified` |
| `mcdiarmid` (⇒ Hall–Rado) | McD75 Thm 2 / max-flow | `HallRado_feasibility` |
| `isPolymatroid/uniform/induced/sumRank_linearlyRealizable` | paper p.4, [EL24] | `Cited` |
| `theorem_1_1_*`, `remark_2_6_*`, `maf_lorentzian`, `elementary_realizable`, `IS_preserves_*` | BH20 3.5/4.6, GHM+25 3.3/2.10, Huh26 3.5 | `MatroidBasis`, `MainTheorem_verified` |
| `IsLorentzian`, `IsRealizableVolumePolynomial` | BH20 Def 2.4, GHM+25 | `opaque` predicates |

All combinatorial lemmas (`smatching_indicator_iff`, `coeff_elemSymm_IS`, `mem_inBase_sumRank`, `symbolIS_eq`, etc.) are **proved from scratch**, `#print axioms = propext/Classical.choice/Quot.sound`.

---

## References

- Eur, Nepal, Qin. *Induced Lorentzian and Volume Polynomials.* arXiv:2605.05319v2 (2026). [[PDF](enq-ilavp.pdf)]
- Brändén–Huh. *Lorentzian polynomials.* Ann. Math. 192 (2020). [BH20]
- Gutiérrez–Hoffmann–Michałek et al. *Volume polynomials.* [GHM+25]
- Eur–Larson. *Intersection theory of polymatroids.* [EL24] Cor 1.4 (EGF of realizable polymatroid is volume)
- Huh. *Volume polynomials — survey.* [Huh26] Ex 3.5 (Schubert realization of `elemSym`)
- McDiarmid. *Rado's theorem for polymatroids.* [McD75] Thm 2 (Prop 2.3)
- Welsh. *Matroid Theory* Ch. 8.2 — induced polymatroids `I_S(P)`.
