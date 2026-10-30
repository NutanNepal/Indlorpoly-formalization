# Formalization Plan: Induced Lorentzian Polynomials ( Eur–Nepal–Qin )

Source: `ilp-cdraft.tex` / `ilp-cdraft.pdf` — 6 pages.
Lean: `leanprover/lean4:v4.30.0-rc2`, Mathlib `452dba9` (master).

## 1. Source theorems in dependency order

| # | Paper statement | Lean name (frozen) | Depends on |
|---|---|---|---|
| D1 | §1 `C_T(S)` , `Γ_S` , `α ↔_S β` (Def 1.2) | `AdmitsSMatching`, `CT`, `SMatching` | `Fin m`, `Fin n`, `S : Fin n → Finset (Fin m)` |
| D2 | Thm 1.2 operator `I_S : R[x] → R[y]`, `I_S(x^α/α!)= Σ_{β: α↔β} y^β/β!` | `IS_Operator` | D1 + `MvPolynomial (Fin k) R` basis |
| D3 | p.2 polymatroid, `rk_P`, `Q(P)`, matroid extra axiom, induced `rk_{I_S(P)}(I)=rk_P(∪_{i∈I} S_i)` | `IsPolymatroid`, `BasePolytope`, `InducedPolymatroid` | D1 |
| D4 | §2 symbol `sym_T(y,u)=T((x+u)^κ)` and `Prop 2.1` (BH20 Thm 3.2, GHMSW Thm 1.12) | `symbol` , `Prop_2_1` | D2 — *external: import as axiom/opaque* |
| D5 | Thm 2.2 — `sym_{I_S}` is EGF of linearly-realizable polymatroid on `[m]⊔[n]` | `Theorem_symbol_realizable` | D1–D4 + `Δ^r_[N]`, direct sum, `P` on edges |
| D6 | Prop 2.3 Hall–Rado for polymatroids (McD75 Thm 2) | `hall_rado_polymatroid` | D3 — *external, axiomatize then prove combinatorial equivalence* |
| D7 | Thm 1.3 — `I_S` preserves Lorentzian / realizable volume polynomials | `Theorem_1_2` | D5+D4+D6 |
| D8 | Thm 1.1 — `f_{S,r}= Σ_{T∈binom n r} C_T(S) y^T` is Lorentzian / volume | `Theorem_1_1` | D7 + `elemSym`, multi-affine part, Prop 2.10/3.5 |
| D9 | §3 `(*)` support property, `A_S : f(x)↦f(A_S y)`, general `A`, Prop 3.1 deformation retract | `Property_star`, `A_S_operator`, `Prop_3_1` | D1–D2 |
| D10 | Ex 2.5 instability, Ex 3.3, Rem 2.4 r-restricted, Rem 2.6 matroid `C_T(M,S)` | examples | D1–D2 |

Math dependencies are linear except D4/D6 are black-box imports. D5 is the heart; everything else is corollary.

## 2. What Mathlib already has / lacks

Has:
- `MvPolynomial (Fin n) R` with `support : Finset (σ →₀ ℕ)`, `coeff`, `monomial`, `X`, `C`, `Finset.sum`, `Finsupp`, `PDeriv` — sufficient for multidegree polynomials, homogeneous degree filtering, exponential scaling.
- `Matrix (Fin m) (Fin n) ℕ`, `Finset` lattice, `Fintype (Fin n → ℕ)` via `piFinset`.
- `Combinatorics.Matroid` (+ Minor, Map, Dual) — but no polymatroid, no `BasePolytope`, no direct sum `Δ^r_[N]`, no linear realizability.
- No `IsLorentzian`, `IsRealizableVolumePolynomial`, no Hessian-eigenvalue machinery, no stable-polynomial theory.

Decision: define Lorentzian / volume as `opaque` predicates satisfying exactly the imported properties needed for the paper, with `axiom` wrappers for Prop 2.1, EL2024 Cor 1.4, BH20 Thm 2.25/4.6, Prop 2.10, 3.5. This isolates the combinatorial core (D1,D2,D5–D6) which is provable from scratch, and lets the main implications type-check. Later phase can replace opaques by real definitions without changing statement types.

## 3. Foundational API choices

### 3.1 Carrier for `[m]`,`[n]`

Keep `Fin m`, `Fin n`. Variables `m n : ℕ` implicit. `S : Fin n → Finset (Fin m)` matches paper `S=(S₁,…,Sₙ)`. Alternative `Matrix Bool` is isomorphic but obscures `S_j` filtering and `E_v` definitions; keep Finset and provide `toBipartiteGraph : SimpleGraph (Fin m ⊕ Fin n)` helper if needed.

### 3.2 `α ↔_S β`

Current:
```lean
def SMatching (α : Fin m → ℕ) (β : Fin n → ℕ) : Prop :=
  ∃ W : Matrix (Fin m) (Fin n) ℕ,
    (∀ i j, W i j > 0 → i ∈ S j) ∧
    (∀ i, (∑ j, W i j) = α i) ∧
    (∀ j, (∑ i, W i j) = β j)
```
This is correct. Add API lemmas: `SMatching.sum_eq` (already in Basic.lean), `SMatching.zero`, symmetry via transpose *not* true (m≠n), `SMatching.mono` w.r.t. edge-superset.

For `C_T(S)` the paper's bijection version: `AdmitsSMatching T B := ∃ f : T ≃ B, ∀ t, f t ∈ S t`. This is the `r=1` slice of `SMatching`; prove bridge lemma `AdmitsSMatching ↔ SMatching (indicator T) (indicator B)` later.

Need `Decidable (SMatching S α β)` — brute-force search over bounded `W` (`W i j ≤ min(α i, β j)`). Provide `Fintype` bound `N = Σ α i` as in `matchingBetas`.

### 3.3 Polynomials

Use `MvPolynomial (Fin m) ℝ` (paper uses `ℝ`, volume over any field — keep `ℝ` for Lorentzian, parameterize volume `R` later). Multidegree exponents are `Fin m →₀ ℕ` (= `Finsupp`). Current code uses `Fin m → ℕ`; add coercion `toFinsupp : (Fin m → ℕ) → Fin m →₀ ℕ` and back for `coeff`/`monomial` API.

`vecFact α = ∏ i, (α i)! : ℝ` — correct, but also need `ℕ` version for divisibility lemmas. Add `vecFact_ne_zero`.

`f_{S,r} : MvPolynomial (Fin n) ℝ` as
`∑ T ∈ {T : Finset (Fin n) // |T|=r} C (CT S T) * ∏ t∈T, X t`
current definition via `Finset.univ.filter` is fine; add `f_S_r_coeff` lemma linking `coeff` to `CT`.

### 3.4 Inducing operator

Paper: `I_S(x^α/α!) = Σ_{β: α↔β} y^β/β!`. So `I_S(x^α) = Σ β (α!/β!) y^β`. Current `IS_monomial` is correct.

Full `IS_Operator : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ` must be built by linear extension of the monomial basis.

Lean recipe:
- `MvPolynomial` has `Finsupp`-indexed basis `monomial`. Use `Finsupp.linearCombination ℝ (fun d => IS_monomial (toVec d))` or define via `MvPolynomial.lift` from `MvPolynomial.eval₂` universal property. Simpler: `def IS_Operator : … := Finsupp.lsum ℝ … ` composed with `toFinsuppIso : MvPolynomial ≃ₗ Finsupp …`.
- Must prove `ℚ`-linear and respects finite support; `matchingBetas` finiteness already shows image is polynomial (degree bounded by `Σ α`).
- Provide `IS_Operator_monomial`, `IS_Operator_C`, `IS_Operator_X_pow`, `IS_Operator_homogeneous`.

Symbol: for `κ : Fin m → ℕ` fixed,
`sym_IS κ : MvPolynomial (Fin n ⊕ Fin m) ℝ`
`sym_IS = Σ_{0≤α≤κ} (κ choose α) • IS_Operator (X^α) * u^{κ-α}` with `u` variables `Fin m` second copy. Use disjoint sum `Fin n ⊕ Fin m` and `MvPolynomial.rename` embeddings.

## 4. Proposed module DAG (replaces current 4 files)

```
IndLorPoly/Basic.lean              — D1: S, Γ_S, AdmitsSMatching, CT, SMatching, sum_eq
  ↓
IndLorPoly/Polymatroid.lean        — D3: IsPolymatroid, RankFn axioms, Q(P), Induced, Δ^r, directSum, linearRealizable
  ↓
IndLorPoly/Operator.lean           — D2: vecFact, matchingBetas, IS_monomial, IS_Operator (linear), coeff lemmas, support lemmas
  ↓
IndLorPoly/Symbol.lean             — κ-box, symbol, symbol_expansion lemma (the displayed sum)
  ↓
IndLorPoly/Lorentzian.lean         — opaque IsLorentzian, IsRealizableVolumePolynomial, Prop 2.1 as axioms + derived wrappers
  ↓
IndLorPoly/HallRado.lean           — Prop 2.3 statement (axiom + combinatorial reformulation)
  ↓
IndLorPoly/SymbolRealizable.lean   — Thm 2.2 proof (the core: build P=⊕ Δ^{κ_i}_{E_{i∈[m]}}, invoke Hall-Rado, double-weight w↔w' argument)
  ↓
IndLorPoly/Preservation.lean       — Thm 1.3 from Thm 2.2 + Prop 2.1 + Cor 1.4
  ↓
IndLorPoly/MainTheorem.lean        — Thm 1.1 from Preservation + elemSym realizable + multi-affine part preserves
  ↓
IndLorPoly/InducingSpace.lean      — §3: A_S, Property (*), Prop 3.1 + Examples 2.5/3.3 as #eval checks
  ↓
IndLorPoly.lean (root) — re-exports public API
```

Rationale: each file = one paper section's definitions; consumers only import what they need; cycle-free. Existing `Lorentzian.lean` / `Operator.lean` / `Theorems.lean` map to 3 of these — split `Theorems.lean` into `Preservation` + `MainTheorem`, add `Polymatroid`, `Symbol`, `HallRado`.

Public API (frozen statements, types must not change without approval):
- `SMatching`, `AdmitsSMatching`, `CT`, `f_S_r`, `IS_Operator`, `IsLorentzian`, `IsRealizableVolumePolynomial`, `Theorem_1_1`, `Theorem_1_2` (=Thm 1.3), `Theorem_symbol_realizable`.

## 5. Milestones (each compiles with `lake build IndLorPoly.<file>`)

### M1 — Combinatorics (1–2 days)
- Clean `Basic.lean` already done; add missing lemmas: `SMatching_sum_eq`, `SMatching_iff_exists_weight`, `CT_nonneg`, finiteness of `matchingBetas`, bridge `AdmitsSMatching ↔ SMatching_of_indicator`.
- Tests: `#eval CT example` on `m=n=2, S=({0},{1})` → `CT {0}=1`, `CT {0,1}=1`; `m=3 n=3 S=(123,123,12)` → `I_S(x123)` manual check yields `((y1+y2+y3)^3 - y3^3)/6`.

### M2 — Polymatroid API (2–3 days)
- Define:
```lean
structure IsPolymatroid {E : Type} [Fintype E] (rk : Finset E → ℕ) : Prop where
  rk_empty : rk ∅ = 0
  mono : ∀ I J, I ⊆ J → rk I ≤ rk J
  submod : ∀ I J, rk I + rk J ≥ rk (I ∪ J) + rk (I ∩ J)
def BasePolytope (rk) : Set (E → ℝ) := {x | (∀ I, ∑ i∈I, x i ≤ rk I) ∧ ∑ i, x i = rk univ}
def inducedRank (rk : Finset E → ℕ) (Ss : Fin n → Finset E) (I : Finset (Fin n)) : ℕ := rk (I.biUnion Ss)
def uniformPolymatroid (N r : ℕ) : Finset (Fin N) → ℕ := fun A => if A=∅ then 0 else r
def directSum ...
def LinearlyRealizable ...
```
- Prove `Δ^r_[N]` is polymatroid and linearly realizable over infinite field (generic embedding — axiomatize existence of generic subspace, state as `axiom uniform_realizable` to avoid linear algebra of generic matrices in M1).
- Provide `BasePolytope.latticePoints` as `Finset`.

### M3 — Operator linearity (2 days)
- Fill `sorry` in `IS_Operator` via `Finsupp.linearCombination`.
- Prove `IS_Operator_monomial`, `IS_Operator_C`, `IS_Operator_X_pow`, `IS_Operator_homogeneous`.
- Define `multiAffinePart : MvPolynomial σ ℝ → MvPolynomial σ ℝ` (keep only squarefree monomials; filter `support` by `∀ s, d s ≤ 1`).
- Lemma `f_S_r_eq : f_S_r = multiAffinePart (IS_Operator (elemSym m r))` where `elemSym m r = Σ_{B∈binom m r} x^B`.

### M4 — Symbol (1–2 days)
- Fix `κ : Fin m → ℕ`.
- Define `κ.choose α = ∏ i, Nat.choose (κ i) (α i)` and `uPow`.
- Define `symbol (κ) (T) = T((x+u)^κ)` expansion lemma.
- Compute `sym_IS` expansion as displayed paper formula; this is pure algebra, no Lorentzian input.

### M5 — Core proof Thm 2.2 (3–5 days, the project’s real work)
- State `hall_rado`: `δ ∈ Q(I_E(P)) ↔ ∃ γ∈Q(P), EMatching γ δ`.
- Construct `E = edges Γ_S`, `Ev`, `P = ⊕_i Δ^{κ_i}_{E_{i∈[m]}}`, `𝓔 = (Ev)_{v∈[m]⊔[n]}`, `I_𝓔(P)`.
- Formalize double weight argument:
  - Forward: existence of `w' : E→ℕ` witnessing `α↔_S β` → extend to `w : E→ℕ×ℕ` with `w+w' ∈ Q(P)`, second bullet `Σ_{e∈E_{i∈[m]}} w_e = κ_i - α_i`.
  - Backward: `w` with three bullets → projection to `w'` witnesses `α↔β` (uses `Q(P)=∏ Q(Δ)` → `Σ (w+w')=κ_i`).
- Prove `LinearlyRealizable P` → `LinearlyRealizable I_𝓔(P)` (lemma: induced of realizable is realizable — axiomatize or prove from definition of `I_𝓔`).
- Conclude `sym_IS = EGF (Q(I_𝓔(P)) ∩ ℤ^{m+n})`.

### M6 — Preservation + Main (2 days, given opaques)
- Axioms (with precise citations):
  - `BH20_Thm_3_2 : IsLorentzian sym_T → PreservesLorentzian T`
  - `GHMSW_Thm_1_12 : IsRealizableVolume sym_T → PreservesVolume T`
  - `EL2024_Cor_1_4 : LinearlyRealizable P → IsRealizableVolume (EGF Q(P))`
  - `BH20_Thm_4_6 : IsRealizableVolume → IsLorentzian`, `BH20_Thm_2_25`, `GHMSW_Prop_2_10`, `BH20_Cor_3_5` (multi-affine part preserves).
- Prove `Theorem_1_2` (Thm 1.3) from M5 + axioms.
- Prove `Theorem_1_1` : `elemSym m r` is realizable volume (axiom: Schubert variety), apply M6, then multi-affine part.

### M7 — §3 + Examples (1–2 days, optional)
- Define `A_S : Matrix (Fin m) (Fin n) ℝ` with columns `e_{S_j}`, `A_S_op f = f(A_S·y)`.
- Prove `support (A_S_op (X^α)) = support (IS_Operator (X^α))` and coefficient formula `coeff = number of weightings`.
- `Prop 3.1` deformation retract: symbol with `c^q` coefficients, using `BH20 Prop 3.25` as axiom.
- Examples: compute `IS(x1x2x3)` for `S=(123,123,12)` and verify non-stable witness via numeric `Complex` evaluation; `S=(1,2,12)` product-equality for `A`.

## 6. What to assume vs. prove

Prove in Lean: D1 bridge lemmas, D2 finiteness/linearity, D5 combinatorial double-weight (bulk of work). The paper’s 2-page proof of Thm 2.2 is self-contained given Prop 2.3.

Assume (axiom/opaque with citation):
- Lorentzian / volume definitions + all preservation implications (Prop 2.1 family). Reason: requires Hessian spectral theory + Chow rings + intersection theory not in Mathlib; formalizing them is a separate project comparable to the paper.
- Prop 2.3 Hall–Rado for polymatroids — can be proved combinatorially but is an imported theorem (McD75); treat as axiom with explicit reduction to needed corollary.
- Realizability of `Δ^r` via generic embedding and of `elemSym` via Schubert — need algebraic geometry.

Tag each `axiom` with `-- Axiom from [BH20, Thm X]` so later replacement is tracked.

## 7. Verification

- `lake build` gate: each milestone file builds; final `lake build IndLorPoly` succeeds with `sorry` only inside clearly marked axioms/examples, `0 sorry` in M5 core.
- `#eval` sanity checks on small `m,n` for `CT`, `SMatching`, `IS_monomial` vs hand-computed paper examples (2.5, 3.3).
- Statement audit: run `lean-statement-audit` on `Theorem_1_1`, `Theorem_1_2`, `SMatching`, `IS_Operator` against paper definitions (quantifiers, carriers `ℝ` vs field, `ℕ` vs `ℤ≥0`, `Finset` vs set).
- No hidden `sorry` in statement types: every theorem’s `Prop` mentions only `IsLorentzian`, `IsRealizableVolumePolynomial`, `SMatching`.

## 8. Open questions for owner

1. Keep `ℝ` for Lorentzian but volume polynomials over arbitrary field `k`? Paper proves over any field; Lean could param `R : Type [Field]` for `IsRealizableVolumePolynomial R` — do you want the extra generality or specialization to `ℝ` first?
2. Model `Γ_S` as `Matrix Bool` vs `Finset` vs `SimpleGraph (Fin m ⊕ Fin n)`? Current Finset is minimal; `SimpleGraph` gives edge API for free.
3. Replace opaques by real Lorentzian definition later? If yes, plan a sub-project importing `Mathlib.Analysis.Convex` + Hessian.
4. File granularity: keep `Basic.lean` as one file or split `Matching.lean` + `CT.lean`? Current DAG keeps `Basic` small (<200 lines).

## 9. Next action (if approved)

1. Copy this plan to `FORMALIZATION_PLAN.md`.
2. Generate boilerplate `IndLorPoly/Polymatroid.lean`, `IndLorPoly/Symbol.lean`, `IndLorPoly/HallRado.lean` with `sorry`-free axiom stubs and `#eval` examples.
3. Fill `IS_Operator` `sorry` and prove `SMatching_sum_eq` already done; add `CT ↔ SMatching` bridge.
4. Schedule M5 deep dive.
