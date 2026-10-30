# §2 "The symbol of I_S" — formalization (member m6, direction D4)

File: [`IndLorPoly/Symbol.lean`](IndLorPoly/Symbol.lean) (395 lines, **no `sorry`**).
It imports only `Mathlib` and the repo's `IndLorPoly/Basic.lean`.

## Build

```bash
cd .ultramath/smvu128xo/m6
export LEAN_PATH="$LEAN_PATH:$(pwd)"
lean IndLorPoly/Basic.lean        # copy of the repo file, needed for the olean
lean IndLorPoly/Symbol.lean       # 0 errors, 0 warnings, ~8 s
```

## What is proved (all sorry-free; only `propext`, `Classical.choice`, `Quot.sound`)

| Paper reference | Lean name |
|---|---|
| §2 `R[x]_κ`, `α ≤ κ` | `boxFinset`, `mem_boxFinset`, `InBox` |
| §1 Notation `α!`, `x^[α]=x^α/α!` | `vecFact`, `xBr`, `vecMultinom`, `vecMultinom_eq_div` (`κ!/(α!(κ-α)!) = ∏ binom`) |
| — (fills a `sorry` of the skeleton) | `prod_X_pow_eq_monomial : ∏_j X_j^{α_j} = monomial α 1` |
| §2 `sym_T(y,u) = T((x+u)^κ)`, "equivalently `κ! Σ_{0≤α≤κ} T(x^[α])u^[κ-α]`" | `prod_add_pow_eq_sum` — the multinomial expansion of `(x+u)^κ` in `ℝ[x₁..x_m,u₁..u_m]` |
| Thm 1.3 on monomials, `I_S(x^[α]) = Σ_{β:α↔β} y^[β]` | `inducingOperator` (via `MvPolynomial.basisMonomials.constr`), `inducingOperator_monomial`, `inducingOperator_xBr` |
| §2 definition `sym_T` | `symbol`, `yBrInl`, `uBrInr` |
| **§2 displayed computation** `sym_{I_S} = κ! Σ_{0≤α≤κ} Σ_{β:α↔β} y^[β]u^[κ-α]` | `symbolIS`, **`symbolIS_eq`** |
| §2 support / EGF of lattice points | `symLattice`, `mem_symLattice`, `symLatticeFam`, **`symbolIS_eq_latticeEGF`** (coefficient of `y^βu^δ` is `κ!/(β!δ!)` exactly on `{(β,κ-α) : 0≤α≤κ, α↔β}`) |
| Prop 2.1 ([BH20] Thm 3.2, [GHM+25] Thm 1.12) | `Prop_2_1_lorentzian`, `Prop_2_1_volume` — **`axiom`, cited** |
| Proof of Thm 1.3 from Thm 2.2 | `Theorem_1_3_of_symbol_volume` |

Lorentzian / volume predicates are `opaque` (`IsLorentzianPoly`, `IsVolumePoly`) and are
generalized from `Fin n` to an arbitrary finite variable set, since the symbol lives in
the variables `[n] ⊔ [m]`.

## Not done here (belongs to other directions)

* The product form `sym_T = T((x+u)^κ)` as an equality of polynomials (needs an
  "acts trivially on `u`" extension `ℝ[x,u] → ℝ[y,u]`; the *content* of the equivalence,
  `prod_add_pow_eq_sum`, is proved). Noted in the file.
* The polymatroid realisability half of Theorem 2.2 (that `symLattice` is
  `Q(I_E(P)) ∩ ℤ` for a linearly realizable polymatroid) — direction D1/D5.
* The global (un-boxed) version of Prop 2.1: `Theorem_1_3_of_symbol_volume` is stated
  for a fixed `κ`-box, matching the paper's operator `T : ℝ[x]_κ → ℝ[y]`.
