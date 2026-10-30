# §3 inducing operators — status

`Sec3.lean` (compiles with `lean Sec3.lean`, 1 sorry):

Proved, sorry-free:
* `linForm`, `coeff_linForm`, `coeff_linForm_ne`, `coeff_linForm_nonneg`,
  `coeff_linForm_single_pos` — linear-form coefficient calculus over ℚ.
* `ASmat` : Matrix (Fin m) (Fin n) ℚ, the matrix of columns e_{S_j} (Example 3.1).
* `Tmat M` : the operator f(x) ↦ f(M y) as an algebra hom (MvPolynomial.aeval).
* `Tmat_X`, `Tmat_C`, `lin_mul`, `Tmat_mul` : **functoriality**
  `Tmat (M₁ * M₂) = (Tmat M₂).comp (Tmat M₁)` — the change-of-variables operator
  composes with matrix multiplication (contrast: I_S does not compose; Example 3.6).
* `AS_S`, `AS_sqfree_monomial` : monomial action on squarefree monomials.

Remaining gap: `AS_support_eq_smatching` (Example 3.1's support statement) is stated,
not proved.  The intended proof is the combinatorial lemma

  coeff β (∏_{a∈s} (∑_j c a j y_j)) ≠ 0 ↔ ∃ g : τ → σ,
      (∀ a ∈ s, c a g(a) ≠ 0) ∧ β = ∑_{a∈s} single (g a) 1     (c ≥ 0),

proved by induction on `s`: direction ⇒ via `MvPolynomial.coeff_mul` +
`coeff_linForm_ne`; direction ⇐ via `Finset.single_le_sum` (nonneg coefficient
counts give no cancellation).  Blocker met at the deadline: `Finset.antidiagonal`
for `σ →₀ ℕ` is not synthesised in this Mathlib version (`HasAntidiagonal` instance
missing), which is what `coeff_mul` is stated in terms of; the fix is to restate the
step using `MvPolynomial.coeff_mul_monomial` (`coeff (γ + s) (p * monomial s r) =
coeff γ p * r`) instead of the antidiagonal decomposition.

Not started: Proposition 3.2 (coefficient powering c ↦ c^q, endpoints q=0 ↔ I_S,
q=1 ↔ T; needs [BH20, Prop 3.25] as a cited axiom), Examples 3.4/3.6 computations.
