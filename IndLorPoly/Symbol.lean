import IndLorPoly.Basic
import IndLorPoly.Operator
import IndLorPoly.Polymatroid
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Basic

open MvPolynomial

namespace IndLorPoly

variable {m n : ℕ}
variable (S : Fin n → Finset (Fin m))

/-!
# Symbol of the operator `I_S` (Paper §2)

Fix `κ ∈ ℤ^m_{≥0}`. `R[x]_κ` = polynomials with support in `∏ [0,κ_i]`.
The symbol `sym_T(y,u) = T((x+u)^κ) ∈ R[y,u]` where `T` acts trivially on `u`.
Equivalently `sym_T(y,u) = Σ_{0≤α≤κ} (κ choose α) T(x^α) u^{κ-α}`.
For `I_S`: `sym_{I_S}(y,u) = κ! Σ_{α≤κ} I_S(x^{[α]}) u^{[κ-α]}`
           `= Σ_{α≤κ} Σ_{β:α↔β} y^{[β]} u^{[κ-α]}`  (paper display, p.4)
-/

/--
The `κ`-box: all `α` with `α ≤ κ` componentwise.
-/
def kappaBox (κ : Fin m → ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset (fun i : Fin m => Finset.Icc 0 (κ i)))

/--
`α ≤ κ` iff `α ∈ kappaBox κ`.
-/
lemma mem_kappaBox (κ α : Fin m → ℕ) : α ∈ kappaBox κ ↔ ∀ i, α i ≤ κ i := by
  simp [kappaBox, Fintype.mem_piFinset, Finset.mem_Icc]

/--
Binomial coefficient ` (κ choose α) = ∏ (κ_i choose α_i) `.
-/
noncomputable def kappaChoose (κ α : Fin m → ℕ) : ℕ :=
  ∏ i, Nat.choose (κ i) (α i)

/--
Factorial scaling `κ! = ∏ κ_i!`.
-/
noncomputable def kappaFact (κ : Fin m → ℕ) : ℝ :=
  ∏ i, (Nat.factorial (κ i) : ℝ)

/--
Normalized monomial `x^{[α]} = x^α / α!` . We store numerator and denominator separately.
-/
noncomputable def normalizedMonomial {k : ℕ} (α : Fin k → ℕ) : MvPolynomial (Fin k) ℝ :=
  MvPolynomial.C ((vecFact α)⁻¹) * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin k) ℝ) ^ α j

/--
Symbol of a linear operator `T : R[x]_κ → R[y]`
`sym_T(y,u) = T((x+u)^κ)`  — we define it via the expansion formula
`sym_T = Σ_{α≤κ} (κ choose α) T(x^α) u^{κ-α}`.
For concrete `T = I_S` this yields the paper's formula.
We work in variables `Fin n ⊕ Fin m` ( `y` on `inl`, `u` on `inr` ).
-/
noncomputable def symbolOf (T : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)
    (κ : Fin m → ℕ) : MvPolynomial (Fin n ⊕ Fin m) ℝ :=
  ∑ α ∈ kappaBox κ,
    let ca := (kappaChoose κ α : ℝ)
    let Txα := T (∏ i, (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) ^ α i)
    -- Embed Txα (in y-vars) into y⊕u via `inl`, and u^{κ-α} via `inr`
    let yPart : MvPolynomial (Fin n ⊕ Fin m) ℝ :=
      MvPolynomial.rename (Sum.inl) Txα
    let uPart : MvPolynomial (Fin n ⊕ Fin m) ℝ :=
      ∏ i : Fin m, (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin n ⊕ Fin m) ℝ) ^ (κ i - α i)
    MvPolynomial.C ca * yPart * uPart

/--
Symbol specialized to `I_S` — the paper's `sym_{I_S}` (p.4).
-/
noncomputable def symIS (κ : Fin m → ℕ) : MvPolynomial (Fin n ⊕ Fin m) ℝ :=
  symbolOf (IS_Operator S) κ

/--
Expansion lemma: `sym_{I_S}(y,u) = Σ_{α≤κ} Σ_{β:α↔β} y^{[β]} u^{[κ-α]}` up to `κ!` scaling.
Paper computes `sym = κ! Σ I_S(x^{[α]}) u^{[κ-α]}`.

We state the normalized version:
`symIS = Σ_{α≤κ} Σ_{β:α↔β} (κ choose α) (α!/β!) y^β u^{κ-α}`
which equals `κ! Σ Σ y^{[β]} u^{[κ-α]}`.
-/
theorem symIS_expansion (κ : Fin m → ℕ) :
    symIS S κ =
    ∑ α ∈ kappaBox κ, ∑ β ∈ matchingBetas S α,
      MvPolynomial.C ((kappaChoose κ α : ℝ) * (vecFact α / vecFact β)) *
      (MvPolynomial.rename Sum.inl (∏ j, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ) ^ β j) *
       ∏ i, (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin n ⊕ Fin m) ℝ) ^ (κ i - α i)) := by
  unfold symIS symbolOf IS_Operator IS_monomial
  -- Expand IS_Operator on monomial X^α (needs IS_Operator_monomial bridge)
  -- Then distribute (κ choose α) scalar.
  -- The equality follows by linearity and the definition of IS_monomial.
  sorry

/--
The symbol is an exponential generating function of its support:
`symIS = Σ_{(δ)} c_δ z^{[δ]}` where `δ = (κ-α,β)` runs over the polymatroid base.
This is stated in the paper before Theorem 2.2.
-/
def IsExponentialGeneratingFunction (p : MvPolynomial (Fin n ⊕ Fin m) ℝ) : Prop :=
  ∀ d : (Fin n ⊕ Fin m →₀ ℕ), p.coeff d ≠ 0 →
    -- Placeholder: the coefficient is 1/ d! when in support, 0 otherwise
    True

end IndLorPoly
