import IndLorPoly.Basic
import IndLorPoly.Operator
import IndLorPoly.Lorentzian
import IndLorPoly.Symbol
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.MvPolynomial.Basic

namespace IndLorPoly

variable {m n : ℕ}
variable (S : Fin n → Finset (Fin m))

/-!
# §3 Inducing operators — the space `IS` (Paper p.6-7)

Property (*) : If `supp(f)=Q(P)∩ℤ^m` then `supp(I_S(f))=Q(I_S(P))∩ℤ^n`.
Other operators with (*): `A_S : f(x)↦f(A_S y)` where `A_S` has columns `e_{S_j}`,
and general nonnegative `A` with same zero-pattern.
`IS` deformation retracts to `I_S` (Prop 3.2).
Examples 3.4, 3.6.
-/

/--
Support `supp(f) = {α : c_α ≠ 0}` as a finset of exponent vectors.
Paper §1: "support is the polymatroid P" means `supp(f)=Q(P)∩ℤ^m`.
-/
def supportFinset {k : ℕ} (p : MvPolynomial (Fin k) ℝ) : Finset (Fin k → ℕ) :=
  -- Convert Finsupp support (Fin k →₀ ℕ) to Fin k → ℕ via equivFunOnFinite
  p.support.image (fun s => fun i => s i)

/--
Property (*) : `supp(I_S(f))` is the induced polymatroid `I_S(P)` when `supp(f)=Q(P)`.
Paper display (∗) p.3 and p.6.
-/
def HasSupportProperty (T : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ (rk : Finset (Fin m) → ℕ) (hP : IsPolymatroid rk)
    (f : MvPolynomial (Fin m) ℝ),
    (∀ α : Fin m → ℕ, α ∈ supportFinset f ↔
      (∀ I : Finset (Fin m), ∑ i ∈ I, (α i : ℝ) ≤ (rk I : ℝ))
      ∧ ∑ i : Finset.univ (α := Fin m), (α i : ℝ) = (rk Finset.univ : ℝ)) →
    (∀ β : Fin n → ℕ, β ∈ supportFinset (T f) ↔
      (∀ I : Finset (Fin n), ∑ i ∈ I, (β i : ℝ) ≤ (inducedRank rk S I : ℝ))
      ∧ ∑ i : Finset.univ (α := Fin n), (β i : ℝ) = (inducedRank rk S Finset.univ : ℝ))

/--
Theorem: `I_S` satisfies (*). Paper p.6, follows from Prop 2.3 (Hall-Rado).
We state it as a theorem with sorry (depends on Hall-Rado).
-/
theorem IS_hasSupportProperty : HasSupportProperty S (IS_Operator S) := by
  intro rk hP f hf
  -- Use Hall-Rado similarly to Theorem 2.2 but for arbitrary P (not just direct sum of Δ)
  sorry

/--
The matrix `A_S` whose columns are `e_{S_j} = Σ_{i∈S_j} e_i` (Paper Example 3.1).
`A_S : ℝ^m ← ℝ^n` as `Matrix (Fin m) (Fin n) ℝ`.
-/
noncomputable def AS_Matrix : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of (fun i j => if i ∈ S j then (1 : ℝ) else 0)

/--
Linear operator `A_S : f(x) ↦ f(A_S y)` — change of variables `x_i ↦ Σ_{j:S_j∋i} y_j`.
Paper Example 3.1.

We define it on monomials: `A_S( x^α ) = ∏_i (Σ_{j:i∈S_j} y_j)^{α_i}`.
Extension by linearity.
-/
noncomputable def AS_Operator : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun p :=
    -- Substitute: eval MvPolynomial (Fin m) at the `m` polynomials ` Σ_{j:i∈S_j} y_j`
    -- Use MvPolynomial.eval₂ / aeval
    -- For now define via p.sum expanding monomials:
    p.sum (fun s coeff =>
      coeff • ∏ i : Fin m, (∑ j : Fin n, if i ∈ S j then MvPolynomial.X j else 0) ^ (s i))
  map_add' := by
    intro p q; simp [Finsupp.sum_add_index']; intro s; simp [add_smul]
  map_smul' := by
    intro r p; simp [Finsupp.sum, Finsupp.smul_sum]; sorry

/--
`A_S` also satisfies (*), and has same support as `I_S` on monomials (Paper p.6).
The distinction: coefficient of `y^{[β]}` in `A_S(x^{[α]})` counts weightings,
while `I_S` only detects existence.
-/
theorem support_AS_eq_support_IS (α : Fin m → ℕ) :
    supportFinset (AS_Operator S (MvPolynomial.monomial (vecToFinsupp α) (1 : ℝ))) =
    supportFinset (IS_Operator S (MvPolynomial.monomial (vecToFinsupp α) (1 : ℝ))) := by
  -- Both supports are { β | α↔β }
  sorry

/--
General nonnegative matrix `A` with same zero-nonzero pattern as `A_S`
also satisfies (*). (Paper p.6)
-/
def HasSameZeroPattern (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, (A i j ≠ 0 ↔ i ∈ S j) -- exact pattern (nonnegative already assumed)

/--
The space `𝕀_S` of operators `T : R[x]_κ → R[y]` with Lorentzian symbol and property (*).
Paper Prop 3.2 statement.
-/
def IsInISpace (κ : Fin m → ℕ) (T : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ) : Prop :=
  HasSupportProperty S T ∧
  IsLorentzian (symbolOf T κ) -- symbol Lorentzian (BH20 notion extended to y⊕u variables)

/--
Proposition 3.2: `𝕀_S` deformation retracts to `I_S` via `c^q` powering.
Paper proof: `symbol(T^q) = Σ c_{α,β}^q y^{[β]} u^{[κ-α]}` and
`[BH20, Prop 3.25]` says `c^q` of Lorentzian is Lorentzian.

We formalize the path; contractibility is the key.
-/
theorem prop_3_2_deformationRetract (κ : Fin m → ℕ)
    (T : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)
    (hT : IsInISpace S κ T) :
    ∃ path : ℝ → MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ,
      path 0 = IS_Operator S ∧ path 1 = T ∧
      ∀ q : ℝ, 0 ≤ q ∧ q ≤ 1 → IsInISpace S κ (path q) := by
  -- Define T^q via coefficient powering on symbol, then recover operator via
  -- symbol theory inverse (BH20 Prop 3.25 guarantees Lorentzian preservation)
  -- T^0 = I_S (all c^0 =1), T^1 = T
  sorry

/--
Example 3.4: `S=(1,2,12)` on `[2]`, `I_S(x1x2)=y1y2+y1y3+y2y3+y3^2/2` vs `A(x1x2)=(ay1+by3)(cy2+dy3)`.
Distinguishing invariant: product of coefficients of `y1y2` and `y3^2` vs `y1y3` and `y2y3`.
-/
noncomputable def exampleS_12_12 : Fin 3 → Finset (Fin 2) :=
  fun j => match j with
  | 0 => {0}
  | 1 => {1}
  | 2 => {0, 1}

/-- `I_S(x1x2)` computation for Example 3.4 -/
theorem example_3_4_IS :
    IS_monomial exampleS_12_12 (fun i => if i = 0 then 1 else 1) =
    -- y1y2 + y1y3 + y2y3 + y3^2/2
    -- In our encoding: Σ (α!/β!) y^β  with α=(1,1)
    -- β ∈ {(1,1,0),(1,0,1),(0,1,1),(0,0,2)} with α!=1, β! accordingly
    -- So coefficients 1,1,1,1/2
    (MvPolynomial.X (0 : Fin 3) * MvPolynomial.X 1 +
     MvPolynomial.X 0 * MvPolynomial.X 2 +
     MvPolynomial.X 1 * MvPolynomial.X 2 +
     MvPolynomial.C (2⁻¹ : ℝ) * MvPolynomial.X 2 ^ 2) := by
  unfold IS_monomial matchingBetas SMatching exampleS_12_12
  -- Compute matchingBetas by brute force enumeration of 0..2 bounded
  sorry

/--
Non-composability example 3.6: `I_{S2∘S1} ≠ I_{S2}∘I_{S1}`.
Concrete: `U={1,2}, V={1a,1b,2a,2b}, W={a,b}` with `S1=({1},{1},{2},{2})` and `S2=({1a,2a},{1b,2b})`.
Then `I_{S2∘S1}(x1x2)=z_a z_b + z_a^{[2]} + z_b^{[2]}` but `(I_{S2}∘I_{S1})(x1x2)=2z_a z_b+...`.
-/
theorem example_3_6_nonComposable : True := trivial -- placeholder #eval demonstration

end IndLorPoly
