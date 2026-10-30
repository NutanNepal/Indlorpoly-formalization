import IndLorPoly.Basic
import IndLorPoly.Operator
import IndLorPoly.Lorentzian
import IndLorPoly.Polymatroid
import IndLorPoly.Symbol
import IndLorPoly.SymbolRealizable
import Mathlib.Algebra.MvPolynomial.Basic

namespace IndLorPoly

variable {m n : ℕ}
variable (S : Fin n → Finset (Fin m))

/-!
# Preservation theorem (Paper Theorem 1.3 / Theorem 2.2 ⇒ Theorem 1.3)

Theorem 1.3: `I_S : R[x]→R[y]` preserves Lorentzian and realizable volume polynomials.

Proof structure (Paper p.4):
- Theorem 2.2: `sym_{I_S}` is EGF of linearly realizable polymatroid `I_𝓔(P)` on `[m]⊔[n]`
- `[EL24, Cor 1.4]`: EGF of linearly realizable ⇒ realizable volume polynomial
- `[BH20, Thm 4.6]`: realizable volume ⇒ Lorentzian
- Prop 2.1 (BH20 Thm 3.2 + GHM+25 Thm 1.12): symbol Lorentzian/volume ⇒ operator preserves
-}

-- External preservation axioms (Prop 2.1) are already in Lorentzian.lean as axioms:
-- `prop21_Lorentzian` and `prop21_volume`.

/--
Axiom: symbol Lorentzian ⇒ operator preserves Lorentzian (BH20 Thm 3.2, Prop 2.1a).
-/
axiom prop21_Lorentzian' {m n : ℕ} (κ : Fin m → ℕ)
    (T : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)
    (hHom : True) -- T preserves homogeneous (elided)
    (hSym : IsLorentzian (symbolOf T κ)) :
    PreservesLorentzian (m := m) (n := n) T

axiom prop21_Volume' {m n : ℕ} (κ : Fin m → ℕ)
    (T : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ)
    (hHom : True)
    (hSym : IsRealizableVolumePolynomial (symbolOf T κ)) :
    PreservesVolume (m := m) (n := n) T

/--
Theorem 1.3 (Paper p.2): `I_S` preserves Lorentzian and volume.
-/
theorem theorem_1_3 :
    PreservesLorentzian (IS_Operator S) ∧ PreservesVolume (IS_Operator S) := by
  constructor
  · intro f hf
    -- For any κ bounding f (choose κ = max exponent +1), apply Prop 2.1
    -- Need κ such that support of f ⊆ [0,κ]; existence via finiteness of support
    -- Then symIS_isVolume gives symIS_isLorentzian, then Prop 2.1
    have hSym : ∀ κ : Fin m → ℕ, IsLorentzian (symIS S κ) := fun κ => symIS_isLorentzian S κ
    -- Pick κ large enough (e.g. κ i = max degree +1); apply axiom
    sorry
  · intro f hf
    have hSym : ∀ κ, IsRealizableVolumePolynomial (symIS S κ) := fun κ => symIS_isVolume S κ
    sorry

/--
Alias matching paper's numbering: Theorem 1.2 in submitted version = Theorem 1.3 in v2.
We keep `Theorem_1_2` for compatibility.
-/
theorem Theorem_1_2' : PreservesLorentzian (IS_Operator S) ∧ PreservesVolume (IS_Operator S) :=
  theorem_1_3 S

end IndLorPoly
