import IndLorPoly.Basic
import IndLorPoly.Operator
import IndLorPoly.Lorentzian

open MvPolynomial

namespace IndLorPoly

variable {m n : ℕ}
variable (S : Fin n → Finset (Fin m))

/--
Theorem 1.1: For any integer $0 \leq r \leq m$, the polynomial $f_{\mathcal{S}, r}$
is Lorentzian and a realizable volume polynomial.
-/
theorem Theorem_1_1 (r : ℕ) (hr : r ≤ m) :
    IsLorentzian (f_S_r S r) ∧ IsRealizableVolumePolynomial (f_S_r S r) := by
  sorry

/--
Theorem 1.2: The linear operator $\mathcal{I}_{\mathcal{S}}$ preserves
Lorentzian polynomials and realizable volume polynomials over a field.
-/
theorem Theorem_1_2 :
    PreservesLorentzian (IS_Operator S) ∧ PreservesVolume (IS_Operator S) := by
  sorry

end IndLorPoly
