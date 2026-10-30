/-
Copyright: formalization of §1–2 of Eur–Nepal–Qin, "Induced Lorentzian and
Volume Polynomials" (arXiv 2605.05319v2).

# The direct-sum step of the proof of Theorem 2.2, in the uniform case

In the proof of Theorem 2.2 (paper p. 4) the polymatroid

  `P = Δ^{κ_1}_{E_1} ⊕ ⋯ ⊕ Δ^{κ_m}_{E_m}`

is a direct sum of uniform polymatroids, so

  `Q(P) = ∏_{i∈[m]} Q(Δ^{κ_i}_{E_i})`,

and, since `Q(Δ^κ_{[N]}) = {x ∈ ℝ_{≥0}^N : ∑ x_i = κ}`, a vector belongs to
`Q(P)` if and only if for every `i` the sum of its coordinates over `E_i` is
`κ_i`.  This file records that statement for two summands (the general case is
obtained by iterating `mem_inBase_sumRank`), both in the lattice-point form used
in the paper and in counting form.
-/
import IndLorPoly.Polymatroid_verified
import IndLorPoly.DirectSum_verified

open Finset
open scoped BigOperators

namespace IndLorPoly

/-- The base polytope of `Δ^{κ₁}_{E₁} ⊕ Δ^{κ₂}_{E₂}`: lattice points are exactly
the vectors whose sums over the two parts are `κ₁` and `κ₂` (paper p. 4). -/
theorem mem_inBase_uniform_sumRank {N₁ N₂ κ₁ κ₂ : ℕ} (h₁ : 0 < N₁) (h₂ : 0 < N₂)
    {x : Fin N₁ ⊕ Fin N₂ → ℕ} :
    InBase (sumRank (uniformRank N₁ κ₁) (uniformRank N₂ κ₂)) x ↔
      (∑ a, x (Sum.inl a)) = κ₁ ∧ (∑ b, x (Sum.inr b)) = κ₂ := by
  rw [mem_inBase_sumRank (isPolymatroid_uniform N₁ κ₁) (isPolymatroid_uniform N₂ κ₂),
    mem_inBase_uniform h₁, mem_inBase_uniform h₂]

/-- The counting form of the direct-sum step: the number of lattice points of
`Q(Δ^{κ₁} ⊕ Δ^{κ₂})` is the product of the numbers of lattice points of the
two summands (paper p. 4, "Since `P` is the direct sum …"). -/
theorem card_basePolytopeLatticePoints_uniform_sumRank (N₁ N₂ κ₁ κ₂ : ℕ) :
    (basePolytopeLatticePoints
        (sumRank (uniformRank N₁ κ₁) (uniformRank N₂ κ₂))).card =
      (basePolytopeLatticePoints (uniformRank N₁ κ₁)).card *
        (basePolytopeLatticePoints (uniformRank N₂ κ₂)).card :=
  card_basePolytopeLatticePoints_sumRank (isPolymatroid_uniform N₁ κ₁)
    (isPolymatroid_uniform N₂ κ₂)

/-- A worked instance of the factorisation: for `N₁ = N₂ = κ₁ = κ₂ = 1` the
constant vector `(1,1)` is a lattice point of `Q(Δ^1 ⊕ Δ^1)`, as predicted by
the criterion `∑_{e ∈ E_i} x_e = κ_i`. -/
example : InBase (sumRank (uniformRank 1 1) (uniformRank 1 1)) (fun _ => 1) := by
  rw [mem_inBase_uniform_sumRank (by norm_num) (by norm_num)]
  constructor <;> simp

end IndLorPoly
