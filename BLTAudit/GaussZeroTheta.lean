import BLTAudit.GaussLinearNearZero
import BLTAudit.Candidates

/-!
# H8. [HZ] as a statement about Mathlib's `jacobiTheta₂`

`GaussZeroUnique` (the input [HZ] of H3: `(1/2, 1/2)` is the only zero of `F = gaussZak` in
`[0,1)²`) is equivalent to the nonvanishing of `θ z = jacobiTheta₂ z i` at every point `z = y − x i`
with `x, y ∈ [0,1)`, `(x, y) ≠ (1/2, 1/2)`: `gaussZeroUnique_iff_theta`. The prefactor `gauss x` is
positive (C3), so the two zero sets coincide (`gaussZak_eq_zero_iff`).

This isolates the Jacobi-triple-product input of Appendix A.3 as one statement about Mathlib's theta
function: the zeros of `z ↦ jacobiTheta₂ z i` are exactly `1/2 + i/2 + ℤ + iℤ`.

What this file does NOT prove: that statement, hence not [HZ]; nothing toward [HV], [HL] or
Theorem 1.1.
-/

noncomputable section

namespace BLT

/-- `F(x, y) = 0` iff `θ (y − x i) = 0`. -/
theorem gaussZak_eq_zero_iff (x y : ℝ) :
    gaussZak x y = 0 ↔ thetaI ((y : ℂ) - (x : ℂ) * Complex.I) = 0 := by
  rw [gaussZak_eq_gauss_mul_thetaI]
  have hg : ((gauss x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (gauss_pos x).ne'
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hg
  · intro h
    rw [h, mul_zero]

/-- **H8.** [HZ] is the nonvanishing of `jacobiTheta₂ (· i)` on the half-open square minus its
centre. -/
theorem gaussZeroUnique_iff_theta :
    GaussZeroUnique ↔ ∀ x y : ℝ, 0 ≤ x → x < 1 → 0 ≤ y → y < 1 → ¬ (x = 1 / 2 ∧ y = 1 / 2) →
      jacobiTheta₂ ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I ≠ 0 := by
  constructor
  · intro hz x y hx0 hx1 hy0 hy1 hne hθ
    exact hne (hz x y hx0 hx1 hy0 hy1 ((gaussZak_eq_zero_iff x y).mpr hθ))
  · intro h x y hx0 hx1 hy0 hy1 hF
    by_contra hne
    exact h x y hx0 hx1 hy0 hy1 hne ((gaussZak_eq_zero_iff x y).mp hF)

/-- The zero `z₀ = 1/2 − i/2` itself: `θ z₀ = 0` (restating H6 in the form of the statement above). -/
theorem jacobiTheta₂_zakZeroPt : jacobiTheta₂ zakZeroPt Complex.I = 0 :=
  thetaI_zakZeroPt

end BLT

end
