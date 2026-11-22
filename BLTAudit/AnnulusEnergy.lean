import BLTAudit.Basic

/-!
# E2. Annulus logarithm (L13)

Integrating a lower bound `c ≤ g ρ` against `dρ / ρ` over `[r, s]`, with `0 < r < s`:

* `inv_continuousOn_of_pos`: `ρ ↦ ρ⁻¹` is continuous on `[r, s]` when `0 < r ≤ s`;
* `integral_const_mul_inv`: `∫ ρ in r..s, c * ρ⁻¹ = c * log (s / r)` for `0 < r`, `0 < s`;
* `annulus_log_lower`: if `g` is interval integrable on `[r, s]` and `c ≤ g ρ` for every `ρ` in
  `[r, s]`, then `c * log (s / r) ≤ ∫ ρ in r..s, g ρ / ρ`;
* `annulus_energy`: the statement of E2, the case `c = 2π Q²`:
  `2π Q² * log (s / r) ≤ ∫ ρ in r..s, g ρ / ρ`.

In the paper `g ρ` stands for the energy on the circle of radius `ρ` (bounded below by E1); here
`g` is an arbitrary real function and the lower bound is a hypothesis.

What this file does NOT prove: that the circle energy of a phase on the twisted torus is at least
`2π Q²`, any statement about the degree of a phase, the ball growth, or Theorem 4.1. It proves
nothing toward Theorem 1.1 of the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

open scoped Real

namespace BLT

/-- `ρ ↦ ρ⁻¹` is continuous on `[r, s]` for `0 < r ≤ s`. -/
theorem inv_continuousOn_of_pos {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    ContinuousOn (fun ρ : ℝ => ρ⁻¹) (Set.uIcc r s) := by
  have hpos : ∀ ρ ∈ Set.uIcc r s, ρ ≠ 0 := by
    intro ρ hρ
    rw [Set.uIcc_of_le hrs] at hρ
    exact (lt_of_lt_of_le hr hρ.1).ne'
  first
    | exact continuousOn_id.inv₀ hpos
    | exact continuousOn_inv₀.mono hpos

/-- `∫ ρ in r..s, c / ρ = c log (s / r)`, written with `ρ⁻¹`. -/
theorem integral_const_mul_inv (c : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∫ ρ in r..s, c * ρ⁻¹ = c * Real.log (s / r) := by
  have h : ∫ ρ in r..s, ρ⁻¹ = Real.log (s / r) := by
    first
      | exact integral_inv_of_pos hr hs
      | simp [integral_inv_of_pos hr hs]
  first
    | rw [intervalIntegral.integral_const_mul, h]
    | simp [h]

/-- **E2, general constant.** A lower bound `c ≤ g` on `[r, s]` gives
`c log (s / r) ≤ ∫ ρ in r..s, g ρ / ρ`. -/
theorem annulus_log_lower (c : ℝ) (g : ℝ → ℝ) {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hg : IntervalIntegrable g MeasureTheory.volume r s)
    (hlow : ∀ ρ ∈ Set.Icc r s, c ≤ g ρ) :
    c * Real.log (s / r) ≤ ∫ ρ in r..s, g ρ / ρ := by
  have hinv := inv_continuousOn_of_pos hr hrs.le
  have hgi : IntervalIntegrable (fun ρ => g ρ * ρ⁻¹) MeasureTheory.volume r s :=
    hg.mul_continuousOn hinv
  have hci : IntervalIntegrable (fun ρ : ℝ => c * ρ⁻¹) MeasureTheory.volume r s :=
    hinv.intervalIntegrable.const_mul c
  have hmono : ∫ ρ in r..s, c * ρ⁻¹ ≤ ∫ ρ in r..s, g ρ * ρ⁻¹ := by
    refine intervalIntegral.integral_mono_on hrs.le hci hgi fun ρ hρ => ?_
    have hρ0 : 0 ≤ ρ⁻¹ := inv_nonneg.mpr (le_trans hr.le hρ.1)
    exact mul_le_mul_of_nonneg_right (hlow ρ hρ) hρ0
  have hdiv : ∫ ρ in r..s, g ρ * ρ⁻¹ = ∫ ρ in r..s, g ρ / ρ := by
    first
      | simp only [div_eq_mul_inv]
      | exact intervalIntegral.integral_congr fun ρ _ => (div_eq_mul_inv (g ρ) ρ).symm
  calc c * Real.log (s / r) = ∫ ρ in r..s, c * ρ⁻¹ :=
        (integral_const_mul_inv c hr (hr.trans hrs)).symm
    _ ≤ ∫ ρ in r..s, g ρ * ρ⁻¹ := hmono
    _ = ∫ ρ in r..s, g ρ / ρ := hdiv

/-- **E2.** Annulus logarithm (L13): for `0 < r < s` and `g` interval integrable on `[r, s]` with
`2π Q² ≤ g ρ` there, `2π Q² log (s / r) ≤ ∫ ρ in r..s, g ρ / ρ`. -/
theorem annulus_energy (Q : ℝ) (g : ℝ → ℝ) {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hg : IntervalIntegrable g MeasureTheory.volume r s)
    (hlow : ∀ ρ ∈ Set.Icc r s, 2 * π * Q ^ 2 ≤ g ρ) :
    2 * π * Q ^ 2 * Real.log (s / r) ≤ ∫ ρ in r..s, g ρ / ρ :=
  annulus_log_lower (2 * π * Q ^ 2) g hr hrs hg hlow

end BLT

end
