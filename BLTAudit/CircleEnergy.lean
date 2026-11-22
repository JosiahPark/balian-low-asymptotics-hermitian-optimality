import BLTAudit.Basic

/-!
# E1. Circle energy

The one-variable estimate behind the energy of a phase winding `Q` times around a circle: expand
`∫ (θ' − Q)² ≥ 0` and use `∫ θ' = θ (end) − θ (start)`.

* `integral_sq_sub_const`: for `f` continuous on `[a, b]` and real `Q`,
  `∫ x in a..b, (f x − Q) ^ 2 = ∫ x in a..b, f x ^ 2 − 2 Q ∫ x in a..b, f x + (b − a) Q ^ 2`;
* `interval_energy_lower`: for `a ≤ b`, if `θ` is differentiable at every point of `[a, b]`,
  `deriv θ` is continuous on `[a, b]` and `θ b − θ a = (b − a) Q`, then
  `(b − a) Q ^ 2 ≤ ∫ x in a..b, (deriv θ x) ^ 2`;
* `circle_energy`: the statement of E1, the case `[0, 2π]`: if `θ (2π) − θ 0 = 2π Q`, then
  `2π Q ^ 2 ≤ ∫ φ in 0..2π, (deriv θ φ) ^ 2`.

"`θ` is `C¹` on `[0, 2π]`" is read as: `θ : ℝ → ℝ` is differentiable, as a function on `ℝ`, at every
point of the closed interval, and `deriv θ` is continuous on the closed interval. `Q` is any real
number; it need not be an integer.

What this file does NOT prove: anything about phases on the twisted torus, the degree of a phase,
the annulus bound (E2), or Theorem 4.1. It proves nothing toward Theorem 1.1 of the paper, and
nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

open scoped Real

namespace BLT

/-- Expansion of `∫ (f − Q)²` for `f` continuous on `[a, b]`. -/
theorem integral_sq_sub_const (f : ℝ → ℝ) (a b Q : ℝ) (hf : ContinuousOn f (Set.uIcc a b)) :
    ∫ x in a..b, (f x - Q) ^ 2 =
      (∫ x in a..b, f x ^ 2) - 2 * Q * (∫ x in a..b, f x) + (b - a) * Q ^ 2 := by
  have h1 : IntervalIntegrable (fun x => f x ^ 2) MeasureTheory.volume a b :=
    (hf.pow 2).intervalIntegrable
  have h2 : IntervalIntegrable (fun x => 2 * Q * f x) MeasureTheory.volume a b :=
    (continuousOn_const.mul hf).intervalIntegrable
  have h12 : IntervalIntegrable (fun x => f x ^ 2 - 2 * Q * f x) MeasureTheory.volume a b :=
    ((hf.pow 2).sub (continuousOn_const.mul hf)).intervalIntegrable
  have h3 : IntervalIntegrable (fun _ : ℝ => Q ^ 2) MeasureTheory.volume a b := by
    first
      | exact continuousOn_const.intervalIntegrable
      | exact intervalIntegrable_const
  have e1 : ∫ x in a..b, (f x - Q) ^ 2 = ∫ x in a..b, (f x ^ 2 - 2 * Q * f x + Q ^ 2) := by
    first
      | (congr 1; funext x; ring)
      | exact intervalIntegral.integral_congr fun x _ => by ring
  have e2 : ∫ x in a..b, (f x ^ 2 - 2 * Q * f x + Q ^ 2) =
      (∫ x in a..b, (f x ^ 2 - 2 * Q * f x)) + ∫ _ in a..b, Q ^ 2 :=
    intervalIntegral.integral_add h12 h3
  have e3 : ∫ x in a..b, (f x ^ 2 - 2 * Q * f x) =
      (∫ x in a..b, f x ^ 2) - ∫ x in a..b, 2 * Q * f x :=
    intervalIntegral.integral_sub h1 h2
  have e4 : ∫ x in a..b, 2 * Q * f x = 2 * Q * ∫ x in a..b, f x := by
    first
      | exact intervalIntegral.integral_const_mul (2 * Q) f
      | exact intervalIntegral.integral_const_mul _ _
      | rw [intervalIntegral.integral_const_mul]
  have e5 : ∫ _ in a..b, Q ^ 2 = (b - a) * Q ^ 2 := by
    first
      | rw [intervalIntegral.integral_const, smul_eq_mul]
      | simp
  first
    | (rw [e1, e2, e3, e4, e5]; done)
    | linear_combination e1 + e2 + e3 - e4 + e5

/-- **E1 on an interval.** If `θ b − θ a = (b − a) Q`, then `(b − a) Q² ≤ ∫ (θ')²`. -/
theorem interval_energy_lower (θ : ℝ → ℝ) (a b Q : ℝ) (hab : a ≤ b)
    (hd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ θ x)
    (hc : ContinuousOn (deriv θ) (Set.Icc a b))
    (hQ : θ b - θ a = (b - a) * Q) :
    (b - a) * Q ^ 2 ≤ ∫ x in a..b, deriv θ x ^ 2 := by
  have hu : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hc' : ContinuousOn (deriv θ) (Set.uIcc a b) := by
    rw [hu]
    exact hc
  have hd' : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ θ x := by
    rw [hu]
    exact hd
  have hftc : ∫ x in a..b, deriv θ x = θ b - θ a := by
    first
      | exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => (hd' x hx).hasDerivAt) hc'.intervalIntegrable
      | exact intervalIntegral.integral_deriv_eq_sub' θ rfl hd' hc'
  have hexp := integral_sq_sub_const (deriv θ) a b Q hc'
  have hnn : 0 ≤ ∫ x in a..b, (deriv θ x - Q) ^ 2 := by
    first
      | exact intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg (deriv θ x - Q)
      | exact intervalIntegral.integral_nonneg_of_forall hab fun x => sq_nonneg (deriv θ x - Q)
  rw [hexp, hftc, hQ] at hnn
  first
    | linarith
    | nlinarith [hnn]

/-- **E1.** Circle energy: if `θ` is `C¹` on `[0, 2π]` and `θ (2π) − θ 0 = 2π Q`, then
`2π Q² ≤ ∫ φ in 0..2π, (θ' φ)²`. -/
theorem circle_energy (θ : ℝ → ℝ) (Q : ℝ)
    (hd : ∀ x ∈ Set.Icc 0 (2 * π), DifferentiableAt ℝ θ x)
    (hc : ContinuousOn (deriv θ) (Set.Icc 0 (2 * π)))
    (hQ : θ (2 * π) - θ 0 = 2 * π * Q) :
    2 * π * Q ^ 2 ≤ ∫ φ in (0 : ℝ)..(2 * π), deriv θ φ ^ 2 := by
  have h0 : (0 : ℝ) ≤ 2 * π := by
    first
      | positivity
      | exact Real.two_pi_pos.le
  have hQ' : θ (2 * π) - θ 0 = (2 * π - 0) * Q := by
    first
      | (rw [sub_zero]; exact hQ)
      | linarith [hQ]
  have h := interval_energy_lower θ 0 (2 * π) Q h0 hd hc hQ'
  first
    | (rw [sub_zero] at h; exact h)
    | linarith [h]

end BLT

end
