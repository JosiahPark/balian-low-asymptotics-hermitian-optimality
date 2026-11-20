import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# F3. The limit constant `2π` from the two-sided bound

If eventually `2π log d − 7π log log d − C ≤ a_d ≤ 2π log d + C`, then `a_d / log d → 2π`. With
`a_d` the minimal rescaled energy, the two-sided bound is the conclusion of Theorem 1.1 of the paper,
so this file shows that its limit constant is `2π`, the energy of one unit phase winding.

* `tendsto_loglog_div_log`: `log log x / log x → 0`;
* `limit_constant`: the statement above, for any real sequence.

What this file does NOT prove: the two-sided bound itself. It is a hypothesis here; Theorem 1.1 is
not proved in this repository.
-/

noncomputable section

open Filter Topology Real

namespace BLT

/-- `log (log x) / log x → 0` as `x → ∞`. -/
theorem tendsto_loglog_div_log :
    Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simp only [pow_one, one_mul, add_zero] at h
  exact h.comp Real.tendsto_log_atTop

/-- **F3.** A two-sided bound `2π log d − 7π log log d − C ≤ a_d ≤ 2π log d + C` forces
`a_d / log d → 2π`. -/
theorem limit_constant (a : ℕ → ℝ) (C : ℝ)
    (h : ∀ᶠ d : ℕ in atTop, 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C ≤ a d ∧
      a d ≤ 2 * π * Real.log d + C) :
    Tendsto (fun d : ℕ => a d / Real.log d) atTop (𝓝 (2 * π)) := by
  have hN : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun d : ℕ => Real.log d) atTop atTop := Real.tendsto_log_atTop.comp hN
  have hll : Tendsto (fun d : ℕ => Real.log (Real.log d) / Real.log d) atTop (𝓝 0) :=
    tendsto_loglog_div_log.comp hN
  have hc : Tendsto (fun d : ℕ => C / Real.log d) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have hlow : Tendsto (fun d : ℕ => 2 * π - 7 * π * (Real.log (Real.log d) / Real.log d) -
      C / Real.log d) atTop (𝓝 (2 * π)) := by
    have := ((tendsto_const_nhds (x := 2 * π)).sub (hll.const_mul (7 * π))).sub hc
    simpa only [mul_zero, sub_zero] using this
  have hup : Tendsto (fun d : ℕ => 2 * π + C / Real.log d) atTop (𝓝 (2 * π)) := by
    have := (tendsto_const_nhds (x := 2 * π)).add hc
    simpa only [add_zero] using this
  have hpos : ∀ᶠ d : ℕ in atTop, 0 < Real.log d := hL.eventually_gt_atTop 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [h, hpos] with d hd hl
    rw [le_div_iff₀ hl]
    have e : (2 * π - 7 * π * (Real.log (Real.log d) / Real.log d) - C / Real.log d) *
        Real.log d = 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C := by
      field_simp
    linarith [hd.1]
  · filter_upwards [h, hpos] with d hd hl
    rw [div_le_iff₀ hl]
    have e : (2 * π + C / Real.log d) * Real.log d = 2 * π * Real.log d + C := by
      field_simp
    linarith [hd.2]

end BLT

end
