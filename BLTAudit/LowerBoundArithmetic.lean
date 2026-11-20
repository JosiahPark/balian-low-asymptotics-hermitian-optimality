import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# E5. The final arithmetic of Theorem 4.1, (L17)–(L19)

The end of §4 combines three facts: (L17) `2π log T_d ≤ (1 + C η_d) A_d + O(1)` with
`η_d = 1/log d`; the stopping time `T_d = R_d / S₀` with `R_d = d/√(log d)`, (L6); and the radius
sum `S₀ ≤ C₂ (log d)³`, (L14). With the trial bound `A_d ≤ C₀ log d`, this gives (L19),
`A_d ≥ 2π log d − 7π log log d − O(1)`. Here all of these enter as named real hypotheses, and Lean
checks only the arithmetic:

* `log_stopTime`: `log T = log d − (log log d)/2 − log S₀`;
* `lower_bound_arithmetic`: (L19) with the explicit constant `2π log C₂ + C C₀ + K`.

What this file does NOT prove: (L17), (L14) or the trial bound; they are hypotheses. Nothing here
proves Theorem 4.1 or Theorem 1.1.
-/

noncomputable section

open Real

namespace BLT

/-- `log (d / √(log d) / S₀) = log d − (log log d)/2 − log S₀`. -/
theorem log_stopTime {d S₀ : ℝ} (hd : 1 < d) (hS₀ : 0 < S₀) :
    Real.log (d / Real.sqrt (Real.log d) / S₀) =
      Real.log d - Real.log (Real.log d) / 2 - Real.log S₀ := by
  have hd0 : 0 < d := by linarith
  have hl : 0 < Real.log d := Real.log_pos hd
  have hsq : 0 < Real.sqrt (Real.log d) := Real.sqrt_pos.mpr hl
  rw [Real.log_div (div_pos hd0 hsq).ne' hS₀.ne', Real.log_div hd0.ne' hsq.ne',
    Real.log_sqrt hl.le]
  ring

/-- **E5, (L17)–(L19).** The final arithmetic of Theorem 4.1, from named real hypotheses. -/
theorem lower_bound_arithmetic {d C C₀ C₂ K A S₀ T : ℝ} (hd : 3 ≤ d) (hC : 0 ≤ C)
    (hL17 : 2 * π * Real.log T ≤ (1 + C / Real.log d) * A + K)
    (hT : T = d / Real.sqrt (Real.log d) / S₀) (hS₀ : 0 < S₀)
    (hL14 : S₀ ≤ C₂ * Real.log d ^ 3) (htrial : A ≤ C₀ * Real.log d) :
    2 * π * Real.log d - 7 * π * Real.log (Real.log d) -
      (2 * π * Real.log C₂ + C * C₀ + K) ≤ A := by
  have hl : 0 < Real.log d := Real.log_pos (by linarith)
  have hl3 : 0 < Real.log d ^ 3 := pow_pos hl 3
  have hC₂ : 0 < C₂ := by
    by_contra hneg
    push_neg at hneg
    have : C₂ * Real.log d ^ 3 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hl3.le
    linarith
  have hlogT : Real.log T = Real.log d - Real.log (Real.log d) / 2 - Real.log S₀ := by
    rw [hT]
    exact log_stopTime (by linarith) hS₀
  have hlogS : Real.log S₀ ≤ Real.log C₂ + 3 * Real.log (Real.log d) := by
    calc Real.log S₀ ≤ Real.log (C₂ * Real.log d ^ 3) := Real.log_le_log hS₀ hL14
      _ = Real.log C₂ + 3 * Real.log (Real.log d) := by
        rw [Real.log_mul hC₂.ne' hl3.ne', Real.log_pow]
        push_cast
        ring
  have hCA : C / Real.log d * A ≤ C * C₀ := by
    have hA' : A / Real.log d ≤ C₀ := by
      rw [div_le_iff₀ hl]
      linarith
    calc C / Real.log d * A = C * (A / Real.log d) := by ring
      _ ≤ C * C₀ := mul_le_mul_of_nonneg_left hA' hC
  have h2 := mul_le_mul_of_nonneg_left hlogS (by positivity : (0 : ℝ) ≤ 2 * π)
  rw [hlogT] at hL17
  nlinarith [hL17, h2, hCA]

end BLT

end
