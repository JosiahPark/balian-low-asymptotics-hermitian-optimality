import BLTAudit.Basic

/-!
# E5. Final arithmetic of Theorem 4.1, (L17)–(L19), from named real hypotheses

Real-number bookkeeping only. For real `d ≥ 3` and `0 ≤ C`, write `L = log d`. If

* `hT`:    `2π log T ≤ (1 + C / L) * A + K`,
* `hTdef`: `T = d / √L / S₀`,
* `hS₀`, `hS`: `0 < S₀ ≤ C₂ L³`,
* `hA`:    `A ≤ C₀ L`,

then `2π L − 7π log L − (2π log C₂ + C * C₀ + K) ≤ A`, the shape of (L19).

* `log_T_eq`: `log T = L − (log L) / 2 − log S₀`;
* `pos_of_le_mul_pow`: `0 < C₂` follows from `0 < S₀ ≤ C₂ L³` and `0 < L`;
* `log_S₀_le`: `log S₀ ≤ log C₂ + 3 log L`;
* `div_mul_le_of_le_mul`: `C / L * A ≤ C * C₀`;
* `lower_bound_arithmetic`: the statement of E5.

Each of `hT`, `hTdef`, `hS₀`, `hS`, `hA` is a hypothesis of the theorem, not a fact proved here; in
the paper they come from the proof of Theorem 4.1 (§4.2–§4.3), which is not formalized in this file.

What this file does NOT prove: any of those hypotheses, Theorem 4.1, or the lower bound [HL]. It
proves nothing toward Theorem 1.1 of the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

open scoped Real

namespace BLT

/-- `log (d / √L / S₀) = log d − (log L) / 2 − log S₀` for `L = log d > 0`, `d ≠ 0`, `S₀ ≠ 0`. -/
theorem log_T_eq {d S₀ : ℝ} (hd0 : d ≠ 0) (hL : 0 < Real.log d) (hS₀ : S₀ ≠ 0) :
    Real.log (d / Real.sqrt (Real.log d) / S₀) =
      Real.log d - Real.log (Real.log d) / 2 - Real.log S₀ := by
  have hsq : 0 < Real.sqrt (Real.log d) := Real.sqrt_pos.mpr hL
  rw [Real.log_div (div_ne_zero hd0 hsq.ne') hS₀, Real.log_div hd0 hsq.ne', Real.log_sqrt hL.le]

/-- `0 < S₀ ≤ C₂ L³` with `0 < L` forces `0 < C₂`. -/
theorem pos_of_le_mul_pow {S₀ C₂ L : ℝ} (hS₀ : 0 < S₀) (hS : S₀ ≤ C₂ * L ^ 3) (hL : 0 < L) :
    0 < C₂ := by
  have hL3 : 0 < L ^ 3 := pow_pos hL 3
  by_contra hc
  have hc' : C₂ ≤ 0 := not_lt.mp hc
  have h := mul_nonneg (neg_nonneg.mpr hc') hL3.le
  nlinarith [h]

/-- `log S₀ ≤ log C₂ + 3 log L`. -/
theorem log_S₀_le {S₀ C₂ L : ℝ} (hS₀ : 0 < S₀) (hS : S₀ ≤ C₂ * L ^ 3) (hL : 0 < L) :
    Real.log S₀ ≤ Real.log C₂ + 3 * Real.log L := by
  have hC₂ := pos_of_le_mul_pow hS₀ hS hL
  have hL3 : 0 < L ^ 3 := pow_pos hL 3
  have h1 : Real.log S₀ ≤ Real.log (C₂ * L ^ 3) := by
    first
      | exact Real.log_le_log hS₀ hS
      | exact (Real.log_le_log_iff hS₀ (lt_of_lt_of_le hS₀ hS)).mpr hS
  have h2 : Real.log (C₂ * L ^ 3) = Real.log C₂ + 3 * Real.log L := by
    first
      | (rw [Real.log_mul hC₂.ne' hL3.ne', Real.log_pow, Nat.cast_ofNat]; done)
      | (rw [Real.log_mul hC₂.ne' hL3.ne', Real.log_pow]; norm_num)
      | simp [Real.log_mul hC₂.ne' hL3.ne', Real.log_pow]
  linarith

/-- `A ≤ C₀ L`, `0 ≤ C`, `0 < L` give `C / L * A ≤ C * C₀`. -/
theorem div_mul_le_of_le_mul {A C C₀ L : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hA : A ≤ C₀ * L) :
    C / L * A ≤ C * C₀ := by
  have hAd : A / L ≤ C₀ := by
    first
      | exact (div_le_iff₀ hL).mpr hA
      | exact (div_le_iff hL).mpr hA
  have e : C / L * A = C * (A / L) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hAd hC

/-- **E5.** The final arithmetic of Theorem 4.1, (L17)–(L19), from the named real hypotheses
`hT`, `hTdef`, `hS₀`, `hS`, `hA`. -/
theorem lower_bound_arithmetic (d C C₀ C₂ K A T S₀ : ℝ) (hd : 3 ≤ d) (hC : 0 ≤ C)
    (hT : 2 * π * Real.log T ≤ (1 + C / Real.log d) * A + K)
    (hTdef : T = d / Real.sqrt (Real.log d) / S₀)
    (hS₀ : 0 < S₀) (hS : S₀ ≤ C₂ * Real.log d ^ 3)
    (hA : A ≤ C₀ * Real.log d) :
    2 * π * Real.log d - 7 * π * Real.log (Real.log d) -
      (2 * π * Real.log C₂ + C * C₀ + K) ≤ A := by
  have hd0 : d ≠ 0 := (lt_of_lt_of_le (by norm_num) hd).ne'
  have hL : 0 < Real.log d := Real.log_pos (lt_of_lt_of_le (by norm_num) hd)
  have hlogT : Real.log T = Real.log d - Real.log (Real.log d) / 2 - Real.log S₀ := by
    rw [hTdef]
    exact log_T_eq hd0 hL hS₀.ne'
  have hlogS := log_S₀_le hS₀ hS hL
  have hpi0 : (0 : ℝ) ≤ 2 * π := by
    first
      | positivity
      | exact Real.two_pi_pos.le
  have hpi : 2 * π * Real.log S₀ ≤ 2 * π * (Real.log C₂ + 3 * Real.log (Real.log d)) :=
    mul_le_mul_of_nonneg_left hlogS hpi0
  have hCA := div_mul_le_of_le_mul hC hL hA
  rw [hlogT] at hT
  first
    | linarith
    | nlinarith [hT, hpi, hCA]

end BLT

end
