import BLTAudit.ZakInverse

/-!
# H11. Perturbation of the phase map `ph w = w / |w|`

Proved here:

* `ph_zero`, `norm_ph_le_one`: `ph 0 = 0` and `‖ph w‖ ≤ 1`;
* `ph_mul`: `ph (c * a) = ph c * ph a` for all `c a : ℂ`;
* `ph_natCast_mul`: `ph (n * a) = ph a` for a positive natural `n`;
* `norm_ph_sub_ph_le`: `‖ph a − ph b‖ ≤ 2 ‖a − b‖ / ‖b‖` for `b ≠ 0`;
* `norm_ph_sub_ph_le_of_approx`: if `‖a − b‖ ≤ ε` and `0 < m ≤ ‖b‖`, then `‖ph a − ph b‖ ≤ 2 ε / m`.

These are the pointwise steps of §3.2 that turn an approximation of `Z g_d` by the samples of `F`
into an approximation of the phases.

What this file does NOT prove: any estimate involving `d`, `g_d` or `F`; nothing toward [HE], [HV],
[HL] or Theorem 1.1.
-/

noncomputable section

namespace BLT

theorem ph_zero : ph 0 = 0 := by
  unfold ph
  simp

theorem norm_ph_le_one (w : ℂ) : ‖ph w‖ ≤ 1 := by
  by_cases hw : w = 0
  · rw [hw, ph_zero, norm_zero]
    exact zero_le_one
  · exact (norm_ph hw).le

/-- **H11.** `ph` is multiplicative. -/
theorem ph_mul (c a : ℂ) : ph (c * a) = ph c * ph a := by
  unfold ph
  rw [norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

/-- **H11.** A positive real scalar does not change the phase. -/
theorem ph_natCast_mul {n : ℕ} (hn : n ≠ 0) (a : ℂ) : ph ((n : ℂ) * a) = ph a := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : ph (n : ℂ) = 1 := by
    unfold ph
    have hnorm : ((‖(n : ℂ)‖ : ℝ) : ℂ) = (n : ℂ) := by
      first
        | (rw [Complex.norm_natCast]; push_cast; rfl)
        | simp
    rw [hnorm]
    exact div_self hn'
  rw [ph_mul, h1, one_mul]

/-- **H11.** `‖ph a − ph b‖ ≤ 2 ‖a − b‖ / ‖b‖` for `b ≠ 0`. -/
theorem norm_ph_sub_ph_le {a b : ℂ} (hb : b ≠ 0) : ‖ph a - ph b‖ ≤ 2 * ‖a - b‖ / ‖b‖ := by
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
  by_cases ha : a = 0
  · simp only [ha, ph_zero, zero_sub, norm_neg, norm_ph hb]
    rw [le_div_iff₀ hB]
    linarith
  · have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hA' : ‖a‖ ≠ 0 := hA.ne'
    have hB' : ‖b‖ ≠ 0 := hB.ne'
    have key : ph a - ph b = (a - b) * (((‖b‖ : ℝ) : ℂ))⁻¹ +
        a * ((‖a‖⁻¹ - ‖b‖⁻¹ : ℝ) : ℂ) := by
      unfold ph
      push_cast
      simp only [div_eq_mul_inv]
      ring
    have n1 : ‖(a - b) * (((‖b‖ : ℝ) : ℂ))⁻¹‖ = ‖a - b‖ / ‖b‖ := by
      rw [norm_mul, norm_inv, Complex.norm_of_nonneg (norm_nonneg b), div_eq_mul_inv]
    have e : ‖a‖ * (‖a‖⁻¹ - ‖b‖⁻¹) = (‖b‖ - ‖a‖) / ‖b‖ := by
      first
        | (field_simp; ring)
        | field_simp
    have n2 : ‖a * ((‖a‖⁻¹ - ‖b‖⁻¹ : ℝ) : ℂ)‖ = |‖b‖ - ‖a‖| / ‖b‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖a‖ * |‖a‖⁻¹ - ‖b‖⁻¹| = |‖a‖ * (‖a‖⁻¹ - ‖b‖⁻¹)| := by
            rw [abs_mul, abs_of_pos hA]
        _ = |(‖b‖ - ‖a‖) / ‖b‖| := by rw [e]
        _ = |‖b‖ - ‖a‖| / ‖b‖ := by rw [abs_div, abs_of_pos hB]
    have h3 : |‖b‖ - ‖a‖| ≤ ‖a - b‖ :=
      (abs_norm_sub_norm_le b a).trans (norm_sub_rev b a).le
    have h4 : |‖b‖ - ‖a‖| / ‖b‖ ≤ ‖a - b‖ / ‖b‖ := div_le_div_of_nonneg_right h3 hB.le
    rw [key]
    calc ‖(a - b) * (((‖b‖ : ℝ) : ℂ))⁻¹ + a * ((‖a‖⁻¹ - ‖b‖⁻¹ : ℝ) : ℂ)‖
        ≤ ‖(a - b) * (((‖b‖ : ℝ) : ℂ))⁻¹‖ + ‖a * ((‖a‖⁻¹ - ‖b‖⁻¹ : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖a - b‖ / ‖b‖ + |‖b‖ - ‖a‖| / ‖b‖ := by rw [n1, n2]
      _ ≤ ‖a - b‖ / ‖b‖ + ‖a - b‖ / ‖b‖ := by linarith
      _ = 2 * ‖a - b‖ / ‖b‖ := by ring

/-- **H11.** If `‖a − b‖ ≤ ε` and `0 < m ≤ ‖b‖`, then `‖ph a − ph b‖ ≤ 2 ε / m`. -/
theorem norm_ph_sub_ph_le_of_approx {a b : ℂ} {ε m : ℝ} (hab : ‖a - b‖ ≤ ε) (hm : 0 < m)
    (hmb : m ≤ ‖b‖) : ‖ph a - ph b‖ ≤ 2 * ε / m := by
  have hb : b ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hm hmb)
  have hε : 0 ≤ 2 * ε := by linarith [norm_nonneg (a - b)]
  exact (norm_ph_sub_ph_le hb).trans
    (div_le_div₀ hε (by linarith) hm hmb)

end BLT

end
