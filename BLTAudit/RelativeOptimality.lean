import BLTAudit.Basic

/-!
# F2. Relative optimality from two named bounds (§5)

Real sequences only. For `A a : ℕ → ℝ` (in the paper `A d = d² E(f_d)`, the energy of the
candidate window, and `a d = a_d`, the minimum), with `L = log d`, assume for all large `d`:

* `hle`: `a d ≤ A d`;
* `hU`, the shape of the named hypothesis **[HU]**: `A d ≤ 2π L + C₁`;
* `hL`, the shape of the named hypothesis **[HL]**: `2π L − 7π log L − C₂ ≤ a d`.

Proved here, from these hypotheses only:

* `tendsto_log_nat`, `tendsto_inv_log_nat`: `log d → ∞` and `(log d)⁻¹ → 0` along `ℕ`;
* `tendsto_log_div_self`, `tendsto_loglog_div_log`: `log x / x → 0`, hence `log (log d) / log d → 0`;
* `tendsto_div_log_of_bounds`: if eventually `2π L − 7π log L − C₂ ≤ a d ≤ 2π L + C₁`, then
  `a d / log d → 2π`;
* `relative_optimality`: the statement of F2, eventually `0 ≤ A d − a d ≤ 7π log L + C₁ + C₂`, and
  `A d / a d → 1`.

What this file does NOT prove: [HU] or [HL] themselves (the trial bound (U4) with (U14), and the
lower bound (L19) of Theorem 4.1), any link between `A`, `a` and the energies of the paper (that is
F4), or Theorem 1.1. It proves statements FROM the two named hypotheses only.
-/

noncomputable section

open Filter Topology
open scoped Real

namespace BLT

/-- `log d → ∞` along the naturals. -/
theorem tendsto_log_nat : Tendsto (fun d : ℕ => Real.log d) atTop atTop := by
  first
    | exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    | exact Real.tendsto_log_atTop.comp tendsto_nat_cast_atTop_atTop

/-- `(log d)⁻¹ → 0` along the naturals. -/
theorem tendsto_inv_log_nat : Tendsto (fun d : ℕ => (Real.log d)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_nat

/-- `log x / x → 0` as `x → ∞`. -/
theorem tendsto_log_div_self : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  first
    | exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    | (have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero; simpa using h)

/-- `log (log d) / log d → 0` along the naturals. -/
theorem tendsto_loglog_div_log :
    Tendsto (fun d : ℕ => Real.log (Real.log d) / Real.log d) atTop (𝓝 0) :=
  tendsto_log_div_self.comp tendsto_log_nat

/-- Two-sided bounds of the shape of [HL] and [HU] force `a d / log d → 2π`. -/
theorem tendsto_div_log_of_bounds (a : ℕ → ℝ) (C₁ C₂ : ℝ)
    (hlo : ∀ᶠ d : ℕ in atTop, 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C₂ ≤ a d)
    (hhi : ∀ᶠ d : ℕ in atTop, a d ≤ 2 * π * Real.log d + C₁) :
    Tendsto (fun d : ℕ => a d / Real.log d) atTop (𝓝 (2 * π)) := by
  have hpos : ∀ᶠ d : ℕ in atTop, 0 < Real.log d := tendsto_log_nat.eventually_gt_atTop 0
  have hlow : Tendsto (fun d : ℕ => 2 * π - 7 * π * (Real.log (Real.log d) / Real.log d) -
      C₂ * (Real.log d)⁻¹) atTop (𝓝 (2 * π)) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * π) atTop (𝓝 (2 * π))).sub
      (tendsto_loglog_div_log.const_mul (7 * π))).sub (tendsto_inv_log_nat.const_mul C₂)
    have h0 : (2 * π - 7 * π * 0 - C₂ * 0 : ℝ) = 2 * π := by ring
    rw [h0] at h
    exact h
  have hup : Tendsto (fun d : ℕ => 2 * π + C₁ * (Real.log d)⁻¹) atTop (𝓝 (2 * π)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * π) atTop (𝓝 (2 * π))).add
      (tendsto_inv_log_nat.const_mul C₁)
    have h0 : (2 * π + C₁ * 0 : ℝ) = 2 * π := by ring
    rw [h0] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [hlo, hpos] with d h1 h2
    have hne : Real.log d ≠ 0 := h2.ne'
    have e1 : Real.log (Real.log d) / Real.log d * Real.log d = Real.log (Real.log d) := by
      first
        | exact div_mul_cancel₀ _ hne
        | field_simp
    have e2 : (Real.log d)⁻¹ * Real.log d = 1 := by
      first
        | exact inv_mul_cancel₀ hne
        | field_simp
    have e : (2 * π - 7 * π * (Real.log (Real.log d) / Real.log d) - C₂ * (Real.log d)⁻¹) *
        Real.log d = 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C₂ := by
      linear_combination (-7 * π) * e1 - C₂ * e2
    have key : 2 * π - 7 * π * (Real.log (Real.log d) / Real.log d) - C₂ * (Real.log d)⁻¹ ≤
        a d / Real.log d := by
      first
        | (rw [le_div_iff₀ h2, e]; exact h1)
        | (rw [le_div_iff h2, e]; exact h1)
    exact key
  · filter_upwards [hhi, hpos] with d h1 h2
    have hne : Real.log d ≠ 0 := h2.ne'
    have e2 : (Real.log d)⁻¹ * Real.log d = 1 := by
      first
        | exact inv_mul_cancel₀ hne
        | field_simp
    have e : (2 * π + C₁ * (Real.log d)⁻¹) * Real.log d = 2 * π * Real.log d + C₁ := by
      linear_combination C₁ * e2
    have key : a d / Real.log d ≤ 2 * π + C₁ * (Real.log d)⁻¹ := by
      first
        | (rw [div_le_iff₀ h2, e]; exact h1)
        | (rw [div_le_iff h2, e]; exact h1)
    exact key

/-- **F2.** Relative optimality from the named bounds [HU] (`hU`) and [HL] (`hL`): eventually
`0 ≤ A d − a d ≤ 7π log (log d) + C₁ + C₂`, and `A d / a d → 1`. -/
theorem relative_optimality (A a : ℕ → ℝ) (C₁ C₂ : ℝ)
    (hle : ∀ᶠ d : ℕ in atTop, a d ≤ A d)
    (hU : ∀ᶠ d : ℕ in atTop, A d ≤ 2 * π * Real.log d + C₁)
    (hL : ∀ᶠ d : ℕ in atTop, 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C₂ ≤ a d) :
    (∀ᶠ d : ℕ in atTop, 0 ≤ A d - a d ∧ A d - a d ≤ 7 * π * Real.log (Real.log d) + C₁ + C₂) ∧
      Tendsto (fun d : ℕ => A d / a d) atTop (𝓝 1) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hle, hU, hL] with d h1 h2 h3
    exact ⟨by linarith, by linarith⟩
  · have hA : Tendsto (fun d : ℕ => A d / Real.log d) atTop (𝓝 (2 * π)) :=
      tendsto_div_log_of_bounds A C₁ C₂ (by filter_upwards [hle, hL] with d h1 h3; linarith) hU
    have ha : Tendsto (fun d : ℕ => a d / Real.log d) atTop (𝓝 (2 * π)) :=
      tendsto_div_log_of_bounds a C₁ C₂ hL (by filter_upwards [hle, hU] with d h1 h2; linarith)
    have hne : (2 * π : ℝ) ≠ 0 := by
      first
        | positivity
        | exact Real.two_pi_pos.ne'
    have hq := hA.div ha hne
    rw [div_self hne] at hq
    refine hq.congr' ?_
    filter_upwards [tendsto_log_nat.eventually_gt_atTop 0] with d hd
    have hL0 : Real.log d ≠ 0 := hd.ne'
    show A d / Real.log d / (a d / Real.log d) = A d / a d
    first
      | rw [div_div_eq_mul_div, div_mul_cancel₀ (A d) hL0]
      | exact div_div_div_cancel_right₀ hL0 (A d) (a d)
      | exact div_div_div_cancel_right (A d) hL0

end BLT

end
