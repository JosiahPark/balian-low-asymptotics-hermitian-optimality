import BLTAudit.LimitConstant

/-!
# F2. Relative optimality from two named bounds (§5)

§5 of the paper combines the trial bound `[HU]` (`A_d ≤ 2π log d + C₁`, from (U4) and (U14)) with
the lower bound `[HL]` (`a_d ≥ 2π log d − 7π log log d − C₂`, from (L19)). For any real sequences
with `a_d ≤ A_d` and these two bounds:

* `gap_bound`: eventually `0 ≤ A_d − a_d ≤ 7π log log d + C₁ + C₂`;
* `relative_optimality`: `A_d / a_d → 1`.

What this file does NOT prove: `[HU]` or `[HL]`; they are hypotheses. With `A_d = A_d(f_d)` and
`a_d` the minimum, the conclusion is the last display of Theorem 1.1, conditional on them.
-/

noncomputable section

open Filter Topology Real

namespace BLT

/-- **F2.** The optimality gap is `O(log log d)`. -/
theorem gap_bound (A a : ℕ → ℝ) (C₁ C₂ : ℝ)
    (hle : ∀ᶠ d : ℕ in atTop, a d ≤ A d)
    (hHU : ∀ᶠ d : ℕ in atTop, A d ≤ 2 * π * Real.log d + C₁)
    (hHL : ∀ᶠ d : ℕ in atTop, 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C₂ ≤ a d) :
    ∀ᶠ d : ℕ in atTop, 0 ≤ A d - a d ∧ A d - a d ≤ 7 * π * Real.log (Real.log d) + C₁ + C₂ := by
  filter_upwards [hle, hHU, hHL] with d h1 h2 h3
  constructor <;> linarith

/-- **F2.** Relative optimality: `A_d / a_d → 1`. -/
theorem relative_optimality (A a : ℕ → ℝ) (C₁ C₂ : ℝ)
    (hle : ∀ᶠ d : ℕ in atTop, a d ≤ A d)
    (hHU : ∀ᶠ d : ℕ in atTop, A d ≤ 2 * π * Real.log d + C₁)
    (hHL : ∀ᶠ d : ℕ in atTop, 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C₂ ≤ a d) :
    Tendsto (fun d : ℕ => A d / a d) atTop (𝓝 1) := by
  set C := max C₁ C₂
  have hA : Tendsto (fun d : ℕ => A d / Real.log d) atTop (𝓝 (2 * π)) := by
    refine limit_constant A C ?_
    filter_upwards [hle, hHU, hHL] with d h1 h2 h3
    constructor
    · have : C₂ ≤ C := le_max_right _ _
      linarith
    · have : C₁ ≤ C := le_max_left _ _
      linarith
  have ha : Tendsto (fun d : ℕ => a d / Real.log d) atTop (𝓝 (2 * π)) := by
    refine limit_constant a C ?_
    filter_upwards [hle, hHU, hHL] with d h1 h2 h3
    constructor
    · have : C₂ ≤ C := le_max_right _ _
      linarith
    · have : C₁ ≤ C := le_max_left _ _
      linarith
  have hpi : (2 * π : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hdiv := hA.div ha hpi
  rw [div_self hpi] at hdiv
  have hN : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ d : ℕ in atTop, 0 < Real.log d :=
    (Real.tendsto_log_atTop.comp hN).eventually_gt_atTop 0
  refine hdiv.congr' ?_
  filter_upwards [hpos] with d hl
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hl.ne']

end BLT

end
