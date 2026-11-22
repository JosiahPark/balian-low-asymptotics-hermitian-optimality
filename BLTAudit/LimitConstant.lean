import BLTAudit.RelativeOptimality

/-!
# F3. The limit constant from the same two bounds (§5)

Real sequences only. For `a : ℕ → ℝ` (in the paper `a d = a_d`), if for all large `d`
`2π log d − 7π log (log d) − C ≤ a d ≤ 2π log d + C` (the shapes of the named hypotheses [HL] and
[HU] together, with one constant `C`), then `a d / log d → 2π`.

* `limit_constant`: the statement of F3, from `tendsto_div_log_of_bounds` of
  `BLTAudit/RelativeOptimality.lean` (F2) with `C₁ = C₂ = C`;
* `limit_constant_of_bounds`: the same with the two bounds given as separate hypotheses.

What this file does NOT prove: either bound (they are hypotheses; in the paper they are [HU], the
trial bound (U4) with (U14), and [HL], the lower bound (L19) of Theorem 4.1), any link between `a` and
`aMin` of F1 (that is F4), or Theorem 1.1. It proves a statement FROM the two named hypotheses only.
-/

noncomputable section

open Filter Topology
open scoped Real

namespace BLT

/-- **F3**, with the two bounds as separate hypotheses. -/
theorem limit_constant_of_bounds (a : ℕ → ℝ) (C : ℝ)
    (hlo : ∀ᶠ d : ℕ in atTop, 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C ≤ a d)
    (hhi : ∀ᶠ d : ℕ in atTop, a d ≤ 2 * π * Real.log d + C) :
    Tendsto (fun d : ℕ => a d / Real.log d) atTop (𝓝 (2 * π)) :=
  tendsto_div_log_of_bounds a C C hlo hhi

/-- **F3.** The limit constant: if eventually
`2π log d − 7π log (log d) − C ≤ a d ≤ 2π log d + C`, then `a d / log d → 2π`. -/
theorem limit_constant (a : ℕ → ℝ) (C : ℝ)
    (h : ∀ᶠ d : ℕ in atTop, 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C ≤ a d ∧
      a d ≤ 2 * π * Real.log d + C) :
    Tendsto (fun d : ℕ => a d / Real.log d) atTop (𝓝 (2 * π)) :=
  limit_constant_of_bounds a C (h.mono fun _ hd => hd.1) (h.mono fun _ hd => hd.2)

end BLT

end
