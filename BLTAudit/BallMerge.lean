import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# E4. Merging two balls (§4.3)

The ball-growth argument of §4.3 replaces two intersecting balls `B(c₁, r₁)`, `B(c₂, r₂)` by one ball
of radius exactly `r₁ + r₂`, centred on the segment `[c₁, c₂]` at
`c = c₁ + (r₂ / (r₁ + r₂)) • (c₂ − c₁)`. In any real normed space:

* `norm_mergeCenter_sub_left`, `norm_mergeCenter_sub_right`: `‖c − c₁‖ ≤ r₂` and `‖c − c₂‖ ≤ r₁`;
* `ball_union_subset_mergeBall`: `B(c₁, r₁) ∪ B(c₂, r₂) ⊆ B(c, r₁ + r₂)`;
* `margin_mergeBall_left`, `margin_mergeBall_right`: inward margins do not decrease,
  `r₁ − ‖x − c₁‖ ≤ (r₁ + r₂) − ‖x − c‖` (and the same for the second ball). This is the invariant
  `r − |x − c| ≥ 10` of §4.3 under one merge.

What this file does NOT prove: the ball-growth construction itself, disjointness of swept annuli,
the degree lemma (L12), or the bound (L16); nothing here bears on Theorem 4.1 or Theorem 1.1.
-/

noncomputable section

namespace BLT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The centre of the merged ball. -/
def mergeCenter (c₁ c₂ : E) (r₁ r₂ : ℝ) : E := c₁ + (r₂ / (r₁ + r₂)) • (c₂ - c₁)

theorem norm_mergeCenter_sub_left (c₁ c₂ : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) : ‖mergeCenter c₁ c₂ r₁ r₂ - c₁‖ ≤ r₂ := by
  have hs : 0 < r₁ + r₂ := by linarith
  unfold mergeCenter
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity), norm_sub_rev,
    div_mul_eq_mul_div, div_le_iff₀ hs]
  nlinarith

theorem norm_mergeCenter_sub_right (c₁ c₂ : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) : ‖mergeCenter c₁ c₂ r₁ r₂ - c₂‖ ≤ r₁ := by
  have hs : 0 < r₁ + r₂ := by linarith
  have ht : r₁ / (r₁ + r₂) = 1 - r₂ / (r₁ + r₂) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_self hs.ne']
  have he : mergeCenter c₁ c₂ r₁ r₂ - c₂ = (r₁ / (r₁ + r₂)) • (c₁ - c₂) := by
    unfold mergeCenter
    rw [ht, sub_smul, one_smul, smul_sub, smul_sub]
    abel
  rw [he, norm_smul, Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div, div_le_iff₀ hs]
  nlinarith

/-- **E4.** Inward margins do not decrease under a merge (first ball). -/
theorem margin_mergeBall_left (c₁ c₂ x : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) :
    r₁ - ‖x - c₁‖ ≤ (r₁ + r₂) - ‖x - mergeCenter c₁ c₂ r₁ r₂‖ := by
  have h1 := norm_mergeCenter_sub_left c₁ c₂ h₁ h₂ h
  have h2 := norm_sub_le_norm_sub_add_norm_sub x c₁ (mergeCenter c₁ c₂ r₁ r₂)
  rw [norm_sub_rev c₁] at h2
  linarith

/-- **E4.** Inward margins do not decrease under a merge (second ball). -/
theorem margin_mergeBall_right (c₁ c₂ x : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) :
    r₂ - ‖x - c₂‖ ≤ (r₁ + r₂) - ‖x - mergeCenter c₁ c₂ r₁ r₂‖ := by
  have h1 := norm_mergeCenter_sub_right c₁ c₂ h₁ h₂ h
  have h2 := norm_sub_le_norm_sub_add_norm_sub x c₂ (mergeCenter c₁ c₂ r₁ r₂)
  rw [norm_sub_rev c₂] at h2
  linarith

/-- **E4.** The merged ball contains both balls. -/
theorem ball_union_subset_mergeBall (c₁ c₂ : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) :
    Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂ ⊆ Metric.ball (mergeCenter c₁ c₂ r₁ r₂) (r₁ + r₂) := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm]
  rcases hx with hx | hx
  · rw [Metric.mem_ball, dist_eq_norm] at hx
    have := margin_mergeBall_left c₁ c₂ x h₁ h₂ h
    linarith
  · rw [Metric.mem_ball, dist_eq_norm] at hx
    have := margin_mergeBall_right c₁ c₂ x h₁ h₂ h
    linarith

end BLT

end
