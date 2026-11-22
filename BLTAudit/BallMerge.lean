import BLTAudit.Basic

/-!
# E4. Ball merging (§4.3)

In a real normed space `E`, for `0 < r₁`, `0 < r₂` and `‖c₁ − c₂‖ ≤ r₁ + r₂`, the merged center is
`mergeCenter c₁ c₂ r₁ r₂ = c₁ + (r₂ / (r₁ + r₂)) • (c₂ − c₁)`. Then:

* `norm_mergeCenter_sub_left`: `‖c − c₁‖ ≤ r₂`;
* `norm_mergeCenter_sub_right`: `‖c − c₂‖ ≤ r₁`;
* `norm_sub_le_of_left`: the triangle inequality through a point `p`, `‖x − c‖ ≤ ‖x − p‖ + ‖c − p‖`;
* `ball_union_subset_merge`: `ball c₁ r₁ ∪ ball c₂ r₂ ⊆ ball c (r₁ + r₂)`;
* `merge_margin_left`, `merge_margin_right`: `r₁ − ‖x − c₁‖ ≤ (r₁ + r₂) − ‖x − c‖` and
  `r₂ − ‖x − c₂‖ ≤ (r₁ + r₂) − ‖x − c‖` for every `x`;
* `ball_merge`: the statement of E4: `‖c − c₁‖ ≤ r₂`, `‖c − c₂‖ ≤ r₁`, the inclusion of balls and the
  first margin inequality, together.

What this file does NOT prove: the ball growth construction of §4.3 as a whole (the choice of balls,
their energy bookkeeping, or the radius estimates (L14)–(L18)), or Theorem 4.1. It proves nothing
toward Theorem 1.1 of the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The center of the merged ball, `c₁ + (r₂ / (r₁ + r₂)) • (c₂ − c₁)`. -/
def mergeCenter (c₁ c₂ : E) (r₁ r₂ : ℝ) : E := c₁ + (r₂ / (r₁ + r₂)) • (c₂ - c₁)

/-- `‖c − c₁‖ ≤ r₂`. -/
theorem norm_mergeCenter_sub_left (c₁ c₂ : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) : ‖mergeCenter c₁ c₂ r₁ r₂ - c₁‖ ≤ r₂ := by
  have hs : 0 < r₁ + r₂ := add_pos h₁ h₂
  have ht : 0 ≤ r₂ / (r₁ + r₂) := div_nonneg h₂.le hs.le
  have e : mergeCenter c₁ c₂ r₁ r₂ - c₁ = (r₂ / (r₁ + r₂)) • (c₂ - c₁) := by
    simp only [mergeCenter]
    first
      | abel
      | exact add_sub_cancel_left _ _
  rw [e, norm_smul, Real.norm_of_nonneg ht, norm_sub_rev]
  calc r₂ / (r₁ + r₂) * ‖c₁ - c₂‖ ≤ r₂ / (r₁ + r₂) * (r₁ + r₂) :=
        mul_le_mul_of_nonneg_left h ht
    _ = r₂ := by
        first
          | exact div_mul_cancel₀ r₂ hs.ne'
          | field_simp

/-- `‖c − c₂‖ ≤ r₁`. -/
theorem norm_mergeCenter_sub_right (c₁ c₂ : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) : ‖mergeCenter c₁ c₂ r₁ r₂ - c₂‖ ≤ r₁ := by
  have hs : 0 < r₁ + r₂ := add_pos h₁ h₂
  have hne : r₁ + r₂ ≠ 0 := hs.ne'
  have ht : 0 ≤ r₁ / (r₁ + r₂) := div_nonneg h₁.le hs.le
  have hsplit : r₁ / (r₁ + r₂) = 1 - r₂ / (r₁ + r₂) := by
    first
      | (rw [eq_sub_iff_add_eq, div_add_div_same, div_self hne]; done)
      | (field_simp; ring)
      | field_simp
  have e : mergeCenter c₁ c₂ r₁ r₂ - c₂ = (r₁ / (r₁ + r₂)) • (c₁ - c₂) := by
    simp only [mergeCenter]
    rw [hsplit, sub_smul, one_smul, smul_sub, smul_sub]
    abel
  rw [e, norm_smul, Real.norm_of_nonneg ht]
  calc r₁ / (r₁ + r₂) * ‖c₁ - c₂‖ ≤ r₁ / (r₁ + r₂) * (r₁ + r₂) :=
        mul_le_mul_of_nonneg_left h ht
    _ = r₁ := by
        first
          | exact div_mul_cancel₀ r₁ hne
          | field_simp

/-- Triangle inequality through a point `p`: `‖x − c‖ ≤ ‖x − p‖ + ‖c − p‖`. -/
theorem norm_sub_le_of_left (x p c : E) : ‖x - c‖ ≤ ‖x - p‖ + ‖c - p‖ := by
  have tri : ‖x - c‖ ≤ ‖x - p‖ + ‖p - c‖ := by
    first
      | exact norm_sub_le_norm_sub_add_norm_sub x p c
      | (have h := norm_add_le (x - p) (p - c); rwa [sub_add_sub_cancel] at h)
  rw [norm_sub_rev p c] at tri
  exact tri

/-- `r₁ − ‖x − c₁‖ ≤ (r₁ + r₂) − ‖x − c‖`. -/
theorem merge_margin_left (c₁ c₂ x : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) :
    r₁ - ‖x - c₁‖ ≤ (r₁ + r₂) - ‖x - mergeCenter c₁ c₂ r₁ r₂‖ := by
  have h1 := norm_mergeCenter_sub_left c₁ c₂ h₁ h₂ h
  have h2 := norm_sub_le_of_left x c₁ (mergeCenter c₁ c₂ r₁ r₂)
  linarith

/-- `r₂ − ‖x − c₂‖ ≤ (r₁ + r₂) − ‖x − c‖`. -/
theorem merge_margin_right (c₁ c₂ x : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) :
    r₂ - ‖x - c₂‖ ≤ (r₁ + r₂) - ‖x - mergeCenter c₁ c₂ r₁ r₂‖ := by
  have h1 := norm_mergeCenter_sub_right c₁ c₂ h₁ h₂ h
  have h2 := norm_sub_le_of_left x c₂ (mergeCenter c₁ c₂ r₁ r₂)
  linarith

/-- `ball c₁ r₁ ∪ ball c₂ r₂ ⊆ ball c (r₁ + r₂)`. -/
theorem ball_union_subset_merge (c₁ c₂ : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) :
    Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂ ⊆ Metric.ball (mergeCenter c₁ c₂ r₁ r₂) (r₁ + r₂) := by
  have key : ∀ (y c : E) (r : ℝ), y ∈ Metric.ball c r ↔ ‖y - c‖ < r := by
    intro y c r
    first
      | exact mem_ball_iff_norm
      | rw [Metric.mem_ball, dist_eq_norm]
  intro x hx
  rw [key]
  rcases hx with hx | hx
  · rw [key] at hx
    have := merge_margin_left c₁ c₂ x h₁ h₂ h
    linarith
  · rw [key] at hx
    have := merge_margin_right c₁ c₂ x h₁ h₂ h
    linarith

/-- **E4.** Ball merging: with `c = c₁ + (r₂ / (r₁ + r₂)) • (c₂ − c₁)`, `‖c − c₁‖ ≤ r₂`,
`‖c − c₂‖ ≤ r₁`, `ball c₁ r₁ ∪ ball c₂ r₂ ⊆ ball c (r₁ + r₂)`, and
`r₁ − ‖x − c₁‖ ≤ (r₁ + r₂) − ‖x − c‖` for all `x`. -/
theorem ball_merge (c₁ c₂ : E) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : ‖c₁ - c₂‖ ≤ r₁ + r₂) :
    ‖mergeCenter c₁ c₂ r₁ r₂ - c₁‖ ≤ r₂ ∧ ‖mergeCenter c₁ c₂ r₁ r₂ - c₂‖ ≤ r₁ ∧
      Metric.ball c₁ r₁ ∪ Metric.ball c₂ r₂ ⊆ Metric.ball (mergeCenter c₁ c₂ r₁ r₂) (r₁ + r₂) ∧
      ∀ x : E, r₁ - ‖x - c₁‖ ≤ (r₁ + r₂) - ‖x - mergeCenter c₁ c₂ r₁ r₂‖ :=
  ⟨norm_mergeCenter_sub_left c₁ c₂ h₁ h₂ h, norm_mergeCenter_sub_right c₁ c₂ h₁ h₂ h,
    ball_union_subset_merge c₁ c₂ h₁ h₂ h, fun x => merge_margin_left c₁ c₂ x h₁ h₂ h⟩

end BLT

end
