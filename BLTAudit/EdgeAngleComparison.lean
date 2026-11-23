import BLTAudit.Basic
import BLTAudit.GoodPlaquette

/-!
# G1. Edge-angle comparison, the inequality behind (L10) (§4.2)

Paper §4.2, just before (L10): for a good edge (one with `|a_e| < η_d`),
`a_e² ≤ (1 + C η_d²) · 4 sin²(a_e / 2)`. Proved here for real numbers, with the constant `C = 1`:

* `edge_angle_sq_le`: for real `a η` with `|a| ≤ η` and `η ≤ 1`,
  `a ^ 2 ≤ (1 + η ^ 2) * (4 * Real.sin (a / 2) ^ 2)`;
* `sum_edge_angle_sq_le`: for a finset `s` and `a : ι → ℝ` with `|a e| ≤ η` on `s` and `η ≤ 1`,
  `∑ e ∈ s, a e ^ 2 ≤ (1 + η ^ 2) * ∑ e ∈ s, 4 * Real.sin (a e / 2) ^ 2`;
* `weighted_edge_angle_sq_le`: the same with weights `0 ≤ w e ≤ 1` on the left,
  `∑ e ∈ s, w e * a e ^ 2 ≤ (1 + η ^ 2) * ∑ e ∈ s, 4 * Real.sin (a e / 2) ^ 2` (the paper integrates
  the weight `W` of (L8), which counts each edge with a coefficient at most `1`);
* `edge_angle_sq_le_self`: the case `η = |a|`, `a ^ 2 ≤ (1 + a ^ 2) * (4 * Real.sin (a / 2) ^ 2)`
  for `|a| ≤ 1`.

Helpers: `cos_le_quartic` (`cos a ≤ 1 − a²/2 + (5/96) a⁴` for `|a| ≤ 1`, from Mathlib's
`Real.cos_bound`) and `sq_sub_quartic_le_four_sin_half_sq` (`a² − (5/48) a⁴ ≤ 4 sin²(a/2)` for
`|a| ≤ 1`, with `four_sin_half_sq` of B4). The hypothesis `η ≤ 1` stands in for the paper's
`η_d = 1 / log d → 0`; the roadmap item's statement is proved as written.

What this file does NOT prove: (L10) itself (which edges are good, the integral of `W` over the good
squares, the count of each edge at most twice with coefficient `1/2`), (L9), the identification of
`∑ 4 sin²(a_e/2)` with `zakEnergy`, or any part of the ball-growth argument (L12)–(L19). It proves
nothing toward [HL], [HU], Theorem 4.1 or Theorem 1.1; F4 and H3 keep [HL] as a named hypothesis.
-/

noncomputable section

open Finset

namespace BLT

/-- One side of Mathlib's `Real.cos_bound`: `cos a ≤ 1 − a²/2 + (5/96) a⁴` for `|a| ≤ 1`. -/
theorem cos_le_quartic {a : ℝ} (ha : |a| ≤ 1) :
    Real.cos a ≤ 1 - a ^ 2 / 2 + a ^ 4 * (5 / 96) := by
  have hb := Real.cos_bound ha
  have h4 : |a| ^ 4 = a ^ 4 := by
    calc |a| ^ 4 = (|a| ^ 2) ^ 2 := by ring
      _ = (a ^ 2) ^ 2 := by rw [sq_abs]
      _ = a ^ 4 := by ring
  have hup := (abs_le.mp hb).2
  first
    | linarith [hup, h4]
    | (rw [h4] at hup; linarith)
    | nlinarith [hup, h4]

/-- The edge weight from below: `a² − (5/48) a⁴ ≤ 4 sin²(a/2)` for `|a| ≤ 1`. -/
theorem sq_sub_quartic_le_four_sin_half_sq {a : ℝ} (ha : |a| ≤ 1) :
    a ^ 2 - a ^ 4 * (5 / 48) ≤ 4 * Real.sin (a / 2) ^ 2 := by
  have hc := cos_le_quartic ha
  have hs := four_sin_half_sq a
  linarith

/-- **G1, edge-angle comparison (the inequality before (L10)).** For `|a| ≤ η ≤ 1`,
`a² ≤ (1 + η²) · 4 sin²(a/2)`: the paper's bound with `C = 1`. -/
theorem edge_angle_sq_le {a η : ℝ} (ha : |a| ≤ η) (hη : η ≤ 1) :
    a ^ 2 ≤ (1 + η ^ 2) * (4 * Real.sin (a / 2) ^ 2) := by
  have hη0 : 0 ≤ η := le_trans (abs_nonneg a) ha
  have ha1 : |a| ≤ 1 := le_trans ha hη
  have hsin := sq_sub_quartic_le_four_sin_half_sq ha1
  have hx0 : 0 ≤ a ^ 2 := sq_nonneg a
  have ha2 : a ^ 2 ≤ η ^ 2 := by
    first
      | exact sq_le_sq' (abs_le.mp ha).1 (abs_le.mp ha).2
      | nlinarith [abs_nonneg a, sq_abs a, ha]
  have hη2 : η ^ 2 ≤ 1 := by
    first
      | nlinarith [hη0, hη]
      | exact pow_le_one₀ hη0 hη
  have hy0 : 0 ≤ η ^ 2 * a ^ 2 := mul_nonneg (sq_nonneg η) hx0
  have h1 : a ^ 2 * a ^ 2 ≤ η ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_right ha2 hx0
  have h2 : η ^ 2 * (a ^ 2 * a ^ 2) ≤ 1 * (a ^ 2 * a ^ 2) :=
    mul_le_mul_of_nonneg_right hη2 (mul_nonneg hx0 hx0)
  have key : a ^ 2 ≤ (1 + η ^ 2) * (a ^ 2 - a ^ 4 * (5 / 48)) := by
    have e : a ^ 4 = a ^ 2 * a ^ 2 := by ring
    rw [e]
    first
      | nlinarith [h1, h2, hy0]
      | linarith [h1, h2, hy0]
  have h1η : 0 ≤ 1 + η ^ 2 := by positivity
  calc a ^ 2 ≤ (1 + η ^ 2) * (a ^ 2 - a ^ 4 * (5 / 48)) := key
    _ ≤ (1 + η ^ 2) * (4 * Real.sin (a / 2) ^ 2) := mul_le_mul_of_nonneg_left hsin h1η

/-- The case `η = |a|`: `a² ≤ (1 + a²) · 4 sin²(a/2)` for `|a| ≤ 1`. -/
theorem edge_angle_sq_le_self {a : ℝ} (ha : |a| ≤ 1) :
    a ^ 2 ≤ (1 + a ^ 2) * (4 * Real.sin (a / 2) ^ 2) := by
  have h := edge_angle_sq_le (le_refl (|a|)) ha
  first
    | (rw [sq_abs] at h; exact h)
    | simpa [sq_abs] using h

/-- **G1, summed form.** If `|a e| ≤ η ≤ 1` on `s`, then
`∑ a_e² ≤ (1 + η²) ∑ 4 sin²(a_e/2)`. -/
theorem sum_edge_angle_sq_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) {η : ℝ}
    (ha : ∀ e ∈ s, |a e| ≤ η) (hη : η ≤ 1) :
    ∑ e ∈ s, a e ^ 2 ≤ (1 + η ^ 2) * ∑ e ∈ s, 4 * Real.sin (a e / 2) ^ 2 := by
  have h : ∑ e ∈ s, a e ^ 2 ≤ ∑ e ∈ s, (1 + η ^ 2) * (4 * Real.sin (a e / 2) ^ 2) :=
    Finset.sum_le_sum fun e he => edge_angle_sq_le (ha e he) hη
  first
    | (rw [Finset.mul_sum]; exact h)
    | simpa [Finset.mul_sum] using h

/-- **G1, weighted form.** If `|a e| ≤ η ≤ 1` and `0 ≤ w e ≤ 1` on `s`, then
`∑ w_e a_e² ≤ (1 + η²) ∑ 4 sin²(a_e/2)`. -/
theorem weighted_edge_angle_sq_le {ι : Type*} (s : Finset ι) (a w : ι → ℝ) {η : ℝ}
    (ha : ∀ e ∈ s, |a e| ≤ η) (hη : η ≤ 1) (hw : ∀ e ∈ s, 0 ≤ w e ∧ w e ≤ 1) :
    ∑ e ∈ s, w e * a e ^ 2 ≤ (1 + η ^ 2) * ∑ e ∈ s, 4 * Real.sin (a e / 2) ^ 2 := by
  have h : ∑ e ∈ s, w e * a e ^ 2 ≤ ∑ e ∈ s, (1 + η ^ 2) * (4 * Real.sin (a e / 2) ^ 2) := by
    apply Finset.sum_le_sum
    intro e he
    have h1 := edge_angle_sq_le (ha e he) hη
    have hP : 0 ≤ (1 + η ^ 2) * (4 * Real.sin (a e / 2) ^ 2) := by positivity
    calc w e * a e ^ 2 ≤ w e * ((1 + η ^ 2) * (4 * Real.sin (a e / 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (hw e he).1
      _ ≤ 1 * ((1 + η ^ 2) * (4 * Real.sin (a e / 2) ^ 2)) :=
          mul_le_mul_of_nonneg_right (hw e he).2 hP
      _ = (1 + η ^ 2) * (4 * Real.sin (a e / 2) ^ 2) := one_mul _
  first
    | (rw [Finset.mul_sum]; exact h)
    | simpa [Finset.mul_sum] using h

end BLT

end
