import BLTAudit.GaussLinearNearZero
import BLTAudit.ZakGluing
import BLTAudit.Candidates

/-!
# H7. The global linear lower bound `|F(z)| ≥ c |z − z₀|` on the unit square, under [HZ]

With `GaussZeroUnique` ([HZ], the hypothesis that `(1/2, 1/2)` is the only zero of `F = gaussZak` in
`[0,1)²`) as the single input:

* `gaussZak_ne_zero_of_closed`: `F` does not vanish on the closed square `[0,1]²` away from
  `(1/2, 1/2)` (the edges `x = 1`, `y = 1` through the gluing C2);
* `continuous_gaussZak_pair`: `(x, y) ↦ F(x, y)` is continuous (C1 and the theta function);
* `gaussZak_ge_linear`: there is `c > 0` with `c ‖(y − x i) − z₀‖ ≤ ‖F(x, y)‖` on `[0,1]²`
  (H6 inside a disk around `z₀`, a positive minimum on the compact complement).

With `norm_sub_zakZeroPt_sq` of H6 this is `|F(x, y)| ≥ c · dist((x, y), (1/2, 1/2))` on the square,
the estimate of §3.1 from which the grid bound `|F| ≥ c h / √2` of §3.2 follows.

What this file does NOT prove: [HZ] itself (the Jacobi triple product), hence not the unconditional
estimate; nothing about the grid, [HV] or Theorem 1.1.
-/

noncomputable section

open scoped Real
open Set

namespace BLT

theorem gaussZak_ne_zero_of_lt (hz : GaussZeroUnique) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) (hne : ¬ (x = 1 / 2 ∧ y = 1 / 2)) : gaussZak x y ≠ 0 :=
  fun h => hne (hz x y hx0 hx1 hy0 hy1 h)

theorem gaussZak_one_left (y : ℝ) :
    gaussZak 1 y = Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) * gaussZak 0 y := by
  have h := gaussZak_add_one_left 0 y
  rwa [zero_add] at h

theorem gaussZak_one_right (x : ℝ) : gaussZak x 1 = gaussZak x 0 := by
  have h := gaussZak_add_one_right x 0
  rwa [zero_add] at h

/-- **H7.** Under [HZ], `F` has no zero on the closed square other than `(1/2, 1/2)`. -/
theorem gaussZak_ne_zero_of_closed (hz : GaussZeroUnique) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (hne : ¬ (x = 1 / 2 ∧ y = 1 / 2)) : gaussZak x y ≠ 0 := by
  have h0 : (0 : ℝ) ≠ 1 / 2 := by norm_num
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  rcases lt_or_eq_of_le hx.2 with hx1 | hx1 <;> rcases lt_or_eq_of_le hy.2 with hy1 | hy1
  · exact gaussZak_ne_zero_of_lt hz hx.1 hx1 hy.1 hy1 hne
  · rw [hy1, gaussZak_one_right]
    exact gaussZak_ne_zero_of_lt hz hx.1 hx1 le_rfl one_pos fun h => h0 h.2
  · rw [hx1, gaussZak_one_left]
    exact mul_ne_zero hexp
      (gaussZak_ne_zero_of_lt hz le_rfl one_pos hy.1 hy1 fun h => h0 h.1)
  · rw [hx1, hy1, gaussZak_one_left, gaussZak_one_right]
    exact mul_ne_zero (Complex.exp_ne_zero _)
      (gaussZak_ne_zero_of_lt hz le_rfl one_pos le_rfl one_pos fun h => h0 h.1)

theorem continuous_gauss : Continuous gauss := by
  unfold gauss
  fun_prop

theorem continuous_thetaI : Continuous thetaI :=
  continuous_iff_continuousAt.mpr fun z => (hasDerivAt_thetaI z).continuousAt

/-- **H7.** `(x, y) ↦ F(x, y)` is continuous. -/
theorem continuous_gaussZak_pair : Continuous fun p : ℝ × ℝ => gaussZak p.1 p.2 := by
  have h : (fun p : ℝ × ℝ => gaussZak p.1 p.2) = fun p : ℝ × ℝ =>
      ((gauss p.1 : ℝ) : ℂ) * thetaI ((p.2 : ℂ) - (p.1 : ℂ) * Complex.I) := by
    funext p
    exact gaussZak_eq_gauss_mul_thetaI p.1 p.2
  rw [h]
  have h1 : Continuous fun p : ℝ × ℝ => ((gauss p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_gauss.comp continuous_fst)
  have h2 : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) - (p.1 : ℂ) * Complex.I := by fun_prop
  exact h1.mul (continuous_thetaI.comp h2)

/-- The point `(y − x i) − z₀` has norm at most `2` on the closed square. -/
theorem norm_sub_zakZeroPt_le_two {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖ ≤ 2 := by
  have hre : (((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt).re = y - 1 / 2 := by
    simp only [zakZeroPt, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : (((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt).im = -(x - 1 / 2) := by
    simp only [zakZeroPt, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [hre, him, abs_neg]
  have h1 : |y - 1 / 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have h2 : |x - 1 / 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  linarith

/-- **H7.** Under [HZ], `c ‖(y − x i) − z₀‖ ≤ ‖F(x, y)‖` on the closed unit square. -/
theorem gaussZak_ge_linear (hz : GaussZeroUnique) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : ℝ, x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
      c * ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖ ≤ ‖gaussZak x y‖ := by
  obtain ⟨ρ, hρ, c₁, hc₁, hloc⟩ := gaussZak_ge_linear_near_zero
  -- the compact part of the square away from the zero
  have hKc : IsCompact ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩
      {p : ℝ × ℝ | ρ ≤ ‖((p.2 : ℂ) - (p.1 : ℂ) * Complex.I) - zakZeroPt‖}) := by
    refine (isCompact_Icc.prod isCompact_Icc).inter_right ?_
    exact isClosed_le continuous_const (by fun_prop)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖gaussZak p.1 p.2‖)
      ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩
      {p : ℝ × ℝ | ρ ≤ ‖((p.2 : ℂ) - (p.1 : ℂ) * Complex.I) - zakZeroPt‖}) :=
    (continuous_gaussZak_pair.norm).continuousOn
  by_cases hne : ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩
      {p : ℝ × ℝ | ρ ≤ ‖((p.2 : ℂ) - (p.1 : ℂ) * Complex.I) - zakZeroPt‖}).Nonempty
  · obtain ⟨p₀, hp₀K, hmin⟩ := hKc.exists_isMinOn hne hcont
    set m : ℝ := ‖gaussZak p₀.1 p₀.2‖ with hm
    have hp₀sq := hp₀K.1
    have hp₀far : ρ ≤ ‖((p₀.2 : ℂ) - (p₀.1 : ℂ) * Complex.I) - zakZeroPt‖ := hp₀K.2
    have hmpos : 0 < m := by
      rw [hm]
      refine norm_pos_iff.mpr (gaussZak_ne_zero_of_closed hz hp₀sq.1 hp₀sq.2 ?_)
      rintro ⟨h1, h2⟩
      have hz0 : ((p₀.2 : ℂ) - (p₀.1 : ℂ) * Complex.I) - zakZeroPt = 0 := by
        rw [h1, h2]
        unfold zakZeroPt
        first
          | exact sub_self _
          | (push_cast; ring)
      rw [hz0, norm_zero] at hp₀far
      linarith
    refine ⟨min c₁ (m / 2), lt_min hc₁ (half_pos hmpos), fun x y hx hy => ?_⟩
    by_cases hnear : ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖ < ρ
    · calc min c₁ (m / 2) * ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖
          ≤ c₁ * ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖ :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
        _ ≤ ‖gaussZak x y‖ := hloc x y hnear
    · push_neg at hnear
      have hmem : (x, y) ∈ ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩
      {p : ℝ × ℝ | ρ ≤ ‖((p.2 : ℂ) - (p.1 : ℂ) * Complex.I) - zakZeroPt‖}) := ⟨⟨hx, hy⟩, hnear⟩
      have hge : m ≤ ‖gaussZak x y‖ := isMinOn_iff.mp hmin (x, y) hmem
      have hle2 := norm_sub_zakZeroPt_le_two hx hy
      calc min c₁ (m / 2) * ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖
          ≤ m / 2 * ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ ≤ m / 2 * 2 := mul_le_mul_of_nonneg_left hle2 (half_pos hmpos).le
        _ = m := by ring
        _ ≤ ‖gaussZak x y‖ := hge
  · -- every point of the square is within `ρ` of the zero
    refine ⟨c₁, hc₁, fun x y hx hy => ?_⟩
    have hnear : ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖ < ρ := by
      by_contra hcon
      push_neg at hcon
      exact hne ⟨(x, y), ⟨⟨hx, hy⟩, hcon⟩⟩
    exact hloc x y hnear

end BLT

end
