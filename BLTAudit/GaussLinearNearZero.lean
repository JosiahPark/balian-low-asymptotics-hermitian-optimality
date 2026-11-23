import BLTAudit.ZakDerivNonzero
import BLTAudit.ZakZero

/-!
# H6. Linear lower bound for the Gaussian Zak transform near its zero

Write `θ z = jacobiTheta₂ z i` and `z₀ = 1/2 − (1/2) i`, so that `gaussZak x y = gauss x · θ (y − x i)`
(C1) and `(x, y) = (1/2, 1/2)` corresponds to `z = z₀`. Proved here:

* `thetaI_zakZeroPt`: `θ z₀ = 0` (from C3);
* `thetaI'_zakZeroPt_ne_zero`: `θ' z₀ ≠ 0` (from C5);
* `thetaI_ge_linear_near_zero`: there are `ρ > 0` and `c > 0` with `c ‖z − z₀‖ ≤ ‖θ z‖` for
  `‖z − z₀‖ < ρ` (the derivative at `z₀`, `hasDerivAt_jacobiTheta₂_fst`, through `=o`);
* `gaussZak_ge_linear_near_zero`: there are `ρ > 0` and `c > 0` with
  `c ‖(y − x i) − z₀‖ ≤ ‖gaussZak x y‖` whenever `‖(y − x i) − z₀‖ < ρ`;
* `norm_sub_zakZeroPt_sq`: `‖(y − x i) − z₀‖² = (x − 1/2)² + (y − 1/2)²`, so the bound is
  `c · dist ((x, y), (1/2, 1/2)) ≤ |F(x, y)|` near the zero, the local half of §3.1's `|F(z)| ≥ c|z − z₀|`.

What this file does NOT prove: the global half on the whole square (H7, which needs the uniqueness
of the zero, [HZ]), nor anything about `d`, the grid, [HV] or Theorem 1.1.
-/

noncomputable section

open scoped Real
open Filter Topology Asymptotics

namespace BLT

/-- `z₀ = 1/2 − (1/2) i`, the point `(x, y) = (1/2, 1/2)` in the variable `y − x i`. -/
def zakZeroPt : ℂ := ((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I

/-- `θ z = jacobiTheta₂ z i`. -/
def thetaI (z : ℂ) : ℂ := jacobiTheta₂ z Complex.I

theorem gaussZak_eq_gauss_mul_thetaI (x y : ℝ) :
    gaussZak x y = ((gauss x : ℝ) : ℂ) * thetaI ((y : ℂ) - (x : ℂ) * Complex.I) :=
  gaussZak_eq_gauss_mul_theta x y

/-- **H6.** `θ z₀ = 0`. -/
theorem thetaI_zakZeroPt : thetaI zakZeroPt = 0 := by
  have h := gaussZak_half_half
  rw [gaussZak_eq_gauss_mul_thetaI] at h
  have hg : ((gauss (1 / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (gauss_pos (1 / 2)).ne'
  have h' : thetaI (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) = 0 :=
    (mul_eq_zero.mp h).resolve_left hg
  exact h'

/-- **H6.** `θ' z₀ ≠ 0`. -/
theorem thetaI'_zakZeroPt_ne_zero : jacobiTheta₂' zakZeroPt Complex.I ≠ 0 := by
  intro h
  apply zakA0_ne_zero
  unfold zakA0
  have h' : jacobiTheta₂' (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I = 0 := h
  rw [h', zero_mul, mul_zero]

theorem hasDerivAt_thetaI (z : ℂ) : HasDerivAt thetaI (jacobiTheta₂' z Complex.I) z :=
  hasDerivAt_jacobiTheta₂_fst z im_I_pos

/-- **H6.** Near `z₀`, `‖θ z‖ ≥ (‖θ' z₀‖ / 2) ‖z − z₀‖`. -/
theorem thetaI_ge_linear_near_zero :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, ‖z - zakZeroPt‖ < ρ →
      ‖jacobiTheta₂' zakZeroPt Complex.I‖ / 2 * ‖z - zakZeroPt‖ ≤ ‖thetaI z‖ := by
  set A := jacobiTheta₂' zakZeroPt Complex.I with hA
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr thetaI'_zakZeroPt_ne_zero
  have ho := hasDerivAt_iff_isLittleO.mp (hasDerivAt_thetaI zakZeroPt)
  have hev := ho.def (half_pos hApos)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  have hd : dist z zakZeroPt < ρ := by rwa [dist_eq_norm]
  have h1 := hball hd
  beta_reduce at h1
  rw [thetaI_zakZeroPt, sub_zero, smul_eq_mul] at h1
  have h2 : ‖(z - zakZeroPt) * A‖ - ‖thetaI z‖ ≤ ‖thetaI z - (z - zakZeroPt) * A‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le _ _
  rw [norm_mul] at h2
  have h3 : ‖A‖ * ‖z - zakZeroPt‖ - ‖thetaI z‖ ≤ ‖A‖ / 2 * ‖z - zakZeroPt‖ := by
    linarith [h2, h1]
  linarith

/-- `gauss x ≥ 2^{1/4} e^{−4π}` for `|x| ≤ 2`. -/
theorem gauss_ge_of_abs_le {x : ℝ} (hx : |x| ≤ 2) :
    (2 : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-(4 * Real.pi)) ≤ gauss x := by
  unfold gauss
  have hx2 : x ^ 2 ≤ 4 := by
    have := abs_le.mp hx
    nlinarith [this.1, this.2]
  have h : -(4 * Real.pi) ≤ -Real.pi * x ^ 2 := by nlinarith [Real.pi_pos]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) hpos.le

/-- **H6.** The local linear lower bound `c ‖(y − x i) − z₀‖ ≤ ‖gaussZak x y‖`. -/
theorem gaussZak_ge_linear_near_zero :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧ ∀ x y : ℝ,
      ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖ < ρ →
        c * ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖ ≤ ‖gaussZak x y‖ := by
  obtain ⟨ρ, hρ, hθ⟩ := thetaI_ge_linear_near_zero
  have hApos : 0 < ‖jacobiTheta₂' zakZeroPt Complex.I‖ :=
    norm_pos_iff.mpr thetaI'_zakZeroPt_ne_zero
  set g₀ : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-(4 * Real.pi)) with hg₀
  have hg₀pos : 0 < g₀ := by positivity
  refine ⟨min ρ 1, lt_min hρ one_pos, g₀ * (‖jacobiTheta₂' zakZeroPt Complex.I‖ / 2),
    mul_pos hg₀pos (half_pos hApos), fun x y hz => ?_⟩
  set z : ℂ := (y : ℂ) - (x : ℂ) * Complex.I with hzdef
  have hzρ : ‖z - zakZeroPt‖ < ρ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz1 : ‖z - zakZeroPt‖ < 1 := lt_of_lt_of_le hz (min_le_right _ _)
  have him : (z - zakZeroPt).im = -(x - 1 / 2) := by
    simp only [hzdef, zakZeroPt, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hxabs : |x| ≤ 2 := by
    have h1 : |(z - zakZeroPt).im| ≤ ‖z - zakZeroPt‖ := Complex.abs_im_le_norm _
    rw [him, abs_neg] at h1
    have h2 := abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hz1))
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2]
  have hg : g₀ ≤ gauss x := gauss_ge_of_abs_le hxabs
  have hθz := hθ z hzρ
  rw [gaussZak_eq_gauss_mul_thetaI, norm_mul, Complex.norm_of_nonneg (gauss_pos x).le]
  calc g₀ * (‖jacobiTheta₂' zakZeroPt Complex.I‖ / 2) * ‖z - zakZeroPt‖
      = g₀ * (‖jacobiTheta₂' zakZeroPt Complex.I‖ / 2 * ‖z - zakZeroPt‖) := by ring
    _ ≤ gauss x * ‖thetaI z‖ := by
      exact mul_le_mul hg hθz (by positivity) (gauss_pos x).le

/-- `‖(y − x i) − z₀‖² = (x − 1/2)² + (y − 1/2)²`. -/
theorem norm_sub_zakZeroPt_sq (x y : ℝ) :
    ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖ ^ 2 = (x - 1 / 2) ^ 2 + (y - 1 / 2) ^ 2 := by
  have hre : (((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt).re = y - 1 / 2 := by
    simp only [zakZeroPt, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : (((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt).im = -(x - 1 / 2) := by
    simp only [zakZeroPt, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  ring

end BLT

end
