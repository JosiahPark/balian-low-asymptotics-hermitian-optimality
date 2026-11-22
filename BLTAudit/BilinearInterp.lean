import BLTAudit.Basic

/-!
# E3. Bilinear interpolation (L8)–(L10) with zero gauge error

For corner values `t00 t10 t01 t11` (the values of a phase at `(0,0)`, `(1,0)`, `(0,1)`, `(1,1)`) the
bilinear interpolant on `[0,1]²` is
`bilinInterp t00 t10 t01 t11 x y = (1−x)(1−y) t00 + x(1−y) t10 + (1−x)y t01 + xy t11`.
With the edge differences `b_bot = t10 − t00`, `b_top = t11 − t01`, `b_left = t01 − t00`,
`b_right = t11 − t10` ("zero gauge error": the edge angles are the plain differences of the corner
values, with no connection term) and
`bilinW b_bot b_top b_left b_right x y = (1−y) b_bot² + y b_top² + (1−x) b_left² + x b_right²`:

* `bilinInterp_corners`: the interpolant takes the four corner values;
* `hasDerivAt_bilinInterp_x`, `hasDerivAt_bilinInterp_y`: `∂ₓθ = (1−y) b_bot + y b_top` and
  `∂ᵧθ = (1−x) b_left + x b_right`;
* `sq_convex_comb_le`: `((1−t) a + t b)² ≤ (1−t) a² + t b²` for `0 ≤ t ≤ 1`;
* `bilinInterp_grad_le`: `(∂ₓθ)² + (∂ᵧθ)² ≤ W x y` at every point of `[0,1]²`;
* `integral_zero_one_affine`, `integral_bilinW`: `∫ y in 0..1, ∫ x in 0..1, W x y =
  (b_bot² + b_top² + b_left² + b_right²) / 2` (as an iterated interval integral, for any four reals);
* `bilinInterp_energy`: the statement of E3, both facts together.

What this file does NOT prove: the version with a nonzero gauge error (covariant edge angles that
are not differences of corner values), the comparison of `b²` with `4 sin² (b / 2)` of (L10), or any
statement about phases on the twisted torus or Theorem 4.1. It proves nothing toward Theorem 1.1 of
the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

/-- The bilinear interpolant of four corner values on `[0,1]²`. -/
def bilinInterp (t00 t10 t01 t11 x y : ℝ) : ℝ :=
  (1 - x) * (1 - y) * t00 + x * (1 - y) * t10 + (1 - x) * y * t01 + x * y * t11

/-- The edge weight `W x y = (1−y) b_bot² + y b_top² + (1−x) b_left² + x b_right²`. -/
def bilinW (bb bt bl br x y : ℝ) : ℝ :=
  (1 - y) * bb ^ 2 + y * bt ^ 2 + (1 - x) * bl ^ 2 + x * br ^ 2

/-- The interpolant takes the four corner values. -/
theorem bilinInterp_corners (t00 t10 t01 t11 : ℝ) :
    bilinInterp t00 t10 t01 t11 0 0 = t00 ∧ bilinInterp t00 t10 t01 t11 1 0 = t10 ∧
      bilinInterp t00 t10 t01 t11 0 1 = t01 ∧ bilinInterp t00 t10 t01 t11 1 1 = t11 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [bilinInterp] <;> ring

/-- `∂ₓθ = (1−y) b_bot + y b_top`. -/
theorem hasDerivAt_bilinInterp_x (t00 t10 t01 t11 x y : ℝ) :
    HasDerivAt (fun x => bilinInterp t00 t10 t01 t11 x y)
      ((1 - y) * (t10 - t00) + y * (t11 - t01)) x := by
  have e : (fun x => bilinInterp t00 t10 t01 t11 x y) =
      fun x => x * ((1 - y) * (t10 - t00) + y * (t11 - t01)) + ((1 - y) * t00 + y * t01) := by
    funext x
    simp only [bilinInterp]
    ring
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := by
    first
      | exact hasDerivAt_id' x
      | exact hasDerivAt_id x
      | exact hasDerivAt_id'
  have h := (hid.mul_const ((1 - y) * (t10 - t00) + y * (t11 - t01))).add_const
    ((1 - y) * t00 + y * t01)
  rw [e]
  first
    | (rw [one_mul] at h; exact h)
    | simpa using h

/-- `∂ᵧθ = (1−x) b_left + x b_right`, from the `x` case by the symmetry `x ↔ y`, `t10 ↔ t01`. -/
theorem hasDerivAt_bilinInterp_y (t00 t10 t01 t11 x y : ℝ) :
    HasDerivAt (fun y => bilinInterp t00 t10 t01 t11 x y)
      ((1 - x) * (t01 - t00) + x * (t11 - t10)) y := by
  have e : (fun y => bilinInterp t00 t10 t01 t11 x y) =
      fun y => bilinInterp t00 t01 t10 t11 y x := by
    funext y
    simp only [bilinInterp]
    ring
  rw [e]
  exact hasDerivAt_bilinInterp_x t00 t01 t10 t11 y x

/-- Convexity of the square: `((1−t) a + t b)² ≤ (1−t) a² + t b²` for `0 ≤ t ≤ 1`. -/
theorem sq_convex_comb_le (a b t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ((1 - t) * a + t * b) ^ 2 ≤ (1 - t) * a ^ 2 + t * b ^ 2 := by
  have h := mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) (sq_nonneg (a - b))
  nlinarith [h]

/-- **E3, pointwise.** `(∂ₓθ)² + (∂ᵧθ)² ≤ W x y` on `[0,1]²`. -/
theorem bilinInterp_grad_le (t00 t10 t01 t11 x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    deriv (fun x => bilinInterp t00 t10 t01 t11 x y) x ^ 2 +
        deriv (fun y => bilinInterp t00 t10 t01 t11 x y) y ^ 2 ≤
      bilinW (t10 - t00) (t11 - t01) (t01 - t00) (t11 - t10) x y := by
  rw [(hasDerivAt_bilinInterp_x t00 t10 t01 t11 x y).deriv,
    (hasDerivAt_bilinInterp_y t00 t10 t01 t11 x y).deriv]
  have h1 := sq_convex_comb_le (t10 - t00) (t11 - t01) y hy0 hy1
  have h2 := sq_convex_comb_le (t01 - t00) (t11 - t10) x hx0 hx1
  simp only [bilinW]
  linarith

/-- `∫ x in 0..1, (α + β x) = α + β / 2`. -/
theorem integral_zero_one_affine (α β : ℝ) : ∫ x in (0 : ℝ)..1, (α + β * x) = α + β / 2 := by
  have hc : IntervalIntegrable (fun _ : ℝ => α) MeasureTheory.volume 0 1 := by
    first
      | exact continuousOn_const.intervalIntegrable
      | exact intervalIntegrable_const
  have hl : IntervalIntegrable (fun x : ℝ => β * x) MeasureTheory.volume 0 1 := by
    first
      | exact (continuous_const.mul continuous_id).continuousOn.intervalIntegrable
      | exact (continuousOn_const.mul continuousOn_id).intervalIntegrable
  have e1 : ∫ x in (0 : ℝ)..1, (α + β * x) =
      (∫ _ in (0 : ℝ)..1, α) + ∫ x in (0 : ℝ)..1, β * x :=
    intervalIntegral.integral_add hc hl
  have e2 : ∫ _ in (0 : ℝ)..1, α = α := by
    first
      | (rw [intervalIntegral.integral_const, smul_eq_mul]; ring)
      | simp
  have e3 : ∫ x in (0 : ℝ)..1, β * x = β / 2 := by
    first
      | (rw [intervalIntegral.integral_const_mul, integral_id]; ring)
      | (simp; ring)
  rw [e1, e2, e3]

/-- **E3, the integral.** `∫∫ W = (b_bot² + b_top² + b_left² + b_right²) / 2`. -/
theorem integral_bilinW (bb bt bl br : ℝ) :
    ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, bilinW bb bt bl br x y =
      (bb ^ 2 + bt ^ 2 + bl ^ 2 + br ^ 2) / 2 := by
  have inner : ∀ y : ℝ, ∫ x in (0 : ℝ)..1, bilinW bb bt bl br x y =
      ((1 - y) * bb ^ 2 + y * bt ^ 2 + bl ^ 2) + (br ^ 2 - bl ^ 2) / 2 := by
    intro y
    have e : ∫ x in (0 : ℝ)..1, bilinW bb bt bl br x y =
        ∫ x in (0 : ℝ)..1, (((1 - y) * bb ^ 2 + y * bt ^ 2 + bl ^ 2) + (br ^ 2 - bl ^ 2) * x) := by
      first
        | (congr 1; funext x; simp only [bilinW]; ring)
        | exact intervalIntegral.integral_congr fun x _ => by simp only [bilinW]; ring
    rw [e, integral_zero_one_affine]
  have e2 : ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, bilinW bb bt bl br x y =
      ∫ y in (0 : ℝ)..1, ((bl ^ 2 + (br ^ 2 - bl ^ 2) / 2 + bb ^ 2) + (bt ^ 2 - bb ^ 2) * y) := by
    first
      | (congr 1; funext y; rw [inner y]; ring)
      | exact intervalIntegral.integral_congr fun y _ => by simp only [inner y]; ring
  rw [e2, integral_zero_one_affine]
  ring

/-- **E3.** Bilinear interpolation with zero gauge error: the gradient bound on `[0,1]²` and the
value of `∫∫ W`. -/
theorem bilinInterp_energy (t00 t10 t01 t11 : ℝ) :
    (∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
      deriv (fun x => bilinInterp t00 t10 t01 t11 x y) x ^ 2 +
          deriv (fun y => bilinInterp t00 t10 t01 t11 x y) y ^ 2 ≤
        bilinW (t10 - t00) (t11 - t01) (t01 - t00) (t11 - t10) x y) ∧
    ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
        bilinW (t10 - t00) (t11 - t01) (t01 - t00) (t11 - t10) x y =
      ((t10 - t00) ^ 2 + (t11 - t01) ^ 2 + (t01 - t00) ^ 2 + (t11 - t10) ^ 2) / 2 :=
  ⟨fun x y hx0 hx1 hy0 hy1 => bilinInterp_grad_le t00 t10 t01 t11 x y hx0 hx1 hy0 hy1,
    integral_bilinW _ _ _ _⟩

end BLT

end
