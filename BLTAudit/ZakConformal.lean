import BLTAudit.Basic
import BLTAudit.ZakTheta
import BLTAudit.ZakZero

/-!
# C4. Conformality of the Gaussian Zak transform at its zero, (A10) (§3.1, Appendix A.3)

For `gaussZak x y = ∑' r : ℤ, gauss (x - r) * exp (2πi r y)` of `BLTAudit/Basic.lean`, this file
proves the two statements of roadmap item C4.

* `exp_mul_gaussZak`: `e^{πx²} * gaussZak x y = 2^{1/4} * jacobiTheta₂ (y - x * I) I` (from C1), and
  `exp_mul_gaussZak_holomorphic`: there is an entire `Θ : ℂ → ℂ` with
  `e^{πx²} * gaussZak x y = Θ (y - x * I)` for all real `x y`.
* `deriv_gaussZak_snd_zero`: `∂_y gaussZak = I * ∂_x gaussZak` at `(1/2, 1/2)`, the two sides being
  `deriv (fun t : ℝ => gaussZak (1/2) t) (1/2)` and `deriv (fun s : ℝ => gaussZak s (1/2)) (1/2)`.
  Both derivatives exist: `hasDerivAt_gaussZak_fst_zero` gives the value `zakA0` in `x`, and
  `hasDerivAt_gaussZak_snd_zero` the value `I * zakA0` in `y`.

Here `zakA0 = gauss (1/2) * (jacobiTheta₂' (1/2 - (1/2) * I) I * (-I))`, with Mathlib's
`jacobiTheta₂'` (the derivative of `jacobiTheta₂` in its first argument); it is the number `A₀` of
(A10). `hasDerivAt_gaussZak_snd` and `hasDerivAt_gaussZak_fst` give the two partial derivatives at
every point; the `x`-derivative has the extra term `gauss' x * jacobiTheta₂ (y - x * I) I`, which
vanishes at the zero by `jacobiTheta_zakZero` of C3. `hasDerivAt_gauss` is `gauss' = -2πx gauss`.

Conventions: nothing in the paper's conventions had to be changed.

What this file does NOT prove: `zakA0 ≠ 0` or its series (C5); joint (Fréchet) differentiability
of `gaussZak` on `ℝ²` (only the two one-variable derivatives are stated); the expansion (U2),
`F(z₀ + (s, t)) = a (s + i t) + O(s² + t²)`, with its error term; uniqueness or simplicity of the
zero; or any estimate of the paper. It proves nothing toward Theorem 1.1 or
Theorem 4.1, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

/-- `0 < im I`, the hypothesis of Mathlib's theta lemmas at `τ = I`. -/
theorem im_I_pos : 0 < Complex.I.im := by
  first
    | (rw [Complex.I_im]
       exact one_pos)
    | simp

/-- `e^{πx²} * gaussZak x y = 2^{1/4} * jacobiTheta₂ (y - x * I) I`. -/
theorem exp_mul_gaussZak (x y : ℝ) :
    ((Real.exp (Real.pi * x ^ 2) : ℝ) : ℂ) * gaussZak x y =
      (((2 : ℝ) ^ ((1 : ℝ) / 4) : ℝ) : ℂ) *
        jacobiTheta₂ ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I := by
  have h0 : Real.pi * x ^ 2 + -Real.pi * x ^ 2 = 0 := by ring
  have h1 : Real.exp (Real.pi * x ^ 2) * Real.exp (-Real.pi * x ^ 2) = 1 := by
    rw [← Real.exp_add, h0, Real.exp_zero]
  have hE : Real.exp (Real.pi * x ^ 2) *
      ((2 : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-Real.pi * x ^ 2)) = (2 : ℝ) ^ ((1 : ℝ) / 4) := by
    linear_combination (2 : ℝ) ^ ((1 : ℝ) / 4) * h1
  have hC : ((Real.exp (Real.pi * x ^ 2) : ℝ) : ℂ) *
      (((2 : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ) =
      (((2 : ℝ) ^ ((1 : ℝ) / 4) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hE]
  rw [gaussZak_eq_theta, ← mul_assoc, hC]

/-- `e^{πx²} * gaussZak x y` is an entire function of `y - x * I`. -/
theorem exp_mul_gaussZak_holomorphic :
    ∃ Θ : ℂ → ℂ, Differentiable ℂ Θ ∧ ∀ x y : ℝ,
      ((Real.exp (Real.pi * x ^ 2) : ℝ) : ℂ) * gaussZak x y =
        Θ ((y : ℂ) - (x : ℂ) * Complex.I) := by
  refine ⟨fun z => (((2 : ℝ) ^ ((1 : ℝ) / 4) : ℝ) : ℂ) * jacobiTheta₂ z Complex.I, ?_, ?_⟩
  · intro z
    exact (differentiableAt_jacobiTheta₂_fst z im_I_pos).const_mul _
  · intro x y
    exact exp_mul_gaussZak x y

/-- `gauss' x = -2πx * gauss x`. -/
theorem hasDerivAt_gauss (x : ℝ) : HasDerivAt gauss (-(2 * Real.pi * x) * gauss x) x := by
  have h0 : HasDerivAt (fun s : ℝ => -Real.pi * s ^ 2) (-Real.pi * (2 * x)) x := by
    have h00 : HasDerivAt (fun s : ℝ => -Real.pi * (s * s)) (-Real.pi * (1 * x + x * 1)) x :=
      ((hasDerivAt_id' x).mul (hasDerivAt_id' x)).const_mul (-Real.pi)
    have hf : (fun s : ℝ => -Real.pi * s ^ 2) = fun s : ℝ => -Real.pi * (s * s) :=
      funext fun s => by rw [pow_two]
    rw [hf]
    exact h00.congr_deriv (by ring)
  have h1 : HasDerivAt (fun s : ℝ => (2 : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-Real.pi * s ^ 2))
      ((2 : ℝ) ^ ((1 : ℝ) / 4) * (Real.exp (-Real.pi * x ^ 2) * (-Real.pi * (2 * x)))) x :=
    (h0.exp).const_mul ((2 : ℝ) ^ ((1 : ℝ) / 4))
  have hval : (2 : ℝ) ^ ((1 : ℝ) / 4) * (Real.exp (-Real.pi * x ^ 2) * (-Real.pi * (2 * x))) =
      -(2 * Real.pi * x) * gauss x := by
    unfold gauss
    ring
  exact h1.congr_deriv hval

/-- The `y`-derivative of `gaussZak` at any point. -/
theorem hasDerivAt_gaussZak_snd (x y : ℝ) :
    HasDerivAt (fun t : ℝ => gaussZak x t)
      (((gauss x : ℝ) : ℂ) * jacobiTheta₂' ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I) y := by
  have hθ := hasDerivAt_jacobiTheta₂_fst ((y : ℂ) - (x : ℂ) * Complex.I) im_I_pos
  have hc : HasDerivAt (fun w : ℂ => jacobiTheta₂ (w - (x : ℂ) * Complex.I) Complex.I)
      (jacobiTheta₂' ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I) (y : ℂ) :=
    HasDerivAt.comp_sub_const (y : ℂ) ((x : ℂ) * Complex.I) hθ
  have hr : HasDerivAt (fun t : ℝ => jacobiTheta₂ ((t : ℂ) - (x : ℂ) * Complex.I) Complex.I)
      (jacobiTheta₂' ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I) y := hc.comp_ofReal
  have hm := hr.const_mul ((gauss x : ℝ) : ℂ)
  have hfun : (fun t : ℝ => gaussZak x t) = fun t : ℝ =>
      ((gauss x : ℝ) : ℂ) * jacobiTheta₂ ((t : ℂ) - (x : ℂ) * Complex.I) Complex.I :=
    funext fun t => gaussZak_eq_gauss_mul_theta x t
  first
    | (rw [hfun]
       exact hm)
    | exact hm.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => gaussZak_eq_gauss_mul_theta x t)

/-- The `x`-derivative of `gaussZak` at any point. -/
theorem hasDerivAt_gaussZak_fst (x y : ℝ) :
    HasDerivAt (fun s : ℝ => gaussZak s y)
      (((-(2 * Real.pi * x) * gauss x : ℝ) : ℂ) *
          jacobiTheta₂ ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I +
        ((gauss x : ℝ) : ℂ) *
          (jacobiTheta₂' ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I * (-Complex.I))) x := by
  have hθ := hasDerivAt_jacobiTheta₂_fst ((y : ℂ) - (x : ℂ) * Complex.I) im_I_pos
  have hin : HasDerivAt (fun w : ℂ => (y : ℂ) - w * Complex.I) (-Complex.I) (x : ℂ) :=
    (((hasDerivAt_id' (x : ℂ)).mul_const Complex.I).const_sub (y : ℂ)).congr_deriv
      (by rw [one_mul])
  have hc : HasDerivAt (fun w : ℂ => jacobiTheta₂ ((y : ℂ) - w * Complex.I) Complex.I)
      (jacobiTheta₂' ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I * (-Complex.I)) (x : ℂ) := by
    first
      | exact hθ.comp_of_eq (x : ℂ) hin rfl
      | exact HasDerivAt.comp (h := fun w : ℂ => (y : ℂ) - w * Complex.I) (x : ℂ) hθ hin
  have hr : HasDerivAt (fun s : ℝ => jacobiTheta₂ ((y : ℂ) - (s : ℂ) * Complex.I) Complex.I)
      (jacobiTheta₂' ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I * (-Complex.I)) x :=
    hc.comp_ofReal
  have hg : HasDerivAt (fun s : ℝ => ((gauss s : ℝ) : ℂ))
      ((-(2 * Real.pi * x) * gauss x : ℝ) : ℂ) x := (hasDerivAt_gauss x).ofReal_comp
  have hm := hg.mul hr
  have hfun : (fun s : ℝ => gaussZak s y) = fun s : ℝ =>
      ((gauss s : ℝ) : ℂ) * jacobiTheta₂ ((y : ℂ) - (s : ℂ) * Complex.I) Complex.I :=
    funext fun s => gaussZak_eq_gauss_mul_theta s y
  first
    | (rw [hfun]
       exact hm)
    | exact hm.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => gaussZak_eq_gauss_mul_theta s y)

/-- `A₀` of (A10): the `x`-derivative of `gaussZak` at its zero `(1/2, 1/2)`. -/
def zakA0 : ℂ :=
  ((gauss (1 / 2) : ℝ) : ℂ) *
    (jacobiTheta₂' (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I * (-Complex.I))

/-- At the zero, `∂_x gaussZak = zakA0`. -/
theorem hasDerivAt_gaussZak_fst_zero :
    HasDerivAt (fun s : ℝ => gaussZak s (1 / 2)) zakA0 (1 / 2) := by
  have h := hasDerivAt_gaussZak_fst (1 / 2) (1 / 2)
  first
    | (rw [jacobiTheta_zakZero, mul_zero, zero_add] at h
       exact h)
    | (simp only [jacobiTheta_zakZero, mul_zero, zero_add] at h
       exact h)

/-- At the zero, `∂_y gaussZak = I * zakA0`. -/
theorem hasDerivAt_gaussZak_snd_zero :
    HasDerivAt (fun t : ℝ => gaussZak (1 / 2) t) (Complex.I * zakA0) (1 / 2) := by
  have hval : Complex.I * (((gauss (1 / 2) : ℝ) : ℂ) *
      (jacobiTheta₂' (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I *
        (-Complex.I))) = ((gauss (1 / 2) : ℝ) : ℂ) *
      jacobiTheta₂' (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I := by
    linear_combination (-(((gauss (1 / 2) : ℝ) : ℂ) *
      jacobiTheta₂' (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I)) * Complex.I_sq
  exact (hasDerivAt_gaussZak_snd (1 / 2) (1 / 2)).congr_deriv hval.symm

/-- Conformality at the zero, the statement of roadmap item C4: `∂_y gaussZak = I * ∂_x gaussZak`
at `(1/2, 1/2)`. -/
theorem deriv_gaussZak_snd_zero :
    deriv (fun t : ℝ => gaussZak (1 / 2) t) (1 / 2) =
      Complex.I * deriv (fun s : ℝ => gaussZak s (1 / 2)) (1 / 2) := by
  first
    | rw [hasDerivAt_gaussZak_snd_zero.deriv, hasDerivAt_gaussZak_fst_zero.deriv]
    | exact hasDerivAt_gaussZak_snd_zero.deriv.trans
        (congrArg (fun a : ℂ => Complex.I * a) hasDerivAt_gaussZak_fst_zero.deriv.symm)

end BLT

end
