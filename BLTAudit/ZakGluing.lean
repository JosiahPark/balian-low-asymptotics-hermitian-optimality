import BLTAudit.Basic
import BLTAudit.ZakTheta

/-!
# C2. Quasi-periodicity of the Zak transform of the Gaussian, (U1) of §3.1

For `gaussZak x y = ∑' r : ℤ, gauss (x - r) * exp (2πi r y)` of `BLTAudit/Basic.lean` and all real
`x y`, this file proves the two statements of roadmap item C2:

* `gaussZak_add_one_left`: `gaussZak (x + 1) y = exp (2πi y) * gaussZak x y`;
* `gaussZak_add_one_right`: `gaussZak x (y + 1) = gaussZak x y`.

Both are proved termwise, with the convergence of the series taken from `hasSum_gaussZak_term`
of C1 (`BLTAudit/ZakTheta.lean`). In `y`, `e^{2πi r (y + 1)} = e^{2πi r y}` for an integer `r`
(`exp_two_pi_int_mul_add_one`). In `x`, the series is reindexed by `r = s + 1`
(`Equiv.addRight 1` on `ℤ`), and the summand at `s + 1` is `e^{2πi y}` times the summand of
`gaussZak x y` at `s` (`gaussZak_term_shift`).

Conventions: the factor is `Complex.exp (2 * π * I * y)`, as in (U1). Nothing in the paper's
conventions had to be changed.

What this file does NOT prove: shifts by integers other than `1`; that the samples of `gaussZak`
on a `d × d` grid give an array with the gluing of `IsTwisted` (this needs a change of variables,
which is not made here); the zero at `(1/2, 1/2)` (C3), conformality there (C4), the nonvanishing
derivative (C5); or any estimate of the paper. It proves nothing toward Theorem 1.1 or
Theorem 4.1, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

/-- `e^{2πi r (y + 1)} = e^{2πi r y}` for an integer `r`. -/
theorem exp_two_pi_int_mul_add_one (r : ℤ) (y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * ((y + 1 : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (y : ℂ)) := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * ((y + 1 : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (y : ℂ) +
        (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    first
      | (push_cast
         ring)
      | (rw [Complex.ofReal_add, Complex.ofReal_one]
         ring)
  have h1 : Complex.exp ((r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I r
  first
    | rw [h, Complex.exp_add, h1, mul_one]
    | exact (congrArg Complex.exp h).trans (by rw [Complex.exp_add, h1, mul_one])

/-- The summand of `gaussZak (x + 1) y` at `s + 1` is `e^{2πi y}` times the summand of
`gaussZak x y` at `s`. -/
theorem gaussZak_term_shift (x y : ℝ) (s : ℤ) :
    ((gauss (x + 1 - ((s + 1 : ℤ) : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((s + 1 : ℤ) : ℂ) * (y : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) *
        (((gauss (x - (s : ℝ)) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * (y : ℂ))) := by
  have hx : x + 1 - ((s + 1 : ℤ) : ℝ) = x - (s : ℝ) := by
    first
      | (push_cast
         ring)
      | (rw [Int.cast_add, Int.cast_one]
         ring)
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((s + 1 : ℤ) : ℂ) * (y : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * (y : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) * (y : ℂ) := by
    first
      | (push_cast
         ring)
      | (rw [Int.cast_add, Int.cast_one]
         ring)
  first
    | (rw [hx, he, Complex.exp_add]
       ring)
    | (simp only [hx, he, Complex.exp_add]
       ring)

/-- Quasi-periodicity in `x`, the first statement of (U1):
`gaussZak (x + 1) y = e^{2πi y} * gaussZak x y`. -/
theorem gaussZak_add_one_left (x y : ℝ) :
    gaussZak (x + 1) y = Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) * gaussZak x y := by
  have h2 := (hasSum_gaussZak_term x y).mul_left
    (Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)))
  have h1 := (Equiv.addRight (1 : ℤ)).hasSum_iff.mpr (hasSum_gaussZak_term (x + 1) y)
  have hfun : (fun s : ℤ => Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) *
      (((gauss (x - (s : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * (y : ℂ)))) =
      (fun r : ℤ => ((gauss (x + 1 - (r : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (y : ℂ))) ∘
          ⇑(Equiv.addRight (1 : ℤ)) := by
    first
      | exact funext fun s => (gaussZak_term_shift x y s).symm
      | (funext s
         simp only [Function.comp_apply, Equiv.coe_addRight]
         exact (gaussZak_term_shift x y s).symm)
      | (funext s
         rw [Function.comp_apply, Equiv.coe_addRight]
         exact (gaussZak_term_shift x y s).symm)
  have h3 : HasSum (fun s : ℤ => Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) *
      (((gauss (x - (s : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * (y : ℂ)))) (gaussZak (x + 1) y) := by
    first
      | (rw [hfun]
         exact h1)
      | exact hfun ▸ h1
  exact h3.unique h2

/-- Periodicity in `y`, the second statement of (U1): `gaussZak x (y + 1) = gaussZak x y`. -/
theorem gaussZak_add_one_right (x y : ℝ) : gaussZak x (y + 1) = gaussZak x y := by
  first
    | (have h0 := hasSum_gaussZak_term x (y + 1)
       simp only [exp_two_pi_int_mul_add_one] at h0
       exact h0.unique (hasSum_gaussZak_term x y))
    | (unfold gaussZak
       exact tsum_congr fun r => by rw [exp_two_pi_int_mul_add_one])
    | (unfold gaussZak
       refine tsum_congr fun r => ?_
       simp only [exp_two_pi_int_mul_add_one])

end BLT

end
