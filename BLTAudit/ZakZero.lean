import BLTAudit.Basic
import BLTAudit.ZakTheta

/-!
# C3. The Zak zero of the Gaussian, (A10) first part (§3.1, Appendix A.3)

For `gauss x = 2^{1/4} e^{-πx²}` and `gaussZak x y = ∑' r : ℤ, gauss (x - r) * exp (2πi r y)` of
`BLTAudit/Basic.lean`, this file proves the statement of roadmap item C3:

* `gaussZak_half_half`: `gaussZak (1/2) (1/2) = 0`.

The proof pairs `r ↔ 1 - r` in the series, whose convergence is `hasSum_gaussZak_term` of C1
(`BLTAudit/ZakTheta.lean`). The summand at `1 - r` is minus the summand at `r`
(`gaussZak_half_term_reflect`): `gauss` is even (`gauss_neg`) and `1/2 - (1 - r) = -(1/2 - r)`,
while `e^{2πi (1 - r) / 2} = -e^{2πi r / 2}` (`exp_reflect_half`, from `e^{πi} = -1` and
`e^{-2πi r} = 1`). Reindexing the series by `Equiv.subLeft 1` on `ℤ` then shows that its sum equals
its own negative.

Also proved: `gauss_pos` (`0 < gauss t`) and, through `gaussZak_eq_gauss_mul_theta` of C1,
`jacobiTheta_zakZero`: Mathlib's `jacobiTheta₂ z I` vanishes at `z = 1/2 - (1/2) * I`, the two
numbers `1/2` being real numbers cast to `ℂ`.

Conventions: nothing in the paper's conventions had to be changed.

What this file does NOT prove: that `(1/2, 1/2)` is the only zero of `gaussZak` in the unit
square, or that the zero is simple (Jacobi triple product, Appendix A.3); zeros at the other
half-integer points (they would follow from C2, and are not stated); conformality at the zero
(C4); the nonvanishing derivative (C5); continuity or differentiability of `gaussZak`; or any
estimate of the paper. It proves nothing toward Theorem 1.1 or Theorem 4.1, and nothing toward
the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

/-- The Gaussian is even. -/
theorem gauss_neg (t : ℝ) : gauss (-t) = gauss t := by
  have h : -Real.pi * (-t) ^ 2 = -Real.pi * t ^ 2 := by ring
  first
    | (unfold gauss
       rw [h])
    | simp only [gauss, h]
    | (unfold gauss
       rw [neg_sq])

/-- The Gaussian is strictly positive. -/
theorem gauss_pos (t : ℝ) : 0 < gauss t := by
  first
    | (unfold gauss
       positivity)
    | (unfold gauss
       exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.exp_pos _))

/-- `e^{2πi (1 - r) / 2} = -e^{2πi r / 2}` for an integer `r`. -/
theorem exp_reflect_half (r : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((1 - r : ℤ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) =
      -Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * ((1 / 2 : ℝ) : ℂ)) := by
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by
    first
      | (push_cast
         ring)
      | norm_num
      | simp
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((1 - r : ℤ) : ℂ) * ((1 / 2 : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * ((1 / 2 : ℝ) : ℂ) +
        ((Real.pi : ℂ) * Complex.I + ((-r : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    first
      | (rw [hhalf]
         push_cast
         ring)
      | (push_cast
         ring)
      | (rw [hhalf, Int.cast_sub, Int.cast_one, Int.cast_neg]
         ring)
  have h1 : Complex.exp (((-r : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I (-r)
  have hpi : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  first
    | (rw [h, Complex.exp_add, Complex.exp_add, hpi, h1]
       ring)
    | (have e := congrArg Complex.exp h
       rw [Complex.exp_add, Complex.exp_add, hpi, h1] at e
       rw [e]
       ring)

/-- At `x = y = 1/2` the summand of `gaussZak` at `1 - r` is minus the summand at `r`. -/
theorem gaussZak_half_term_reflect (r : ℤ) :
    ((gauss (1 / 2 - ((1 - r : ℤ) : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((1 - r : ℤ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) =
      -(((gauss (1 / 2 - (r : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * ((1 / 2 : ℝ) : ℂ))) := by
  have hx : (1 / 2 : ℝ) - ((1 - r : ℤ) : ℝ) = -((1 / 2 : ℝ) - (r : ℝ)) := by
    first
      | (push_cast
         ring)
      | (rw [Int.cast_sub, Int.cast_one]
         ring)
  have hg : gauss (1 / 2 - ((1 - r : ℤ) : ℝ)) = gauss (1 / 2 - (r : ℝ)) := by
    rw [hx]
    exact gauss_neg _
  first
    | (rw [hg, exp_reflect_half r]
       ring)
    | (rw [hg, exp_reflect_half r, mul_neg])
    | (simp only [hg, exp_reflect_half r]
       ring)

/-- The Zak zero, the statement of roadmap item C3: `gaussZak (1/2) (1/2) = 0`. -/
theorem gaussZak_half_half : gaussZak (1 / 2) (1 / 2) = 0 := by
  have h := hasSum_gaussZak_term (1 / 2) (1 / 2)
  have h1 := (Equiv.subLeft (1 : ℤ)).hasSum_iff.mpr h
  have hfun : (fun r : ℤ => -(((gauss (1 / 2 - (r : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * ((1 / 2 : ℝ) : ℂ)))) =
      (fun r : ℤ => ((gauss (1 / 2 - (r : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * ((1 / 2 : ℝ) : ℂ))) ∘
          ⇑(Equiv.subLeft (1 : ℤ)) := by
    first
      | exact funext fun r => (gaussZak_half_term_reflect r).symm
      | (funext r
         simp only [Function.comp_apply, Equiv.subLeft_apply]
         exact (gaussZak_half_term_reflect r).symm)
      | (funext r
         rw [Function.comp_apply, Equiv.subLeft_apply]
         exact (gaussZak_half_term_reflect r).symm)
      | (funext r
         exact (gaussZak_half_term_reflect r).symm)
  have h2 : HasSum (fun r : ℤ => -(((gauss (1 / 2 - (r : ℝ)) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * ((1 / 2 : ℝ) : ℂ))))
      (gaussZak (1 / 2) (1 / 2)) := by
    first
      | (rw [hfun]
         exact h1)
      | exact hfun ▸ h1
  have h3 : gaussZak (1 / 2) (1 / 2) = -gaussZak (1 / 2) (1 / 2) := by
    first
      | exact h2.unique h.neg
      | (have h5 := h.mul_left (-1 : ℂ)
         simp only [neg_one_mul] at h5
         exact h2.unique h5)
  first
    | linear_combination (1 / 2 : ℂ) * h3
    | exact self_eq_neg.mp h3
    | (have h4 : (2 : ℂ) * gaussZak (1 / 2) (1 / 2) = 0 := by linear_combination h3
       simpa using h4)

/-- In Mathlib's notation: `jacobiTheta₂ z I` vanishes at `z = 1/2 - (1/2) * I`. -/
theorem jacobiTheta_zakZero :
    jacobiTheta₂ (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I = 0 := by
  have h := gaussZak_eq_gauss_mul_theta (1 / 2) (1 / 2)
  rw [gaussZak_half_half] at h
  have hg : ((gauss (1 / 2) : ℝ) : ℂ) ≠ 0 := by
    first
      | exact Complex.ofReal_ne_zero.mpr (gauss_pos (1 / 2)).ne'
      | exact_mod_cast (gauss_pos (1 / 2)).ne'
  exact (mul_eq_zero.mp h.symm).resolve_left hg

end BLT

end
