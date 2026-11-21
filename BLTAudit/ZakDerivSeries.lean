import BLTAudit.Basic
import BLTAudit.ZakTheta
import BLTAudit.ZakConformal

/-!
# C5a. The series of `A₀` over `ℤ`, (A10) (§3.1, Appendix A.3)

`zakA0` of C4 (`BLTAudit/ZakConformal.lean`) is the `x`-derivative of
`gaussZak x y = ∑' r : ℤ, gauss (x - r) * exp (2πi r y)` at its zero `(1/2, 1/2)`; it is defined
there as `gauss (1/2) * (jacobiTheta₂' (1/2 - (1/2) * I) I * (-I))`, with Mathlib's
`jacobiTheta₂'`. This file proves the statement of roadmap item C5a:

* `hasSum_zakA0`: in `ℂ`,
  `HasSum (fun n : ℤ => 2 * π * n * (gauss (1/2 - n) * exp (2πi n (1/2)))) zakA0`.
  The summand is `2πn` times the summand of `gaussZak (1/2) (1/2)`.

Also proved: `hasSum_deriv_gaussZak_fst_zero` (the same series sums to
`deriv (fun s : ℝ => gaussZak s (1/2)) (1/2)`, by `hasDerivAt_gaussZak_fst_zero` of C4),
`summable_zakA0_term` (the series is summable) and `zakA0_eq_tsum` (`zakA0` is its `tsum`).

Helpers: `thetaDerivTerm_eq` (Mathlib's summand `jacobiTheta₂'_term n z τ` is
`2πi n * jacobiTheta₂_term n z τ`), `hasSum_thetaDerivTerm` (Mathlib's series of `jacobiTheta₂'`
at `τ = I`) and `zakA0_term_eq` (the summand above is
`gauss (1/2) * (jacobiTheta₂'_term n (1/2 - (1/2) * I) I * (-I))`, by `gaussZak_term_eq` of C1 and
`I² = -1`).

The series is not obtained here by differentiating the series of `gaussZak` term by term: it is
Mathlib's series of `jacobiTheta₂'` (`hasSum_jacobiTheta₂'_term`), multiplied by
`gauss (1/2) * (-I)`; that `zakA0` is the derivative is C4, which rests on Mathlib's
`hasDerivAt_jacobiTheta₂_fst`.

Conventions: the two numbers `1/2` are real numbers cast to `ℂ`, as in C3 and C4, and the summand
is written with `Complex.exp (2 * π * I * n * (1/2))`, the form of the summand of `gaussZak`.
Nothing in the paper's conventions had to be changed.

What this file does NOT prove: `exp (2πi n (1/2)) = (-1) ^ n` and the folding of the series to
`A₀ = -4π ∑_{k ≥ 0} (-1)^k (k + 1/2) gauss (k + 1/2)` (C5b); that the terms of that series are
positive and strictly decreasing (C5c); `zakA0 ≠ 0` (C5d); the series of the derivatives of
`gaussZak` at other points; or any estimate of the paper. It proves nothing toward Theorem 1.1 or
Theorem 4.1, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

/-- Mathlib's summand of `jacobiTheta₂'` is `2πi n` times the summand of `jacobiTheta₂`. -/
theorem thetaDerivTerm_eq (n : ℤ) (z τ : ℂ) :
    jacobiTheta₂'_term n z τ =
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * jacobiTheta₂_term n z τ := by
  first
    | rfl
    | (unfold jacobiTheta₂'_term
       ring)
    | (rw [jacobiTheta₂'_term])
    | (simp only [jacobiTheta₂'_term])
    | (unfold jacobiTheta₂'_term jacobiTheta₂_term
       ring)

/-- Mathlib's series of `jacobiTheta₂'` at `τ = I`. -/
theorem hasSum_thetaDerivTerm (z : ℂ) :
    HasSum (fun n : ℤ => jacobiTheta₂'_term n z Complex.I) (jacobiTheta₂' z Complex.I) := by
  first
    | exact hasSum_jacobiTheta₂'_term z im_I_pos
    | exact ((summable_jacobiTheta₂'_term_iff z Complex.I).mpr im_I_pos).hasSum

/-- `2πn` times the summand of `gaussZak (1/2) (1/2)` is `gauss (1/2) * (-I)` times Mathlib's
summand of `jacobiTheta₂' (1/2 - (1/2) * I) I`. -/
theorem zakA0_term_eq (n : ℤ) :
    2 * (Real.pi : ℂ) * (n : ℂ) *
        (((gauss (1 / 2 - (n : ℝ)) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ))) =
      ((gauss (1 / 2) : ℝ) : ℂ) *
        (jacobiTheta₂'_term n (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I *
          (-Complex.I)) := by
  have h := gaussZak_term_eq (1 / 2) (1 / 2) n
  have h' := thetaDerivTerm_eq n (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I
  first
    | linear_combination (2 * (Real.pi : ℂ) * (n : ℂ)) * h +
        (((gauss (1 / 2) : ℝ) : ℂ) * Complex.I) * h' +
        (2 * (Real.pi : ℂ) * (n : ℂ) * ((gauss (1 / 2) : ℝ) : ℂ) *
          jacobiTheta₂_term n (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I) *
          Complex.I_sq
    | (rw [h, h']
       linear_combination (2 * (Real.pi : ℂ) * (n : ℂ) * ((gauss (1 / 2) : ℝ) : ℂ) *
         jacobiTheta₂_term n (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I) *
         Complex.I_sq)

/-- The series of `A₀` over `ℤ`, the statement of roadmap item C5a. -/
theorem hasSum_zakA0 :
    HasSum (fun n : ℤ => 2 * (Real.pi : ℂ) * (n : ℂ) *
        (((gauss (1 / 2 - (n : ℝ)) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ))))
      zakA0 := by
  have h := ((hasSum_thetaDerivTerm
    (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I)).mul_right (-Complex.I)).mul_left
      ((gauss (1 / 2) : ℝ) : ℂ)
  have hfun : (fun n : ℤ => 2 * (Real.pi : ℂ) * (n : ℂ) *
        (((gauss (1 / 2 - (n : ℝ)) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ)))) =
      fun n : ℤ => ((gauss (1 / 2) : ℝ) : ℂ) *
        (jacobiTheta₂'_term n (((1 / 2 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) Complex.I *
          (-Complex.I)) :=
    funext zakA0_term_eq
  first
    | (rw [hfun]
       exact h)
    | (unfold zakA0
       rw [hfun]
       exact h)
    | exact hfun ▸ h
    | (unfold zakA0
       exact hfun ▸ h)

/-- The series of `hasSum_zakA0` is summable. -/
theorem summable_zakA0_term :
    Summable (fun n : ℤ => 2 * (Real.pi : ℂ) * (n : ℂ) *
      (((gauss (1 / 2 - (n : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ)))) :=
  hasSum_zakA0.summable

/-- `zakA0` as a `tsum` over `ℤ`. -/
theorem zakA0_eq_tsum :
    zakA0 = ∑' n : ℤ, 2 * (Real.pi : ℂ) * (n : ℂ) *
      (((gauss (1 / 2 - (n : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ))) :=
  hasSum_zakA0.tsum_eq.symm

/-- The same series sums to the `x`-derivative of `gaussZak` at its zero `(1/2, 1/2)`. -/
theorem hasSum_deriv_gaussZak_fst_zero :
    HasSum (fun n : ℤ => 2 * (Real.pi : ℂ) * (n : ℂ) *
        (((gauss (1 / 2 - (n : ℝ)) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ))))
      (deriv (fun s : ℝ => gaussZak s (1 / 2)) (1 / 2)) := by
  have h := hasSum_zakA0
  have e : deriv (fun s : ℝ => gaussZak s (1 / 2)) (1 / 2) = zakA0 :=
    hasDerivAt_gaussZak_fst_zero.deriv
  first
    | (rw [e]
       exact h)
    | (rw [← e] at h
       exact h)
    | exact e.symm ▸ h

end BLT

end
