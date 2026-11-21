import BLTAudit.Basic

/-!
# C1. Theta representation of the Zak transform of the Gaussian (§3.1, Appendix A.3)

With `gauss x = 2^{1/4} e^{-πx²}` and `gaussZak x y = ∑' r : ℤ, gauss (x - r) * exp (2πi r y)` of
`BLTAudit/Basic.lean`, and Mathlib's `jacobiTheta₂ z τ = ∑' n : ℤ, exp (2πi n z + πi n² τ)` with
summand `jacobiTheta₂_term n z τ`, this file proves, for all real `x y`:

* `gaussZak_term_eq`: the summand at `r : ℤ` is `gauss x * jacobiTheta₂_term r (y - x * I) I`
  (complete the square: `-π(x - r)² + 2πi r y = -πx² + 2πi r (y - x i) + πi r² · i`);
* `summable_gaussZak_term`: `r ↦ gauss (x - r) * exp (2πi r y)` is summable over `ℤ`;
* `hasSum_gaussZak_term`: its sum is `gaussZak x y`;
* `gaussZak_eq_theta`: `gaussZak x y = 2^{1/4} e^{-πx²} * jacobiTheta₂ (y - x * I) I`, the
  statement of roadmap item C1. `gaussZak_eq_gauss_mul_theta` is the same with the constant
  written `gauss x`, and `hasSum_gaussZak_term_theta` is the same as a `HasSum`.

Helpers: `ofReal_mul_exp_mul_exp_eq` (two products `c e^a e^b` with equal total exponent agree)
and `gaussZak_term_aux` (the summand identity with any real constant `c` in place of `2^{1/4}`).

Conventions: the constant is the real number `2^{1/4} e^{-πx²}`, with the real power
`(2 : ℝ) ^ ((1 : ℝ) / 4)`, cast to `ℂ`; the theta function is taken at `z = y - x * I`, `τ = I`.
Nothing in the paper's conventions had to be changed.

What this file does NOT prove: the quasi-periodicity (U1) of `gaussZak` (item C2), the zero at
`(1/2, 1/2)` (C3), conformality there (C4), the nonvanishing derivative (C5), continuity or
differentiability of `gaussZak`, uniqueness of the zero, or any estimate of the paper. It proves
nothing toward Theorem 1.1 or Theorem 4.1, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

/-- Two products `c e^a e^b` and `c e^{a'} e^{b'}` (`c a a'` real, `b b'` complex) agree as soon
as the total exponents do. -/
theorem ofReal_mul_exp_mul_exp_eq (c a a' : ℝ) (b b' : ℂ) (h : (a : ℂ) + b = (a' : ℂ) + b') :
    ((c * Real.exp a : ℝ) : ℂ) * Complex.exp b =
      ((c * Real.exp a' : ℝ) : ℂ) * Complex.exp b' := by
  first
    | rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp,
        mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add, h]
    | (have e1 : Complex.exp ((a : ℂ) + b) = Complex.exp ((a' : ℂ) + b') := by rw [h]
       rw [Complex.exp_add, Complex.exp_add] at e1
       push_cast
       linear_combination (c : ℂ) * e1)
    | simp only [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add, h]

/-- Completing the square in one summand, with an arbitrary real constant `c` in place of
`2^{1/4}`: `c e^{-π(x-r)²} e^{2πi r y} = c e^{-πx²} · jacobiTheta₂_term r (y - x i) i`. -/
theorem gaussZak_term_aux (c x y : ℝ) (r : ℤ) :
    ((c * Real.exp (-Real.pi * (x - (r : ℝ)) ^ 2) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (y : ℂ)) =
      ((c * Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ) *
        jacobiTheta₂_term r ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hexp : ((-Real.pi * (x - (r : ℝ)) ^ 2 : ℝ) : ℂ) +
        2 * Real.pi * Complex.I * (r : ℂ) * (y : ℂ) =
      ((-Real.pi * x ^ 2 : ℝ) : ℂ) +
        (2 * Real.pi * Complex.I * (r : ℂ) * ((y : ℂ) - (x : ℂ) * Complex.I) +
          Real.pi * Complex.I * (r : ℂ) ^ 2 * Complex.I) := by
    first
      | (push_cast
         linear_combination (2 * (Real.pi : ℂ) * (x : ℂ) * (r : ℂ) -
           (Real.pi : ℂ) * (r : ℂ) ^ 2) * hI)
      | (simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
           Complex.ofReal_sub, Complex.ofReal_intCast]
         linear_combination (2 * (Real.pi : ℂ) * (x : ℂ) * (r : ℂ) -
           (Real.pi : ℂ) * (r : ℂ) ^ 2) * hI)
  first
    | (rw [jacobiTheta₂_term]
       exact ofReal_mul_exp_mul_exp_eq c _ _ _ _ hexp)
    | (unfold jacobiTheta₂_term
       exact ofReal_mul_exp_mul_exp_eq c _ _ _ _ hexp)
    | exact ofReal_mul_exp_mul_exp_eq c _ _ _ _ hexp

/-- One summand of `gaussZak x y` is `gauss x` times the summand of `jacobiTheta₂ (y - x i) i`. -/
theorem gaussZak_term_eq (x y : ℝ) (r : ℤ) :
    ((gauss (x - (r : ℝ)) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (y : ℂ)) =
      ((gauss x : ℝ) : ℂ) * jacobiTheta₂_term r ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I := by
  first
    | exact gaussZak_term_aux ((2 : ℝ) ^ ((1 : ℝ) / 4)) x y r
    | (unfold gauss
       exact gaussZak_term_aux _ x y r)
    | (simp only [gauss]
       exact gaussZak_term_aux _ x y r)

/-- The series of `gaussZak x y` sums to `gauss x * jacobiTheta₂ (y - x i) i`. -/
theorem hasSum_gaussZak_term_theta (x y : ℝ) :
    HasSum (fun r : ℤ => ((gauss (x - (r : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (y : ℂ)))
      (((gauss x : ℝ) : ℂ) * jacobiTheta₂ ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I) := by
  have hI : 0 < Complex.I.im := by
    first
      | (rw [Complex.I_im]
         exact one_pos)
      | simp
      | norm_num
  have h := (hasSum_jacobiTheta₂_term ((y : ℂ) - (x : ℂ) * Complex.I) hI).mul_left
    ((gauss x : ℝ) : ℂ)
  have hfun : (fun r : ℤ => ((gauss (x - (r : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (y : ℂ))) =
      fun r : ℤ => ((gauss x : ℝ) : ℂ) *
        jacobiTheta₂_term r ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I :=
    funext fun r => gaussZak_term_eq x y r
  first
    | (rw [hfun]
       exact h)
    | exact hfun ▸ h
    | simpa only [gaussZak_term_eq] using h

/-- Summability of the series that defines `gaussZak x y`. -/
theorem summable_gaussZak_term (x y : ℝ) :
    Summable (fun r : ℤ => ((gauss (x - (r : ℝ)) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (y : ℂ))) :=
  (hasSum_gaussZak_term_theta x y).summable

/-- `gaussZak x y = gauss x * jacobiTheta₂ (y - x i) i`. -/
theorem gaussZak_eq_gauss_mul_theta (x y : ℝ) :
    gaussZak x y =
      ((gauss x : ℝ) : ℂ) * jacobiTheta₂ ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I := by
  first
    | exact (hasSum_gaussZak_term_theta x y).tsum_eq
    | (unfold gaussZak
       exact (hasSum_gaussZak_term_theta x y).tsum_eq)

/-- Theta representation, the statement of roadmap item C1:
`gaussZak x y = 2^{1/4} e^{-πx²} * jacobiTheta₂ (y - x i) i`. -/
theorem gaussZak_eq_theta (x y : ℝ) :
    gaussZak x y = (((2 : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ) *
      jacobiTheta₂ ((y : ℂ) - (x : ℂ) * Complex.I) Complex.I := by
  first
    | exact gaussZak_eq_gauss_mul_theta x y
    | (have h := gaussZak_eq_gauss_mul_theta x y
       unfold gauss at h
       exact h)

/-- The series that defines `gaussZak x y` converges to it. -/
theorem hasSum_gaussZak_term (x y : ℝ) :
    HasSum (fun r : ℤ => ((gauss (x - (r : ℝ)) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (y : ℂ))) (gaussZak x y) := by
  first
    | exact (summable_gaussZak_term x y).hasSum
    | (unfold gaussZak
       exact (summable_gaussZak_term x y).hasSum)

end BLT

end
