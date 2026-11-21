import BLTAudit.Basic
import BLTAudit.ZakZero
import BLTAudit.ZakConformal
import BLTAudit.ZakDerivSeries

/-!
# C5b. Folding the series of `A₀` to a series over `ℕ`, (A10) (§3.1, Appendix A.3)

`zakA0` of C4 (`BLTAudit/ZakConformal.lean`) is the `x`-derivative of `gaussZak` at its zero
`(1/2, 1/2)`, and C5a (`BLTAudit/ZakDerivSeries.lean`) wrote it as a series over `ℤ`,
`HasSum (fun n : ℤ => 2 * π * n * (gauss (1/2 - n) * exp (2πi n (1/2)))) zakA0`. This file proves
the two statements of roadmap item C5b:

* `exp_half_int`: `Complex.exp (2πi n (1/2)) = (-1) ^ n` for `n : ℤ` (an integer power in `ℂ`).
* `hasSum_zakA0_nat`:
  `HasSum (fun k : ℕ => -(4 * π) * ((-1) ^ k * ((k + 1/2) * gauss (k + 1/2)))) zakA0`, each term a
  real number cast to `ℂ`; that is, `A₀ = -4π ∑_{k ≥ 0} (-1)^k (k + 1/2) gauss (k + 1/2)`.

Proof of the second: reindex the series of C5a by `n = m + 1` (`Equiv.addRight 1` on `ℤ`), then
pair `m = k` with `m = -(k + 1)` (Mathlib's `HasSum.nat_add_neg_add_one`). The two summands, at
`n = k + 1` and at `n = -k`, add up to the term above (`zakA0Term_fold`): `gauss` is even
(`gauss_neg` of C3), `e^{2πi (k + 1) / 2} = -(-1)^k` (`exp_half_succ`) and
`e^{2πi (-k) / 2} = (-1)^k` (`exp_half_neg`); both follow from `e^{πi k} = (-1)^k`
(`exp_nat_mul_pi_I`).

Also proved: `zakA0_eq_tsum_nat` (`zakA0` is the `tsum` of the folded series) and
`hasSum_zakA0_re` (the same series, as a series of real numbers, sums to `zakA0.re`).

Defined here: `zakA0Term n`, the summand of the series of C5a, so that C5a reads
`HasSum zakA0Term zakA0` (`hasSum_zakA0Term`).

Conventions: as in C5a, the `1/2` of the exponent is a real number cast to `ℂ`. The integer `-k`
is written `-(k + 1) + 1`, the form in which the pairing produces it. Mathlib's
`HasSum.of_nat_of_neg_add_one` and `Summable.comp_injective`, named in the roadmap hint, are not
needed. Nothing in the paper's conventions had to be changed.

What this file does NOT prove: that the terms `(k + 1/2) * gauss (k + 1/2)` are positive and
strictly decreasing (C5c); `zakA0 ≠ 0` (C5d); that `zakA0` is a real number (its imaginary part
is not computed here); or any estimate of the paper. It proves nothing toward Theorem 1.1 or
Theorem 4.1, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

/-- `e^{πi k} = (-1)^k` for a natural number `k`. -/
theorem exp_nat_mul_pi_I (k : ℕ) :
    Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ k := by
  first
    | rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    | exact (Complex.exp_nat_mul _ k).trans (by rw [Complex.exp_pi_mul_I])

/-- `e^{2πi n (1/2)} = (-1)^n` for an integer `n`, the first statement of roadmap item C5b. -/
theorem exp_half_int (n : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ)) = (-1 : ℂ) ^ n := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ) =
      (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    first
      | (push_cast
         ring)
      | (rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
         ring)
  first
    | rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I]
    | exact (congrArg Complex.exp h).trans
        ((Complex.exp_int_mul _ n).trans (by rw [Complex.exp_pi_mul_I]))

/-- `e^{2πi (k + 1) (1/2)} = -(-1)^k` for a natural number `k`. -/
theorem exp_half_succ (k : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ℤ) + 1 : ℤ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) =
      -((-1 : ℂ) ^ k) := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * (((k : ℤ) + 1 : ℤ) : ℂ) * ((1 / 2 : ℝ) : ℂ) =
      (Real.pi : ℂ) * Complex.I + (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  have hpi : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  first
    | (rw [h, Complex.exp_add, hpi, exp_nat_mul_pi_I]
       ring)
    | rw [h, Complex.exp_add, hpi, exp_nat_mul_pi_I, neg_one_mul]
    | (have e := congrArg Complex.exp h
       rw [Complex.exp_add, hpi, exp_nat_mul_pi_I, neg_one_mul] at e
       exact e)

/-- `e^{2πi (-k) (1/2)} = (-1)^k` for a natural number `k`, with `-k` written `-(k + 1) + 1`. -/
theorem exp_half_neg (k : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((-((k : ℤ) + 1) + 1 : ℤ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) =
      (-1 : ℂ) ^ k := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((-((k : ℤ) + 1) + 1 : ℤ) : ℂ) * ((1 / 2 : ℝ) : ℂ) =
      (k : ℂ) * ((Real.pi : ℂ) * Complex.I) +
        ((-(k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  have h1 : Complex.exp (((-(k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))
  first
    | rw [h, Complex.exp_add, h1, mul_one, exp_nat_mul_pi_I]
    | (have e := congrArg Complex.exp h
       rw [Complex.exp_add, h1, mul_one, exp_nat_mul_pi_I] at e
       exact e)

/-- The summand of the series of C5a (`hasSum_zakA0`). -/
def zakA0Term (n : ℤ) : ℂ :=
  2 * (Real.pi : ℂ) * (n : ℂ) *
    (((gauss (1 / 2 - (n : ℝ)) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * ((1 / 2 : ℝ) : ℂ)))

/-- C5a in terms of `zakA0Term`. -/
theorem hasSum_zakA0Term : HasSum zakA0Term zakA0 := by
  first
    | exact hasSum_zakA0
    | (unfold zakA0Term
       exact hasSum_zakA0)
    | (delta zakA0Term
       exact hasSum_zakA0)

/-- The summands at `n = k + 1` and at `n = -k` add up to the `k`-th term of the folded series. -/
theorem zakA0Term_fold (k : ℕ) :
    zakA0Term ((k : ℤ) + 1) + zakA0Term (-((k : ℤ) + 1) + 1) =
      ((-(4 * Real.pi) * ((-1) ^ k * (((k : ℝ) + 1 / 2) * gauss ((k : ℝ) + 1 / 2))) : ℝ) : ℂ) := by
  have hx1 : (1 / 2 : ℝ) - (((k : ℤ) + 1 : ℤ) : ℝ) = -((k : ℝ) + 1 / 2) := by
    push_cast
    ring
  have hx2 : (1 / 2 : ℝ) - ((-((k : ℤ) + 1) + 1 : ℤ) : ℝ) = (k : ℝ) + 1 / 2 := by
    push_cast
    ring
  have g1 : gauss (1 / 2 - (((k : ℤ) + 1 : ℤ) : ℝ)) = gauss ((k : ℝ) + 1 / 2) := by
    rw [hx1]
    exact gauss_neg _
  have g2 : gauss (1 / 2 - ((-((k : ℤ) + 1) + 1 : ℤ) : ℝ)) = gauss ((k : ℝ) + 1 / 2) := by
    rw [hx2]
  first
    | (unfold zakA0Term
       rw [exp_half_succ k, exp_half_neg k, g1, g2]
       push_cast
       ring)
    | (simp only [zakA0Term, exp_half_succ k, exp_half_neg k, g1, g2]
       push_cast
       ring)
    | (unfold zakA0Term
       rw [exp_half_succ k, exp_half_neg k, g1, g2]
       push_cast
       generalize (-1 : ℂ) ^ k = s
       ring)

/-- The folded series, the second statement of roadmap item C5b:
`A₀ = -4π ∑_{k ≥ 0} (-1)^k (k + 1/2) gauss (k + 1/2)`. -/
theorem hasSum_zakA0_nat :
    HasSum (fun k : ℕ =>
        ((-(4 * Real.pi) * ((-1) ^ k * (((k : ℝ) + 1 / 2) * gauss ((k : ℝ) + 1 / 2))) : ℝ) : ℂ))
      zakA0 := by
  have h := (Equiv.addRight (1 : ℤ)).hasSum_iff.mpr hasSum_zakA0Term
  have hshift : (fun m : ℤ => zakA0Term (m + 1)) = zakA0Term ∘ ⇑(Equiv.addRight (1 : ℤ)) := by
    first
      | rfl
      | (funext m
         simp only [Function.comp_apply, Equiv.coe_addRight])
      | (funext m
         rw [Function.comp_apply, Equiv.coe_addRight])
  have h1 : HasSum (fun m : ℤ => zakA0Term (m + 1)) zakA0 := by
    first
      | (rw [hshift]
         exact h)
      | exact hshift ▸ h
  have h2 := h1.nat_add_neg_add_one
  have hfun : (fun k : ℕ =>
      ((-(4 * Real.pi) * ((-1) ^ k * (((k : ℝ) + 1 / 2) * gauss ((k : ℝ) + 1 / 2))) : ℝ) : ℂ)) =
      fun k : ℕ => zakA0Term ((k : ℤ) + 1) + zakA0Term (-((k : ℤ) + 1) + 1) :=
    funext fun k => (zakA0Term_fold k).symm
  first
    | (rw [hfun]
       exact h2)
    | exact hfun ▸ h2

/-- `zakA0` as a `tsum` over `ℕ`. -/
theorem zakA0_eq_tsum_nat :
    zakA0 = ∑' k : ℕ,
      ((-(4 * Real.pi) * ((-1) ^ k * (((k : ℝ) + 1 / 2) * gauss ((k : ℝ) + 1 / 2))) : ℝ) : ℂ) :=
  hasSum_zakA0_nat.tsum_eq.symm

/-- The same series, as a series of real numbers, sums to the real part of `zakA0`. -/
theorem hasSum_zakA0_re :
    HasSum (fun k : ℕ =>
        -(4 * Real.pi) * ((-1) ^ k * (((k : ℝ) + 1 / 2) * gauss ((k : ℝ) + 1 / 2))))
      zakA0.re := by
  have h := Complex.hasSum_re hasSum_zakA0_nat
  first
    | (simp only [Complex.ofReal_re] at h
       exact h)
    | simpa using h

end BLT

end
