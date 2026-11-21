import BLTAudit.Basic
import BLTAudit.ZakConformal
import BLTAudit.ZakDerivFold
import BLTAudit.ZakDerivTerms

/-!
# C5d. The alternating-series bound and `A₀ ≠ 0`, (A10) (§3.1, Appendix A.3)

`zakA0` of C4 (`BLTAudit/ZakConformal.lean`) is the `x`-derivative of `gaussZak` at its zero
`(1/2, 1/2)`, the number `A₀` of (A10). C5b and C5c wrote its real part as
`zakA0.re = -4π ∑_{k ≥ 0} (-1)^k a k` with `a k = zakA0Coeff k = (k + 1/2) * gauss (k + 1/2)`,
positive and strictly decreasing. This file proves the two statements of roadmap item C5d:

* `le_hasSum_alternating`: if `a : ℕ → ℝ` satisfies `a (k + 1) ≤ a k` for all `k` and
  `HasSum (fun k => (-1) ^ k * a k) S`, then `a 0 - a 1 ≤ S`.
* `zakA0_ne_zero`: `zakA0 ≠ 0`.

Proof of the first: a summable real series may be summed in consecutive pairs (`hasSum_pairs`:
`HasSum f S → HasSum (fun k => f (2 * k) + f (2 * k + 1)) S`, from Mathlib's
`Summable.comp_injective` and `HasSum.even_add_odd`); the pairs of the alternating series are
`a (2k) - a (2k + 1) ≥ 0`, and the pair at `k = 0` is `a 0 - a 1` (Mathlib's `le_hasSum`). The
roadmap hint argues with the even partial sums instead; `HasSum` on `ℝ` is unconditional
summation, so the regrouping is available and the limit of partial sums is not needed.

Proof of the second: `hasSum_alternating_zakA0Coeff` divides the series of C5c by `-4π`; the
bound then gives `zakA0_re_le`, `zakA0.re ≤ -4π (a 0 - a 1)`, and `a 1 < a 0` (C5c) gives
`zakA0_re_neg`, `zakA0.re < 0`.

Also proved: `deriv_gaussZak_fst_zero_ne_zero` and `deriv_gaussZak_snd_zero_ne_zero`, the two
one-variable derivatives of `gaussZak` at `(1/2, 1/2)` are nonzero (they are `zakA0` and
`I * zakA0` by C4).

Conventions: nothing in the paper's conventions had to be changed.

What this file does NOT prove: the upper bound `S ≤ a 0` or convergence of an alternating series
that is not summable in Mathlib's unconditional sense; that `zakA0` is a real number (only its
real part is bounded); any numerical value of `zakA0`; that the zero of `gaussZak` at
`(1/2, 1/2)` is its only zero in the unit square; the expansion (U2) with its error term; or any
estimate of the paper. It proves nothing toward Theorem 1.1 or Theorem 4.1, and nothing toward
the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

/-- A summable real series may be summed in consecutive pairs. -/
theorem hasSum_pairs {f : ℕ → ℝ} {S : ℝ} (hf : HasSum f S) :
    HasSum (fun k : ℕ => f (2 * k) + f (2 * k + 1)) S := by
  have hinj0 : Function.Injective (fun k : ℕ => 2 * k) := by
    intro m n hmn
    have h' : 2 * m = 2 * n := hmn
    omega
  have hinj1 : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro m n hmn
    have h' : 2 * m + 1 = 2 * n + 1 := hmn
    omega
  have he' : Summable (fun k : ℕ => f (2 * k)) := hf.summable.comp_injective hinj0
  have ho' : Summable (fun k : ℕ => f (2 * k + 1)) := hf.summable.comp_injective hinj1
  obtain ⟨Se, he⟩ := he'
  obtain ⟨So, ho⟩ := ho'
  have hS : S = Se + So := hf.unique (he.even_add_odd ho)
  have hadd : HasSum (fun k : ℕ => f (2 * k) + f (2 * k + 1)) (Se + So) := he.add ho
  first
    | (rw [hS]
       exact hadd)
    | exact hS ▸ hadd

/-- The alternating-series bound, the first statement of roadmap item C5d: for a decreasing
sequence `a` whose alternating series has sum `S`, `a 0 - a 1 ≤ S`. -/
theorem le_hasSum_alternating {a : ℕ → ℝ} {S : ℝ} (hanti : ∀ k : ℕ, a (k + 1) ≤ a k)
    (h : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * a k) S) : a 0 - a 1 ≤ S := by
  have hterm : ∀ k : ℕ,
      (-1 : ℝ) ^ (2 * k) * a (2 * k) + (-1 : ℝ) ^ (2 * k + 1) * a (2 * k + 1) =
        a (2 * k) - a (2 * k + 1) := by
    intro k
    have h1 : (-1 : ℝ) ^ (2 * k) = 1 := by
      first
        | rw [pow_mul, neg_one_sq, one_pow]
        | exact Even.neg_one_pow (even_two_mul k)
        | simp
    have h2 : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
      first
        | rw [pow_succ, h1, one_mul]
        | exact Odd.neg_one_pow (odd_two_mul_add_one k)
        | simp
    rw [h1, h2]
    ring
  have hp : HasSum (fun k : ℕ =>
      (-1 : ℝ) ^ (2 * k) * a (2 * k) + (-1 : ℝ) ^ (2 * k + 1) * a (2 * k + 1)) S :=
    hasSum_pairs h
  have hfun : (fun k : ℕ =>
      (-1 : ℝ) ^ (2 * k) * a (2 * k) + (-1 : ℝ) ^ (2 * k + 1) * a (2 * k + 1)) =
      fun k : ℕ => a (2 * k) - a (2 * k + 1) := funext hterm
  have hp' : HasSum (fun k : ℕ => a (2 * k) - a (2 * k + 1)) S := by
    first
      | (rw [hfun] at hp
         exact hp)
      | exact hfun ▸ hp
      | simpa only [hterm] using hp
  have h0 : a (2 * 0) - a (2 * 0 + 1) ≤ S :=
    le_hasSum hp' 0 (fun j _ => sub_nonneg.mpr (hanti (2 * j)))
  first
    | simpa using h0
    | exact h0

/-- The series of C5c divided by `-4π`: the alternating series of the terms `zakA0Coeff k`. -/
theorem hasSum_alternating_zakA0Coeff :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * zakA0Coeff k) ((-(4 * Real.pi))⁻¹ * zakA0.re) := by
  have hneg : -(4 * Real.pi) < 0 := by linarith [Real.pi_pos]
  have hne : -(4 * Real.pi) ≠ 0 := hneg.ne
  have h : HasSum (fun k : ℕ =>
      (-(4 * Real.pi))⁻¹ * (-(4 * Real.pi) * ((-1 : ℝ) ^ k * zakA0Coeff k)))
      ((-(4 * Real.pi))⁻¹ * zakA0.re) :=
    hasSum_zakA0_re_coeff.mul_left ((-(4 * Real.pi))⁻¹)
  have hfun : (fun k : ℕ =>
      (-(4 * Real.pi))⁻¹ * (-(4 * Real.pi) * ((-1 : ℝ) ^ k * zakA0Coeff k))) =
      fun k : ℕ => (-1 : ℝ) ^ k * zakA0Coeff k :=
    funext fun k => inv_mul_cancel_left₀ hne _
  first
    | (rw [hfun] at h
       exact h)
    | exact hfun ▸ h
    | simpa only [inv_mul_cancel_left₀ hne] using h

/-- `zakA0.re ≤ -4π (a 0 - a 1)` with `a k = zakA0Coeff k`. -/
theorem zakA0_re_le : zakA0.re ≤ -(4 * Real.pi) * (zakA0Coeff 0 - zakA0Coeff 1) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hneg : -(4 * Real.pi) < 0 := by linarith
  have hb : zakA0Coeff 0 - zakA0Coeff 1 ≤ (-(4 * Real.pi))⁻¹ * zakA0.re :=
    le_hasSum_alternating (a := zakA0Coeff) zakA0Coeff_succ_le hasSum_alternating_zakA0Coeff
  have hc : -(4 * Real.pi) * ((-(4 * Real.pi))⁻¹ * zakA0.re) = zakA0.re := by
    first
      | exact mul_inv_cancel_left₀ hneg.ne _
      | field_simp
  have hm : 0 ≤ ((-(4 * Real.pi))⁻¹ * zakA0.re - (zakA0Coeff 0 - zakA0Coeff 1)) * Real.pi :=
    mul_nonneg (sub_nonneg.mpr hb) hpi.le
  first
    | linarith [hm, hc]
    | nlinarith [hm, hc]

/-- The real part of `A₀` is negative. -/
theorem zakA0_re_neg : zakA0.re < 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h01 : zakA0Coeff 1 < zakA0Coeff 0 := zakA0Coeff_succ_lt 0
  have hprod : 0 < Real.pi * (zakA0Coeff 0 - zakA0Coeff 1) := mul_pos hpi (sub_pos.mpr h01)
  have h := zakA0_re_le
  first
    | linarith [h, hprod]
    | nlinarith [h, hprod]

/-- `A₀ ≠ 0`, the second statement of roadmap item C5d and the statement of C5. -/
theorem zakA0_ne_zero : zakA0 ≠ 0 := by
  intro h0
  have hre : zakA0.re = 0 := by
    first
      | rw [h0, Complex.zero_re]
      | simp [h0]
  have hneg : zakA0.re < 0 := zakA0_re_neg
  linarith

/-- The `x`-derivative of `gaussZak` at its zero `(1/2, 1/2)` does not vanish. -/
theorem deriv_gaussZak_fst_zero_ne_zero :
    deriv (fun s : ℝ => gaussZak s (1 / 2)) (1 / 2) ≠ 0 := by
  first
    | (rw [hasDerivAt_gaussZak_fst_zero.deriv]
       exact zakA0_ne_zero)
    | exact fun h => zakA0_ne_zero (hasDerivAt_gaussZak_fst_zero.deriv.symm.trans h)

/-- The `y`-derivative of `gaussZak` at its zero `(1/2, 1/2)` does not vanish. -/
theorem deriv_gaussZak_snd_zero_ne_zero :
    deriv (fun t : ℝ => gaussZak (1 / 2) t) (1 / 2) ≠ 0 := by
  have hI : Complex.I * zakA0 ≠ 0 := mul_ne_zero Complex.I_ne_zero zakA0_ne_zero
  first
    | (rw [hasDerivAt_gaussZak_snd_zero.deriv]
       exact hI)
    | exact fun h => hI (hasDerivAt_gaussZak_snd_zero.deriv.symm.trans h)

end BLT

end
