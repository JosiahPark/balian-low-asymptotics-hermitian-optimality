import BLTAudit.Basic
import BLTAudit.ZakZero
import BLTAudit.ZakDerivFold

/-!
# C5c. The terms of the series of `A₀` are positive and strictly decreasing, (A10) (Appendix A.3)

C5b (`BLTAudit/ZakDerivFold.lean`) wrote `zakA0`, the `x`-derivative of `gaussZak` at its zero
`(1/2, 1/2)`, as `A₀ = -4π ∑_{k ≥ 0} (-1)^k a k` with `a k = (k + 1/2) * gauss (k + 1/2)` and
`gauss x = 2^{1/4} e^{-πx²}`. This file defines `zakA0Coeff k = (k + 1/2) * gauss (k + 1/2)`, a
real number, and proves the statement of roadmap item C5c:

* `zakA0Coeff_pos`: `0 < zakA0Coeff k` for every `k : ℕ`.
* `zakA0Coeff_succ_lt`: `zakA0Coeff (k + 1) < zakA0Coeff k` for every `k : ℕ`.

Proof of the second: `gauss (t + 1) = e^{-π(2t + 1)} * gauss t` (`gauss_add_one`); at
`t = k + 1/2` the factor is `e^{-2π(k + 1)} ≤ e^{-2π} < 1/3` (`exp_neg_two_pi_lt`, from
`x + 1 ≤ e^x` and `3 < π`), and `(k + 3/2) / 3 ≤ k + 1/2`.

Also proved: `zakA0Coeff_succ_le` (the same with `≤`), `strictAnti_zakA0Coeff`
(`StrictAnti zakA0Coeff`) and `hasSum_zakA0_re_coeff`, which is `hasSum_zakA0_re` of C5b written
with `zakA0Coeff`: `HasSum (fun k : ℕ => -(4 * π) * ((-1) ^ k * zakA0Coeff k)) zakA0.re`.

Conventions: nothing in the paper's conventions had to be changed.

What this file does NOT prove: the alternating-series bound, and hence `zakA0 ≠ 0` (C5d); any
numerical value or bound for `zakA0`; that `zakA0` is a real number; or any estimate of the
paper. It proves nothing toward Theorem 1.1 or Theorem 4.1, and nothing toward the hypotheses
[HU] and [HL].
-/

noncomputable section

namespace BLT

/-- `gauss (t + 1) = e^{-π(2t + 1)} * gauss t`. -/
theorem gauss_add_one (t : ℝ) :
    gauss (t + 1) = Real.exp (-Real.pi * (2 * t + 1)) * gauss t := by
  have h : -Real.pi * (t + 1) ^ 2 = -Real.pi * (2 * t + 1) + -Real.pi * t ^ 2 := by ring
  first
    | (unfold gauss
       rw [h, Real.exp_add]
       ring)
    | (simp only [gauss, h, Real.exp_add]
       ring)

/-- `e^{-2π} < 1/3`, from `x + 1 ≤ e^x` and `3 < π`. -/
theorem exp_neg_two_pi_lt : Real.exp (-(2 * Real.pi)) < 1 / 3 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h1 : 2 * Real.pi + 1 ≤ Real.exp (2 * Real.pi) := Real.add_one_le_exp (2 * Real.pi)
  have h7 : (3 : ℝ) < Real.exp (2 * Real.pi) := by linarith
  have he : 0 < Real.exp (-(2 * Real.pi)) := Real.exp_pos _
  have h3 : Real.exp (-(2 * Real.pi)) * Real.exp (2 * Real.pi) = 1 := by
    first
      | rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      | (rw [← Real.exp_add]
         simp)
  have h4 : 0 < Real.exp (-(2 * Real.pi)) * (Real.exp (2 * Real.pi) - 3) :=
    mul_pos he (sub_pos.mpr h7)
  first
    | linarith [h3, h4]
    | nlinarith [h3, h4]

/-- The term `a k = (k + 1/2) * gauss (k + 1/2)` of the folded series of C5b. -/
def zakA0Coeff (k : ℕ) : ℝ := ((k : ℝ) + 1 / 2) * gauss ((k : ℝ) + 1 / 2)

/-- The terms are positive, the first statement of roadmap item C5c. -/
theorem zakA0Coeff_pos (k : ℕ) : 0 < zakA0Coeff k := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by linarith
  first
    | (unfold zakA0Coeff
       exact mul_pos hpos (gauss_pos _))
    | exact mul_pos hpos (gauss_pos _)

/-- The terms are strictly decreasing, the second statement of roadmap item C5c. -/
theorem zakA0Coeff_succ_lt (k : ℕ) : zakA0Coeff (k + 1) < zakA0Coeff k := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hg : 0 < gauss ((k : ℝ) + 1 / 2) := gauss_pos _
  have hcast : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by
    first
      | (push_cast
         ring)
      | push_cast
  have hstep : gauss (((k : ℝ) + 1 / 2) + 1) =
      Real.exp (-Real.pi * (2 * ((k : ℝ) + 1 / 2) + 1)) * gauss ((k : ℝ) + 1 / 2) :=
    gauss_add_one _
  have hpik : 0 ≤ Real.pi * (k : ℝ) := mul_nonneg Real.pi_pos.le hk
  have hle : -Real.pi * (2 * ((k : ℝ) + 1 / 2) + 1) ≤ -(2 * Real.pi) := by
    first
      | linarith [hpik]
      | nlinarith [hpik]
  have hE : Real.exp (-Real.pi * (2 * ((k : ℝ) + 1 / 2) + 1)) < 1 / 3 :=
    lt_of_le_of_lt (Real.exp_le_exp.mpr hle) exp_neg_two_pi_lt
  have hprod : 0 < (((k : ℝ) + 1 / 2) + 1) *
      (1 / 3 - Real.exp (-Real.pi * (2 * ((k : ℝ) + 1 / 2) + 1))) :=
    mul_pos (by linarith) (sub_pos.mpr hE)
  have h1 : (((k : ℝ) + 1 / 2) + 1) * Real.exp (-Real.pi * (2 * ((k : ℝ) + 1 / 2) + 1)) <
      (k : ℝ) + 1 / 2 := by
    first
      | linarith [hprod, hk]
      | nlinarith [hprod, hk]
  have h2 : 0 < ((k : ℝ) + 1 / 2 -
      (((k : ℝ) + 1 / 2) + 1) * Real.exp (-Real.pi * (2 * ((k : ℝ) + 1 / 2) + 1))) *
        gauss ((k : ℝ) + 1 / 2) :=
    mul_pos (sub_pos.mpr h1) hg
  have hval : zakA0Coeff (k + 1) = (((k : ℝ) + 1 / 2) + 1) *
      (Real.exp (-Real.pi * (2 * ((k : ℝ) + 1 / 2) + 1)) * gauss ((k : ℝ) + 1 / 2)) := by
    first
      | (unfold zakA0Coeff
         rw [hcast, hstep])
      | simp only [zakA0Coeff, hcast, hstep]
  have hval0 : zakA0Coeff k = ((k : ℝ) + 1 / 2) * gauss ((k : ℝ) + 1 / 2) := rfl
  rw [hval, hval0]
  first
    | linarith [h2]
    | nlinarith [h2]

/-- The terms are decreasing, in the form used by the alternating-series bound of C5d. -/
theorem zakA0Coeff_succ_le (k : ℕ) : zakA0Coeff (k + 1) ≤ zakA0Coeff k :=
  (zakA0Coeff_succ_lt k).le

/-- The terms form a strictly decreasing sequence. -/
theorem strictAnti_zakA0Coeff : StrictAnti zakA0Coeff :=
  strictAnti_nat_of_succ_lt zakA0Coeff_succ_lt

/-- `hasSum_zakA0_re` of C5b, written with `zakA0Coeff`. -/
theorem hasSum_zakA0_re_coeff :
    HasSum (fun k : ℕ => -(4 * Real.pi) * ((-1) ^ k * zakA0Coeff k)) zakA0.re := by
  first
    | exact hasSum_zakA0_re
    | (unfold zakA0Coeff
       exact hasSum_zakA0_re)
    | (simp only [zakA0Coeff]
       exact hasSum_zakA0_re)

end BLT

end
