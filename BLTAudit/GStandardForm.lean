import BLTAudit.UnitaryDFT
import BLTAudit.TimeFrequency
import BLTAudit.FiniteZak

/-!
# A6. The standard form of `G_N`

The paper (§1) writes `E_N(f) = ⟨f, G_N f⟩` with `G_N = D*D + F*D*DF`, and states that in standard
coordinates `(G_N f)(j) = (4 − 2 cos(2πj/N)) f(j) − f(j−1) − f(j+1)`. This file proves that the
energy `energy f = ‖D f‖² + ‖D F f‖²` of `BLTAudit/Basic.lean` equals `⟨f, gStd f⟩`:

* `normSq_one_sub_stdAddChar`: `|1 − e^{2πij/N}|² = 2 − 2 cos(2πj/N)`;
* `energy_eq_ip_gStd`: `(energy f : ℂ) = ip f (gStd f)`;
* `energy_eq_re_ip_gStd`, `im_ip_gStd`: `energy f = Re ⟨f, gStd f⟩` and `Im ⟨f, gStd f⟩ = 0`.

What this file does NOT prove: anything about the ground state of `G_N` (items D2–D4), the Zak
energy identity (A7), or anything toward Theorem 1.1 or Theorem 4.1.
-/

noncomputable section

open Finset Complex
open scoped ComplexConjugate Real

namespace BLT

variable {N : ℕ} [NeZero N]

/-- `e^{2πij/N} + e^{-2πij/N} = 2 cos(2πj/N)`. -/
theorem stdAddChar_add_neg (j : ZMod N) :
    ZMod.stdAddChar j + ZMod.stdAddChar (-j) =
      ((2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ)) : ℝ) : ℂ) := by
  have h1 : ZMod.stdAddChar j = Complex.exp (2 * π * I * (j.val : ℂ) / N) := by
    rw [← stdAddChar_natCast, ZMod.natCast_zmod_val]
  have h2 : ZMod.stdAddChar (-j) = Complex.exp (-(2 * π * I * (j.val : ℂ) / N)) := by
    have := ZMod.stdAddChar_coe (N := N) (-(j.val : ℤ))
    rw [Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val] at this
    rw [this]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  push_cast
  rw [Complex.two_cos]
  congr 1 <;> congr 1 <;> ring

/-- `|1 − e^{2πij/N}|² = 2 − 2 cos(2πj/N)`, as a complex identity. -/
theorem normSq_one_sub_stdAddChar (j : ZMod N) :
    conj (1 - ZMod.stdAddChar j) * (1 - ZMod.stdAddChar j) =
      ((2 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ)) : ℝ) : ℂ) := by
  have hm : ZMod.stdAddChar (-j) * ZMod.stdAddChar j = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hs := stdAddChar_add_neg j
  rw [map_sub, map_one, conj_stdAddChar]
  push_cast at hs ⊢
  linear_combination hm - hs

/-- `∑_j ‖g j‖² = ∑_j conj (g j) * g j` in `ℂ`. -/
theorem sum_norm_sq_eq (g : ZMod N → ℂ) :
    ((∑ j : ZMod N, ‖g j‖ ^ 2 : ℝ) : ℂ) = ∑ j : ZMod N, conj (g j) * g j := by
  push_cast
  exact Finset.sum_congr rfl fun j _ => (Complex.conj_mul' (g j)).symm

/-- **A6.** The energy is the quadratic form of `gStd`. -/
theorem energy_eq_ip_gStd (f : ZMod N → ℂ) : (energy f : ℂ) = ip f (gStd f) := by
  have hF : ∑ k : ZMod N, ‖diffOp (dftU f) k‖ ^ 2 = ∑ j : ZMod N, ‖f j - modul f j‖ ^ 2 := by
    rw [diffOp_dftU, parseval_dftU]
    rfl
  have shift1 : ∑ j : ZMod N, conj (f (j + 1)) * f (j + 1) = ∑ j : ZMod N, conj (f j) * f j :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) (fun j => conj (f j) * f j)
  have shift2 : ∑ j : ZMod N, conj (f (j + 1)) * f j = ∑ j : ZMod N, conj (f j) * f (j - 1) := by
    have := Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) (fun j => conj (f j) * f (j - 1))
    simpa only [Equiv.coe_addRight, add_sub_cancel_right] using this
  have hc : ∀ j : ZMod N, conj (f j - ZMod.stdAddChar j * f j) * (f j - ZMod.stdAddChar j * f j) =
      ((2 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ)) : ℝ) : ℂ) * (conj (f j) * f j) := by
    intro j
    rw [← normSq_one_sub_stdAddChar j, map_sub, map_mul, map_sub, map_one]
    ring
  have key : ∑ j : ZMod N, conj (f j - f (j + 1)) * (f j - f (j + 1)) =
      ∑ j : ZMod N, (2 * (conj (f j) * f j) - conj (f j) * f (j + 1) - conj (f j) * f (j - 1)) := by
    have e : ∀ j : ZMod N, conj (f j - f (j + 1)) * (f j - f (j + 1)) =
        (2 * (conj (f j) * f j) - conj (f j) * f (j + 1) - conj (f j) * f (j - 1)) +
          (conj (f (j + 1)) * f (j + 1) - conj (f j) * f j) -
          (conj (f (j + 1)) * f j - conj (f j) * f (j - 1)) := by
      intro j
      rw [map_sub]
      ring
    simp_rw [e]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, shift1, shift2]
    ring
  unfold energy
  rw [hF, Complex.ofReal_add, sum_norm_sq_eq, sum_norm_sq_eq]
  simp only [diffOp_apply, modul_apply]
  simp_rw [hc]
  rw [key, ← Finset.sum_add_distrib]
  unfold ip gStd
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- **A6.** `energy f = Re ⟨f, gStd f⟩`. -/
theorem energy_eq_re_ip_gStd (f : ZMod N → ℂ) : energy f = (ip f (gStd f)).re := by
  rw [← energy_eq_ip_gStd, Complex.ofReal_re]

/-- **A6.** `⟨f, gStd f⟩` is real. -/
theorem im_ip_gStd (f : ZMod N → ℂ) : (ip f (gStd f)).im = 0 := by
  rw [← energy_eq_ip_gStd, Complex.ofReal_im]

end BLT

end
