import BLTAudit.Basic

/-!
# A3c. The finite Zak transform of a modulate

For `f : ZMod (d * d) → ℂ`, `M = modul` and
`zak f q r = d^{-1/2} ∑_b e^{2πiqb/d} f(b d + r)` of `BLTAudit/Basic.lean` (paper §2):

* `stdAddChar_natCast`: `ZMod.stdAddChar (n : ZMod N) = e^{2πi n/N}` for a natural number `n`;
* `zak_modul`: `zak (M f) q r = e^{2πi r/d²} zak f (q + 1) r`, because the character of
  `ZMod (d * d)` at `b d + r` is `e^{2πi b/d} · e^{2πi r/d²}`.

The factor is written `Complex.exp (2 * π * I * r.val / d ^ 2)`. It is the value `mag d r.val`
of `BLTAudit/Basic.lean`, but that identification (a cast of `r.val` through `ℤ`) is not stated
as a lemma here.

What this file does NOT prove: the norm identity for `zak` (A3a), its behaviour under
translation (A3b), the critical Gabor criterion `|Z f| = 1/d` (A4, A5), the energy identity
(A7), or anything toward Theorem 1.1 or Theorem 4.1.
-/

noncomputable section

open Finset Complex
open scoped Real

namespace BLT

variable {d : ℕ} [NeZero d]

/-- The standard character at a natural number. -/
theorem stdAddChar_natCast {N : ℕ} [NeZero N] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod N) = Complex.exp (2 * π * I * n / N) := by
  have h := ZMod.stdAddChar_coe (N := N) (n : ℤ)
  simpa using h

/-- **A3c.** Modulation shifts the first Zak variable, with the phase `e^{2πi r/d²}`. -/
theorem zak_modul (f : ZMod (d * d) → ℂ) (q r : ZMod d) :
    zak (modul f) q r =
      Complex.exp (2 * π * I * (r.val : ℂ) / ((d : ℂ) ^ 2)) * zak f (q + 1) r := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [zak, modul_apply]
  rw [mul_left_comm (Complex.exp _)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb : ZMod.stdAddChar ((q + 1) * b) =
      ZMod.stdAddChar (q * b) * Complex.exp (2 * π * I * (b.val : ℂ) / d) := by
    rw [add_mul, one_mul, AddChar.map_add_eq_mul, ← stdAddChar_natCast, ZMod.natCast_zmod_val]
  rw [hb, stdAddChar_natCast]
  have he : Complex.exp (2 * π * I * ((b.val * d + r.val : ℕ) : ℂ) / ((d * d : ℕ) : ℂ)) =
      Complex.exp (2 * π * I * (r.val : ℂ) / ((d : ℂ) ^ 2)) *
        Complex.exp (2 * π * I * (b.val : ℂ) / d) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [he]
  ring

end BLT

end
