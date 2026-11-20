import BLTAudit.Basic

/-!
# A3b. The finite Zak transform of a translate

For `f : ZMod (d * d) → ℂ`, `T = transl` and
`zak f q r = d^{-1/2} ∑_b e^{2πiqb/d} f(b d + r)` of `BLTAudit/Basic.lean` (paper §2):

* `zak_transl_of_lt`: `zak (T f) q r = zak f q (r + 1)` when `r.val + 1 < d`;
* `zak_transl_seam`: `zak (T f) q r = e^{-2πiq/d} zak f q 0` when `r.val + 1 = d` (the seam:
  `b d + r + 1 = (b + 1) d`, and the term with `b.val + 1 = d` wraps to index `0` because
  `d * d = 0` in `ZMod (d * d)`).

What this file does NOT prove: the norm identity for `zak` (A3a,
`BLTAudit/FiniteZakUnitary.lean`), the behaviour of `zak` under modulation (A3c), the critical
Gabor criterion `|Z f| = 1/d` (A4, A5), the energy identity (A7), or anything toward
Theorem 1.1 or Theorem 4.1.
-/

noncomputable section

open Finset Complex
open scoped Real

namespace BLT

variable {d : ℕ} [NeZero d]

/-- **A3b.** Away from the seam, translation shifts the second Zak variable. -/
theorem zak_transl_of_lt (f : ZMod (d * d) → ℂ) (q r : ZMod d) (hr : r.val + 1 < d) :
    zak (transl f) q r = zak f q (r + 1) := by
  have h1 : (1 : ZMod d).val = 1 := ZMod.val_one'' (by omega)
  have hv : (r + 1).val = r.val + 1 := by
    rw [ZMod.val_add_of_lt (by rw [h1]; exact hr), h1]
  simp only [zak, transl_apply, hv]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring_nf

/-- **A3b, the seam.** At `r = d - 1`, translation wraps to `r = 0` with the factor
`e^{-2πiq/d}`. -/
theorem zak_transl_seam (f : ZMod (d * d) → ℂ) (q r : ZMod d) (hr : r.val + 1 = d) :
    zak (transl f) q r = ZMod.stdAddChar (-q) * zak f q 0 := by
  have key : ∀ b : ZMod d,
      ((b.val * d + r.val : ℕ) : ZMod (d * d)) + 1 = (((b + 1).val * d + (0 : ZMod d).val : ℕ) :
        ZMod (d * d)) := by
    intro b
    rw [← Nat.cast_one (R := ZMod (d * d)), ← Nat.cast_add, ZMod.natCast_eq_natCast_iff',
      ZMod.val_zero, add_zero, ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod,
      ← Nat.mul_mod_mul_right, Nat.mod_mod]
    congr 1
    rw [add_assoc, hr]
    ring
  simp only [zak, transl_apply, key]
  rw [mul_left_comm (ZMod.stdAddChar (-q))]
  congr 1
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.addRight (1 : ZMod d)) _ _ fun b => ?_)
  simp only [Equiv.coe_addRight]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

end BLT

end
