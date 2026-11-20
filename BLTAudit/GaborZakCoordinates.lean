import BLTAudit.FiniteZakUnitary
import BLTAudit.FiniteZakModulation
import BLTAudit.GaborFormula

/-!
# A4b. Gabor vectors in Zak coordinates

For `f : ZMod (d * d) → ℂ`, the index map `zakIndex d (b, r) = b d + r` of A3a and the closed
form `gabor_apply` of A4a (paper §2):

* `zakIndex_add_natCast_mul`: `zakIndex d (b, r) + n d = zakIndex d (b + n, r)` in
  `ZMod (d * d)`, where `b + n` is taken in `ZMod d` (it wraps modulo `d`);
* `stdAddChar_natCast_mul_self`: the character of `ZMod (d * d)` at `k d` is the character of
  `ZMod d` at `k`;
* `stdAddChar_mul_zakIndex`: the character of `ZMod (d * d)` at `(m d) · zakIndex d (b, r)` is
  the character of `ZMod d` at `m · r`;
* `gabor_zakIndex`: `gabor f n m (zakIndex d (b, r)) = e^{2πi m r / d} f (zakIndex d (b + n, r))`.

What this file does NOT prove: the Zak correlation identity (A4c), the orthonormality of the
Gabor system under `|Z f| = 1/d` (A4d), that it is a basis (A4e), the converse (A5), or anything
toward Theorem 1.1 or Theorem 4.1.
-/

noncomputable section

namespace BLT

variable {d : ℕ} [NeZero d]

/-- Adding `n d` to a Zak index shifts the block variable `b` by `n` (modulo `d`). -/
theorem zakIndex_add_natCast_mul (n : ℕ) (b r : ZMod d) :
    zakIndex d (b, r) + ((n * d : ℕ) : ZMod (d * d)) = zakIndex d (b + (n : ZMod d), r) := by
  simp only [zakIndex]
  rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff', ZMod.val_add]
  first
    | rw [ZMod.val_natCast]
    | simp only [ZMod.val_natCast]
  rw [Nat.add_mod_mod, ← Nat.mul_mod_mul_right, Nat.mod_add_mod]
  congr 1
  ring

/-- The character of `ZMod (d * d)` at `k d` is the character of `ZMod d` at `k`. -/
theorem stdAddChar_natCast_mul_self (k : ℕ) :
    ZMod.stdAddChar ((k * d : ℕ) : ZMod (d * d)) = ZMod.stdAddChar ((k : ℕ) : ZMod d) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [stdAddChar_natCast, stdAddChar_natCast]
  congr 1
  push_cast
  first
    | (field_simp; ring)
    | field_simp
    | rw [← mul_assoc, mul_div_mul_right _ _ hd]
    | (rw [div_eq_div_iff (mul_ne_zero hd hd) hd]; ring)

/-- The character of `ZMod (d * d)` at `(m d) · (b d + r)` is the character of `ZMod d` at
`m · r`. -/
theorem stdAddChar_mul_zakIndex (m : ℕ) (b r : ZMod d) :
    ZMod.stdAddChar (((m * d : ℕ) : ZMod (d * d)) * zakIndex d (b, r)) =
      ZMod.stdAddChar ((m : ZMod d) * r) := by
  have hdd : ((d * d : ℕ) : ZMod (d * d)) = 0 := by
    first
      | exact ZMod.natCast_self (d * d)
      | exact CharP.cast_eq_zero (ZMod (d * d)) (d * d)
  have e : m * d * (b.val * d + r.val) = m * b.val * (d * d) + m * r.val * d := by ring
  have h1 : ((m * d : ℕ) : ZMod (d * d)) * zakIndex d (b, r) =
      ((m * r.val * d : ℕ) : ZMod (d * d)) := by
    simp only [zakIndex]
    rw [← Nat.cast_mul, e, Nat.cast_add, Nat.cast_mul (m * b.val) (d * d), hdd, mul_zero,
      zero_add]
  have h2 : (m : ZMod d) * r = ((m * r.val : ℕ) : ZMod d) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [h1, h2, stdAddChar_natCast_mul_self]

/-- **A4b.** The Gabor vectors in Zak coordinates. -/
theorem gabor_zakIndex (f : ZMod (d * d) → ℂ) (n m : ℕ) (b r : ZMod d) :
    gabor f n m (zakIndex d (b, r)) =
      ZMod.stdAddChar ((m : ZMod d) * r) * f (zakIndex d (b + (n : ZMod d), r)) := by
  rw [gabor_apply, zakIndex_add_natCast_mul, stdAddChar_mul_zakIndex]

end BLT

end
