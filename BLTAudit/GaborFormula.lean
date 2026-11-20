import BLTAudit.Basic

/-!
# A4a. Closed form of the Gabor vectors

With `T = transl`, `M = modul` and `gabor f n m = T^[n d] (M^[m d] f)` of `BLTAudit/Basic.lean`
(paper §1–§2):

* `transl_iterate_apply`: `(T^[k] f) j = f (j + k)` for `f : ZMod N → ℂ`;
* `modul_iterate_apply`: `(M^[k] f) j = e^{2πi k j / N} f j`;
* `gabor_apply`: for `f : ZMod (d * d) → ℂ` and all `n m : ℕ`,
  `gabor f n m j = e^{2πi (m d) j / d²} f (j + n d)`. The cross term `(m d)(n d)` in the
  character vanishes because `d * d = 0` in `ZMod (d * d)`.

What this file does NOT prove: anything about the Zak transform of a Gabor vector (A4b), the
orthonormality of the Gabor system or the critical criterion `|Z f| = 1/d` (A4c–A4e, A5), or
anything toward Theorem 1.1 or Theorem 4.1.
-/

noncomputable section

open Finset

namespace BLT

/-- Iterated translation: `(T^[k] f) j = f (j + k)`. -/
theorem transl_iterate_apply {N : ℕ} (f : ZMod N → ℂ) (k : ℕ) (j : ZMod N) :
    ((transl (N := N))^[k] f) j = f (j + (k : ZMod N)) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', transl_apply, ih]
    congr 1
    push_cast
    ring

/-- Iterated modulation: `(M^[k] f) j = e^{2πi k j / N} f j`. -/
theorem modul_iterate_apply {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (k : ℕ) (j : ZMod N) :
    ((modul (N := N))^[k] f) j = ZMod.stdAddChar ((k : ZMod N) * j) * f j := by
  induction k with
  | zero => simp [AddChar.map_zero_eq_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', modul_apply, ih, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    push_cast
    ring

/-- **A4a.** Closed form of the Gabor vectors `T^[n d] M^[m d] f` on `ZMod (d * d)`. -/
theorem gabor_apply {d : ℕ} [NeZero (d * d)] (f : ZMod (d * d) → ℂ) (n m : ℕ)
    (j : ZMod (d * d)) :
    gabor f n m j =
      ZMod.stdAddChar (((m * d : ℕ) : ZMod (d * d)) * j) *
        f (j + ((n * d : ℕ) : ZMod (d * d))) := by
  have hdd : ((d * d : ℕ) : ZMod (d * d)) = 0 := by
    first
      | exact ZMod.natCast_self (d * d)
      | exact CharP.cast_eq_zero (ZMod (d * d)) (d * d)
  have h : ((m * d : ℕ) : ZMod (d * d)) * ((n * d : ℕ) : ZMod (d * d)) = 0 := by
    have e : m * d * (n * d) = m * n * (d * d) := by ring
    rw [← Nat.cast_mul, e, Nat.cast_mul, hdd, mul_zero]
  unfold gabor
  rw [transl_iterate_apply, modul_iterate_apply, mul_add, h, add_zero]

end BLT

end
