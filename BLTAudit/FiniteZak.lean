import BLTAudit.UnitaryDFT

/-!
# A3. The finite Zak transform for `N = d²`

For `f : ZMod (d * d) → ℂ` and `zak f q r = d^{-1/2} ∑_b e^{2πiqb/d} f(b d + r)` (paper §2):

* `zak_eq_dftU`: for fixed `r`, `q ↦ zak f q r` is the unitary DFT on `ZMod d` of
  `b ↦ f(b d + r)`;
* `zakIndex_bijective`: `(b, r) ↦ b d + r` is a bijection `ZMod d × ZMod d → ZMod (d * d)`;
* `parseval_zak`: `∑_{q,r} ‖zak f q r‖² = ∑_j ‖f j‖²`;
* `zak_transl_of_lt`: `zak (T f) q r = zak f q (r + 1)` when `r.val + 1 < d`;
* `zak_transl_seam`: `zak (T f) q r = e^{-2πiq/d} zak f q 0` when `r.val + 1 = d` (the seam);
* `zak_modul`: `zak (M f) q r = e^{2πi r/d²} zak f (q + 1) r`.

What this file does NOT prove: the critical Gabor criterion `|Z f| = 1/d` (items A4, A5), the
energy identity (A7), or anything toward Theorem 1.1 or Theorem 4.1.
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

/-- The index map `(b, r) ↦ b d + r` of the Zak transform. -/
def zakIndex (d : ℕ) (p : ZMod d × ZMod d) : ZMod (d * d) :=
  ((p.1.val * d + p.2.val : ℕ) : ZMod (d * d))

theorem zakIndex_lt (b r : ZMod d) : b.val * d + r.val < d * d := by
  have hb := ZMod.val_lt b
  have hr := ZMod.val_lt r
  have : (b.val + 1) * d ≤ d * d := Nat.mul_le_mul_right d hb
  nlinarith

theorem zakIndex_injective : Function.Injective (zakIndex d) := by
  rintro ⟨b, r⟩ ⟨b', r'⟩ h
  simp only [zakIndex, ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt (zakIndex_lt b r), Nat.mod_eq_of_lt (zakIndex_lt b' r')] at h
  have hr : r.val = r'.val := by
    have h2 := congrArg (· % d) h
    simp only [Nat.mul_add_mod', Nat.mod_eq_of_lt (ZMod.val_lt r),
      Nat.mod_eq_of_lt (ZMod.val_lt r')] at h2
    exact h2
  have hb : b.val = b'.val := by
    rw [hr] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne d)) (Nat.add_right_cancel h)
  simp only [Prod.mk.injEq]
  exact ⟨ZMod.val_injective d hb, ZMod.val_injective d hr⟩

theorem zakIndex_bijective : Function.Bijective (zakIndex d) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨zakIndex_injective, by simp [ZMod.card]⟩

/-- For fixed `r`, the Zak transform is the unitary DFT on `ZMod d`. -/
theorem zak_eq_dftU (f : ZMod (d * d) → ℂ) (q r : ZMod d) :
    zak f q r = dftU (fun b : ZMod d => f (zakIndex d (b, r))) q := by
  unfold zak dftU zakIndex
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [mul_comm q b]

/-- **A3, Parseval.** `∑_{q,r} ‖zak f q r‖² = ∑_j ‖f j‖²`. -/
theorem parseval_zak (f : ZMod (d * d) → ℂ) :
    ∑ q : ZMod d, ∑ r : ZMod d, ‖zak f q r‖ ^ 2 = ∑ j : ZMod (d * d), ‖f j‖ ^ 2 := by
  rw [Finset.sum_comm]
  simp_rw [zak_eq_dftU, parseval_dftU]
  rw [← Fintype.sum_bijective (zakIndex d) zakIndex_bijective
    (fun p => ‖f (zakIndex d p)‖ ^ 2) (fun j => ‖f j‖ ^ 2) (fun _ => rfl)]
  rw [Fintype.sum_prod_type_right]

/-- **A3.** Away from the seam, translation shifts the second Zak variable. -/
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

/-- **A3, the seam.** At `r = d - 1`, translation wraps to `r = 0` with the factor
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

/-- **A3.** Modulation shifts the first Zak variable, with the phase `e^{2πi r/d²}`. -/
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
