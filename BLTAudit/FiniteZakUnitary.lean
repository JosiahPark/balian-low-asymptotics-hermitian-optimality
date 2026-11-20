import BLTAudit.UnitaryDFT

/-!
# A3a. The finite Zak transform preserves the norm

For `f : ZMod (d * d) → ℂ` and `zak f q r = d^{-1/2} ∑_b e^{2πiqb/d} f(b d + r)` of
`BLTAudit/Basic.lean` (paper §2):

* `zakIndex`, `zakIndex_bijective`: the index map `(b, r) ↦ b d + r` is a bijection
  `ZMod d × ZMod d → ZMod (d * d)`;
* `zak_eq_dftU`: for fixed `r`, `q ↦ zak f q r` is the unitary DFT on `ZMod d` of
  `b ↦ f(b d + r)`;
* `parseval_zak`: `∑_{q,r} ‖zak f q r‖² = ∑_j ‖f j‖²`, from Parseval for the DFT (A1) in the
  variable `b` and the bijection.

What this file does NOT prove: the inner-product form `⟨Z f, Z g⟩ = ⟨f, g⟩` or an inverse of the
Zak transform (only the norm identity is stated), the behaviour of `zak` under translation and
modulation (items A3b, A3c), the critical Gabor criterion `|Z f| = 1/d` (A4, A5), the energy
identity (A7), or anything toward Theorem 1.1 or Theorem 4.1.
-/

noncomputable section

open Finset Complex
open scoped Real

namespace BLT

variable {d : ℕ} [NeZero d]

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

/-- **A3a, Parseval.** `∑_{q,r} ‖zak f q r‖² = ∑_j ‖f j‖²`. -/
theorem parseval_zak (f : ZMod (d * d) → ℂ) :
    ∑ q : ZMod d, ∑ r : ZMod d, ‖zak f q r‖ ^ 2 = ∑ j : ZMod (d * d), ‖f j‖ ^ 2 := by
  rw [Finset.sum_comm]
  simp_rw [zak_eq_dftU, parseval_dftU]
  rw [← Fintype.sum_bijective (zakIndex d) zakIndex_bijective
    (fun p => ‖f (zakIndex d p)‖ ^ 2) (fun j => ‖f j‖ ^ 2) (fun _ => rfl)]
  rw [Fintype.sum_prod_type_right]

end BLT

end
