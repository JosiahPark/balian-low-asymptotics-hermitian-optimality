import BLTAudit.UnitaryDFT
import BLTAudit.FiniteZakUnitary

/-!
# A4c. The Zak correlation identity

For `f : ZMod (d * d) → ℂ`, `zak` of `BLTAudit/Basic.lean` and the index map `zakIndex` of A3a
(paper §2):

* `dftU_shift`: the unitary DFT of a translate, `F (g (· + s)) q = e^{-2πi s q / N} (F g) q`;
* `zak_correlation`: for `r s t : ZMod d`,
  `∑_b conj (f (zakIndex (b + s, r))) f (zakIndex (b + t, r)) = ∑_q e^{2πi (s − t) q / d} ‖zak f q r‖²`
  (from A1 applied to the two translates of `b ↦ f (zakIndex (b, r))`, and A3a);
* `zak_correlation_of_norm`: if `‖zak f q r‖ = 1 / d` for all `q`, the left side is `1 / d` when
  `s = t` and `0` otherwise.

What this file does NOT prove: the orthonormality of the Gabor system under `|Z f| = 1/d` (A4d),
that it is a basis (A4e), the converse (A5), or anything toward Theorem 1.1 or Theorem 4.1.
-/

noncomputable section

open Finset
open scoped ComplexConjugate

namespace BLT

/-- The unitary DFT of a translate. -/
theorem dftU_shift {N : ℕ} [NeZero N] (g : ZMod N → ℂ) (s q : ZMod N) :
    dftU (fun b => g (b + s)) q = ZMod.stdAddChar (-(s * q)) * dftU g q := by
  simp only [dftU]
  rw [mul_left_comm (ZMod.stdAddChar (-(s * q)))]
  congr 1
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun b => ?_
  simp only [Equiv.coe_addRight]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

variable {d : ℕ} [NeZero d]

/-- **A4c.** The Zak correlation identity. -/
theorem zak_correlation (f : ZMod (d * d) → ℂ) (r s t : ZMod d) :
    ∑ b : ZMod d, conj (f (zakIndex d (b + s, r))) * f (zakIndex d (b + t, r)) =
      ∑ q : ZMod d, ZMod.stdAddChar ((s - t) * q) * (‖zak f q r‖ : ℂ) ^ 2 := by
  have h := ip_dftU (fun b : ZMod d => f (zakIndex d (b + s, r)))
    (fun b : ZMod d => f (zakIndex d (b + t, r)))
  have hs : ∀ u q : ZMod d, dftU (fun b : ZMod d => f (zakIndex d (b + u, r))) q =
      ZMod.stdAddChar (-(u * q)) * zak f q r := by
    intro u q
    rw [zak_eq_dftU]
    exact dftU_shift (fun b : ZMod d => f (zakIndex d (b, r))) u q
  calc ∑ b : ZMod d, conj (f (zakIndex d (b + s, r))) * f (zakIndex d (b + t, r))
      = ip (fun b : ZMod d => f (zakIndex d (b + s, r)))
          (fun b : ZMod d => f (zakIndex d (b + t, r))) := rfl
    _ = ip (dftU (fun b : ZMod d => f (zakIndex d (b + s, r))))
          (dftU (fun b : ZMod d => f (zakIndex d (b + t, r)))) := h.symm
    _ = ∑ q : ZMod d, conj (ZMod.stdAddChar (-(s * q)) * zak f q r) *
          (ZMod.stdAddChar (-(t * q)) * zak f q r) := by
        unfold ip
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hs s q, hs t q]
    _ = ∑ q : ZMod d, ZMod.stdAddChar ((s - t) * q) * (‖zak f q r‖ : ℂ) ^ 2 := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have hz : conj (zak f q r) * zak f q r = (‖zak f q r‖ : ℂ) ^ 2 :=
          Complex.conj_mul' (zak f q r)
        have hc : conj (ZMod.stdAddChar (-(s * q))) = ZMod.stdAddChar (s * q) := by
          rw [conj_stdAddChar, neg_neg]
        have hchar : ZMod.stdAddChar ((s - t) * q) =
            ZMod.stdAddChar (s * q) * ZMod.stdAddChar (-(t * q)) := by
          rw [← AddChar.map_add_eq_mul]
          congr 1
          ring
        rw [map_mul, hc, hchar, ← hz]
        ring

/-- **A4c, unit-modulus case.** If `‖zak f q r‖ = 1 / d` for all `q`, the correlation is
`1 / d` on the diagonal `s = t` and `0` off it. -/
theorem zak_correlation_of_norm (f : ZMod (d * d) → ℂ) (r s t : ZMod d)
    (h : ∀ q : ZMod d, ‖zak f q r‖ = 1 / (d : ℝ)) :
    ∑ b : ZMod d, conj (f (zakIndex d (b + s, r))) * f (zakIndex d (b + t, r)) =
      if s = t then 1 / (d : ℂ) else 0 := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdiag : (d : ℂ) * (1 / (d : ℂ)) ^ 2 = 1 / (d : ℂ) := by
    first
      | (field_simp; ring)
      | field_simp
      | rw [one_div, sq, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hcast : ((1 / (d : ℝ) : ℝ) : ℂ) = 1 / (d : ℂ) := by simp
  rw [zak_correlation]
  simp_rw [h]
  rw [← Finset.sum_mul, sum_stdAddChar_mul]
  by_cases hst : s = t
  · rw [if_pos hst, if_pos (sub_eq_zero.mpr hst), hcast]
    exact hdiag
  · rw [if_neg hst, if_neg (fun h0 => hst (sub_eq_zero.mp h0)), zero_mul]

end BLT

end
