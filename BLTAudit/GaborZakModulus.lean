import BLTAudit.ZakCriterion

/-!
# A5a. Gabor inner products through the Zak modulus

For `f : ZMod (d * d) → ℂ`, with `zak`, `gabor`, `ip` of `BLTAudit/Basic.lean` (paper §2, the
first step of the necessity half of the critical Gabor criterion). No hypothesis on `f` is used.

* `ip_gabor_eq_sum_zak`: for all `n m n' m' : ℕ`,
  `⟨gabor f n m, gabor f n' m'⟩ = ∑_r conj (e^{2πi m r / d}) e^{2πi m' r / d} ·
  ∑_q e^{2πi (n − n') q / d} ‖zak f q r‖²` (`ip_gabor_eq_sum` of A4d, then `zak_correlation` of
  A4c);
* `ip_gabor_val_zero`: for `a c : ZMod d`,
  `⟨gabor f a.val 0, gabor f 0 c.val⟩ = ∑_r ∑_q e^{2πi c r / d} e^{2πi a q / d} ‖zak f q r‖²`,
  that is, these inner products are the two-variable discrete Fourier transform of `‖zak f‖²`.

What this file does NOT prove: that this Fourier transform determines `‖zak f‖²` (A5b), or that
orthonormality of the Gabor vectors forces `‖zak f q r‖ = 1 / d` (A5c, the statement of A5). It
proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the hypotheses
[HU] and [HL].
-/

noncomputable section

open scoped ComplexConjugate

namespace BLT

variable {d : ℕ} [NeZero d]

/-- **A5a.** Inner products of Gabor vectors through `‖zak f‖²`; no hypothesis on `f`. -/
theorem ip_gabor_eq_sum_zak (f : ZMod (d * d) → ℂ) (n m n' m' : ℕ) :
    ip (gabor f n m) (gabor f n' m') =
      ∑ r : ZMod d, conj (ZMod.stdAddChar ((m : ZMod d) * r)) *
          ZMod.stdAddChar ((m' : ZMod d) * r) *
        ∑ q : ZMod d, ZMod.stdAddChar (((n : ZMod d) - (n' : ZMod d)) * q) *
          (‖zak f q r‖ : ℂ) ^ 2 := by
  rw [ip_gabor_eq_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [zak_correlation]

/-- **A5a, special case.** The inner products `⟨gabor f a 0, gabor f 0 c⟩` are the two-variable
discrete Fourier transform of `‖zak f‖²`. -/
theorem ip_gabor_val_zero (f : ZMod (d * d) → ℂ) (a c : ZMod d) :
    ip (gabor f a.val 0) (gabor f 0 c.val) =
      ∑ r : ZMod d, ∑ q : ZMod d, ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) *
        (‖zak f q r‖ : ℂ) ^ 2 := by
  have h0 : ∀ r : ZMod d, conj (ZMod.stdAddChar (((0 : ℕ) : ZMod d) * r)) = 1 := by
    intro r
    first
      | rw [Nat.cast_zero, zero_mul, AddChar.map_zero_eq_one, map_one]
      | simp [AddChar.map_zero_eq_one]
  have ha : ((a.val : ℕ) : ZMod d) - ((0 : ℕ) : ZMod d) = a := by
    rw [Nat.cast_zero, sub_zero, ZMod.natCast_zmod_val]
  have hc : ((c.val : ℕ) : ZMod d) = c := ZMod.natCast_zmod_val c
  rw [ip_gabor_eq_sum_zak]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [h0 r, ha, hc, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

end BLT

end
