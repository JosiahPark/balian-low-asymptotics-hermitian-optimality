import BLTAudit.GaborZakCoordinates
import BLTAudit.ZakCorrelation

/-!
# A4d. Orthonormality of the critical Gabor system from `|Z f| = 1/d`

For `f : ZMod (d * d) → ℂ`, with `zak`, `gabor`, `ip` of `BLTAudit/Basic.lean` and the index map
`zakIndex d (b, r) = b d + r` of A3a (paper §2, the sufficiency half of the critical Gabor
criterion, without the word "basis"):

* `natCast_zmod_eq_iff_of_lt`: for `n n' < d`, `(n : ZMod d) = (n' : ZMod d) ↔ n = n'`;
* `ip_eq_sum_zakIndex`: `⟨u, v⟩ = ∑_r ∑_b conj (u (b d + r)) v (b d + r)` for all
  `u v : ZMod (d * d) → ℂ` (the bijection of A3a);
* `ip_gabor_eq_sum`: for all `n m n' m' : ℕ` and with no hypothesis on `f`,
  `⟨gabor f n m, gabor f n' m'⟩ = ∑_r conj (e^{2πi m r / d}) e^{2πi m' r / d} ·
  ∑_b conj (f (zakIndex (b + n, r))) f (zakIndex (b + n', r))` (from A4b);
* `ip_gabor_of_zak_norm`: if `‖zak f q r‖ = 1 / d` for all `q r`, then for `n m n' m' < d`,
  `⟨gabor f n m, gabor f n' m'⟩ = if n = n' ∧ m = m' then 1 else 0` (A4c for the sum over `b`,
  then orthogonality of the characters of `ZMod d` in `r`).

What this file does NOT prove: that the `d²` Gabor vectors are linearly independent or span
`ℂ^{d²}` (A4e), the converse "orthonormal implies `|Z f| = 1/d`" (A5), or any statement about
the energy. It proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward
the hypotheses [HU] and [HL].
-/

noncomputable section

open scoped ComplexConjugate

namespace BLT

/-- Natural numbers below `d` are distinguished by their classes in `ZMod d`. -/
theorem natCast_zmod_eq_iff_of_lt {d n n' : ℕ} (hn : n < d) (hn' : n' < d) :
    (n : ZMod d) = (n' : ZMod d) ↔ n = n' := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn']

variable {d : ℕ} [NeZero d]

/-- The inner product on `ZMod (d * d)` as a double sum over the Zak coordinates
`j = b d + r`. -/
theorem ip_eq_sum_zakIndex (u v : ZMod (d * d) → ℂ) :
    ip u v = ∑ r : ZMod d, ∑ b : ZMod d,
      conj (u (zakIndex d (b, r))) * v (zakIndex d (b, r)) := by
  unfold ip
  rw [← Fintype.sum_bijective (zakIndex d) zakIndex_bijective
    (fun p => conj (u (zakIndex d p)) * v (zakIndex d p))
    (fun j => conj (u j) * v j) (fun _ => rfl)]
  rw [Fintype.sum_prod_type_right]

/-- The inner product of two Gabor vectors in Zak coordinates; no hypothesis on `f`. -/
theorem ip_gabor_eq_sum (f : ZMod (d * d) → ℂ) (n m n' m' : ℕ) :
    ip (gabor f n m) (gabor f n' m') =
      ∑ r : ZMod d, conj (ZMod.stdAddChar ((m : ZMod d) * r)) *
          ZMod.stdAddChar ((m' : ZMod d) * r) *
        ∑ b : ZMod d, conj (f (zakIndex d (b + (n : ZMod d), r))) *
          f (zakIndex d (b + (n' : ZMod d), r)) := by
  rw [ip_eq_sum_zakIndex (gabor f n m) (gabor f n' m')]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [gabor_zakIndex, gabor_zakIndex, map_mul (starRingEnd ℂ)]
  ring

/-- **A4d.** If `|Z f| = 1/d` everywhere, the Gabor vectors `gabor f n m` with `n m < d` are
orthonormal for `ip`. -/
theorem ip_gabor_of_zak_norm (f : ZMod (d * d) → ℂ)
    (h : ∀ q r : ZMod d, ‖zak f q r‖ = 1 / (d : ℝ))
    {n m n' m' : ℕ} (hn : n < d) (hm : m < d) (hn' : n' < d) (hm' : m' < d) :
    ip (gabor f n m) (gabor f n' m') = if n = n' ∧ m = m' then (1 : ℂ) else 0 := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hnn : (n : ZMod d) = (n' : ZMod d) ↔ n = n' := natCast_zmod_eq_iff_of_lt hn hn'
  have hmm : (m' : ZMod d) = (m : ZMod d) ↔ m' = m := natCast_zmod_eq_iff_of_lt hm' hm
  have hcorr : ∀ r : ZMod d,
      ∑ b : ZMod d, conj (f (zakIndex d (b + (n : ZMod d), r))) *
          f (zakIndex d (b + (n' : ZMod d), r)) =
        if (n : ZMod d) = (n' : ZMod d) then 1 / (d : ℂ) else 0 :=
    fun r => zak_correlation_of_norm f r (n : ZMod d) (n' : ZMod d) (fun q => h q r)
  rw [ip_gabor_eq_sum]
  simp_rw [hcorr]
  rw [← Finset.sum_mul, sum_conj_stdAddChar_mul]
  by_cases h1 : n = n'
  · by_cases h2 : m = m'
    · rw [if_pos (hmm.mpr h2.symm), if_pos (hnn.mpr h1), if_pos (And.intro h1 h2)]
      first
        | exact mul_one_div_cancel hd
        | (rw [one_div]; exact mul_inv_cancel₀ hd)
        | field_simp
    · have hne : ¬ (m' : ZMod d) = (m : ZMod d) := fun e => h2 (hmm.mp e).symm
      have hne' : ¬ (n = n' ∧ m = m') := fun e => h2 e.2
      rw [if_neg hne, if_neg hne', zero_mul]
  · have hne : ¬ (n : ZMod d) = (n' : ZMod d) := fun e => h1 (hnn.mp e)
    have hne' : ¬ (n = n' ∧ m = m') := fun e => h1 e.1
    rw [if_neg hne, if_neg hne', mul_zero]

end BLT

end
