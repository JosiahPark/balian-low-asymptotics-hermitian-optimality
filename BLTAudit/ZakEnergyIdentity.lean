import BLTAudit.GStandardForm

/-!
# A7. The Zak energy identity (paper §2)

For `f : ZMod (d * d) → ℂ`, let `ζ : ℤ × ℤ → ℂ` agree with `d · Z_N f` on the fundamental square
`0 ≤ q, r < d` and satisfy the twisted gluing of §2,
`ζ(q + d, r) = ζ(q, r)` and `ζ(q, r + d) = e^{-2πiq/d} ζ(q, r)`.
Then `d² E_{d²}(f) = A_d(ζ)`, where `A_d` counts every positive edge of the square once, both seams
included, with no factor `1/2`:

* `zak_sub`: the Zak transform is additive;
* `zeta_r_succ`, `zeta_q_succ`: the gluing identifies the edge endpoints `ζ(q, r + 1)` and
  `ζ(q + 1, r)` with `d · Z(T f)(q, r)` and `d · Z f(q + 1, r)`;
* `sum_range_eq_sum_zmod`: sums over `range d` and over `ZMod d` agree;
* `zak_energy_identity`: `d² · energy f = zakEnergy d ζ`.

Unit modulus of `ζ` (the critical Gabor condition) is not needed. What this file does NOT prove:
the critical Gabor criterion (A4, A5), any bound on the energy, Theorem 4.1 or Theorem 1.1.
-/

noncomputable section

open Finset Complex
open scoped ComplexConjugate Real

namespace BLT

variable {d : ℕ} [NeZero d]

/-- The Zak transform is additive. -/
theorem zak_sub (f g : ZMod (d * d) → ℂ) (q r : ZMod d) :
    zak (f - g) q r = zak f q r - zak g q r := by
  simp only [zak, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Sums over `range d` and over `ZMod d` agree. -/
theorem sum_range_eq_sum_zmod (F : ZMod d → ℝ) :
    ∑ q ∈ range d, F (q : ZMod d) = ∑ q : ZMod d, F q := by
  refine Finset.sum_nbij' (fun n : ℕ => (n : ZMod d)) (fun q : ZMod d => q.val) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a ha
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
  · intro a _
    exact ZMod.natCast_zmod_val a
  · intro a _
    rfl

/-- `e^{-2πiq/d}` is the standard character at `-q`. -/
theorem exp_neg_eq_stdAddChar (q : ℕ) :
    Complex.exp (-2 * Real.pi * Complex.I * ((q : ℤ) : ℂ) / (d : ℂ)) =
      ZMod.stdAddChar (-(q : ZMod d)) := by
  have h := ZMod.stdAddChar_coe (N := d) (-(q : ℤ))
  rw [Int.cast_neg, Int.cast_natCast] at h
  rw [h]
  congr 1
  push_cast
  ring

/-- The `r`-edge endpoint: `ζ(q, r + 1) = d · Z(T f)(q, r)` for `q, r < d`. -/
theorem zeta_r_succ (f : ZMod (d * d) → ℂ) (ζ : ℤ × ℤ → ℂ)
    (hζ : ∀ q r : ℕ, q < d → r < d → ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) * zak f (q : ZMod d) (r : ZMod d))
    (hr : ∀ q r : ℤ, ζ (q, r + (d : ℤ)) =
      Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) * ζ (q, r))
    (q r : ℕ) (hq : q < d) (hrd : r < d) :
    ζ ((q : ℤ), (r : ℤ) + 1) = (d : ℂ) * zak (transl f) (q : ZMod d) (r : ZMod d) := by
  have hval : (r : ZMod d).val = r := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrd]
  rcases Nat.lt_or_ge (r + 1) d with h | h
  · rw [zak_transl_of_lt f _ _ (by rw [hval]; exact h)]
    have := hζ q (r + 1) hq h
    push_cast at this
    rw [this]
  · have hr1 : r + 1 = d := by omega
    rw [zak_transl_seam f _ _ (by rw [hval]; exact hr1)]
    have e : ((r : ℤ) + 1) = 0 + (d : ℤ) := by rw [zero_add]; exact_mod_cast hr1
    have h0 := hζ q 0 hq (Nat.pos_of_ne_zero (NeZero.ne d))
    simp only [Nat.cast_zero] at h0
    rw [e, hr, h0, exp_neg_eq_stdAddChar]
    ring

/-- The `q`-edge endpoint: `ζ(q + 1, r) = d · Z f(q + 1, r)` for `q, r < d`. -/
theorem zeta_q_succ (f : ZMod (d * d) → ℂ) (ζ : ℤ × ℤ → ℂ)
    (hζ : ∀ q r : ℕ, q < d → r < d → ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) * zak f (q : ZMod d) (r : ZMod d))
    (hq' : ∀ q r : ℤ, ζ (q + (d : ℤ), r) = ζ (q, r))
    (q r : ℕ) (hq : q < d) (hrd : r < d) :
    ζ ((q : ℤ) + 1, (r : ℤ)) = (d : ℂ) * zak f ((q : ZMod d) + 1) (r : ZMod d) := by
  rcases Nat.lt_or_ge (q + 1) d with h | h
  · have := hζ (q + 1) r h hrd
    push_cast at this
    exact this
  · have hq1 : q + 1 = d := by omega
    have e : ((q : ℤ) + 1) = 0 + (d : ℤ) := by rw [zero_add]; exact_mod_cast hq1
    have ez : (q : ZMod d) + 1 = ((0 : ℕ) : ZMod d) := by
      rw [← Nat.cast_one, ← Nat.cast_add, hq1, ZMod.natCast_self, Nat.cast_zero]
    rw [e, hq', ez]
    exact_mod_cast hζ 0 r (Nat.pos_of_ne_zero (NeZero.ne d)) hrd

/-- The magnetic multiplier on the fundamental square is the phase of `zak_modul`. -/
theorem mag_eq_exp (r : ℕ) (hrd : r < d) :
    mag d (r : ℤ) = Complex.exp (2 * π * I * (((r : ZMod d).val : ℕ) : ℂ) / ((d : ℂ) ^ 2)) := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrd]
  unfold mag
  simp only [Int.cast_natCast]

/-- **A7.** The Zak energy identity `d² E(f) = A_d(ζ)`. -/
theorem zak_energy_identity (f : ZMod (d * d) → ℂ) (ζ : ℤ × ℤ → ℂ)
    (hζ : ∀ q r : ℕ, q < d → r < d → ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) * zak f (q : ZMod d) (r : ZMod d))
    (hq' : ∀ q r : ℤ, ζ (q + (d : ℤ), r) = ζ (q, r))
    (hr : ∀ q r : ℤ, ζ (q, r + (d : ℤ)) =
      Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) * ζ (q, r)) :
    (d : ℝ) ^ 2 * energy f = zakEnergy d ζ := by
  -- the two halves of the energy as Zak sums
  have hT : ∑ j : ZMod (d * d), ‖diffOp f j‖ ^ 2 =
      ∑ q : ZMod d, ∑ r : ZMod d, ‖zak f q r - zak (transl f) q r‖ ^ 2 := by
    have e : ∑ j : ZMod (d * d), ‖diffOp f j‖ ^ 2 =
        ∑ j : ZMod (d * d), ‖(f - transl f) j‖ ^ 2 := rfl
    rw [e, ← parseval_zak (f - transl f)]
    simp only [zak_sub]
  have hM : ∑ k : ZMod (d * d), ‖diffOp (dftU f) k‖ ^ 2 =
      ∑ q : ZMod d, ∑ r : ZMod d, ‖zak f q r - zak (modul f) q r‖ ^ 2 := by
    rw [diffOp_dftU, parseval_dftU, ← parseval_zak (f - modul f)]
    simp only [zak_sub]
  -- each edge of the square in terms of the Zak transform
  have edge : ∀ q r : ℕ, q < d → r < d →
      ‖ζ ((q : ℤ), (r : ℤ) + 1) - ζ ((q : ℤ), (r : ℤ))‖ ^ 2 +
        ‖mag d (r : ℤ) * ζ ((q : ℤ) + 1, (r : ℤ)) - ζ ((q : ℤ), (r : ℤ))‖ ^ 2 =
      (d : ℝ) ^ 2 * (‖zak f (q : ZMod d) (r : ZMod d) - zak (transl f) (q : ZMod d) (r : ZMod d)‖ ^ 2 +
        ‖zak f (q : ZMod d) (r : ZMod d) - zak (modul f) (q : ZMod d) (r : ZMod d)‖ ^ 2) := by
    intro q r hq hrd
    rw [zeta_r_succ f ζ hζ hr q r hq hrd, zeta_q_succ f ζ hζ hq' q r hq hrd, hζ q r hq hrd,
      mag_eq_exp r hrd, mul_left_comm, ← zak_modul, ← mul_sub, ← mul_sub, norm_mul, norm_mul,
      norm_sub_rev (zak (transl f) _ _), norm_sub_rev (zak (modul f) _ _), Complex.norm_natCast]
    ring
  unfold zakEnergy energy
  rw [hT, hM, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [← sum_range_eq_sum_zmod]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [← sum_range_eq_sum_zmod (fun r : ZMod d => (d : ℝ) ^ 2 *
    ‖zak f (q : ZMod d) r - zak (transl f) (q : ZMod d) r‖ ^ 2 + (d : ℝ) ^ 2 *
    ‖zak f (q : ZMod d) r - zak (modul f) (q : ZMod d) r‖ ^ 2)]
  refine Finset.sum_congr rfl fun r hr' => ?_
  rw [edge q r (Finset.mem_range.mp hq) (Finset.mem_range.mp hr')]
  ring

end BLT

end
