import BLTAudit.FiniteZakTranslation
import BLTAudit.FiniteZakModulation

/-!
# A7b. The Zak array across the two seams

Let `f : ZMod (d * d) → ℂ` and let `ζ : ℤ × ℤ → ℂ` satisfy three named hypotheses:

* `hζ`: `ζ (q, r) = d * zak f q r` for natural numbers `q r < d`;
* `hq`: `ζ (q + d, r) = ζ (q, r)` for all integers `q r` (`shift_q` of `IsTwisted`);
* `hr`: `ζ (q, r + d) = e^{-2πiq/d} ζ (q, r)` for all integers `q r` (`shift_r` of `IsTwisted`).

Unit modulus of `ζ` is not assumed. Then, for natural numbers `q r < d` (paper §2):

* `zeta_r_succ`: `ζ (q, r + 1) = d * zak (transl f) q r`, from A3b; at the seam `r + 1 = d` by
  `hr` and `stdAddChar_neg_natCast`, `ZMod.stdAddChar (-(q : ZMod d)) = e^{-2πiq/d}`;
* `mag_mul_zeta_q_succ`: `mag d r * ζ (q + 1, r) = d * zak (modul f) q r`, from A3c, whose
  factor is `mag d r`; at the seam `q + 1 = d` by `hq`;
* `norm_sq_zeta_r_edge`: `|ζ (q, r + 1) − ζ (q, r)|² = d² |zak f q r − zak (transl f) q r|²`;
* `norm_sq_zeta_q_edge`:
  `|mag d r * ζ (q + 1, r) − ζ (q, r)|² = d² |zak f q r − zak (modul f) q r|²`.

Helper lemmas: `zmod_val_natCast_of_lt`, `norm_sq_natCast_mul`.

What this file does NOT prove: the Zak energy identity `d² E(f) = A_d(ζ)` of §2 (item A7); the
edge terms are not summed over `q r < d` here (A7c). It does not show that an array `ζ` with the
three properties exists. It proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and
nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

variable {d : ℕ} [NeZero d]

/-- A natural number below `d` is its own least representative in `ZMod d`. -/
theorem zmod_val_natCast_of_lt {r : ℕ} (hr : r < d) : (r : ZMod d).val = r := by
  first
    | exact ZMod.val_natCast_of_lt hr
    | rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr]
    | simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hr]

/-- `|n w|² = n² |w|²` for a natural number `n` and `w : ℂ`. -/
theorem norm_sq_natCast_mul (n : ℕ) (w : ℂ) : ‖(n : ℂ) * w‖ ^ 2 = (n : ℝ) ^ 2 * ‖w‖ ^ 2 := by
  have hn : ‖(n : ℂ)‖ = (n : ℝ) := by
    first
      | exact Complex.norm_natCast n
      | simp
  rw [norm_mul, mul_pow, hn]

/-- The standard character at the negative of a natural number:
`ZMod.stdAddChar (-(q : ZMod d)) = e^{-2πiq/d}`. -/
theorem stdAddChar_neg_natCast (q : ℕ) :
    ZMod.stdAddChar (-(q : ZMod d)) =
      Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) := by
  have h1 : ZMod.stdAddChar (-(q : ZMod d)) * ZMod.stdAddChar (q : ZMod d) = 1 := by
    have h0 : -(q : ZMod d) + (q : ZMod d) = 0 := by
      first | ring | simp
    rw [← AddChar.map_add_eq_mul, h0, AddChar.map_zero_eq_one]
  have h3 : ZMod.stdAddChar (q : ZMod d) =
      Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) := stdAddChar_natCast q
  have h2 : Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) = 1 := by
    have h0 : -2 * (Real.pi : ℂ) * Complex.I * (q : ℂ) / (d : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I * (q : ℂ) / (d : ℂ) = 0 := by ring
    first
      | (rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring)
      | rw [← Complex.exp_add, h0, Complex.exp_zero]
  rw [h3] at h1
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) (h1.trans h2.symm)

/-- **A7b, `r`-edges.** One step up in `r`: `ζ (q, r + 1) = d * zak (transl f) q r`, away from
the seam and across it. -/
theorem zeta_r_succ (f : ZMod (d * d) → ℂ) (ζ : ℤ × ℤ → ℂ)
    (hζ : ∀ q r : ℕ, q < d → r < d →
      ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) * zak f (q : ZMod d) (r : ZMod d))
    (hr : ∀ q r : ℤ, ζ (q, r + (d : ℤ)) =
      Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) * ζ (q, r))
    {q r : ℕ} (hq' : q < d) (hr' : r < d) :
    ζ ((q : ℤ), (r : ℤ) + 1) = (d : ℂ) * zak (transl f) (q : ZMod d) (r : ZMod d) := by
  have hv : (r : ZMod d).val = r := zmod_val_natCast_of_lt hr'
  rcases Nat.lt_or_ge (r + 1) d with h | h
  · have e : (r : ℤ) + 1 = ((r + 1 : ℕ) : ℤ) := by
      first | exact (Nat.cast_succ r).symm | omega
    have e2 : ((r + 1 : ℕ) : ZMod d) = (r : ZMod d) + 1 := by
      first | exact Nat.cast_succ r | push_cast
    have ht : zak (transl f) (q : ZMod d) (r : ZMod d) =
        zak f (q : ZMod d) ((r : ZMod d) + 1) :=
      zak_transl_of_lt f (q : ZMod d) (r : ZMod d) (by rw [hv]; exact h)
    rw [e, hζ q (r + 1) hq' h, e2, ht]
  · have hd : r + 1 = d := by omega
    have e : (r : ℤ) + 1 = 0 + (d : ℤ) := by omega
    have h0 : ζ ((q : ℤ), 0) = (d : ℂ) * zak f (q : ZMod d) 0 := by
      have h00 := hζ q 0 hq' (by omega)
      first
        | rwa [Nat.cast_zero, Nat.cast_zero] at h00
        | simpa using h00
    have ht : zak (transl f) (q : ZMod d) (r : ZMod d) =
        ZMod.stdAddChar (-(q : ZMod d)) * zak f (q : ZMod d) 0 :=
      zak_transl_seam f (q : ZMod d) (r : ZMod d) (by rw [hv]; exact hd)
    rw [e, hr (q : ℤ) 0, h0, ht, stdAddChar_neg_natCast]
    first
      | (push_cast; ring)
      | (rw [Int.cast_natCast]; ring)

/-- **A7b, `q`-edges.** One step up in `q` with the magnetic factor:
`mag d r * ζ (q + 1, r) = d * zak (modul f) q r`, away from the seam and across it. -/
theorem mag_mul_zeta_q_succ (f : ZMod (d * d) → ℂ) (ζ : ℤ × ℤ → ℂ)
    (hζ : ∀ q r : ℕ, q < d → r < d →
      ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) * zak f (q : ZMod d) (r : ZMod d))
    (hq : ∀ q r : ℤ, ζ (q + (d : ℤ), r) = ζ (q, r))
    {q r : ℕ} (hq' : q < d) (hr' : r < d) :
    mag d (r : ℤ) * ζ ((q : ℤ) + 1, (r : ℤ)) =
      (d : ℂ) * zak (modul f) (q : ZMod d) (r : ZMod d) := by
  have hv : (r : ZMod d).val = r := zmod_val_natCast_of_lt hr'
  have hz : ζ ((q : ℤ) + 1, (r : ℤ)) =
      (d : ℂ) * zak f ((q : ZMod d) + 1) (r : ZMod d) := by
    rcases Nat.lt_or_ge (q + 1) d with h | h
    · have e : (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) := by
        first | exact (Nat.cast_succ q).symm | omega
      have e2 : ((q + 1 : ℕ) : ZMod d) = (q : ZMod d) + 1 := by
        first | exact Nat.cast_succ q | push_cast
      rw [e, hζ (q + 1) r h hr', e2]
    · have hd : q + 1 = d := by omega
      have e : (q : ℤ) + 1 = 0 + (d : ℤ) := by omega
      have h0 : ζ (0, (r : ℤ)) = (d : ℂ) * zak f 0 (r : ZMod d) := by
        have h00 := hζ 0 r (by omega) hr'
        first
          | rwa [Nat.cast_zero, Nat.cast_zero] at h00
          | simpa using h00
      have h1 : ((q + 1 : ℕ) : ZMod d) = 0 := by
        rw [hd]
        first
          | exact ZMod.natCast_self d
          | exact CharP.cast_eq_zero (ZMod d) d
      have e2 : (q : ZMod d) + 1 = 0 := by
        first | exact (Nat.cast_succ q).symm.trans h1 | simpa using h1
      rw [e, hq 0 (r : ℤ), h0, e2]
  have key : zak (modul f) (q : ZMod d) (r : ZMod d) =
      mag d (r : ℤ) * zak f ((q : ZMod d) + 1) (r : ZMod d) := by
    rw [zak_modul, hv]
    first
      | (rw [mag, Int.cast_natCast]; done)
      | (simp only [mag, Int.cast_natCast]; done)
      | (simp [mag]; done)
      | (congr 1; unfold mag; congr 1; push_cast; ring)
  rw [key, hz]
  ring

/-- **A7b.** An `r`-edge of `ζ` through the Zak transform of `f` and of its translate. -/
theorem norm_sq_zeta_r_edge (f : ZMod (d * d) → ℂ) (ζ : ℤ × ℤ → ℂ)
    (hζ : ∀ q r : ℕ, q < d → r < d →
      ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) * zak f (q : ZMod d) (r : ZMod d))
    (hr : ∀ q r : ℤ, ζ (q, r + (d : ℤ)) =
      Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) * ζ (q, r))
    {q r : ℕ} (hq' : q < d) (hr' : r < d) :
    ‖ζ ((q : ℤ), (r : ℤ) + 1) - ζ ((q : ℤ), (r : ℤ))‖ ^ 2 =
      (d : ℝ) ^ 2 *
        ‖zak f (q : ZMod d) (r : ZMod d) - zak (transl f) (q : ZMod d) (r : ZMod d)‖ ^ 2 := by
  have h : ζ ((q : ℤ), (r : ℤ) + 1) - ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) *
      (zak (transl f) (q : ZMod d) (r : ZMod d) - zak f (q : ZMod d) (r : ZMod d)) := by
    rw [zeta_r_succ f ζ hζ hr hq' hr', hζ q r hq' hr']
    ring
  rw [h, norm_sq_natCast_mul, norm_sub_rev]

/-- **A7b.** A `q`-edge of `ζ` through the Zak transform of `f` and of its modulate. -/
theorem norm_sq_zeta_q_edge (f : ZMod (d * d) → ℂ) (ζ : ℤ × ℤ → ℂ)
    (hζ : ∀ q r : ℕ, q < d → r < d →
      ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) * zak f (q : ZMod d) (r : ZMod d))
    (hq : ∀ q r : ℤ, ζ (q + (d : ℤ), r) = ζ (q, r))
    {q r : ℕ} (hq' : q < d) (hr' : r < d) :
    ‖mag d (r : ℤ) * ζ ((q : ℤ) + 1, (r : ℤ)) - ζ ((q : ℤ), (r : ℤ))‖ ^ 2 =
      (d : ℝ) ^ 2 *
        ‖zak f (q : ZMod d) (r : ZMod d) - zak (modul f) (q : ZMod d) (r : ZMod d)‖ ^ 2 := by
  have h : mag d (r : ℤ) * ζ ((q : ℤ) + 1, (r : ℤ)) - ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) *
      (zak (modul f) (q : ZMod d) (r : ZMod d) - zak f (q : ZMod d) (r : ZMod d)) := by
    rw [mag_mul_zeta_q_succ f ζ hζ hq hq' hr', hζ q r hq' hr']
    ring
  rw [h, norm_sq_natCast_mul, norm_sub_rev]

end BLT

end
