import BLTAudit.ZakInverse
import BLTAudit.ZakEnergyIdentity
import BLTAudit.MainOdd

/-!
# H4. [HL] in Zak coordinates: Theorem 4.1 for twisted arrays implies `LowerBoundHyp`

The twisted continuation of a `d × d` array (paper §2): for `u : ZMod d → ZMod d → ℂ`,
`zakExt d u (q, r) = e^{-2πi q ⌊r/d⌋ / d} · u (q mod d) (r mod d)`. Proved here:

* `zakExt_shift_q`, `zakExt_shift_r`, `norm_zakExt`, `isTwisted_zakExt`: the continuation obeys the
  two gluing rules, and is a twisted unit array when `u` has unit modulus;
* `zakExt_of_lt`: on the fundamental square it is `u`;
* `scaledEnergy_eq_zakEnergy`: for every window `f`, `scaledEnergy f = zakEnergy d (zakExt d (d · zak f))`
  (the energy identity A7c applied to this continuation);
* `ZakLowerBoundHyp`, **[HLζ]**: Theorem 4.1 exactly as §4 states it, for twisted unit arrays
  `ζ` with `zakEnergy d ζ ≤ K log d`;
* `lowerBound_of_zak`: `[HLζ] → LowerBoundHyp`, so the input [HL] of H3 may be replaced by [HLζ].

What this file does NOT prove: [HLζ] itself (the degree lemma and the ball-growth argument), hence
not [HL], Theorem 4.1 or Theorem 1.1.
-/

noncomputable section

open scoped Real

namespace BLT

variable {d : ℕ} [NeZero d]

/-- The twist factor `e^{-2πi q k / d}`. -/
def twistFactor (d : ℕ) (q k : ℤ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ) * (k : ℂ))

/-- **H4.** The twisted continuation of a `d × d` array to `ℤ²`. -/
def zakExt (d : ℕ) [NeZero d] (u : ZMod d → ZMod d → ℂ) (p : ℤ × ℤ) : ℂ :=
  twistFactor d p.1 (p.2 / (d : ℤ)) * u (p.1 : ZMod d) (p.2 : ZMod d)

theorem norm_twistFactor (q k : ℤ) : ‖twistFactor d q k‖ = 1 := by
  unfold twistFactor
  have h : -2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ) * (k : ℂ) =
      ((-2 * Real.pi * q / d * k : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  first
    | exact Complex.norm_exp_ofReal_mul_I _
    | exact Complex.abs_exp_ofReal_mul_I _
    | simp [Complex.norm_exp]

theorem twistFactor_shift_q (q k : ℤ) : twistFactor d (q + (d : ℤ)) k = twistFactor d q k := by
  unfold twistFactor
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have e : (d : ℂ) * (d : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hd
  have h : -2 * Real.pi * Complex.I * ((q + (d : ℤ) : ℤ) : ℂ) / (d : ℂ) * (k : ℂ) =
      -2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ) * (k : ℂ) +
        ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    first
      | (push_cast
         simp only [div_eq_mul_inv]
         linear_combination (-2 * Real.pi * Complex.I * (k : ℂ)) * e)
      | (push_cast; field_simp; ring)
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem twistFactor_shift_k (q k : ℤ) :
    twistFactor d q (k + 1) =
      Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) * twistFactor d q k := by
  unfold twistFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem zakExt_shift_q (u : ZMod d → ZMod d → ℂ) (q r : ℤ) :
    zakExt d u (q + (d : ℤ), r) = zakExt d u (q, r) := by
  have hc : ((q + (d : ℤ) : ℤ) : ZMod d) = (q : ZMod d) := by
    first
      | simp
      | (push_cast; rw [ZMod.natCast_self, add_zero])
  simp only [zakExt]
  rw [twistFactor_shift_q, hc]

theorem zakExt_shift_r (u : ZMod d → ZMod d → ℂ) (q r : ℤ) :
    zakExt d u (q, r + (d : ℤ)) =
      Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) * zakExt d u (q, r) := by
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hdiv : (r + (d : ℤ)) / (d : ℤ) = r / (d : ℤ) + 1 := by
    have h := Int.add_mul_ediv_right r 1 hd
    rwa [one_mul] at h
  have hc : ((r + (d : ℤ) : ℤ) : ZMod d) = (r : ZMod d) := by
    first
      | simp
      | (push_cast; rw [ZMod.natCast_self, add_zero])
  simp only [zakExt]
  rw [hdiv, twistFactor_shift_k, hc, mul_assoc]

theorem norm_zakExt (u : ZMod d → ZMod d → ℂ) (hu : ∀ q r, ‖u q r‖ = 1) (p : ℤ × ℤ) :
    ‖zakExt d u p‖ = 1 := by
  unfold zakExt
  rw [norm_mul, norm_twistFactor, hu, mul_one]

/-- **H4.** A unit-modulus array continues to a twisted unit array. -/
theorem isTwisted_zakExt (u : ZMod d → ZMod d → ℂ) (hu : ∀ q r, ‖u q r‖ = 1) :
    IsTwisted d (zakExt d u) :=
  ⟨norm_zakExt u hu, zakExt_shift_q u, zakExt_shift_r u⟩

/-- On the fundamental square the continuation is `u`. -/
theorem zakExt_of_lt (u : ZMod d → ZMod d → ℂ) {q r : ℕ} (hq : q < d) (hr : r < d) :
    zakExt d u ((q : ℤ), (r : ℤ)) = u (q : ZMod d) (r : ZMod d) := by
  have hdiv : ((r : ℕ) : ℤ) / (d : ℤ) = 0 :=
    Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hr)
  have h0 : twistFactor d (q : ℤ) 0 = 1 := by
    unfold twistFactor
    simp
  simp only [zakExt]
  rw [hdiv, h0, one_mul, Int.cast_natCast, Int.cast_natCast]

/-- **H4.** Every window's rescaled energy is the Zak energy of the continuation of `d · zak f`. -/
theorem scaledEnergy_eq_zakEnergy (f : ZMod (d * d) → ℂ) :
    scaledEnergy f = zakEnergy d (zakExt d fun q r => (d : ℂ) * zak f q r) := by
  unfold scaledEnergy
  exact zak_energy_identity f _ (fun q r hq hr => zakExt_of_lt _ hq hr)
    (zakExt_shift_q _) (zakExt_shift_r _)

/-- Theorem 4.1 in Zak coordinates. -/
structure ZakLowerBoundHyp : Prop where
  /-- [HLζ] For every `K` there are `C` and `D` such that, for `d ≥ D`, every twisted unit array `ζ`
  with `zakEnergy d ζ ≤ K log d` has `2π log d − 7π log log d − C ≤ zakEnergy d ζ`.
  Not proved in this project. -/
  HLζ : ∀ K : ℝ, ∃ C : ℝ, ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀ ζ : ℤ × ℤ → ℂ, IsTwisted d ζ →
    zakEnergy d ζ ≤ K * Real.log d →
      2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C ≤ zakEnergy d ζ

/-- **H4.** `[HLζ]` implies the input `[HL]` of H3. -/
theorem lowerBound_of_zak (H : ZakLowerBoundHyp) : LowerBoundHyp := by
  refine ⟨fun K => ?_⟩
  obtain ⟨C, D, h⟩ := H.HLζ K
  refine ⟨C, D, fun d _ hd f hf hE => ?_⟩
  have hf' : ∀ n m n' m' : ℕ, n < d → m < d → n' < d → m' < d →
      ip (gabor f n m) (gabor f n' m') = if n = n' ∧ m = m' then (1 : ℂ) else 0 := hf
  have hu : ∀ q r : ZMod d, ‖(d : ℂ) * zak f q r‖ = 1 :=
    (ip_gabor_orthonormal_iff_unit_modulus f).mp hf'
  rw [scaledEnergy_eq_zakEnergy f] at hE ⊢
  exact h d hd _ (isTwisted_zakExt _ fun q r => hu q r) hE

end BLT

end
