import BLTAudit.LowerBoundZak
import BLTAudit.Candidates

/-!
# H5. [HV] as a statement about the explicit Gaussian phase array

For a unit-modulus array `u`, the window `zakInv (d⁻¹ u)` of H1 has rescaled energy equal to the
Zak energy of the twisted continuation of `u` (H4): `scaledEnergy_zakInv`. Applied to the Gaussian
phase `gaussPhase d` of H2 this gives `gaussCand_scaledEnergy_eq`, so the input [HV] of H3 is the
same as a bound on `zakEnergy d (zakExt d (gaussPhase d))`, a finite sum of squared differences of
unit complex numbers with no Fourier transform left (`vortex_iff_zakEnergy`). The energy is also
computed as the explicit double sum over the square (`zakEnergy_eq_sum_range`).

What this file does NOT prove: any bound on that sum, hence not [HV], and nothing toward Theorem 1.1
or Theorem 4.1.
-/

noncomputable section

open scoped Real

namespace BLT

variable {d : ℕ} [NeZero d]

/-- **H5.** The rescaled energy of the window with prescribed Zak array `d⁻¹ u`. -/
theorem scaledEnergy_zakInv (u : ZMod d → ZMod d → ℂ) :
    scaledEnergy (zakInv fun q r => (d : ℂ)⁻¹ * u q r) = zakEnergy d (zakExt d u) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  unfold scaledEnergy
  refine zak_energy_identity _ _ (fun q r hq hr => ?_) (zakExt_shift_q _) (zakExt_shift_r _)
  rw [zak_zakInv, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  exact zakExt_of_lt u hq hr

/-- **H5.** The Gaussian trial window's rescaled energy is the Zak energy of the Gaussian phase. -/
theorem gaussCand_scaledEnergy_eq :
    scaledEnergy (gaussCand d) = zakEnergy d (zakExt d (gaussPhase d)) := by
  unfold gaussCand
  exact scaledEnergy_zakInv (gaussPhase d)

/-- **H5.** The input [HV] of H3 restated with no window left. -/
theorem vortex_iff_zakEnergy (C : ℝ) :
    (∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
        scaledEnergy (gaussCand d) ≤ 2 * π * Real.log d + C) ↔
      ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
        zakEnergy d (zakExt d (gaussPhase d)) ≤ 2 * π * Real.log d + C := by
  constructor
  · rintro ⟨D, h⟩
    refine ⟨D, fun d _ hd ho => ?_⟩
    rw [← gaussCand_scaledEnergy_eq]
    exact h d hd ho
  · rintro ⟨D, h⟩
    refine ⟨D, fun d _ hd ho => ?_⟩
    rw [gaussCand_scaledEnergy_eq]
    exact h d hd ho

/-- The Zak energy of the Gaussian phase, written out over the square. -/
theorem zakEnergy_eq_sum_range (u : ZMod d → ZMod d → ℂ) :
    zakEnergy d (zakExt d u) = ∑ q ∈ Finset.range d, ∑ r ∈ Finset.range d,
      (‖zakExt d u ((q : ℤ), (r : ℤ) + 1) - zakExt d u ((q : ℤ), (r : ℤ))‖ ^ 2 +
        ‖mag d (r : ℤ) * zakExt d u ((q : ℤ) + 1, (r : ℤ)) - zakExt d u ((q : ℤ), (r : ℤ))‖ ^ 2) :=
  rfl

end BLT

end
