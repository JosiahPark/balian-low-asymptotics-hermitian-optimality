import BLTAudit.ZakEnergyCompare
import BLTAudit.PhasePerturbation
import BLTAudit.GaussVortexZak
import BLTAudit.NonvanishFromApprox

/-!
# H14. [HE] from the two-sided vortex energy and an `ℓ²` phase bound; the reduced ledger

Paper §3.2: with `W = ph (Z g_d)` (the Zak phase of `f_d`) and `U` the Gaussian phase, (3.3) gives
`A(U) = 2π log d + O(1)`, and `‖W − U‖_{ℓ²} = O(h √log d)` together with polarization gives
`|A(W) − A(U)| = O(h log d)`. Here the two analytic statements are named inputs:

* `TransferHyp C₁ C`:
  - `vortex2`, **[HV₂]**: (3.3) two-sided: for large odd `d`,
    `|zakEnergy d (zakExt d (gaussPhase d)) − 2π log d| ≤ C₁`;
  - `phase_l2`, **[HW]**: (3.5): for large odd `d` there is a unimodular `u₀` with
    `∑_{q,r} ‖ph (zak g_d q r) − u₀ · gaussPhase d q r‖² ≤ C log d / d²`.

Proved here:

* `hermiteCand_scaledEnergy_eq`: `d² E(f_d) = zakEnergy d (zakExt d W)`;
* `zakEnergy_compare`: both one-sided comparisons of `A(zakExt W)` and `A(zakExt U)` with parameter
  `t > 0`, from H12–H13 (no square roots);
* `energy_close_arith`: the real arithmetic with `t = 1/d`;
* `energy_asymp_of_transfer`: `[HV₂] → [HW] → [HE]`, the field `energy_asymp` of `HermiteHyp` (H3),
  with constant `3 C₁ + 4π + 32 |C|`;
* `gaussianTrialHyp_of_transfer`: `[HZ]` and `[HV₂]` give `GaussianTrialHyp C₁` (H3);
* `main_odd_reduced`: Theorem 1.1 along odd `d` for the actual candidate (the conclusion of
  `main_odd_conditional`) from **[HZ]**, **[HA]** (H10), **[HV₂]**, **[HW]** and **[HLζ]** (H4).

A numerical check (outside Lean) of these exact definitions with `u₀ = 1` gives
`d² ∑ ‖W − U‖² / log d ≈ 6e-5, 3e-5, 2.2e-5` at `d = 5, 15, 41`, so [HW] holds there with a small
constant.

What this file does NOT prove: [HZ], [HA], [HV₂], [HW] or [HLζ]; hence neither the milestone nor
Theorem 1.1 nor Theorem 4.1 unconditionally.
-/

noncomputable section

open Filter Topology
open scoped Real

namespace BLT

variable {d : ℕ} [NeZero d]

/-- **H14.** The rescaled energy of `f_d` is the Zak energy of its phase array. -/
theorem hermiteCand_scaledEnergy_eq :
    scaledEnergy (hermiteCand d) = zakEnergy d (zakExt d fun q r => ph (zak (groundC d) q r)) := by
  unfold hermiteCand
  exact scaledEnergy_zakInv (fun q r => ph (zak (groundC d) q r))

/-- **H14.** Comparison of `A(zakExt W)` and `A(zakExt U)` through `∑ ‖W − u₀ U‖²`. -/
theorem zakEnergy_compare (W U : ZMod d → ZMod d → ℂ) (u₀ : ℂ) (hu₀ : ‖u₀‖ = 1) {t : ℝ}
    (ht : 0 < t) :
    zakEnergy d (zakExt d W) ≤ (1 + t) * zakEnergy d (zakExt d U) +
        (1 + t⁻¹) * (8 * ∑ q : ZMod d, ∑ r : ZMod d, ‖W q r - u₀ * U q r‖ ^ 2) ∧
      zakEnergy d (zakExt d U) ≤ (1 + t) * zakEnergy d (zakExt d W) +
        (1 + t⁻¹) * (8 * ∑ q : ZMod d, ∑ r : ZMod d, ‖W q r - u₀ * U q r‖ ^ 2) := by
  have ht' : (0 : ℝ) ≤ 1 + t⁻¹ := by
    have := inv_pos.mpr ht
    linarith
  have hU0 : zakEnergy d (zakExt d fun q r => u₀ * U q r) = zakEnergy d (zakExt d U) := by
    rw [zakExt_const_mul, zakEnergy_const_mul u₀ hu₀]
  have hδ := zakEnergy_zakExt_le (d := d) fun q r => W q r - u₀ * U q r
  have hδ' : zakEnergy d (zakExt d fun q r => -(W q r - u₀ * U q r)) ≤
      8 * ∑ q : ZMod d, ∑ r : ZMod d, ‖W q r - u₀ * U q r‖ ^ 2 := by
    have h := zakEnergy_zakExt_le (d := d) fun q r => -(W q r - u₀ * U q r)
    simp only [norm_neg] at h
    exact h
  constructor
  · have hW : zakExt d W = fun p => zakExt d (fun q r => u₀ * U q r) p +
        zakExt d (fun q r => W q r - u₀ * U q r) p := by
      funext p
      simp only [zakExt]
      ring
    have h1 := zakEnergy_add_le (d := d) (zakExt d fun q r => u₀ * U q r)
      (zakExt d fun q r => W q r - u₀ * U q r) ht
    rw [← hW, hU0] at h1
    have h2 := mul_le_mul_of_nonneg_left hδ ht'
    linarith
  · have hU : zakExt d (fun q r => u₀ * U q r) = fun p => zakExt d W p +
        zakExt d (fun q r => -(W q r - u₀ * U q r)) p := by
      funext p
      simp only [zakExt]
      ring
    have h1 := zakEnergy_add_le (d := d) (zakExt d W)
      (zakExt d fun q r => -(W q r - u₀ * U q r)) ht
    rw [← hU, hU0] at h1
    have h2 := mul_le_mul_of_nonneg_left hδ' ht'
    linarith

/-- `X ≤ 2π L + K` with `0 ≤ K`, `L ≤ d`, `1 ≤ d` give `X / d ≤ 2π + K`. -/
theorem div_le_of_le_two_pi_log {X L K D : ℝ} (hD : 1 ≤ D) (hLD : L ≤ D) (hK : 0 ≤ K)
    (hX : X ≤ 2 * π * L + K) : X / D ≤ 2 * π + K := by
  have hDpos : 0 < D := by linarith
  rw [div_le_iff₀ hDpos]
  have h1 : 2 * π * L ≤ 2 * π * D := mul_le_mul_of_nonneg_left hLD (by positivity)
  have h2 : K * 1 ≤ K * D := mul_le_mul_of_nonneg_left hD hK
  nlinarith [h1, h2]

/-- **H14, arithmetic.** With `t = 1/D`: the two comparisons and the bounds on `A(U)` and on the
`ℓ²` defect give `|A(W) − 2π L| ≤ 3 C₁ + 4π + 32 |C|`. -/
theorem energy_close_arith {a b s L D C₁ C : ℝ} (hD : 1 ≤ D) (hL0 : 0 ≤ L) (hLD : L ≤ D)
    (ha : |a - 2 * π * L| ≤ C₁) (hs0 : 0 ≤ s) (hs : s ≤ C * L / D ^ 2)
    (hup : b ≤ (1 + D⁻¹) * a + (1 + D) * (8 * s))
    (hlo : a ≤ (1 + D⁻¹) * b + (1 + D) * (8 * s)) :
    |b - 2 * π * L| ≤ 3 * C₁ + 4 * π + 32 * |C| := by
  have hDpos : 0 < D := by linarith
  have hC₁ : 0 ≤ C₁ := le_trans (abs_nonneg _) ha
  have ha' := abs_le.mp ha
  -- the defect term
  have h1 : s * D ^ 2 ≤ C * L := (le_div_iff₀ (pow_pos hDpos 2)).mp hs
  have h2 : C * L ≤ |C| * L := mul_le_mul_of_nonneg_right (le_abs_self C) hL0
  have h3 : |C| * L ≤ |C| * D := mul_le_mul_of_nonneg_left hLD (abs_nonneg C)
  have h4 : s * D ≤ |C| := by
    have h5 : s * D * D ≤ |C| * D := by nlinarith [h1, h2, h3]
    exact le_of_mul_le_mul_right h5 hDpos
  have hE8 : (1 + D) * (8 * s) ≤ 16 * |C| := by
    have h6 : (1 + D) * (8 * s) ≤ 2 * D * (8 * s) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [h6, h4]
  -- upper bound
  have hsplit : ∀ x : ℝ, (1 + D⁻¹) * x = x + x / D := fun x => by ring
  have haD : a / D ≤ 2 * π + C₁ :=
    div_le_of_le_two_pi_log hD hLD hC₁ (by linarith [ha'.2])
  have hb_up : b ≤ 2 * π * L + (2 * C₁ + 2 * π + 16 * |C|) := by
    rw [hsplit] at hup
    linarith [ha'.2]
  -- lower bound
  have hK : 0 ≤ 2 * C₁ + 2 * π + 16 * |C| := by
    have := Real.pi_pos
    have := abs_nonneg C
    linarith
  have hbD : b / D ≤ 2 * π + (2 * C₁ + 2 * π + 16 * |C|) :=
    div_le_of_le_two_pi_log hD hLD hK hb_up
  have hb_lo : 2 * π * L - (3 * C₁ + 4 * π + 32 * |C|) ≤ b := by
    rw [hsplit] at hlo
    linarith [ha'.1]
  rw [abs_le]
  constructor
  · linarith
  · have := Real.pi_pos
    have := abs_nonneg C
    linarith

/-- The inputs for the energy transfer from the Gaussian phase to the phase of `f_d`. -/
structure TransferHyp (C₁ C : ℝ) : Prop where
  /-- [HV₂] (3.3) two-sided: for large odd `d`,
  `|zakEnergy d (zakExt d (gaussPhase d)) − 2π log d| ≤ C₁`. Not proved in this project. -/
  vortex2 : ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
    |zakEnergy d (zakExt d (gaussPhase d)) - 2 * π * Real.log d| ≤ C₁
  /-- [HW] (3.5): for large odd `d` there is a unimodular `u₀` with
  `∑_{q,r} ‖ph (zak g_d q r) − u₀ · gaussPhase d q r‖² ≤ C log d / d²`. Not proved in this project. -/
  phase_l2 : ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d → ∃ u₀ : ℂ, ‖u₀‖ = 1 ∧
    ∑ q : ZMod d, ∑ r : ZMod d, ‖ph (zak (groundC d) q r) - u₀ * gaussPhase d q r‖ ^ 2 ≤
      C * Real.log d / (d : ℝ) ^ 2

/-- **H14.** `[HV₂]` and `[HW]` give `[HE]`. -/
theorem energy_asymp_of_transfer {C₁ C : ℝ} (H : TransferHyp C₁ C) :
    ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
      |scaledEnergy (hermiteCand d) - 2 * π * Real.log d| ≤ 3 * C₁ + 4 * π + 32 * |C| := by
  obtain ⟨D₁, h₁⟩ := H.vortex2
  obtain ⟨D₂, h₂⟩ := H.phase_l2
  refine ⟨max (max D₁ D₂) 1, ?_⟩
  intro d _ hd hodd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hL0 : 0 ≤ Real.log d := Real.log_nonneg hd1
  have hLd : Real.log d ≤ (d : ℝ) := by
    have := Real.log_le_sub_one_of_pos hdpos
    linarith
  obtain ⟨u₀, hu₀, hs⟩ := h₂ d (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd) hodd
  have hv := h₁ d (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd) hodd
  have hcmp := zakEnergy_compare (d := d) (fun q r => ph (zak (groundC d) q r)) (gaussPhase d) u₀
    hu₀ (inv_pos.mpr hdpos)
  rw [inv_inv] at hcmp
  have hs0 : 0 ≤ ∑ q : ZMod d, ∑ r : ZMod d,
      ‖ph (zak (groundC d) q r) - u₀ * gaussPhase d q r‖ ^ 2 :=
    Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun r _ => sq_nonneg _
  rw [hermiteCand_scaledEnergy_eq]
  exact energy_close_arith hd1 hL0 hLd hv hs0 hs hcmp.1 hcmp.2

/-- **H14.** `[HZ]` and `[HV₂]` give the inputs `GaussianTrialHyp C₁` of H3. -/
theorem gaussianTrialHyp_of_transfer (hz : GaussZeroUnique) {C₁ C : ℝ} (H : TransferHyp C₁ C) :
    GaussianTrialHyp C₁ := by
  refine ⟨hz, (vortex_iff_zakEnergy C₁).mpr ?_⟩
  obtain ⟨D, h⟩ := H.vortex2
  refine ⟨D, fun d _ hd hodd => ?_⟩
  have := (abs_le.mp (h d hd hodd)).2
  linarith

/-- **H14.** Under `[HZ]`, `[HA]`, `[HV₂]` and `[HW]`, the inputs `HermiteHyp` of H3 hold. -/
theorem hermiteHyp_of_transfer (hz : GaussZeroUnique) {CA C₁ C : ℝ} (HA : ZakApproxHyp CA)
    (H : TransferHyp C₁ C) : HermiteHyp (3 * C₁ + 4 * π + 32 * |C|) :=
  ⟨nonvanish_of_approx hz HA, energy_asymp_of_transfer H⟩

/-- **H14, the reduced ledger.** Theorem 1.1 along odd `d` for the actual candidate `f_d`, from
[HZ] (`GaussZeroUnique`), [HA] (`ZakApproxHyp`), [HV₂] and [HW] (`TransferHyp`) and [HLζ]
(`ZakLowerBoundHyp`): the conclusion of `main_odd_conditional` with `C_G = C₁` and
`C_H = 3 C₁ + 4π + 32 |C|`. -/
theorem main_odd_reduced (hz : GaussZeroUnique) {CA C₁ C : ℝ} (HA : ZakApproxHyp CA)
    (HT : TransferHyp C₁ C) (HLζ : ZakLowerBoundHyp) :
    ∃ C' : ℝ, ∃ D : ℕ,
      (∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
        Admissible (hermiteCand d) ∧
        |scaledEnergy (hermiteCand d) - 2 * π * Real.log d| ≤ 3 * C₁ + 4 * π + 32 * |C| ∧
        2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C' ≤ aMin d ∧
        aMin d ≤ 2 * π * Real.log d + C₁ ∧
        aMin d ≤ scaledEnergy (hermiteCand d) ∧
        scaledEnergy (hermiteCand d) - aMin d ≤
          7 * π * Real.log (Real.log d) + C' + (3 * C₁ + 4 * π + 32 * |C|)) ∧
      Tendsto (fun k : ℕ => aSeq (2 * k + 1) / Real.log ((2 * k + 1 : ℕ) : ℝ)) atTop
        (𝓝 (2 * π)) ∧
      Tendsto (fun k : ℕ => ASeq hermiteFam (2 * k + 1) / aSeq (2 * k + 1)) atTop (𝓝 1) :=
  main_odd_conditional C₁ (3 * C₁ + 4 * π + 32 * |C|) (gaussianTrialHyp_of_transfer hz HT)
    (lowerBound_of_zak HLζ) (hermiteHyp_of_transfer hz HA HT)

end BLT

end
