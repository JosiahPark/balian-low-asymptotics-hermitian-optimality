import BLTAudit.Candidates
import BLTAudit.MainConditional

/-!
# H3. The milestone `a_d / log d → 2π` along odd `d`, and Theorem 1.1 for the actual candidate

This replaces the F4 ledger (`MainHypotheses`, an arbitrary family `f`, all large `d`) by a ledger
aligned with the paper: the restriction to odd `d`, the actual windows of `BLTAudit/Candidates.lean`,
and inputs that are each strictly weaker than a conclusion.

Named inputs (structure fields, none proved here):

* `GaussianTrialHyp C`:
  - `zero_unique`, **[HZ]**: the only zero of the Gaussian Zak transform `F` in `[0,1)²` is
    `(1/2, 1/2)` (Appendix A.3, a statement about one fixed function, independent of `d`);
  - `vortex`, **[HV]**: (3.3) for the Gaussian trial window: for large odd `d`,
    `scaledEnergy (gaussCand d) ≤ 2π log d + C`;
* `LowerBoundHyp`, field `HL`, **[HL]**: Theorem 4.1 as the paper states it, window by window: for
  every `K` there is `C` such that for large `d` (either parity), every admissible `f` with
  `scaledEnergy f ≤ K log d` has `scaledEnergy f ≥ 2π log d − 7π log log d − C`;
* `HermiteHyp C` (only for the statements about `f_d`):
  - `nonvanish`, **[HN]**: for large odd `d`, `Z g_d` has no zero (Lemma 3.1 with (3.4));
  - `energy_asymp`, **[HE]**: for large odd `d`, `|d² E(f_d) − 2π log d| ≤ C` ((3.3) with (3.5)).

Proved here from those inputs:

* `tendsto_odd_of_bounds`: two-sided bounds along odd `d` give `a (2k+1) / log (2k+1) → 2π`;
* `milestone_odd_bounds`, `milestone_odd`: from [HZ], [HV], [HL] only: for large odd `d`,
  `2π log d − 7π log log d − C' ≤ aMin d ≤ 2π log d + C`, and `aMin d / log d → 2π` along odd `d`.
  Admissibility of the Gaussian window comes from [HZ]; that the minimizing class has energy
  `≤ K log d` is not assumed but derived (windows above `K log d` are handled directly);
* `main_odd_conditional`: adding [HN], [HE]: for large odd `d`, `f_d` is admissible (derived from
  [HN], not assumed), its energy is `2π log d + O(1)` (recorded separately, as in the paper), the
  bounds on `aMin d`, `0 ≤ d² E(f_d) − a_d ≤ 7π log log d + O(1)`, and both limits along odd `d`.

What this file does NOT prove: [HZ], [HV], [HL], [HN] or [HE]. Hence it proves neither the
milestone `a_d / log d → 2π` nor Theorem 1.1 nor Theorem 4.1 unconditionally; it derives them from
the five named inputs only.
-/

noncomputable section

open Filter Topology
open scoped Real

namespace BLT

/-- Eventually `c ≤ log d`. -/
theorem exists_le_log (c : ℝ) : ∃ D : ℕ, ∀ d : ℕ, D ≤ d → c ≤ Real.log d :=
  Filter.eventually_atTop.mp (tendsto_log_nat.eventually_ge_atTop c)

open Classical in
/-- `a` on odd `d`, and `2π log d` on even `d`. -/
def oddFill (a : ℕ → ℝ) (d : ℕ) : ℝ := if Odd d then a d else 2 * π * Real.log d

/-- **H3.** Bounds of the shape of [HL] and [HU] along odd `d` give the limit `2π` along odd `d`. -/
theorem tendsto_odd_of_bounds (a : ℕ → ℝ) (C₁ C₂ : ℝ)
    (h : ∃ D : ℕ, ∀ d : ℕ, D ≤ d → Odd d →
      2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C₂ ≤ a d ∧
        a d ≤ 2 * π * Real.log d + C₁) :
    Tendsto (fun k : ℕ => a (2 * k + 1) / Real.log ((2 * k + 1 : ℕ) : ℝ)) atTop (𝓝 (2 * π)) := by
  obtain ⟨D, hD⟩ := h
  have hlo : ∀ᶠ d : ℕ in atTop,
      2 * π * Real.log d - 7 * π * Real.log (Real.log d) - max C₂ 0 ≤ oddFill a d := by
    filter_upwards [eventually_ge_atTop D, tendsto_log_nat.eventually_ge_atTop 1] with d hd hlog
    have hll : 0 ≤ 7 * π * Real.log (Real.log d) :=
      mul_nonneg (by positivity) (Real.log_nonneg hlog)
    unfold oddFill
    split_ifs with ho
    · linarith [(hD d hd ho).1, le_max_left C₂ 0]
    · linarith [le_max_right C₂ 0]
  have hhi : ∀ᶠ d : ℕ in atTop, oddFill a d ≤ 2 * π * Real.log d + max C₁ 0 := by
    filter_upwards [eventually_ge_atTop D] with d hd
    unfold oddFill
    split_ifs with ho
    · linarith [(hD d hd ho).2, le_max_left C₁ 0]
    · linarith [le_max_right C₁ 0]
  have hb := tendsto_div_log_of_bounds (oddFill a) (max C₁ 0) (max C₂ 0) hlo hhi
  have hk : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => show k ≤ 2 * k + 1 by omega) tendsto_id
  refine (hb.comp hk).congr fun k => ?_
  show oddFill a (2 * k + 1) / Real.log ((2 * k + 1 : ℕ) : ℝ) =
    a (2 * k + 1) / Real.log ((2 * k + 1 : ℕ) : ℝ)
  rw [show oddFill a (2 * k + 1) = a (2 * k + 1) from if_pos ⟨k, rfl⟩]

/-- The inputs for the Gaussian trial upper bound. -/
structure GaussianTrialHyp (C : ℝ) : Prop where
  /-- [HZ] The only zero of the Gaussian Zak transform in `[0,1)²` is `(1/2, 1/2)` (Appendix A.3).
  Not proved in this project. -/
  zero_unique : GaussZeroUnique
  /-- [HV] The vortex energy (3.3) of the Gaussian trial window: for large odd `d`,
  `scaledEnergy (gaussCand d) ≤ 2π log d + C`. Not proved in this project. -/
  vortex : ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
    scaledEnergy (gaussCand d) ≤ 2 * π * Real.log d + C

/-- The universal lower bound, as Theorem 4.1 states it. -/
structure LowerBoundHyp : Prop where
  /-- [HL] Theorem 4.1: for every `K` there are `C` and `D` such that, for `d ≥ D`, every admissible
  `f` with `scaledEnergy f ≤ K log d` has `2π log d − 7π log log d − C ≤ scaledEnergy f`.
  Not proved in this project. -/
  HL : ∀ K : ℝ, ∃ C : ℝ, ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d →
    ∀ f : ZMod (d * d) → ℂ, Admissible f → scaledEnergy f ≤ K * Real.log d →
      2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C ≤ scaledEnergy f

/-- The inputs about the finite-Hermite candidate `f_d`. -/
structure HermiteHyp (C : ℝ) : Prop where
  /-- [HN] For large odd `d`, `Z g_d` has no zero (Lemma 3.1 with the uniform Zak approximation).
  Not proved in this project. -/
  nonvanish : ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
    ∀ q r : ZMod d, zak (groundC d) q r ≠ 0
  /-- [HE] For large odd `d`, `|d² E(f_d) − 2π log d| ≤ C` ((3.3) with the transfer (3.5)).
  Not proved in this project. -/
  energy_asymp : ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
    |scaledEnergy (hermiteCand d) - 2 * π * Real.log d| ≤ C

/-- **H3, the milestone bounds.** From [HZ], [HV] and [HL]: for large odd `d`,
`2π log d − 7π log log d − C' ≤ aMin d ≤ 2π log d + C`. -/
theorem milestone_odd_bounds (C : ℝ) (HG : GaussianTrialHyp C) (HL : LowerBoundHyp) :
    ∃ C' : ℝ, ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
      2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C' ≤ aMin d ∧
        aMin d ≤ 2 * π * Real.log d + C := by
  obtain ⟨CK, DL, hL⟩ := HL.HL (2 * π + 1)
  obtain ⟨DV, hV⟩ := HG.vortex
  obtain ⟨Dl, hl⟩ := exists_le_log (max 1 (-CK))
  refine ⟨CK, max (max DL DV) Dl, ?_⟩
  intro d _ hd hodd
  have hDL : DL ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
  have hDV : DV ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
  have hlg := hl d (le_trans (le_max_right _ _) hd)
  have h1 : 1 ≤ Real.log d := le_trans (le_max_left _ _) hlg
  have h2 : -CK ≤ Real.log d := le_trans (le_max_right _ _) hlg
  have hll : 0 ≤ 7 * π * Real.log (Real.log d) :=
    mul_nonneg (by positivity) (Real.log_nonneg h1)
  have hadm : Admissible (gaussCand d) := gaussCand_admissible HG.zero_unique hodd
  refine ⟨le_aMin_of_forall _ ⟨gaussCand d, hadm⟩ fun f hf => ?_,
    (aMin_le d _ hadm).trans (hV d hDV hodd)⟩
  by_cases hE : scaledEnergy f ≤ (2 * π + 1) * Real.log d
  · exact hL d hDL f hf hE
  · push_neg at hE
    linarith

/-- **H3, the milestone.** From [HZ], [HV] and [HL] only: `aMin d / log d → 2π` along odd `d`. -/
theorem milestone_odd (C : ℝ) (HG : GaussianTrialHyp C) (HL : LowerBoundHyp) :
    Tendsto (fun k : ℕ => aSeq (2 * k + 1) / Real.log ((2 * k + 1 : ℕ) : ℝ)) atTop
      (𝓝 (2 * π)) := by
  obtain ⟨C', D, hD⟩ := milestone_odd_bounds C HG HL
  refine tendsto_odd_of_bounds aSeq C C' ⟨max D 1, fun d hd hodd => ?_⟩
  have h1 : 1 ≤ d := le_trans (le_max_right D 1) hd
  haveI : NeZero d := ⟨by omega⟩
  rw [aSeq_eq d]
  exact hD d (le_trans (le_max_left _ _) hd) hodd

/-- **H3.** Theorem 1.1 along odd `d` for the actual candidate `f_d`, from [HZ], [HV], [HL], [HN]
and [HE]: for large odd `d`, `f_d` is admissible, `|d² E(f_d) − 2π log d| ≤ C_H`,
`2π log d − 7π log log d − C' ≤ a_d ≤ 2π log d + C_G`, `a_d ≤ d² E(f_d)` and
`d² E(f_d) − a_d ≤ 7π log log d + C' + C_H`; along odd `d`, `a_d / log d → 2π` and
`d² E(f_d) / a_d → 1`. -/
theorem main_odd_conditional (CG CH : ℝ) (HG : GaussianTrialHyp CG) (HL : LowerBoundHyp)
    (HH : HermiteHyp CH) :
    ∃ C' : ℝ, ∃ D : ℕ,
      (∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
        Admissible (hermiteCand d) ∧
        |scaledEnergy (hermiteCand d) - 2 * π * Real.log d| ≤ CH ∧
        2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C' ≤ aMin d ∧
        aMin d ≤ 2 * π * Real.log d + CG ∧
        aMin d ≤ scaledEnergy (hermiteCand d) ∧
        scaledEnergy (hermiteCand d) - aMin d ≤ 7 * π * Real.log (Real.log d) + C' + CH) ∧
      Tendsto (fun k : ℕ => aSeq (2 * k + 1) / Real.log ((2 * k + 1 : ℕ) : ℝ)) atTop
        (𝓝 (2 * π)) ∧
      Tendsto (fun k : ℕ => ASeq hermiteFam (2 * k + 1) / aSeq (2 * k + 1)) atTop (𝓝 1) := by
  obtain ⟨C', DM, hM⟩ := milestone_odd_bounds CG HG HL
  obtain ⟨DN, hN⟩ := HH.nonvanish
  obtain ⟨DE, hE⟩ := HH.energy_asymp
  have key : ∀ (d : ℕ) [NeZero d], max (max DM DN) DE ≤ d → Odd d →
      Admissible (hermiteCand d) ∧
      |scaledEnergy (hermiteCand d) - 2 * π * Real.log d| ≤ CH ∧
      2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C' ≤ aMin d ∧
      aMin d ≤ 2 * π * Real.log d + CG ∧
      aMin d ≤ scaledEnergy (hermiteCand d) ∧
      scaledEnergy (hermiteCand d) - aMin d ≤ 7 * π * Real.log (Real.log d) + C' + CH := by
    intro d _ hd hodd
    have hdM : DM ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
    have hdN : DN ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
    have hdE : DE ≤ d := le_trans (le_max_right _ _) hd
    have hadm : Admissible (hermiteCand d) := hermiteCand_admissible (hN d hdN hodd)
    have hen := hE d hdE hodd
    obtain ⟨hlo, hhi⟩ := hM d hdM hodd
    have hle := aMin_le d _ hadm
    have habs := abs_le.mp hen
    refine ⟨hadm, hen, hlo, hhi, hle, ?_⟩
    linarith [habs.2]
  have hA : Tendsto (fun k : ℕ => ASeq hermiteFam (2 * k + 1) /
      Real.log ((2 * k + 1 : ℕ) : ℝ)) atTop (𝓝 (2 * π)) := by
    refine tendsto_odd_of_bounds (ASeq hermiteFam) CH C'
      ⟨max (max (max DM DN) DE) 1, fun d hd hodd => ?_⟩
    have h1 : 1 ≤ d := le_trans (le_max_right _ 1) hd
    haveI : NeZero d := ⟨by omega⟩
    obtain ⟨_, hen, hlo, _, hle, _⟩ := key d (le_trans (le_max_left _ _) hd) hodd
    rw [ASeq_eq hermiteFam d, hermiteFam_eq]
    exact ⟨by linarith, by linarith [(abs_le.mp hen).2]⟩
  have ha := milestone_odd CG HG HL
  refine ⟨C', max (max DM DN) DE, key, ha, ?_⟩
  have hne : (2 * π : ℝ) ≠ 0 := by
    first
      | positivity
      | exact Real.two_pi_pos.ne'
  have hq := hA.div ha hne
  rw [div_self hne] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hgt : (1 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by
    have : 1 < 2 * k + 1 := by omega
    exact_mod_cast this
  have hL0 : Real.log ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := (Real.log_pos hgt).ne'
  show ASeq hermiteFam (2 * k + 1) / Real.log ((2 * k + 1 : ℕ) : ℝ) /
      (aSeq (2 * k + 1) / Real.log ((2 * k + 1 : ℕ) : ℝ)) =
    ASeq hermiteFam (2 * k + 1) / aSeq (2 * k + 1)
  first
    | rw [div_div_eq_mul_div, div_mul_cancel₀ (ASeq hermiteFam (2 * k + 1)) hL0]
    | exact div_div_div_cancel_right₀ hL0 (ASeq hermiteFam (2 * k + 1)) (aSeq (2 * k + 1))
    | field_simp

end BLT

end
