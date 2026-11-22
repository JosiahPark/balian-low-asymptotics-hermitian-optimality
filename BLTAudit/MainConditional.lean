import BLTAudit.Statements
import BLTAudit.RelativeOptimality
import BLTAudit.LimitConstant

/-!
# F4. Conditional main theorem: Theorem 1.1 from the named hypotheses [HU] and [HL]

A hypothesis ledger for Theorem 1.1. A candidate family `f : (d : ℕ) → ZMod (d * d) → ℂ` (in the
paper the finite-Hermite windows `f_d`) and two constants `C₁ C₂` are fixed, and the two analytic
halves of the paper enter as the two fields of the structure `MainHypotheses f C₁ C₂`:

* `HU`, **[HU]**: the trial bound (U4) with (U14): for all large `d`, `f d` is admissible and
  `scaledEnergy (f d) ≤ 2π log d + C₁`;
* `HL`, **[HL]**: the lower bound (L19) of Theorem 4.1: for all large `d`,
  `2π log d − 7π log (log d) − C₂ ≤ aMin d`.

`aSeq d` and `ASeq f d` are `aMin d` and `scaledEnergy (f d)` of F1 as real sequences (set to `0` at
`d = 0`, where F1's definitions need `0 < d`). Proved here, from `MainHypotheses f C₁ C₂` only:

* `aSeq_eq`, `ASeq_eq`: for `0 < d` the sequences are `aMin d` and `scaledEnergy (f d)`;
* `main_bounds`: for all large `d`, `2π log d − 7π log (log d) − C₂ ≤ aSeq d ≤ ASeq f d ≤ 2π log d + C₁`
  (uses `aMin_le` of F1);
* `main_conditional`: the shape of Theorem 1.1: those bounds, `aMin d / log d → 2π` (F3, with
  `C = max C₁ C₂`), and `scaledEnergy (f d) / aMin d → 1` (F2).

What this file does NOT prove: [HU] or [HL]. Neither the trial bound (U4) with (U14) nor the lower
bound (L19) of Theorem 4.1 is formalized, so Theorem 1.1 is NOT proved here; it is derived from the
two named hypotheses only. In the paper the candidate `f_d` is used along odd `d`; here [HU] is
assumed for all large `d`, and the restriction to odd `d` is not modelled.
-/

noncomputable section

open Filter Topology
open scoped Real

namespace BLT

/-- `aMin d` as a real sequence (`0` at `d = 0`). -/
def aSeq (d : ℕ) : ℝ := if h : d = 0 then 0 else @aMin d ⟨h⟩

/-- `scaledEnergy (f d)` as a real sequence (`0` at `d = 0`). -/
def ASeq (f : (d : ℕ) → ZMod (d * d) → ℂ) (d : ℕ) : ℝ :=
  if h : d = 0 then 0 else @scaledEnergy d ⟨h⟩ (f d)

/-- The two named hypotheses of Theorem 1.1. -/
structure MainHypotheses (f : (d : ℕ) → ZMod (d * d) → ℂ) (C₁ C₂ : ℝ) : Prop where
  /-- [HU] The trial bound (U4) with (U14): for all large `d`, the candidate `f d` is admissible
  and `scaledEnergy (f d) ≤ 2π log d + C₁`. Not proved in this project. -/
  HU : ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d →
    Admissible (f d) ∧ scaledEnergy (f d) ≤ 2 * π * Real.log d + C₁
  /-- [HL] The lower bound (L19) of Theorem 4.1: for all large `d`,
  `2π log d − 7π log (log d) − C₂ ≤ aMin d`. Not proved in this project. -/
  HL : ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d →
    2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C₂ ≤ aMin d

/-- For `0 < d`, `aSeq d = aMin d`. -/
theorem aSeq_eq (d : ℕ) [NeZero d] : aSeq d = aMin d := by
  unfold aSeq
  first
    | (rw [dif_neg (NeZero.ne d)]; done)
    | simp [NeZero.ne d]

/-- For `0 < d`, `ASeq f d = scaledEnergy (f d)`. -/
theorem ASeq_eq (f : (d : ℕ) → ZMod (d * d) → ℂ) (d : ℕ) [NeZero d] :
    ASeq f d = scaledEnergy (f d) := by
  unfold ASeq
  first
    | (rw [dif_neg (NeZero.ne d)]; done)
    | simp [NeZero.ne d]

/-- **F4, the bounds.** Under [HU] and [HL], for all large `d`,
`2π log d − 7π log (log d) − C₂ ≤ aSeq d ≤ ASeq f d ≤ 2π log d + C₁`. -/
theorem main_bounds (f : (d : ℕ) → ZMod (d * d) → ℂ) (C₁ C₂ : ℝ) (H : MainHypotheses f C₁ C₂) :
    ∀ᶠ d : ℕ in atTop, 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C₂ ≤ aSeq d ∧
      aSeq d ≤ ASeq f d ∧ ASeq f d ≤ 2 * π * Real.log d + C₁ := by
  obtain ⟨DU, hU⟩ := H.HU
  obtain ⟨DL, hL⟩ := H.HL
  rw [Filter.eventually_atTop]
  refine ⟨max (max DU DL) 1, fun d hd => ?_⟩
  have h1 : 1 ≤ d := le_trans (le_max_right _ _) hd
  have hU' : DU ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
  have hL' : DL ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨hadm, hle⟩ := hU d hU'
  rw [aSeq_eq d, ASeq_eq f d]
  exact ⟨hL d hL', aMin_le d (f d) hadm, hle⟩

/-- **F4.** Theorem 1.1 from the named hypotheses [HU] and [HL] (the fields of `MainHypotheses`):
for all large `d`, `2π log d − 7π log (log d) − C₂ ≤ a_d ≤ d² E(f_d) ≤ 2π log d + C₁`; the limit
constant `a_d / log d → 2π`; and relative optimality `d² E(f_d) / a_d → 1`. -/
theorem main_conditional (f : (d : ℕ) → ZMod (d * d) → ℂ) (C₁ C₂ : ℝ)
    (H : MainHypotheses f C₁ C₂) :
    (∀ᶠ d : ℕ in atTop, 2 * π * Real.log d - 7 * π * Real.log (Real.log d) - C₂ ≤ aSeq d ∧
        aSeq d ≤ ASeq f d ∧ ASeq f d ≤ 2 * π * Real.log d + C₁) ∧
      Tendsto (fun d : ℕ => aSeq d / Real.log d) atTop (𝓝 (2 * π)) ∧
      Tendsto (fun d : ℕ => ASeq f d / aSeq d) atTop (𝓝 1) := by
  have hev := main_bounds f C₁ C₂ H
  refine ⟨hev, ?_, ?_⟩
  · refine limit_constant aSeq (max C₁ C₂) (hev.mono fun d hd => ⟨?_, ?_⟩)
    · linarith [le_max_right C₁ C₂, hd.1]
    · linarith [le_max_left C₁ C₂, hd.2.1, hd.2.2]
  · exact (relative_optimality (ASeq f) aSeq C₁ C₂ (hev.mono fun _ hd => hd.2.1)
      (hev.mono fun _ hd => hd.2.2) (hev.mono fun _ hd => hd.1)).2

end BLT

end
