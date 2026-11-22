import BLTAudit.Basic

/-!
# F1. Statement layer: admissible windows, the rescaled energy and `aMin`

Definitions for the statement of Theorem 1.1 of J. Park, "Relative asymptotic optimality of finite
Hermite Gabor windows" (25 Sep 2026), with `ip`, `gabor` and `energy` of `BLTAudit/Basic.lean`, for
`d : ℕ` with `[NeZero d]` and windows `f : ZMod (d * d) → ℂ`:

* `Admissible f`: the `d²` Gabor vectors `gabor f n m`, `n m < d`, are orthonormal for `ip`, that
  is, `ip (gabor f n m) (gabor f n' m') = if n = n' ∧ m = m' then 1 else 0` for all naturals
  `n m n' m' < d` (the same hypothesis as in A5c);
* `scaledEnergy f = d ^ 2 * energy f`, the rescaled critical energy;
* `aMin d = ⨅ f : {f // Admissible f}, scaledEnergy f`, the paper's `a_d`, as an infimum in `ℝ`.

Proved here, and nothing more:

* `scaledEnergy_nonneg`: `0 ≤ scaledEnergy f` for every `f`;
* `bddBelow_scaledEnergy`: the values of `scaledEnergy` on admissible windows are bounded below
  (by `0`);
* `aMin_nonneg`: `0 ≤ aMin d`;
* `aMin_le`: `aMin d ≤ scaledEnergy f` for every admissible `f`.

Convention: `aMin d` is Mathlib's `iInf` on `ℝ`, which is `0` for an empty family. This file does
NOT prove that admissible windows exist, so it does not show that `aMin d` is the infimum of a
nonempty set, nor that the infimum is attained (a minimum). It does not connect `Admissible` with
the Zak criterion `‖zak f q r‖ = 1 / d` (that equivalence is A4d with A5c, and is not restated
here), and it proves no bound on `aMin d` beyond `0 ≤ aMin d`. In particular it proves nothing
toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the hypotheses [HU] (the trial
bound (U4) with (U14)) and [HL] (the lower bound (L19)).
-/

noncomputable section

namespace BLT

section Defs

variable {d : ℕ} [NeZero d]

/-- **F1.** A window `f` is admissible when the Gabor vectors `gabor f n m`, `n m < d`, are
orthonormal for `ip`. -/
def Admissible (f : ZMod (d * d) → ℂ) : Prop :=
  ∀ n m n' m' : ℕ, n < d → m < d → n' < d → m' < d →
    ip (gabor f n m) (gabor f n' m') = if n = n' ∧ m = m' then (1 : ℂ) else 0

/-- **F1.** The rescaled critical energy `d² E_N(f)`, `N = d²`. -/
def scaledEnergy (f : ZMod (d * d) → ℂ) : ℝ := (d : ℝ) ^ 2 * energy f

/-- The rescaled energy is nonnegative. -/
theorem scaledEnergy_nonneg (f : ZMod (d * d) → ℂ) : 0 ≤ scaledEnergy f := by
  unfold scaledEnergy
  exact mul_nonneg (sq_nonneg _) (energy_nonneg f)

end Defs

/-- **F1.** The minimal rescaled critical energy `a_d`: the infimum of `scaledEnergy` over
admissible windows (Mathlib's `iInf` on `ℝ`). -/
def aMin (d : ℕ) [NeZero d] : ℝ :=
  ⨅ f : {f : ZMod (d * d) → ℂ // Admissible (d := d) f}, scaledEnergy f.1

/-- The values of the rescaled energy on admissible windows are bounded below by `0`. -/
theorem bddBelow_scaledEnergy (d : ℕ) [NeZero d] :
    BddBelow (Set.range fun f : {f : ZMod (d * d) → ℂ // Admissible (d := d) f} =>
      scaledEnergy f.1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨f, rfl⟩
  exact scaledEnergy_nonneg f.1

/-- **F1.** `0 ≤ aMin d`. -/
theorem aMin_nonneg (d : ℕ) [NeZero d] : 0 ≤ aMin d := by
  unfold aMin
  rcases isEmpty_or_nonempty {f : ZMod (d * d) → ℂ // Admissible (d := d) f} with h | h
  · first
      | exact Real.iInf_nonneg fun f => scaledEnergy_nonneg f.1
      | exact (Real.iInf_of_isEmpty _).symm.le
      | simp [Real.iInf_of_isEmpty]
      | (rw [iInf, Set.range_eq_empty, Real.sInf_empty])
  · first
      | exact le_ciInf fun f => scaledEnergy_nonneg f.1
      | exact Real.iInf_nonneg fun f => scaledEnergy_nonneg f.1

/-- **F1.** `aMin d ≤ scaledEnergy f` for every admissible window `f`. -/
theorem aMin_le (d : ℕ) [NeZero d] (f : ZMod (d * d) → ℂ) (hf : Admissible f) :
    aMin d ≤ scaledEnergy f := by
  unfold aMin
  exact ciInf_le (bddBelow_scaledEnergy d) ⟨f, hf⟩

end BLT

end
