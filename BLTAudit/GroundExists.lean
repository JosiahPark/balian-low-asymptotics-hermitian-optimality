import BLTAudit.RealQuadForm

/-!
# D4b. `E_N` has a minimizer on the real unit sphere

With `quadR` and `energy_ofReal` of `BLTAudit/RealQuadForm.lean` (D4a1), for `N` with
`[NeZero N]` (that is, `0 < N`):

* `continuous_quadR`: `u ↦ quadR u` is continuous on `ZMod N → ℝ`;
* `isCompact_unitSphereR`: the real unit sphere `{u | ∑ j, u j ^ 2 = 1}` is compact (closed, and
  inside the closed ball of radius `1` for the sup norm of `ZMod N → ℝ`, which is a proper space);
* `unitSphereR_nonempty`: it contains the indicator of `0`;
* `exists_minimizer_quadR`: `quadR` attains its minimum on the real unit sphere
  (`IsCompact.exists_isMinOn`);
* `exists_minimizer`: the statement of D4b, there is `v` with `∑ j, v j ^ 2 = 1` and
  `energy (fun j => (v j : ℂ)) ≤ energy (fun j => (u j : ℂ))` for every real `u` with
  `∑ j, u j ^ 2 = 1`.

What this file does NOT prove: that the minimizer can be taken positive or is unique up to sign
(D4c), or any value or bound for the minimum. It proves nothing toward Theorem 1.1 or Theorem 4.1
of the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

variable {N : ℕ} [NeZero N]

/-- The real form `quadR` is continuous. -/
theorem continuous_quadR : Continuous (quadR : (ZMod N → ℝ) → ℝ) := by
  show Continuous fun u : ZMod N → ℝ =>
    ∑ j : ZMod N, oscDiag N j * u j ^ 2 - 2 * ∑ j : ZMod N, u j * u (j + 1)
  have h1 : Continuous fun u : ZMod N → ℝ => ∑ j : ZMod N, oscDiag N j * u j ^ 2 :=
    continuous_finset_sum _ fun j _ => continuous_const.mul ((continuous_apply j).pow 2)
  have h2 : Continuous fun u : ZMod N → ℝ => ∑ j : ZMod N, u j * u (j + 1) :=
    continuous_finset_sum _ fun j _ => (continuous_apply j).mul (continuous_apply (j + 1))
  exact h1.sub (continuous_const.mul h2)

/-- The real unit sphere is compact. -/
theorem isCompact_unitSphereR : IsCompact {u : ZMod N → ℝ | ∑ j, u j ^ 2 = 1} := by
  have hcont : Continuous fun u : ZMod N → ℝ => ∑ j, u j ^ 2 :=
    continuous_finset_sum _ fun j _ => (continuous_apply j).pow 2
  have hclosed : IsClosed {u : ZMod N → ℝ | ∑ j, u j ^ 2 = 1} :=
    isClosed_eq hcont continuous_const
  have hbdd : Bornology.IsBounded {u : ZMod N → ℝ | ∑ j, u j ^ 2 = 1} := by
    refine (Metric.isBounded_closedBall (x := (0 : ZMod N → ℝ)) (r := 1)).subset ?_
    intro u hu
    have hu' : ∑ i, u i ^ 2 = 1 := hu
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    have h1 : u j ^ 2 ≤ ∑ i, u i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (u i)) (Finset.mem_univ j)
    have h2 : u j ^ 2 ≤ 1 := by linarith
    rw [Real.norm_eq_abs]
    first
      | exact (sq_le_one_iff_abs_le_one (u j)).mp h2
      | exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

/-- The real unit sphere is nonempty. -/
theorem unitSphereR_nonempty : ({u : ZMod N → ℝ | ∑ j, u j ^ 2 = 1}).Nonempty := by
  refine ⟨fun j => if j = 0 then 1 else 0, ?_⟩
  show ∑ j : ZMod N, (if j = 0 then (1 : ℝ) else 0) ^ 2 = 1
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `quadR` attains its minimum on the real unit sphere. -/
theorem exists_minimizer_quadR : ∃ v : ZMod N → ℝ, ∑ j, v j ^ 2 = 1 ∧
    ∀ u : ZMod N → ℝ, ∑ j, u j ^ 2 = 1 → quadR v ≤ quadR u := by
  obtain ⟨v, hv, hm⟩ := (isCompact_unitSphereR (N := N)).exists_isMinOn unitSphereR_nonempty
    continuous_quadR.continuousOn
  exact ⟨v, hv, fun u hu => isMinOn_iff.mp hm u hu⟩

/-- **D4b.** `E_N` has a minimizer on the real unit sphere. -/
theorem exists_minimizer : ∃ v : ZMod N → ℝ, ∑ j, v j ^ 2 = 1 ∧
    ∀ u : ZMod N → ℝ, ∑ j, u j ^ 2 = 1 →
      energy (fun j => (v j : ℂ)) ≤ energy (fun j => (u j : ℂ)) := by
  obtain ⟨v, hv, hm⟩ := exists_minimizer_quadR (N := N)
  refine ⟨v, hv, fun u hu => ?_⟩
  rw [energy_ofReal, energy_ofReal]
  exact hm u hu

end BLT

end
