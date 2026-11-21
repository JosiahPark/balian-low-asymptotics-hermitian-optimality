import BLTAudit.GroundEigen
import BLTAudit.GroundExists
import BLTAudit.GStdPositive

/-!
# D4c. The ground state of `G_N` is simple and strictly positive

`IsGround v` says that `v : ZMod N → ℝ` minimizes `quadR` (the energy of a real vector, D4a1) on
the real unit sphere `∑ j, v j ^ 2 = 1`.

* `quadR_abs_le`, `isGround_abs`: `quadR |v| ≤ quadR v`, so `|v|` is a minimizer with `v`;
* `isGround_ne_zero`: a minimizer has no zero entry (`|v|` is a nonnegative eigenvector of `G_N`
  by D4a, hence strictly positive by D3);
* `quadR_eq_sum_mul_gStdR`, `gStdR_comb`: `quadR x = ∑ j, x j * gStdR x j`, and `gStdR` is linear;
* `ne_zero_of_eig`: a nonzero `x` with `quadR x = λ * ∑ j, x j ^ 2`, `λ` the minimum, has no zero
  entry (its normalization is a minimizer);
* `isGround_unique`: two minimizers `v`, `w` satisfy `v = w ∨ v = -w` (`v 0 • w − w 0 • v` is an
  eigenvector for the minimum that vanishes at `0`, so it is zero);
* `ground_state`: the statement of D4, there is `w` that minimizes `energy (fun j => (w j : ℂ))` on
  the real unit sphere, with `0 < w j` for every `j`, and every minimizer `v` is `w` or `−w`.

What this file does NOT prove: anything about complex minimizers (only real vectors are compared,
as in the item), the value of the minimum, a spectral gap, or the limits `λ₀,d → 2π`, `λ₁,d → 6π`.
It proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the
hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

variable {N : ℕ} [NeZero N]

/-- `v` minimizes `quadR` on the real unit sphere. -/
abbrev IsGround (v : ZMod N → ℝ) : Prop :=
  ∑ j, v j ^ 2 = 1 ∧ ∀ u : ZMod N → ℝ, ∑ j, u j ^ 2 = 1 → quadR v ≤ quadR u

theorem quadR_abs_le (v : ZMod N → ℝ) : quadR (fun j => |v j|) ≤ quadR v := by
  show ∑ j : ZMod N, oscDiag N j * |v j| ^ 2 - 2 * ∑ j : ZMod N, |v j| * |v (j + 1)| ≤
    ∑ j : ZMod N, oscDiag N j * v j ^ 2 - 2 * ∑ j : ZMod N, v j * v (j + 1)
  have e1 : ∑ j : ZMod N, oscDiag N j * |v j| ^ 2 = ∑ j : ZMod N, oscDiag N j * v j ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [sq_abs]
  have e2 : ∑ j : ZMod N, v j * v (j + 1) ≤ ∑ j : ZMod N, |v j| * |v (j + 1)| :=
    Finset.sum_le_sum fun j _ => by rw [← abs_mul]; exact le_abs_self _
  linarith

theorem isGround_abs {v : ZMod N → ℝ} (hv : IsGround v) : IsGround (fun j => |v j|) :=
  ⟨(Finset.sum_congr rfl fun j _ => sq_abs (v j)).trans hv.1,
    fun u hu => (quadR_abs_le v).trans (hv.2 u hu)⟩

/-- A minimizer has no zero entry. -/
theorem isGround_ne_zero {v : ZMod N → ℝ} (hv : IsGround v) (j : ZMod N) : v j ≠ 0 := by
  have ha := isGround_abs hv
  have heig : ∀ i, gStd (fun k => ((|v k| : ℝ) : ℂ)) i =
      ((quadR (fun k => |v k|) : ℝ) : ℂ) * ((|v i| : ℝ) : ℂ) := by
    intro i
    rw [gStd_ofReal, gStdR_eq_of_min (fun k => |v k|) ha.2 ha.1 i, Complex.ofReal_mul]
  have hne : (fun k => |v k|) ≠ 0 := by
    intro h
    have hz : ∀ k, |v k| = 0 := fun k => congrFun h k
    have h1 : ∑ k, |v k| ^ 2 = 0 := Finset.sum_eq_zero fun k _ => by simp [hz k]
    have h2 : ∑ k, |v k| ^ 2 = 1 := ha.1
    linarith
  have hpos := gStd_eigvec_pos (fun k => |v k|) (quadR (fun k => |v k|)) hne
    (fun k => abs_nonneg (v k)) heig j
  exact abs_pos.mp hpos

/-- The form as `∑ x (G x)`. -/
theorem quadR_eq_sum_mul_gStdR (x : ZMod N → ℝ) : quadR x = ∑ j, x j * gStdR x j := by
  have hshift : ∑ j, x j * x (j - 1) = ∑ j, x j * x (j + 1) := by
    calc ∑ j, x j * x (j - 1) = ∑ j, x (j + 1) * x (j + 1 - 1) :=
          (sum_zmod_add_one fun j : ZMod N => x j * x (j - 1)).symm
      _ = ∑ j, x j * x (j + 1) :=
          Finset.sum_congr rfl fun j _ => by rw [add_sub_cancel_right, mul_comm]
  have h1 : ∑ j, x j * gStdR x j =
      ∑ j, oscDiag N j * x j ^ 2 - ∑ j, x j * x (j - 1) - ∑ j, x j * x (j + 1) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [gStdR]; ring
  show ∑ j : ZMod N, oscDiag N j * x j ^ 2 - 2 * ∑ j : ZMod N, x j * x (j + 1) =
    ∑ j, x j * gStdR x j
  linarith [h1, hshift]

theorem gStdR_comb (a b : ℝ) (v w : ZMod N → ℝ) (j : ZMod N) :
    gStdR (fun i => a * v i + b * w i) j = a * gStdR v j + b * gStdR w j := by
  simp only [gStdR]
  ring

/-- A nonzero vector with `quadR x = λ ∑ x²`, `λ` the minimum, has no zero entry. -/
theorem ne_zero_of_eig {w x : ZMod N → ℝ} (hw : IsGround w)
    (hx : quadR x = quadR w * ∑ j, x j ^ 2) (hpos : 0 < ∑ j, x j ^ 2) (j : ZMod N) :
    x j ≠ 0 := by
  have hsq : Real.sqrt (∑ j, x j ^ 2) ^ 2 = ∑ j, x j ^ 2 := Real.sq_sqrt hpos.le
  have ht2 : (Real.sqrt (∑ j, x j ^ 2))⁻¹ ^ 2 * ∑ j, x j ^ 2 = 1 := by
    rw [inv_pow, hsq]
    exact inv_mul_cancel₀ hpos.ne'
  have hunit : ∑ i, ((Real.sqrt (∑ j, x j ^ 2))⁻¹ * x i) ^ 2 = 1 := by
    rw [sum_sq_smul]
    exact ht2
  have hq : quadR (fun i => (Real.sqrt (∑ j, x j ^ 2))⁻¹ * x i) = quadR w := by
    rw [quadR_smul, hx]
    linear_combination quadR w * ht2
  have hg : IsGround (fun i => (Real.sqrt (∑ j, x j ^ 2))⁻¹ * x i) :=
    ⟨hunit, fun u hu => by rw [hq]; exact hw.2 u hu⟩
  have hne := isGround_ne_zero hg j
  intro hxj
  apply hne
  show (Real.sqrt (∑ j, x j ^ 2))⁻¹ * x j = 0
  rw [hxj, mul_zero]

/-- Two minimizers agree up to sign. -/
theorem isGround_unique {v w : ZMod N → ℝ} (hv : IsGround v) (hw : IsGround w) :
    v = w ∨ v = -w := by
  have hlam : quadR v = quadR w := le_antisymm (hv.2 w hw.1) (hw.2 v hv.1)
  have hev : ∀ j, gStdR v j = quadR w * v j := fun j => by
    rw [gStdR_eq_of_min v hv.2 hv.1 j, hlam]
  have hew : ∀ j, gStdR w j = quadR w * w j := fun j => gStdR_eq_of_min w hw.2 hw.1 j
  have hw0 : w 0 ≠ 0 := isGround_ne_zero hw 0
  have heh : ∀ j, gStdR (fun i => v 0 * w i + -w 0 * v i) j =
      quadR w * (v 0 * w j + -w 0 * v j) := by
    intro j
    rw [gStdR_comb, hev, hew]
    ring
  have hq : quadR (fun i => v 0 * w i + -w 0 * v i) =
      quadR w * ∑ j, (v 0 * w j + -w 0 * v j) ^ 2 := by
    rw [quadR_eq_sum_mul_gStdR (fun i => v 0 * w i + -w 0 * v i), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [heh j]; ring
  have hs : ∑ j, (v 0 * w j + -w 0 * v j) ^ 2 = 0 := by
    by_contra hne
    have hs0 : 0 ≤ ∑ j, (v 0 * w j + -w 0 * v j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    exact ne_zero_of_eig hw hq (lt_of_le_of_ne hs0 (Ne.symm hne)) 0
      (by show v 0 * w 0 + -w 0 * v 0 = 0; ring)
  have hvj : ∀ j, v j = v 0 / w 0 * w j := by
    intro j
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      sq_nonneg (v 0 * w i + -w 0 * v i)).mp hs j (Finset.mem_univ j)
    have h1 : v 0 * w j + -w 0 * v j = 0 := by
      first
        | exact (pow_eq_zero_iff two_ne_zero).mp h0
        | nlinarith [sq_nonneg (v 0 * w j + -w 0 * v j)]
    rw [div_mul_eq_mul_div, eq_div_iff hw0]
    linarith
  have hc : (v 0 / w 0) ^ 2 = 1 := by
    have h1 : ∑ j, v j ^ 2 = (v 0 / w 0) ^ 2 * ∑ j, w j ^ 2 := by
      rw [← sum_sq_smul]
      exact Finset.sum_congr rfl fun j _ => by rw [hvj j]
    rw [hv.1, hw.1, mul_one] at h1
    exact h1.symm
  have hfac : (v 0 / w 0 - 1) * (v 0 / w 0 + 1) = 0 := by linear_combination hc
  rcases mul_eq_zero.mp hfac with h | h
  · left
    funext j
    rw [hvj j, show v 0 / w 0 = 1 by linarith, one_mul]
  · right
    funext j
    rw [hvj j, show v 0 / w 0 = -1 by linarith, Pi.neg_apply]
    ring

/-- **D4c, the statement of D4.** `E_N` restricted to real unit vectors has a minimizer `w` with
`0 < w j` for every `j`, and every minimizer is `w` or `−w`. -/
theorem ground_state : ∃ w : ZMod N → ℝ,
    (∑ j, w j ^ 2 = 1 ∧ ∀ u : ZMod N → ℝ, ∑ j, u j ^ 2 = 1 →
      energy (fun j => (w j : ℂ)) ≤ energy (fun j => (u j : ℂ))) ∧
    (∀ j, 0 < w j) ∧
    ∀ v : ZMod N → ℝ, (∑ j, v j ^ 2 = 1 ∧ ∀ u : ZMod N → ℝ, ∑ j, u j ^ 2 = 1 →
      energy (fun j => (v j : ℂ)) ≤ energy (fun j => (u j : ℂ))) → v = w ∨ v = -w := by
  have toG : ∀ v : ZMod N → ℝ, (∑ j, v j ^ 2 = 1 ∧ ∀ u : ZMod N → ℝ, ∑ j, u j ^ 2 = 1 →
      energy (fun j => (v j : ℂ)) ≤ energy (fun j => (u j : ℂ))) → IsGround v := by
    intro v hv
    refine ⟨hv.1, fun u hu => ?_⟩
    have h := hv.2 u hu
    rwa [energy_ofReal, energy_ofReal] at h
  obtain ⟨v₀, hv₀, hm₀⟩ := exists_minimizer_quadR (N := N)
  have hg₀ : IsGround v₀ := ⟨hv₀, hm₀⟩
  have hga : IsGround (fun j => |v₀ j|) := isGround_abs hg₀
  refine ⟨fun j => |v₀ j|, ⟨hga.1, fun u hu => ?_⟩, fun j => ?_,
    fun v hv => isGround_unique (toG v hv) hga⟩
  · rw [energy_ofReal, energy_ofReal]
    exact hga.2 u hu
  · exact abs_pos.mpr (isGround_ne_zero hg₀ j)

end BLT

end
