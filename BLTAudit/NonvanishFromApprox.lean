import BLTAudit.GaussGridLower
import BLTAudit.MainOdd

/-!
# H10. [HN] from the uniform Zak approximation [HA] and [HZ]

Paper §3.2, (3.4): `‖c_d⁻¹ 𝒵_d b_d − F|_grid‖_∞ = O(h²)`, and the lower bound `|F| ≥ c h/√2` on the odd
grid then gives `𝒵_d b_d ≠ 0` for large odd `d`. In the coordinates of this project
`𝒵_d b_d (m, n) = d · zak g_d (−n, m)` with `m = r`, `n = −q`, so the grid value compared with
`F(r/d, (−q)/d)` is `d · zak (groundC d) q r`.

* `ZakApproxHyp C`, **[HA]**: for large odd `d` there is a nonzero scalar `c_d` with
  `‖c_d⁻¹ · d · zak g_d q r − F(r/d, (−q)/d)‖ ≤ C / d²` for all `q r` (Lemma 3.1 with the Zak
  transform of `ψ`; not proved here);
* `nonvanish_of_approx`: `[HZ] → [HA] → [HN]`, the field `nonvanish` of `HermiteHyp` of H3, with
  the grid bound `gaussZak_grid_lower` of H9 and the threshold `d > 2C/c`.

What this file does NOT prove: [HA] (spectral convergence, the fourth-order quasimode, the
boundedness of the Zak transform of `ψ`), nor [HZ]; hence not [HN] unconditionally, and nothing
toward [HE], [HV], [HL] or Theorem 1.1.
-/

noncomputable section

namespace BLT

/-- The uniform Zak approximation of §3.2. -/
structure ZakApproxHyp (C : ℝ) : Prop where
  /-- [HA] For large odd `d` there is `c_d ≠ 0` with
  `‖c_d⁻¹ · d · zak g_d q r − F(r/d, (−q)/d)‖ ≤ C / d²` for all `q r`. Not proved in this project. -/
  approx : ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d → ∃ c : ℂ, c ≠ 0 ∧ ∀ q r : ZMod d,
    ‖c⁻¹ * ((d : ℂ) * zak (groundC d) q r) -
        gaussZak ((r.val : ℝ) / (d : ℝ)) (((-q).val : ℝ) / (d : ℝ))‖ ≤ C / (d : ℝ) ^ 2

/-- **H10.** `[HZ]` and `[HA]` give `[HN]`: for large odd `d`, `zak g_d` has no zero. -/
theorem nonvanish_of_approx (hz : GaussZeroUnique) {C : ℝ} (HA : ZakApproxHyp C) :
    ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d → ∀ q r : ZMod d, zak (groundC d) q r ≠ 0 := by
  obtain ⟨c₀, hc₀, hgrid⟩ := gaussZak_grid_lower hz
  obtain ⟨DA, hA⟩ := HA.approx
  obtain ⟨D₁, hD₁⟩ := exists_nat_gt (2 * C / c₀)
  refine ⟨max DA D₁, fun d _ hd hodd q r hzero => ?_⟩
  obtain ⟨c, _, happ⟩ := hA d (le_trans (le_max_left _ _) hd) hodd
  have h1 := happ q r
  rw [hzero, mul_zero, mul_zero, zero_sub, norm_neg] at h1
  have h2 := hgrid d hodd q r
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hdD : (D₁ : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hd
  have h3 : c₀ / (2 * (d : ℝ)) ≤ C / (d : ℝ) ^ 2 := h2.trans h1
  have hd' : (d : ℝ) ≠ 0 := hdpos.ne'
  have h4 : c₀ * (d : ℝ) ≤ 2 * C := by
    have h5 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ) ^ 2)
    have e1 : c₀ / (2 * (d : ℝ)) * (2 * (d : ℝ) ^ 2) = c₀ * (d : ℝ) := by
      first
        | (field_simp; ring)
        | field_simp
    have e2 : C / (d : ℝ) ^ 2 * (2 * (d : ℝ) ^ 2) = 2 * C := by
      first
        | (field_simp; ring)
        | field_simp
    rw [e1, e2] at h5
    exact h5
  have h6 : (d : ℝ) ≤ 2 * C / c₀ := by
    rw [le_div_iff₀ hc₀]
    linarith
  linarith

/-- **H10, packaged.** Under `[HZ]` and `[HA]`, `HermiteHyp C` needs only its energy field `[HE]`. -/
theorem hermiteHyp_of_approx (hz : GaussZeroUnique) {CA : ℝ} (HA : ZakApproxHyp CA) (C : ℝ)
    (hE : ∃ D : ℕ, ∀ (d : ℕ) [NeZero d], D ≤ d → Odd d →
      |scaledEnergy (hermiteCand d) - 2 * Real.pi * Real.log d| ≤ C) :
    HermiteHyp C :=
  ⟨nonvanish_of_approx hz HA, hE⟩

end BLT

end
