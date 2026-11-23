import BLTAudit.GaussLinearGlobal

/-!
# H9. The grid lower bound `|F| ≥ c / (2d)` on the odd grid, under [HZ]

Paper §3.1–§3.2: an odd grid stays at distance at least `h/√2` from the zero `z₀`, so `|F| ≥ c h/√2`
on the grid. Proved here, with `GaussZeroUnique` ([HZ]) as the single input:

* `odd_grid_abs_sub_half`: for odd `d` and `a : ZMod d`, `|a/d − 1/2| ≥ 1/(2d)`;
* `odd_grid_norm_sub_zakZeroPt`: for odd `d`, every grid point `(r/d, (−q)/d)` has
  `‖(y − x i) − z₀‖ ≥ 1/(2d)` (the weaker constant `1/2` in place of `1/√2`);
* `gaussZak_grid_lower`: there is `c > 0` such that for every odd `d` and all `q r : ZMod d`,
  `c / (2d) ≤ ‖F(r/d, (−q)/d)‖`, the quantitative form of `gaussZak_grid_ne_zero` of H2. This is the
  lower bound `|F| ≥ c h/√2` that the transfer step (3.4)–(3.5) of §3.2 uses to show `Z g_d ≠ 0`.

What this file does NOT prove: [HZ], the uniform approximation `‖c_d⁻¹ Z_d b_d − F‖_∞ = O(h²)`
(Lemma 3.1), hence not [HN]; nothing toward [HV], [HL] or Theorem 1.1.
-/

noncomputable section

open Set

namespace BLT

variable {d : ℕ} [NeZero d]

/-- For odd `d`, a grid coordinate `a/d` is at distance at least `1/(2d)` from `1/2`. -/
theorem odd_grid_abs_sub_half (hodd : Odd d) (a : ZMod d) :
    1 / (2 * (d : ℝ)) ≤ |(a.val : ℝ) / (d : ℝ) - 1 / 2| := by
  have hd : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  set n : ℤ := 2 * (a.val : ℤ) - (d : ℤ) with hn
  have hnodd : Odd n := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨(a.val : ℤ) - k - 1, by omega⟩
  have hn0 : n ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := hnodd
    omega
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    have h2 : ((|n| : ℤ) : ℝ) = |(n : ℝ)| := by
      first
        | exact Int.cast_abs
        | push_cast; rfl
        | simp
    rw [← h2]
    exact_mod_cast h1
  have hd' : (d : ℝ) ≠ 0 := hd.ne'
  have heq : (a.val : ℝ) / (d : ℝ) - 1 / 2 = (n : ℝ) / (2 * (d : ℝ)) := by
    rw [hn]
    push_cast
    first
      | (field_simp; ring)
      | field_simp
      | (rw [eq_div_iff (by positivity)]; field_simp; ring)
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (d : ℝ))]
  first
    | exact div_le_div_of_nonneg_right hn1 (by positivity)
    | exact div_le_div_right (by positivity) |>.mpr hn1

/-- For odd `d`, grid points stay at distance at least `1/(2d)` from `z₀`. -/
theorem odd_grid_norm_sub_zakZeroPt (hodd : Odd d) (q r : ZMod d) :
    1 / (2 * (d : ℝ)) ≤
      ‖((((-q).val : ℝ) / (d : ℝ) : ℝ) : ℂ) - (((r.val : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I -
        zakZeroPt‖ := by
  set x : ℝ := (r.val : ℝ) / (d : ℝ) with hx
  set y : ℝ := ((-q).val : ℝ) / (d : ℝ) with hy
  have hsq := norm_sub_zakZeroPt_sq x y
  have hxa := odd_grid_abs_sub_half hodd r
  have hpos : (0 : ℝ) ≤ 1 / (2 * (d : ℝ)) := by positivity
  have h1 : (1 / (2 * (d : ℝ))) ^ 2 ≤ (x - 1 / 2) ^ 2 := by
    rw [← sq_abs (x - 1 / 2)]
    exact pow_le_pow_left₀ hpos hxa 2
  have h2 : (1 / (2 * (d : ℝ))) ^ 2 ≤
      ‖((y : ℂ) - (x : ℂ) * Complex.I) - zakZeroPt‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (y - 1 / 2)]
  exact (pow_le_pow_iff_left₀ hpos (norm_nonneg _) two_ne_zero).mp h2

/-- **H9.** Under [HZ], `|F| ≥ c/(2d)` on the odd grid, with `c` independent of `d`. -/
theorem gaussZak_grid_lower (hz : GaussZeroUnique) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) [NeZero d], Odd d → ∀ q r : ZMod d,
      c / (2 * (d : ℝ)) ≤ ‖gaussZak ((r.val : ℝ) / (d : ℝ)) (((-q).val : ℝ) / (d : ℝ))‖ := by
  obtain ⟨c, hc, h⟩ := gaussZak_ge_linear hz
  refine ⟨c, hc, fun d _ hodd q r => ?_⟩
  have hd : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hx : (r.val : ℝ) / (d : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (val_div_lt_one r).le⟩
  have hy : ((-q).val : ℝ) / (d : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (val_div_lt_one (-q)).le⟩
  have hlin := h _ _ hx hy
  have hgrid := odd_grid_norm_sub_zakZeroPt hodd q r
  calc c / (2 * (d : ℝ)) = c * (1 / (2 * (d : ℝ))) := by ring
    _ ≤ c * ‖((((-q).val : ℝ) / (d : ℝ) : ℝ) : ℂ) - (((r.val : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I -
          zakZeroPt‖ := mul_le_mul_of_nonneg_left hgrid hc.le
    _ ≤ _ := hlin

end BLT

end
