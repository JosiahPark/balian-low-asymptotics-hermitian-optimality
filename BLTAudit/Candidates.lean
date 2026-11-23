import BLTAudit.ZakInverse
import BLTAudit.GroundState

/-!
# H2. The two concrete windows of the paper: the finite-Hermite candidate and the Gaussian trial

Definitions, with no analytic estimate:

* `groundR d`: the positive unit ground vector `g_d` of `G_N`, `N = d²`, chosen from D4c
  (`ground_state`); `groundR_sq_sum`, `groundR_pos`, `groundR_min` record its defining properties,
  so the choice is not junk (D4c also shows it is the unique positive minimizer);
* `hermiteCand d = Z⁻¹ (d⁻¹ ph (Z g_d))`, the paper's candidate `f_d` (§1), and `hermiteFam`, the
  same as a family indexed by all `d : ℕ` (`0` at `d = 0`);
* `gaussPhase d q r = ph (F (r / d, (-q) / d))` with `F = gaussZak` (the Gaussian phase `U` of §3.1 in
  the coordinates `m = r`, `n = -q`), and the Gaussian trial window `gaussCand d = Z⁻¹ (d⁻¹ gaussPhase)`.

Proved here:

* `hermiteCand_admissible`: if `Z g_d` has no zero, `f_d` is admissible;
* `gaussZak_grid_ne_zero`, `gaussCand_admissible`: for odd `d`, if the only zero of `F` in `[0,1)²`
  is `(1/2, 1/2)` (the hypothesis `hz`, Appendix A.3, not proved here), the odd grid misses it and
  the Gaussian trial window is admissible.

What this file does NOT prove: the uniqueness of the Gaussian Zak zero (it is the hypothesis `hz`),
that `Z g_d` has no zero, or any bound on the energy of either window. A numerical check (not part
of the Lean development) of exactly these definitions gives `d² E(f_d) − 2π log d` equal to
`0.29, 0.15, 0.047, −0.020, −0.037` at `d = 5, 7, 11, 21, 31`, and nearly the same for `gaussCand`.
Theorem 1.1 and Theorem 4.1 are not proved here.
-/

noncomputable section

open scoped Real

namespace BLT

section Defs

variable (d : ℕ) [NeZero d]

/-- **H2.** The positive unit ground vector `g_d` of `G_N`, `N = d²` (chosen from D4c). -/
def groundR : ZMod (d * d) → ℝ := Classical.choose (ground_state (N := d * d))

/-- `g_d` as a complex vector. -/
def groundC : ZMod (d * d) → ℂ := fun j => (groundR d j : ℂ)

/-- **H2.** The finite-Hermite candidate `f_d = Z⁻¹ (d⁻¹ ph (Z g_d))`. -/
def hermiteCand : ZMod (d * d) → ℂ := zakInv (fun q r => (d : ℂ)⁻¹ * ph (zak (groundC d) q r))

/-- **H2.** The Gaussian phase `U` on the `d × d` grid, in Zak coordinates `(q, r)`. -/
def gaussPhase (q r : ZMod d) : ℂ :=
  ph (gaussZak ((r.val : ℝ) / (d : ℝ)) (((-q).val : ℝ) / (d : ℝ)))

/-- **H2.** The Gaussian trial window `Z⁻¹ (d⁻¹ U)`. -/
def gaussCand : ZMod (d * d) → ℂ := zakInv (fun q r => (d : ℂ)⁻¹ * gaussPhase d q r)

end Defs

/-- The finite-Hermite candidates as one family over `ℕ` (`0` at `d = 0`). -/
def hermiteFam (d : ℕ) : ZMod (d * d) → ℂ := if h : d = 0 then 0 else @hermiteCand d ⟨h⟩

variable {d : ℕ} [NeZero d]

theorem hermiteFam_eq : hermiteFam d = hermiteCand d := by
  unfold hermiteFam
  first
    | (rw [dif_neg (NeZero.ne d)]; done)
    | simp [NeZero.ne d]

/-- `g_d` has unit norm. -/
theorem groundR_sq_sum : ∑ j, groundR d j ^ 2 = 1 :=
  (Classical.choose_spec (ground_state (N := d * d))).1.1

/-- `g_d` is entrywise positive. -/
theorem groundR_pos (j : ZMod (d * d)) : 0 < groundR d j :=
  (Classical.choose_spec (ground_state (N := d * d))).2.1 j

/-- `g_d` minimizes the energy among real unit vectors. -/
theorem groundR_min (u : ZMod (d * d) → ℝ) (hu : ∑ j, u j ^ 2 = 1) :
    energy (fun j => (groundR d j : ℂ)) ≤ energy (fun j => (u j : ℂ)) :=
  (Classical.choose_spec (ground_state (N := d * d))).1.2 u hu

/-- **H2.** If `Z g_d` has no zero, the candidate `f_d` is admissible. -/
theorem hermiteCand_admissible (h : ∀ q r : ZMod d, zak (groundC d) q r ≠ 0) :
    Admissible (hermiteCand d) :=
  zakInv_admissible (fun q r => ph (zak (groundC d) q r)) fun q r => norm_ph (h q r)

/-- The uniqueness statement for the Gaussian Zak zero in `[0,1)²` (Appendix A.3). Used only as a
hypothesis. -/
def GaussZeroUnique : Prop :=
  ∀ x y : ℝ, 0 ≤ x → x < 1 → 0 ≤ y → y < 1 → gaussZak x y = 0 → x = 1 / 2 ∧ y = 1 / 2

theorem val_div_lt_one (a : ZMod d) : (a.val : ℝ) / (d : ℝ) < 1 := by
  have hd : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  rw [div_lt_one hd]
  exact_mod_cast ZMod.val_lt a

theorem val_div_ne_half (hodd : Odd d) (a : ZMod d) : (a.val : ℝ) / (d : ℝ) ≠ 1 / 2 := by
  intro h
  have hd : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have h1 : (a.val : ℝ) = 1 / 2 * (d : ℝ) := (div_eq_iff hd.ne').mp h
  have h2 : ((2 * a.val : ℕ) : ℝ) = (d : ℝ) := by
    push_cast
    linarith
  have h3 : 2 * a.val = d := by exact_mod_cast h2
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **H2.** For odd `d`, under `GaussZeroUnique`, `F` does not vanish on the grid. -/
theorem gaussZak_grid_ne_zero (hz : GaussZeroUnique) (hodd : Odd d) (q r : ZMod d) :
    gaussZak ((r.val : ℝ) / (d : ℝ)) (((-q).val : ℝ) / (d : ℝ)) ≠ 0 := by
  intro h
  have hx := (hz _ _ (by positivity) (val_div_lt_one r) (by positivity) (val_div_lt_one (-q)) h).1
  exact val_div_ne_half hodd r hx

/-- **H2.** For odd `d`, under `GaussZeroUnique`, the Gaussian trial window is admissible. -/
theorem gaussCand_admissible (hz : GaussZeroUnique) (hodd : Odd d) : Admissible (gaussCand d) :=
  zakInv_admissible (fun q r => gaussPhase d q r) fun q r =>
    norm_ph (gaussZak_grid_ne_zero hz hodd q r)

end BLT

end
