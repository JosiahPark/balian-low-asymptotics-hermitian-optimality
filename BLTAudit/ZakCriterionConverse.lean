import BLTAudit.GaborZakModulus
import BLTAudit.FourierUniqueness

/-!
# A5c. Necessity in the critical Gabor criterion: orthonormal implies `|Z f| = 1/d`

For `f : ZMod (d * d) → ℂ`, with `zak`, `gabor`, `ip` of `BLTAudit/Basic.lean` (paper §2, the
necessity half of the critical Gabor criterion, and the resulting equivalence). Below,
"orthonormal" means: for all natural numbers `n m n' m' < d`,
`ip (gabor f n m) (gabor f n' m') = if n = n' ∧ m = m' then 1 else 0`.

* `zmod_val_eq_zero_iff`: for `a : ZMod d`, `a.val = 0 ↔ a = 0`;
* `zak_norm_of_ip_gabor`: if the Gabor vectors are orthonormal, then `‖zak f q r‖ = 1 / d` for
  all `q r` (`ip_gabor_val_zero` of A5a at `n = a.val`, `m = 0`, `n' = 0`, `m' = c.val`, then
  `fourier_uniqueness_two` of A5b with `W q r = ‖zak f q r‖²`);
* `ip_gabor_orthonormal_iff_zak_norm`: the Gabor vectors are orthonormal if and only if
  `‖zak f q r‖ = 1 / d` for all `q r` (the other direction is `ip_gabor_of_zak_norm` of A4d);
* `norm_natCast_mul_zak_eq_one_iff`: `‖d * zak f q r‖ = 1 ↔ ‖zak f q r‖ = 1 / d`;
* `ip_gabor_orthonormal_iff_unit_modulus`: the Gabor vectors are orthonormal if and only if
  `‖d * zak f q r‖ = 1` for all `q r`, that is, the array `ζ = d • zak f` on `ZMod d × ZMod d`
  has unit modulus.

What this file does NOT prove: that every unit-modulus array on `ZMod d × ZMod d` is `d • zak f`
for some `f` (the inverse Zak transform is not formalized, so the correspondence between
admissible vectors and unit-modulus arrays is proved only as the equivalence above, not as a
bijection); the extension of `d • zak f` to a twisted array on `ℤ × ℤ` in the sense of
`IsTwisted`; or any statement about the energy (A6, A7). It proves nothing toward Theorem 1.1
or Theorem 4.1 of the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

variable {d : ℕ} [NeZero d]

/-- An element of `ZMod d` is zero exactly when its least nonnegative representative is. -/
theorem zmod_val_eq_zero_iff (a : ZMod d) : a.val = 0 ↔ a = 0 := by
  first
    | exact ZMod.val_eq_zero a
    | exact ⟨fun e => by rw [← ZMod.natCast_zmod_val a, e, Nat.cast_zero],
        fun e => by rw [e, ZMod.val_zero]⟩

/-- **A5c, necessity.** If the Gabor vectors `gabor f n m`, `n m < d`, are orthonormal for `ip`,
then `|Z f| = 1/d` everywhere. -/
theorem zak_norm_of_ip_gabor (f : ZMod (d * d) → ℂ)
    (h : ∀ n m n' m' : ℕ, n < d → m < d → n' < d → m' < d →
      ip (gabor f n m) (gabor f n' m') = if n = n' ∧ m = m' then (1 : ℂ) else 0)
    (q₀ r₀ : ZMod d) : ‖zak f q₀ r₀‖ = 1 / (d : ℝ) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hdpos
  -- the two-variable Fourier transform of `‖zak f‖²` is the indicator of `(0, 0)`
  have hW : ∀ a c : ZMod d,
      ∑ r : ZMod d, ∑ q : ZMod d, ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) *
          (‖zak f q r‖ : ℂ) ^ 2 =
        if a = 0 ∧ c = 0 then (1 : ℂ) else 0 := by
    intro a c
    have h0 := (ip_gabor_val_zero f a c).symm.trans
      (h a.val 0 0 c.val (ZMod.val_lt a) hdpos hdpos (ZMod.val_lt c))
    by_cases hac : a = 0 ∧ c = 0
    · have hv : a.val = 0 ∧ 0 = c.val :=
        ⟨(zmod_val_eq_zero_iff a).mpr hac.1, ((zmod_val_eq_zero_iff c).mpr hac.2).symm⟩
      rw [if_pos hv] at h0
      rw [if_pos hac]
      exact h0
    · have hv : ¬ (a.val = 0 ∧ 0 = c.val) := fun e =>
        hac ⟨(zmod_val_eq_zero_iff a).mp e.1, (zmod_val_eq_zero_iff c).mp e.2.symm⟩
      rw [if_neg hv] at h0
      rw [if_neg hac]
      exact h0
  -- Fourier uniqueness (A5b), then back from `ℂ` to `ℝ`
  have hC : (‖zak f q₀ r₀‖ : ℂ) ^ 2 = 1 / (d : ℂ) ^ 2 :=
    fourier_uniqueness_two (fun q r : ZMod d => (‖zak f q r‖ : ℂ) ^ 2) hW q₀ r₀
  have h2 : ((‖zak f q₀ r₀‖ ^ 2 : ℝ) : ℂ) = ((1 / (d : ℝ) ^ 2 : ℝ) : ℂ) := by
    first
      | (push_cast; exact hC)
      | (rw [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
          Complex.ofReal_natCast]; exact hC)
      | exact_mod_cast hC
  have hR : ‖zak f q₀ r₀‖ ^ 2 = 1 / (d : ℝ) ^ 2 := by
    first
      | exact Complex.ofReal_injective h2
      | exact Complex.ofReal_inj.mp h2
      | exact_mod_cast h2
  have e : (1 / (d : ℝ)) ^ 2 = 1 / (d : ℝ) ^ 2 := by
    first
      | rw [div_pow, one_pow]
      | exact one_div_pow (d : ℝ) 2
      | field_simp
  have hsq : ‖zak f q₀ r₀‖ ^ 2 = (1 / (d : ℝ)) ^ 2 := hR.trans e.symm
  have hx : 0 ≤ ‖zak f q₀ r₀‖ := norm_nonneg _
  have hy : 0 < 1 / (d : ℝ) := div_pos one_pos hdR
  have hfac : (‖zak f q₀ r₀‖ - 1 / (d : ℝ)) * (‖zak f q₀ r₀‖ + 1 / (d : ℝ)) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h1
  · linarith
  · linarith

/-- **A5c, equivalence.** The Gabor vectors `gabor f n m`, `n m < d`, are orthonormal for `ip`
if and only if `|Z f| = 1/d` everywhere (necessity above, sufficiency from A4d). -/
theorem ip_gabor_orthonormal_iff_zak_norm (f : ZMod (d * d) → ℂ) :
    (∀ n m n' m' : ℕ, n < d → m < d → n' < d → m' < d →
      ip (gabor f n m) (gabor f n' m') = if n = n' ∧ m = m' then (1 : ℂ) else 0) ↔
      ∀ q r : ZMod d, ‖zak f q r‖ = 1 / (d : ℝ) := by
  constructor
  · intro h q r
    exact zak_norm_of_ip_gabor f h q r
  · intro h n m n' m' hn hm hn' hm'
    exact ip_gabor_of_zak_norm f h hn hm hn' hm'

/-- `‖d * zak f q r‖ = 1` says the same as `‖zak f q r‖ = 1 / d`. -/
theorem norm_natCast_mul_zak_eq_one_iff (f : ZMod (d * d) → ℂ) (q r : ZMod d) :
    ‖(d : ℂ) * zak f q r‖ = 1 ↔ ‖zak f q r‖ = 1 / (d : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hn : ‖(d : ℂ) * zak f q r‖ = (d : ℝ) * ‖zak f q r‖ := by
    first
      | rw [norm_mul, Complex.norm_natCast]
      | simp
      | (rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_real,
          Real.norm_of_nonneg hdR.le])
  rw [hn]
  constructor
  · intro h
    rw [eq_div_iff hdR.ne']
    linear_combination h
  · intro h
    rw [h]
    first
      | exact mul_one_div_cancel hdR.ne'
      | (rw [one_div]; exact mul_inv_cancel₀ hdR.ne')
      | field_simp

/-- **A5c, unit-modulus form.** The Gabor vectors `gabor f n m`, `n m < d`, are orthonormal for
`ip` if and only if the array `ζ = d • zak f` has unit modulus. -/
theorem ip_gabor_orthonormal_iff_unit_modulus (f : ZMod (d * d) → ℂ) :
    (∀ n m n' m' : ℕ, n < d → m < d → n' < d → m' < d →
      ip (gabor f n m) (gabor f n' m') = if n = n' ∧ m = m' then (1 : ℂ) else 0) ↔
      ∀ q r : ZMod d, ‖(d : ℂ) * zak f q r‖ = 1 := by
  refine (ip_gabor_orthonormal_iff_zak_norm f).trans ?_
  constructor
  · intro h q r
    exact (norm_natCast_mul_zak_eq_one_iff f q r).mpr (h q r)
  · intro h q r
    exact (norm_natCast_mul_zak_eq_one_iff f q r).mp (h q r)

end BLT

end
