import BLTAudit.EdgeEnergy
import BLTAudit.EdgePeriodicity

/-!
# B2b. Plaquette identity (L3)

For a unit-modulus array `ζ : ℤ × ℤ → ℂ` and integers `q r`, the four covariant edge numbers
around the plaquette with lower left corner `(q, r)` (paper §4.1, equation (L3)) satisfy

  `aQ d ζ q r + aR ζ (q + 1) r - aQ d ζ q (r + 1) - aR ζ q r = -(2π / d²) + 2π n`

for some integer `n`. With `mag`, `aQ`, `aR` of `BLTAudit/Basic.lean`:

* `plaquette_identity`: the statement above, for every `d : ℕ` and every `ζ` with `‖ζ p‖ = 1`;
* `plaquette_identity_of_isTwisted`: the same under `IsTwisted d ζ` (only its unit modulus is
  used).

Neither the gluing of `IsTwisted` nor `0 < d` is needed (for `d = 0` both `mag` and `2π / d²` are
trivial in Lean's convention `x / 0 = 0`). Helper lemmas:

* `exp_arg_mul_I_of_norm_eq_one`: `exp (arg w * I) = w` for `‖w‖ = 1`;
* `exists_int_of_exp_mul_I_eq`: real `x y` with `exp (x * I) = exp (y * I)` satisfy
  `x = y + 2π n` for some integer `n`;
* `arg_add_arg_sub_of_mul_eq`: for unit `w₁ w₂ w₃ w₄` with `w₁ * w₂ * exp (θ * I) = w₃ * w₄`,
  `arg w₁ + arg w₂ - arg w₃ - arg w₄ = -θ + 2π n` for some integer `n`;
* `mag_succ`: `mag d (r + 1) = mag d r * exp ((2π / d²) * I)`;
* `plaquette_phase_algebra`, `norm_mul_conj_eq_one`: the product of the four edge phases.

The roadmap item phrases the phase product as `mag d r * conj (mag d (r + 1)) = e^{-2πi/d²}`;
here the same fact is used in the form `mag_succ`, with no conjugate of `mag`.

What this file does NOT prove: the integer `n` is only shown to exist for each `(q, r)`; it is
not defined as a function of the plaquette, and its sum over the `d × d` square (total charge
one, (L4), item B3) is not computed. No bound for `zakEnergy` is proved. This file proves nothing
toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

open scoped ComplexConjugate

namespace BLT

/-- A unit complex number is `exp (arg w * I)`. -/
theorem exp_arg_mul_I_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) :
    Complex.exp ((Complex.arg w : ℂ) * Complex.I) = w := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact zero_ne_one hw
  first
    | (have h := Complex.norm_mul_exp_arg_mul_I w
       rw [hw, Complex.ofReal_one, one_mul] at h
       exact h)
    | (have h := Complex.norm_mul_exp_arg_mul_I w
       simpa [hw] using h)
    | exact Complex.ext
        (by rw [Complex.exp_ofReal_mul_I_re, Complex.cos_arg hw0, hw, div_one])
        (by rw [Complex.exp_ofReal_mul_I_im, Complex.sin_arg, hw, div_one])
    | exact Complex.ext
        (by rw [Complex.exp_ofReal_mul_I_re, Complex.cos_arg hw0, hw, div_one])
        (by simp [Complex.exp_ofReal_mul_I_im, Complex.sin_arg, hw])

/-- Real angles with the same `exp (· * I)` differ by an integer multiple of `2π`. -/
theorem exists_int_of_exp_mul_I_eq {x y : ℝ}
    (h : Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I)) :
    ∃ n : ℤ, x = y + 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have h2 : (x : ℂ) * Complex.I = ((y + 2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    first
      | (push_cast; linear_combination hn)
      | (rw [hn]; push_cast; ring)
      | (simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
          Complex.ofReal_intCast]; linear_combination hn)
  exact Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h2)

/-- If unit complex numbers satisfy `w₁ * w₂ * exp (θ * I) = w₃ * w₄`, their principal arguments
satisfy `arg w₁ + arg w₂ - arg w₃ - arg w₄ = -θ + 2π n` for some integer `n`. -/
theorem arg_add_arg_sub_of_mul_eq {w₁ w₂ w₃ w₄ : ℂ} (h₁ : ‖w₁‖ = 1) (h₂ : ‖w₂‖ = 1)
    (h₃ : ‖w₃‖ = 1) (h₄ : ‖w₄‖ = 1) (θ : ℝ)
    (h : w₁ * w₂ * Complex.exp ((θ : ℂ) * Complex.I) = w₃ * w₄) :
    ∃ n : ℤ, Complex.arg w₁ + Complex.arg w₂ - Complex.arg w₃ - Complex.arg w₄ =
      -θ + 2 * Real.pi * n := by
  have hl : ((Complex.arg w₁ + Complex.arg w₂ + θ : ℝ) : ℂ) * Complex.I =
      (Complex.arg w₁ : ℂ) * Complex.I + (Complex.arg w₂ : ℂ) * Complex.I +
        (θ : ℂ) * Complex.I := by
    first
      | (push_cast; ring)
      | (simp only [Complex.ofReal_add]; ring)
  have hr : ((Complex.arg w₃ + Complex.arg w₄ : ℝ) : ℂ) * Complex.I =
      (Complex.arg w₃ : ℂ) * Complex.I + (Complex.arg w₄ : ℂ) * Complex.I := by
    first
      | (push_cast; ring)
      | (simp only [Complex.ofReal_add]; ring)
  have e : Complex.exp (((Complex.arg w₁ + Complex.arg w₂ + θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((Complex.arg w₃ + Complex.arg w₄ : ℝ) : ℂ) * Complex.I) := by
    rw [hl, hr, Complex.exp_add, Complex.exp_add, Complex.exp_add,
      exp_arg_mul_I_of_norm_eq_one h₁, exp_arg_mul_I_of_norm_eq_one h₂,
      exp_arg_mul_I_of_norm_eq_one h₃, exp_arg_mul_I_of_norm_eq_one h₄]
    exact h
  obtain ⟨n, hn⟩ := exists_int_of_exp_mul_I_eq e
  refine ⟨n, ?_⟩
  first
    | linear_combination hn
    | linarith

/-- The magnetic factor one step up in `r`: `mag d (r + 1) = mag d r * exp ((2π / d²) * I)`. -/
theorem mag_succ (d : ℕ) (r : ℤ) :
    mag d (r + 1) =
      mag d r * Complex.exp (((2 * Real.pi / (d : ℝ) ^ 2 : ℝ) : ℂ) * Complex.I) := by
  have hc : ((r + 1 : ℤ) : ℂ) = (r : ℂ) + 1 := by
    first
      | rw [Int.cast_add, Int.cast_one]
      | push_cast
      | simp
  have hθ : ((2 * Real.pi / (d : ℝ) ^ 2 : ℝ) : ℂ) = 2 * (Real.pi : ℂ) / (d : ℂ) ^ 2 := by
    first
      | (push_cast; ring1)
      | push_cast
      | (simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
          Complex.ofReal_natCast, Complex.ofReal_pow])
      | simp
  unfold mag
  rw [← Complex.exp_add, hc, hθ]
  refine congrArg Complex.exp ?_
  ring

/-- The product of the four edge phases: the corner factors `b` and `f` cancel. -/
theorem plaquette_phase_algebra {m e a b c f : ℂ} (hb : b * conj b = 1) (hf : f * conj f = 1) :
    m * b * conj a * (c * conj b) * e = m * e * c * conj f * (f * conj a) := by
  linear_combination (m * e * conj a * c) * hb - (m * e * conj a * c) * hf

/-- `v * conj u` has modulus one when `u` and `v` do. -/
theorem norm_mul_conj_eq_one {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : ‖v * conj u‖ = 1 := by
  rw [norm_mul, Complex.norm_conj, hu, hv, one_mul]

/-- **B2b, the plaquette identity (L3).** For a unit-modulus array, the oriented sum of the four
covariant edge numbers of a plaquette is `-(2π / d²)` up to an integer multiple of `2π`. -/
theorem plaquette_identity (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1) (q r : ℤ) :
    ∃ n : ℤ, aQ d ζ q r + aR ζ (q + 1) r - aQ d ζ q (r + 1) - aR ζ q r =
      -(2 * Real.pi / (d : ℝ) ^ 2) + 2 * Real.pi * n := by
  have hm : ‖mag d r * ζ (q + 1, r)‖ = 1 := by
    rw [norm_mul, norm_mag, hζ, one_mul]
  have hm' : ‖mag d (r + 1) * ζ (q + 1, r + 1)‖ = 1 := by
    rw [norm_mul, norm_mag, hζ, one_mul]
  have h₁ : ‖mag d r * ζ (q + 1, r) * conj (ζ (q, r))‖ = 1 :=
    norm_mul_conj_eq_one (hζ (q, r)) hm
  have h₂ : ‖ζ (q + 1, r + 1) * conj (ζ (q + 1, r))‖ = 1 :=
    norm_mul_conj_eq_one (hζ (q + 1, r)) (hζ (q + 1, r + 1))
  have h₃ : ‖mag d (r + 1) * ζ (q + 1, r + 1) * conj (ζ (q, r + 1))‖ = 1 :=
    norm_mul_conj_eq_one (hζ (q, r + 1)) hm'
  have h₄ : ‖ζ (q, r + 1) * conj (ζ (q, r))‖ = 1 :=
    norm_mul_conj_eq_one (hζ (q, r)) (hζ (q, r + 1))
  have hprod : mag d r * ζ (q + 1, r) * conj (ζ (q, r)) *
      (ζ (q + 1, r + 1) * conj (ζ (q + 1, r))) *
        Complex.exp (((2 * Real.pi / (d : ℝ) ^ 2 : ℝ) : ℂ) * Complex.I) =
      mag d (r + 1) * ζ (q + 1, r + 1) * conj (ζ (q, r + 1)) *
        (ζ (q, r + 1) * conj (ζ (q, r))) := by
    rw [mag_succ d r]
    exact plaquette_phase_algebra (mul_conj_of_norm_eq_one (hζ (q + 1, r)))
      (mul_conj_of_norm_eq_one (hζ (q, r + 1)))
  unfold aQ aR
  exact arg_add_arg_sub_of_mul_eq h₁ h₂ h₃ h₄ (2 * Real.pi / (d : ℝ) ^ 2) hprod

/-- (L3) for twisted arrays: only the unit modulus of `IsTwisted` is used. -/
theorem plaquette_identity_of_isTwisted {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (q r : ℤ) :
    ∃ n : ℤ, aQ d ζ q r + aR ζ (q + 1) r - aQ d ζ q (r + 1) - aR ζ q r =
      -(2 * Real.pi / (d : ℝ) ^ 2) + 2 * Real.pi * n :=
  plaquette_identity d ζ h.norm_eq_one q r

end BLT

end
