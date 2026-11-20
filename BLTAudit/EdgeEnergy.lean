import BLTAudit.Basic

/-!
# B1. Edge energy in terms of covariant edge angles, (L1)

For unit complex numbers `u`, `v`, `‖v − u‖² = 4 sin²(arg(v ū)/2)`. Applied to every positive edge
of a unit-modulus array, this rewrites the Zak energy `zakEnergy d ζ` of `BLTAudit/Basic.lean` as the
paper's (L1): `A_d(ζ) = ∑_{q,r} (4 sin²(a^r_{q,r}/2) + 4 sin²(a^q_{q,r}/2))`.

* `norm_exp_sub_one_sq`: `‖e^{iθ} − 1‖² = 4 sin²(θ/2)`;
* `norm_sub_sq_eq_four_sin_sq`: the identity for unit `u`, `v`;
* `norm_mag`: the magnetic multiplier `e^{2πir/d²}` has modulus one;
* `zakEnergy_eq_sin_sq`: (L1) for any array with `‖ζ p‖ = 1` for all `p`.

What this file does NOT prove: the plaquette identity (L3), total charge one (L4), the cell count
(L5), or any lower bound on `zakEnergy`; nothing here bears on Theorem 4.1 or Theorem 1.1.
-/

noncomputable section

open Finset Complex
open scoped ComplexConjugate Real

namespace BLT

/-- `‖e^{iθ} − 1‖² = 4 sin²(θ/2)`. -/
theorem norm_exp_sub_one_sq (θ : ℝ) :
    ‖Complex.exp (θ * I) - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
  have h2 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have hθ : θ = 2 * (θ / 2) := by ring
    conv_lhs => rw [hθ]
    rw [Real.cos_two_mul]
    linear_combination 2 * Real.sin_sq_add_cos_sq (θ / 2)
  linear_combination Real.sin_sq_add_cos_sq θ - 2 * h2

/-- **B1.** For unit `u`, `v`: `‖v − u‖² = 4 sin²(arg(v ū)/2)`. -/
theorem norm_sub_sq_eq_four_sin_sq (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖v - u‖ ^ 2 = 4 * Real.sin (Complex.arg (v * conj u) / 2) ^ 2 := by
  have hw1 : ‖v * conj u‖ = 1 := by rw [norm_mul, Complex.norm_conj, hu, hv, one_mul]
  have huu : conj u * u = 1 := by
    rw [Complex.conj_mul', hu]
    norm_num
  have hvu : v - u = (v * conj u - 1) * u := by linear_combination (-v) * huu
  set θ := Complex.arg (v * conj u) with hθ
  have hexp : Complex.exp (θ * I) = v * conj u := by
    have h := Complex.norm_mul_exp_arg_mul_I (v * conj u)
    rwa [hw1, Complex.ofReal_one, one_mul] at h
  rw [hvu, norm_mul, hu, mul_one, ← hexp, norm_exp_sub_one_sq]

/-- The magnetic multiplier has modulus one. -/
theorem norm_mag (d : ℕ) (r : ℤ) : ‖mag d r‖ = 1 := by
  have h : mag d r = Complex.exp (((2 * Real.pi * r / (d : ℝ) ^ 2 : ℝ) : ℂ) * I) := by
    unfold mag
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- **B1, (L1).** For a unit-modulus array, the Zak energy is the sum of `4 sin²(a/2)` over the
covariant edge angles. -/
theorem zakEnergy_eq_sin_sq (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1) :
    zakEnergy d ζ = ∑ q ∈ range d, ∑ r ∈ range d,
      (4 * Real.sin (aR ζ (q : ℤ) (r : ℤ) / 2) ^ 2 +
        4 * Real.sin (aQ d ζ (q : ℤ) (r : ℤ) / 2) ^ 2) := by
  unfold zakEnergy
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  have hm : ‖mag d (r : ℤ) * ζ ((q : ℤ) + 1, (r : ℤ))‖ = 1 := by
    rw [norm_mul, norm_mag, hζ, one_mul]
  rw [norm_sub_sq_eq_four_sin_sq _ _ (hζ _) (hζ _), norm_sub_sq_eq_four_sin_sq _ _ (hζ _) hm]
  rfl

end BLT

end
