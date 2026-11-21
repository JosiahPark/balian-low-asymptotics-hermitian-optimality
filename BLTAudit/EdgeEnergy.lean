import BLTAudit.Basic

/-!
# B1. Edge energy (L1)

For unit complex numbers the squared chord is `4 sin²` of half the principal angle, and therefore
the Zak energy of a unit-modulus array is the sum of `4 sin²(a/2)` over its covariant edge numbers
(paper §4, equation (L1)). With `mag`, `aQ`, `aR`, `zakEnergy` of `BLTAudit/Basic.lean`:

* `norm_sub_one_sq_of_norm_eq_one`: if `‖w‖ = 1` then `‖w − 1‖² = 4 sin²(arg w / 2)`;
* `norm_sub_sq_eq_four_sin_sq`: if `‖u‖ = ‖v‖ = 1` then
  `‖v − u‖² = 4 sin²(arg (v · conj u) / 2)`;
* `norm_mag`: the magnetic multiplier has `‖mag d r‖ = 1`;
* `norm_sq_edgeR`, `norm_sq_edgeQ`: for a unit-modulus `ζ : ℤ × ℤ → ℂ` and all integers `q r`,
  `‖ζ (q, r + 1) − ζ (q, r)‖² = 4 sin²(aR ζ q r / 2)` and
  `‖mag d r · ζ (q + 1, r) − ζ (q, r)‖² = 4 sin²(aQ d ζ q r / 2)`;
* `zakEnergy_eq_sum_sin_sq`: for a unit-modulus `ζ`,
  `zakEnergy d ζ = ∑_{q, r < d} (4 sin²(aR ζ q r / 2) + 4 sin²(aQ d ζ q r / 2))`, which is (L1);
  `zakEnergy_eq_sum_sin_sq_of_isTwisted` is the same under `IsTwisted d ζ`.

Only unit modulus is used; the gluing of `IsTwisted` plays no role here. The sum is over the
naturals `q r < d`, exactly as in the definition of `zakEnergy`; the paper writes it over
`q, r (mod d)`, which agrees once the edge numbers are known to be `d`-periodic (item B2, not
proved here).

What this file does NOT prove: the periodicity of the edge numbers, the plaquette identity (L3),
total charge one (L4), or any lower bound for `zakEnergy`. It proves nothing toward Theorem 1.1
or Theorem 4.1 of the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

open Finset
open scoped ComplexConjugate

namespace BLT

/-- For a unit complex number `w`, `‖w − 1‖² = 4 sin²(arg w / 2)`. -/
theorem norm_sub_one_sq_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) :
    ‖w - 1‖ ^ 2 = 4 * Real.sin (Complex.arg w / 2) ^ 2 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact zero_ne_one hw
  have hcos : Real.cos (Complex.arg w) = w.re := by
    rw [Complex.cos_arg hw0, hw, div_one]
  have hnorm : w.re * w.re + w.im * w.im = 1 := by
    have h : Complex.normSq w = 1 := by
      rw [← Complex.sq_norm, hw, one_pow]
    rwa [Complex.normSq_apply] at h
  have hhalf : Real.cos (Complex.arg w) = 1 - 2 * Real.sin (Complex.arg w / 2) ^ 2 := by
    have h := Real.cos_two_mul_eq_one_sub (Complex.arg w / 2)
    have e : 2 * (Complex.arg w / 2) = Complex.arg w := by ring
    rwa [e] at h
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  first
    | linear_combination hnorm + 2 * hcos - 2 * hhalf
    | nlinarith [hnorm, hcos, hhalf]

/-- **(L1), one edge.** For unit complex numbers `u v`,
`‖v − u‖² = 4 sin²(arg (v · conj u) / 2)`. -/
theorem norm_sub_sq_eq_four_sin_sq {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖v - u‖ ^ 2 = 4 * Real.sin (Complex.arg (v * conj u) / 2) ^ 2 := by
  have hw : ‖v * conj u‖ = 1 := by
    rw [norm_mul, Complex.norm_conj, hu, hv, one_mul]
  have huu : u * conj u = 1 := by
    first
      | (rw [Complex.mul_conj', hu]; simp)
      | (rw [Complex.mul_conj', hu]; norm_num)
      | (rw [Complex.mul_conj, ← Complex.sq_norm, hu]; simp)
  have key : v - u = (v * conj u - 1) * u := by
    have h : (v * conj u - 1) * u = v * (u * conj u) - u := by ring
    rw [h, huu, mul_one]
  rw [key, norm_mul, hu, mul_one]
  exact norm_sub_one_sq_of_norm_eq_one hw

/-- The magnetic multiplier `e^{2πir/d²}` has modulus one. -/
theorem norm_mag (d : ℕ) (r : ℤ) : ‖mag d r‖ = 1 := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) / ((d : ℂ) ^ 2) =
      ((2 * Real.pi * (r : ℝ) / ((d : ℝ) ^ 2) : ℝ) : ℂ) * Complex.I := by
    first
      | (push_cast; ring1)
      | (simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
          Complex.ofReal_intCast, Complex.ofReal_natCast, Complex.ofReal_pow]; ring1)
  show ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) / ((d : ℂ) ^ 2))‖ = 1
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **(L1), `r`-edges.** For a unit-modulus array, `‖ζ (q, r + 1) − ζ (q, r)‖² = 4 sin²(a^r/2)`. -/
theorem norm_sq_edgeR (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1) (q r : ℤ) :
    ‖ζ (q, r + 1) - ζ (q, r)‖ ^ 2 = 4 * Real.sin (aR ζ q r / 2) ^ 2 := by
  unfold aR
  exact norm_sub_sq_eq_four_sin_sq (hζ _) (hζ _)

/-- **(L1), `q`-edges.** For a unit-modulus array,
`‖mag d r · ζ (q + 1, r) − ζ (q, r)‖² = 4 sin²(a^q/2)`. -/
theorem norm_sq_edgeQ (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1) (q r : ℤ) :
    ‖mag d r * ζ (q + 1, r) - ζ (q, r)‖ ^ 2 = 4 * Real.sin (aQ d ζ q r / 2) ^ 2 := by
  have hv : ‖mag d r * ζ (q + 1, r)‖ = 1 := by
    rw [norm_mul, norm_mag, hζ, one_mul]
  unfold aQ
  exact norm_sub_sq_eq_four_sin_sq (hζ _) hv

/-- **B1, the statement (L1).** For a unit-modulus array `ζ`, the Zak energy is the sum of
`4 sin²(a/2)` over the covariant edge numbers of the `d × d` square. -/
theorem zakEnergy_eq_sum_sin_sq (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1) :
    zakEnergy d ζ = ∑ q ∈ range d, ∑ r ∈ range d,
      (4 * Real.sin (aR ζ (q : ℤ) (r : ℤ) / 2) ^ 2 +
        4 * Real.sin (aQ d ζ (q : ℤ) (r : ℤ) / 2) ^ 2) := by
  unfold zakEnergy
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  rw [norm_sq_edgeR ζ hζ (q : ℤ) (r : ℤ), norm_sq_edgeQ d ζ hζ (q : ℤ) (r : ℤ)]

/-- (L1) for twisted arrays: only the unit modulus of `IsTwisted` is used. -/
theorem zakEnergy_eq_sum_sin_sq_of_isTwisted {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) :
    zakEnergy d ζ = ∑ q ∈ range d, ∑ r ∈ range d,
      (4 * Real.sin (aR ζ (q : ℤ) (r : ℤ) / 2) ^ 2 +
        4 * Real.sin (aQ d ζ (q : ℤ) (r : ℤ) / 2) ^ 2) :=
  zakEnergy_eq_sum_sin_sq d ζ h.norm_eq_one

end BLT

end
