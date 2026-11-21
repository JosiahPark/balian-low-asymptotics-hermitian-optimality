import BLTAudit.Basic

/-!
# B2a. Periodic edge numbers

For a twisted unit array (`IsTwisted d ζ` of `BLTAudit/Basic.lean`), the covariant edge numbers
`aQ d ζ` and `aR ζ` of paper §4.1 are `d`-periodic in each variable. For all integers `q r`:

* `aR_add_period_q`: `aR ζ (q + d) r = aR ζ q r` (from `shift_q` alone);
* `aR_add_period_r`: `aR ζ q (r + d) = aR ζ q r` (the twist factor `e^{-2πiq/d}` of `shift_r`
  meets its conjugate);
* `aQ_add_period_q`: `aQ d ζ (q + d) r = aQ d ζ q r` (from `shift_q` alone);
* `aQ_add_period_r`: if `0 < d`, `aQ d ζ q (r + d) = aQ d ζ q r` (the twist factors at `q + 1`
  and at `q` leave `e^{-2πi/d}`, which cancels the factor `e^{2πi/d}` picked up by
  `mag d (r + d)`).

Each is proved as an equality of the complex numbers under `Complex.arg`, so no branch of the
argument is chosen. Helper lemmas: `mul_conj_of_norm_eq_one` (`c * conj c = 1` for `‖c‖ = 1`),
`unit_mul_mul_conj`, `mag_twist_cancel` (two cancellations in `ℂ`), `norm_twist_factor`
(`‖e^{-2πiq/d}‖ = 1`, obtained here from `norm_eq_one` and `shift_r` of the hypothesis, although
it holds for all `q` and `d`), and `mag_add_period_mul_twist`:
`mag d (r + d) * e^{-2πi(q+1)/d} = mag d r * e^{-2πiq/d}` for `0 < d`.

The hypothesis `0 < d` of `aQ_add_period_r` is the one in the roadmap item; it is used to divide
by `d` in `ℂ`. (For `d = 0` the statement is trivial because `r + 0 = r`; that case is not stated
here.) Only one period is shifted; shifts by integer multiples of `d` are not stated.

What this file does NOT prove: the plaquette identity (L3) (item B2b), total charge one (L4)
(item B3), or any bound for `zakEnergy`. It proves nothing toward Theorem 1.1 or Theorem 4.1 of
the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

open scoped ComplexConjugate

namespace BLT

/-- A unit complex number times its conjugate is `1`. -/
theorem mul_conj_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) : c * conj c = 1 := by
  first
    | (rw [Complex.mul_conj', hc]; simp)
    | (rw [Complex.mul_conj', hc]; norm_num)
    | (rw [Complex.mul_conj, ← Complex.sq_norm, hc]; simp)

/-- A common unit factor cancels in `v * conj u`. -/
theorem unit_mul_mul_conj {c : ℂ} (hc : ‖c‖ = 1) (u v : ℂ) :
    c * v * conj (c * u) = v * conj u := by
  have hcc : c * conj c = 1 := mul_conj_of_norm_eq_one hc
  have hm : conj (c * u) = conj c * conj u := by
    first
      | exact map_mul _ _ _
      | rw [map_mul]
      | simp
  rw [hm]
  linear_combination (v * conj u) * hcc

/-- If `m' * c' = m * c` and `‖c‖ = 1`, then `m' * (c' * v) * conj (c * u) = m * v * conj u`. -/
theorem mag_twist_cancel {m m' c c' : ℂ} (hc : ‖c‖ = 1) (hm : m' * c' = m * c) (u v : ℂ) :
    m' * (c' * v) * conj (c * u) = m * v * conj u := by
  have hu : c * v * conj (c * u) = v * conj u := unit_mul_mul_conj hc u v
  linear_combination (v * conj (c * u)) * hm + m * hu

/-- The twist factor `e^{-2πiq/d}` of `shift_r` has modulus one (read off from the unit modulus
of `ζ (q, 0 + d)` and of `ζ (q, 0)`). -/
theorem norm_twist_factor {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (q : ℤ) :
    ‖Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ))‖ = 1 := by
  have h1 : ‖ζ (q, 0 + (d : ℤ))‖ = 1 := h.norm_eq_one _
  rw [h.shift_r q 0, norm_mul, h.norm_eq_one (q, 0), mul_one] at h1
  exact h1

/-- The magnetic factor one period up in `r`, against the twist factors at `q + 1` and at `q`:
`mag d (r + d) * e^{-2πi(q+1)/d} = mag d r * e^{-2πiq/d}` for `0 < d`. -/
theorem mag_add_period_mul_twist {d : ℕ} (hd : 0 < d) (q r : ℤ) :
    mag d (r + (d : ℤ)) *
        Complex.exp (-2 * Real.pi * Complex.I * ((q + 1 : ℤ) : ℂ) / (d : ℂ)) =
      mag d r * Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hinv : (d : ℂ) * (d : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hd0
  have hcr : ((r + (d : ℤ) : ℤ) : ℂ) = (r : ℂ) + (d : ℂ) := by
    first
      | rw [Int.cast_add, Int.cast_natCast]
      | push_cast
      | simp
  have hcq : ((q + 1 : ℤ) : ℂ) = (q : ℂ) + 1 := by
    first
      | rw [Int.cast_add, Int.cast_one]
      | push_cast
      | simp
  unfold mag
  rw [← Complex.exp_add, ← Complex.exp_add, hcr, hcq]
  refine congrArg Complex.exp ?_
  first
    | linear_combination (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ)⁻¹) * hinv
    | (field_simp; ring)
    | field_simp

/-- **B2a.** The `r`-edge numbers are `d`-periodic in `q`. -/
theorem aR_add_period_q {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (q r : ℤ) :
    aR ζ (q + (d : ℤ)) r = aR ζ q r := by
  have key : ζ (q + (d : ℤ), r + 1) * conj (ζ (q + (d : ℤ), r)) =
      ζ (q, r + 1) * conj (ζ (q, r)) := by
    rw [h.shift_q q (r + 1), h.shift_q q r]
  unfold aR
  exact congrArg Complex.arg key

/-- **B2a.** The `r`-edge numbers are `d`-periodic in `r`: the twist factor meets its
conjugate. -/
theorem aR_add_period_r {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (q r : ℤ) :
    aR ζ q (r + (d : ℤ)) = aR ζ q r := by
  have e : r + (d : ℤ) + 1 = r + 1 + (d : ℤ) := by ring
  have key : ζ (q, r + (d : ℤ) + 1) * conj (ζ (q, r + (d : ℤ))) =
      ζ (q, r + 1) * conj (ζ (q, r)) := by
    rw [e, h.shift_r q (r + 1), h.shift_r q r]
    exact unit_mul_mul_conj (norm_twist_factor h q) _ _
  unfold aR
  exact congrArg Complex.arg key

/-- **B2a.** The `q`-edge numbers are `d`-periodic in `q`. -/
theorem aQ_add_period_q {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (q r : ℤ) :
    aQ d ζ (q + (d : ℤ)) r = aQ d ζ q r := by
  have e : q + (d : ℤ) + 1 = q + 1 + (d : ℤ) := by ring
  have key : mag d r * ζ (q + (d : ℤ) + 1, r) * conj (ζ (q + (d : ℤ), r)) =
      mag d r * ζ (q + 1, r) * conj (ζ (q, r)) := by
    rw [e, h.shift_q (q + 1) r, h.shift_q q r]
  unfold aQ
  exact congrArg Complex.arg key

/-- **B2a.** For `0 < d`, the `q`-edge numbers are `d`-periodic in `r`: the magnetic factor
gains `e^{2πi/d}`, and the twist factors at `q + 1` and at `q` leave `e^{-2πi/d}`. -/
theorem aQ_add_period_r {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (hd : 0 < d) (q r : ℤ) :
    aQ d ζ q (r + (d : ℤ)) = aQ d ζ q r := by
  have key : mag d (r + (d : ℤ)) * ζ (q + 1, r + (d : ℤ)) * conj (ζ (q, r + (d : ℤ))) =
      mag d r * ζ (q + 1, r) * conj (ζ (q, r)) := by
    rw [h.shift_r (q + 1) r, h.shift_r q r]
    exact mag_twist_cancel (norm_twist_factor h q) (mag_add_period_mul_twist hd q r) _ _
  unfold aQ
  exact congrArg Complex.arg key

end BLT

end
