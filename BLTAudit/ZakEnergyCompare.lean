import BLTAudit.LowerBoundZak

/-!
# H12–H13. Comparing Zak energies: constant phases, sums, and the `ℓ²` bound

For arrays on `ℤ²` and the twisted continuation `zakExt` of H4. Proved here:

* `norm_mag`: the magnetic multiplier is unimodular;
* `zakExt_add`, `zakExt_const_mul`, `zakExt_neg`: `zakExt` is linear in the array;
* `zakEnergy_const_mul` (H12): a constant unimodular factor does not change `zakEnergy`;
* `sq_norm_add_le_mul`: `‖x + y‖² ≤ (1 + t) ‖x‖² + (1 + t⁻¹) ‖y‖²` for `t > 0`;
* `zakEnergy_add_le` (H13): `A(ζ + δ) ≤ (1 + t) A(ζ) + (1 + t⁻¹) A(δ)` for `t > 0`;
* `zakEnergy_zakExt_le` (H13): `A(zakExt u) ≤ 8 ∑_{q,r} ‖u q r‖²` (each edge costs at most
  `2‖x‖² + 2‖y‖²`, and shifting `q` or `r` by one permutes `ZMod d`).

Together these are the polarization step of §3.2 in a form that needs no square roots: if
`∑ ‖W − U‖²` is small, `A(zakExt W)` and `A(zakExt U)` are close.

What this file does NOT prove: any bound on a specific array; nothing toward [HV], [HE], [HL] or
Theorem 1.1.
-/

noncomputable section

open scoped Real

namespace BLT

variable {d : ℕ} [NeZero d]

theorem norm_mag (r : ℤ) : ‖mag d r‖ = 1 := by
  unfold mag
  have h : 2 * Real.pi * Complex.I * (r : ℂ) / ((d : ℂ) ^ 2) =
      ((2 * Real.pi * r / (d : ℝ) ^ 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  first
    | exact Complex.norm_exp_ofReal_mul_I _
    | simp [Complex.norm_exp]

theorem zakExt_add (u v : ZMod d → ZMod d → ℂ) :
    zakExt d (fun q r => u q r + v q r) = fun p => zakExt d u p + zakExt d v p := by
  funext p
  simp only [zakExt]
  ring

theorem zakExt_const_mul (c : ℂ) (u : ZMod d → ZMod d → ℂ) :
    zakExt d (fun q r => c * u q r) = fun p => c * zakExt d u p := by
  funext p
  simp only [zakExt]
  ring

theorem zakExt_neg (u : ZMod d → ZMod d → ℂ) :
    zakExt d (fun q r => -u q r) = fun p => -zakExt d u p := by
  funext p
  simp only [zakExt]
  ring

/-- **H12.** A constant unimodular factor does not change the Zak energy. -/
theorem zakEnergy_const_mul (u₀ : ℂ) (hu₀ : ‖u₀‖ = 1) (ζ : ℤ × ℤ → ℂ) :
    zakEnergy d (fun p => u₀ * ζ p) = zakEnergy d ζ := by
  unfold zakEnergy
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  have e1 : u₀ * ζ ((q : ℤ), (r : ℤ) + 1) - u₀ * ζ ((q : ℤ), (r : ℤ)) =
      u₀ * (ζ ((q : ℤ), (r : ℤ) + 1) - ζ ((q : ℤ), (r : ℤ))) := by ring
  have e2 : mag d (r : ℤ) * (u₀ * ζ ((q : ℤ) + 1, (r : ℤ))) - u₀ * ζ ((q : ℤ), (r : ℤ)) =
      u₀ * (mag d (r : ℤ) * ζ ((q : ℤ) + 1, (r : ℤ)) - ζ ((q : ℤ), (r : ℤ))) := by ring
  show ‖u₀ * ζ ((q : ℤ), (r : ℤ) + 1) - u₀ * ζ ((q : ℤ), (r : ℤ))‖ ^ 2 +
      ‖mag d (r : ℤ) * (u₀ * ζ ((q : ℤ) + 1, (r : ℤ))) - u₀ * ζ ((q : ℤ), (r : ℤ))‖ ^ 2 = _
  rw [e1, e2, norm_mul, norm_mul, hu₀, one_mul, one_mul]

/-- `‖x + y‖² ≤ (1 + t) ‖x‖² + (1 + t⁻¹) ‖y‖²` for `t > 0`. -/
theorem sq_norm_add_le_mul (x y : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖x + y‖ ^ 2 ≤ (1 + t) * ‖x‖ ^ 2 + (1 + t⁻¹) * ‖y‖ ^ 2 := by
  have hs : t⁻¹ * t = 1 := inv_mul_cancel₀ ht.ne'
  have h1 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  have h2 : t⁻¹ * (t * ‖x‖ - ‖y‖) ^ 2 = t * ‖x‖ ^ 2 - 2 * ‖x‖ * ‖y‖ + t⁻¹ * ‖y‖ ^ 2 := by
    linear_combination (t * ‖x‖ ^ 2 - 2 * ‖x‖ * ‖y‖) * hs
  have h3 : 0 ≤ t⁻¹ * (t * ‖x‖ - ‖y‖) ^ 2 := mul_nonneg (inv_nonneg.mpr ht.le) (sq_nonneg _)
  nlinarith [h1, h2, h3]

/-- **H13.** `A(ζ + δ) ≤ (1 + t) A(ζ) + (1 + t⁻¹) A(δ)` for `t > 0`. -/
theorem zakEnergy_add_le (ζ δ : ℤ × ℤ → ℂ) {t : ℝ} (ht : 0 < t) :
    zakEnergy d (fun p => ζ p + δ p) ≤ (1 + t) * zakEnergy d ζ + (1 + t⁻¹) * zakEnergy d δ := by
  unfold zakEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun r _ => ?_
  have a1 := sq_norm_add_le_mul (ζ ((q : ℤ), (r : ℤ) + 1) - ζ ((q : ℤ), (r : ℤ)))
    (δ ((q : ℤ), (r : ℤ) + 1) - δ ((q : ℤ), (r : ℤ))) ht
  have a2 := sq_norm_add_le_mul (mag d (r : ℤ) * ζ ((q : ℤ) + 1, (r : ℤ)) - ζ ((q : ℤ), (r : ℤ)))
    (mag d (r : ℤ) * δ ((q : ℤ) + 1, (r : ℤ)) - δ ((q : ℤ), (r : ℤ))) ht
  have e1 : ζ ((q : ℤ), (r : ℤ) + 1) + δ ((q : ℤ), (r : ℤ) + 1) -
      (ζ ((q : ℤ), (r : ℤ)) + δ ((q : ℤ), (r : ℤ))) =
      (ζ ((q : ℤ), (r : ℤ) + 1) - ζ ((q : ℤ), (r : ℤ))) +
        (δ ((q : ℤ), (r : ℤ) + 1) - δ ((q : ℤ), (r : ℤ))) := by ring
  have e2 : mag d (r : ℤ) * (ζ ((q : ℤ) + 1, (r : ℤ)) + δ ((q : ℤ) + 1, (r : ℤ))) -
      (ζ ((q : ℤ), (r : ℤ)) + δ ((q : ℤ), (r : ℤ))) =
      (mag d (r : ℤ) * ζ ((q : ℤ) + 1, (r : ℤ)) - ζ ((q : ℤ), (r : ℤ))) +
        (mag d (r : ℤ) * δ ((q : ℤ) + 1, (r : ℤ)) - δ ((q : ℤ), (r : ℤ))) := by ring
  show ‖ζ ((q : ℤ), (r : ℤ) + 1) + δ ((q : ℤ), (r : ℤ) + 1) -
        (ζ ((q : ℤ), (r : ℤ)) + δ ((q : ℤ), (r : ℤ)))‖ ^ 2 +
      ‖mag d (r : ℤ) * (ζ ((q : ℤ) + 1, (r : ℤ)) + δ ((q : ℤ) + 1, (r : ℤ))) -
        (ζ ((q : ℤ), (r : ℤ)) + δ ((q : ℤ), (r : ℤ)))‖ ^ 2 ≤ _
  rw [e1, e2]
  linarith [a1, a2]

/-- `‖x − y‖² ≤ 2 ‖x‖² + 2 ‖y‖²`. -/
theorem sq_norm_sub_le (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith [h, sq_nonneg (‖x‖ - ‖y‖)]

theorem norm_zakExt_eq (u : ZMod d → ZMod d → ℂ) (p : ℤ × ℤ) :
    ‖zakExt d u p‖ = ‖u (p.1 : ZMod d) (p.2 : ZMod d)‖ := by
  unfold zakExt
  rw [norm_mul, norm_twistFactor, one_mul]

/-- **H13.** `A(zakExt u) ≤ 8 ∑_{q,r} ‖u q r‖²`. -/
theorem zakEnergy_zakExt_le (u : ZMod d → ZMod d → ℂ) :
    zakEnergy d (zakExt d u) ≤ 8 * ∑ q : ZMod d, ∑ r : ZMod d, ‖u q r‖ ^ 2 := by
  have hterm : ∀ q r : ℕ,
      ‖zakExt d u ((q : ℤ), (r : ℤ) + 1) - zakExt d u ((q : ℤ), (r : ℤ))‖ ^ 2 +
        ‖mag d (r : ℤ) * zakExt d u ((q : ℤ) + 1, (r : ℤ)) - zakExt d u ((q : ℤ), (r : ℤ))‖ ^ 2 ≤
      2 * ‖u (q : ZMod d) ((r : ZMod d) + 1)‖ ^ 2 + 4 * ‖u (q : ZMod d) (r : ZMod d)‖ ^ 2 +
        2 * ‖u ((q : ZMod d) + 1) (r : ZMod d)‖ ^ 2 := by
    intro q r
    have a1 := sq_norm_sub_le (zakExt d u ((q : ℤ), (r : ℤ) + 1)) (zakExt d u ((q : ℤ), (r : ℤ)))
    have a2 := sq_norm_sub_le (mag d (r : ℤ) * zakExt d u ((q : ℤ) + 1, (r : ℤ)))
      (zakExt d u ((q : ℤ), (r : ℤ)))
    rw [norm_mul, norm_mag, one_mul] at a2
    have n1 : ‖zakExt d u ((q : ℤ), (r : ℤ) + 1)‖ = ‖u (q : ZMod d) ((r : ZMod d) + 1)‖ := by
      rw [norm_zakExt_eq]
      first
        | (push_cast; rfl)
        | push_cast
        | simp
    have n2 : ‖zakExt d u ((q : ℤ), (r : ℤ))‖ = ‖u (q : ZMod d) (r : ZMod d)‖ := by
      rw [norm_zakExt_eq]
      first
        | (push_cast; rfl)
        | push_cast
        | simp
    have n3 : ‖zakExt d u ((q : ℤ) + 1, (r : ℤ))‖ = ‖u ((q : ZMod d) + 1) (r : ZMod d)‖ := by
      rw [norm_zakExt_eq]
      first
        | (push_cast; rfl)
        | push_cast
        | simp
    rw [n1, n2] at a1
    rw [n3, n2] at a2
    linarith
  have hshift_r : ∑ q : ZMod d, ∑ r : ZMod d, ‖u q (r + 1)‖ ^ 2 =
      ∑ q : ZMod d, ∑ r : ZMod d, ‖u q r‖ ^ 2 := by
    refine Finset.sum_congr rfl fun q _ => ?_
    exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod d)) _ _ fun r => rfl
  have hshift_q : ∑ q : ZMod d, ∑ r : ZMod d, ‖u (q + 1) r‖ ^ 2 =
      ∑ q : ZMod d, ∑ r : ZMod d, ‖u q r‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod d)) _ _ fun q => rfl
  set S : ℝ := ∑ q : ZMod d, ∑ r : ZMod d, ‖u q r‖ ^ 2 with hS
  calc zakEnergy d (zakExt d u)
      = ∑ q ∈ Finset.range d, ∑ r ∈ Finset.range d,
          (‖zakExt d u ((q : ℤ), (r : ℤ) + 1) - zakExt d u ((q : ℤ), (r : ℤ))‖ ^ 2 +
            ‖mag d (r : ℤ) * zakExt d u ((q : ℤ) + 1, (r : ℤ)) -
              zakExt d u ((q : ℤ), (r : ℤ))‖ ^ 2) := rfl
    _ ≤ ∑ q ∈ Finset.range d, ∑ r ∈ Finset.range d,
          (2 * ‖u (q : ZMod d) ((r : ZMod d) + 1)‖ ^ 2 + 4 * ‖u (q : ZMod d) (r : ZMod d)‖ ^ 2 +
            2 * ‖u ((q : ZMod d) + 1) (r : ZMod d)‖ ^ 2) :=
        Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun r _ => hterm q r
    _ = ∑ q : ZMod d, ∑ r : ZMod d,
          (2 * ‖u q (r + 1)‖ ^ 2 + 4 * ‖u q r‖ ^ 2 + 2 * ‖u (q + 1) r‖ ^ 2) :=
        (sum_sum_zmod_eq_sum_range fun q r : ZMod d =>
          2 * ‖u q (r + 1)‖ ^ 2 + 4 * ‖u q r‖ ^ 2 + 2 * ‖u (q + 1) r‖ ^ 2).symm
    _ = 2 * (∑ q : ZMod d, ∑ r : ZMod d, ‖u q (r + 1)‖ ^ 2) + 4 * S +
          2 * (∑ q : ZMod d, ∑ r : ZMod d, ‖u (q + 1) r‖ ^ 2) := by
        rw [hS]
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 8 * S := by
        rw [hshift_r, hshift_q]
        ring

end BLT

end
