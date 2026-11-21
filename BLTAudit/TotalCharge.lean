import BLTAudit.Basic
import BLTAudit.EdgePeriodicity
import BLTAudit.PlaquetteCharge

/-!
# B3. Total charge one (L4)

For a twisted unit array (`IsTwisted d ζ` of `BLTAudit/Basic.lean`) with `0 < d`, the plaquette
integers of (L3) over the square `0 ≤ q, r < d` sum to `1` (paper §4.1, equation (L4)).

* `plaquetteCharge d ζ q r : ℤ`: the plaquette integer as a function of the plaquette (the
  oriented sum of the four edge numbers plus `2π / d²`, divided by `2π` and rounded);
* `plaquetteCharge_eq_of_identity`: an integer `n` that satisfies (L3) at `(q, r)` equals
  `plaquetteCharge d ζ q r` (no hypothesis on `ζ`);
* `plaquetteCharge_spec`: for a unit-modulus array, (L3) holds with `n = plaquetteCharge d ζ q r`
  (from `plaquette_identity` of B2b);
* `sum_plaquette_edges_eq_zero`: under `IsTwisted d ζ` and `0 < d`, the oriented edge sums of the
  plaquettes with `q r < d` add up to `0`: they telescope (`sum_range_int_telescope`), and the
  boundary terms cancel by `aQ_add_period_r` and `aR_add_period_q` of B2a;
* `sum_plaquette_int_eq_one`: any integers `n q r` that satisfy (L3) on the square sum to `1`
  (the constants `-(2π / d²)` add up to `-2π`, by `sum_sum_range_const_add_mul`);
* `total_charge_one`: `∑ q r < d, plaquetteCharge d ζ q r = 1`. This is item B3.

The sums are over naturals `q r < d`, as in `zakEnergy`; the paper sums over `q, r (mod d)`.
The hypothesis `0 < d` is needed: for `d = 0` the sum is empty.

What this file does NOT prove: that `plaquetteCharge d ζ` is `d`-periodic, where the charge sits,
that good plaquettes are neutral (item B4), or any bound for `zakEnergy`. It proves nothing
toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

open Finset
open scoped ComplexConjugate

namespace BLT

/-- The plaquette integer of (L3) for the plaquette with lower left corner `(q, r)`. -/
def plaquetteCharge (d : ℕ) (ζ : ℤ × ℤ → ℂ) (q r : ℤ) : ℤ :=
  round ((aQ d ζ q r + aR ζ (q + 1) r - aQ d ζ q (r + 1) - aR ζ q r +
    2 * Real.pi / (d : ℝ) ^ 2) / (2 * Real.pi))

/-- An integer that satisfies the plaquette identity (L3) at `(q, r)` is the plaquette integer. -/
theorem plaquetteCharge_eq_of_identity {d : ℕ} {ζ : ℤ × ℤ → ℂ} {q r n : ℤ}
    (hn : aQ d ζ q r + aR ζ (q + 1) r - aQ d ζ q (r + 1) - aR ζ q r =
      -(2 * Real.pi / (d : ℝ) ^ 2) + 2 * Real.pi * (n : ℝ)) :
    plaquetteCharge d ζ q r = n := by
  have hpi : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hq : (aQ d ζ q r + aR ζ (q + 1) r - aQ d ζ q (r + 1) - aR ζ q r +
      2 * Real.pi / (d : ℝ) ^ 2) / (2 * Real.pi) = (n : ℝ) := by
    rw [hn, div_eq_iff hpi]
    ring
  unfold plaquetteCharge
  rw [hq]
  first | exact round_intCast n | simp

/-- (L3) with the plaquette integer: for a unit-modulus array, the plaquette identity holds with
`n = plaquetteCharge d ζ q r`. -/
theorem plaquetteCharge_spec (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1) (q r : ℤ) :
    aQ d ζ q r + aR ζ (q + 1) r - aQ d ζ q (r + 1) - aR ζ q r =
      -(2 * Real.pi / (d : ℝ) ^ 2) + 2 * Real.pi * (plaquetteCharge d ζ q r : ℝ) := by
  obtain ⟨n, hn⟩ := plaquette_identity d ζ hζ q r
  rw [plaquetteCharge_eq_of_identity hn]
  exact hn

/-- Telescoping over `range n` for a function on `ℤ`. -/
theorem sum_range_int_telescope (F : ℤ → ℝ) (n : ℕ) :
    ∑ k ∈ range n, (F ((k : ℤ) + 1) - F (k : ℤ)) = F (n : ℤ) - F 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    first | (push_cast; ring) | (rw [Nat.cast_add_one]; ring) | (rw [Nat.cast_succ]; ring)

/-- Along a row, the `q`-edge differences over one period in `r` add up to zero. -/
theorem sum_range_aQ_r_edge {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (hd : 0 < d) (q : ℤ) :
    ∑ r ∈ range d, (aQ d ζ q ((r : ℤ) + 1) - aQ d ζ q (r : ℤ)) = 0 := by
  have hp : aQ d ζ q (0 + (d : ℤ)) = aQ d ζ q 0 := aQ_add_period_r h hd q 0
  rw [zero_add] at hp
  have ht : ∑ r ∈ range d, (aQ d ζ q ((r : ℤ) + 1) - aQ d ζ q (r : ℤ)) =
      aQ d ζ q (d : ℤ) - aQ d ζ q 0 := sum_range_int_telescope (fun r : ℤ => aQ d ζ q r) d
  rw [ht, hp, sub_self]

/-- Along a column, the `r`-edge differences over one period in `q` add up to zero. -/
theorem sum_range_aR_q_edge {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (r : ℤ) :
    ∑ q ∈ range d, (aR ζ ((q : ℤ) + 1) r - aR ζ (q : ℤ) r) = 0 := by
  have hp : aR ζ (0 + (d : ℤ)) r = aR ζ 0 r := aR_add_period_q h 0 r
  rw [zero_add] at hp
  have ht : ∑ q ∈ range d, (aR ζ ((q : ℤ) + 1) r - aR ζ (q : ℤ) r) =
      aR ζ (d : ℤ) r - aR ζ 0 r := sum_range_int_telescope (fun q : ℤ => aR ζ q r) d
  rw [ht, hp, sub_self]

/-- The oriented edge sums of all plaquettes of the `d × d` square add up to zero. -/
theorem sum_plaquette_edges_eq_zero {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (hd : 0 < d) :
    ∑ q ∈ range d, ∑ r ∈ range d,
      (aQ d ζ (q : ℤ) (r : ℤ) + aR ζ ((q : ℤ) + 1) (r : ℤ) - aQ d ζ (q : ℤ) ((r : ℤ) + 1) -
        aR ζ (q : ℤ) (r : ℤ)) = 0 := by
  have h1 : ∑ q ∈ range d, ∑ r ∈ range d,
      (aQ d ζ (q : ℤ) (r : ℤ) + aR ζ ((q : ℤ) + 1) (r : ℤ) - aQ d ζ (q : ℤ) ((r : ℤ) + 1) -
        aR ζ (q : ℤ) (r : ℤ)) =
      ∑ q ∈ range d, ∑ r ∈ range d, (aR ζ ((q : ℤ) + 1) (r : ℤ) - aR ζ (q : ℤ) (r : ℤ)) -
        ∑ q ∈ range d, ∑ r ∈ range d,
          (aQ d ζ (q : ℤ) ((r : ℤ) + 1) - aQ d ζ (q : ℤ) (r : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have h2 : ∑ q ∈ range d, ∑ r ∈ range d,
      (aQ d ζ (q : ℤ) ((r : ℤ) + 1) - aQ d ζ (q : ℤ) (r : ℤ)) = 0 :=
    Finset.sum_eq_zero fun q _ => sum_range_aQ_r_edge h hd (q : ℤ)
  have h3 : ∑ q ∈ range d, ∑ r ∈ range d,
      (aR ζ ((q : ℤ) + 1) (r : ℤ) - aR ζ (q : ℤ) (r : ℤ)) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun r _ => sum_range_aR_q_edge h (r : ℤ)
  rw [h1, h2, h3, sub_zero]

/-- The sum of `c + a * g r` over `range d`. -/
theorem sum_range_const_add_mul (d : ℕ) (c a : ℝ) (g : ℕ → ℝ) :
    ∑ r ∈ range d, (c + a * g r) = (d : ℝ) * c + a * ∑ r ∈ range d, g r := by
  first
    | (rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.mul_sum]; done)
    | (simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.mul_sum]; done)
    | (simp [Finset.sum_add_distrib, Finset.mul_sum]; done)

/-- The double sum of `c + a * g q r` over the `d × d` square. -/
theorem sum_sum_range_const_add_mul (d : ℕ) (c a : ℝ) (g : ℕ → ℕ → ℝ) :
    ∑ q ∈ range d, ∑ r ∈ range d, (c + a * g q r) =
      (d : ℝ) * ((d : ℝ) * c) + a * ∑ q ∈ range d, ∑ r ∈ range d, g q r := by
  have inner : ∀ q ∈ range d, ∑ r ∈ range d, (c + a * g q r) =
      (d : ℝ) * c + a * ∑ r ∈ range d, g q r := fun q _ => sum_range_const_add_mul d c a (g q)
  have outer : ∑ q ∈ range d, ((d : ℝ) * c + a * ∑ r ∈ range d, g q r) =
      (d : ℝ) * ((d : ℝ) * c) + a * ∑ q ∈ range d, ∑ r ∈ range d, g q r :=
    sum_range_const_add_mul d ((d : ℝ) * c) a fun q => ∑ r ∈ range d, g q r
  exact (Finset.sum_congr rfl inner).trans outer

/-- **B3, general form.** Integers `n q r` that satisfy the plaquette identity (L3) on the square
`0 ≤ q, r < d` of a twisted array sum to `1`. -/
theorem sum_plaquette_int_eq_one {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (hd : 0 < d)
    (n : ℤ → ℤ → ℤ)
    (hn : ∀ q ∈ range d, ∀ r ∈ range d,
      aQ d ζ (q : ℤ) (r : ℤ) + aR ζ ((q : ℤ) + 1) (r : ℤ) - aQ d ζ (q : ℤ) ((r : ℤ) + 1) -
        aR ζ (q : ℤ) (r : ℤ) =
      -(2 * Real.pi / (d : ℝ) ^ 2) + 2 * Real.pi * (n (q : ℤ) (r : ℤ) : ℝ)) :
    ∑ q ∈ range d, ∑ r ∈ range d, n (q : ℤ) (r : ℤ) = 1 := by
  have hsum : ∑ q ∈ range d, ∑ r ∈ range d,
      (-(2 * Real.pi / (d : ℝ) ^ 2) + 2 * Real.pi * (n (q : ℤ) (r : ℤ) : ℝ)) = 0 := by
    refine Eq.trans ?_ (sum_plaquette_edges_eq_zero h hd)
    refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun r hr => ?_
    exact (hn q hq r hr).symm
  have hsplit : ∑ q ∈ range d, ∑ r ∈ range d,
      (-(2 * Real.pi / (d : ℝ) ^ 2) + 2 * Real.pi * (n (q : ℤ) (r : ℤ) : ℝ)) =
      (d : ℝ) * ((d : ℝ) * -(2 * Real.pi / (d : ℝ) ^ 2)) +
        2 * Real.pi * ∑ q ∈ range d, ∑ r ∈ range d, (n (q : ℤ) (r : ℤ) : ℝ) :=
    sum_sum_range_const_add_mul d (-(2 * Real.pi / (d : ℝ) ^ 2)) (2 * Real.pi)
      (fun q r => (n (q : ℤ) (r : ℤ) : ℝ))
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hinv : (d : ℝ) * (d : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hd0
  have hc : (d : ℝ) * ((d : ℝ) * -(2 * Real.pi / (d : ℝ) ^ 2)) = -(2 * Real.pi) := by
    first
      | linear_combination (-(2 * Real.pi) * ((d : ℝ) * (d : ℝ)⁻¹ + 1)) * hinv
      | (field_simp; ring)
      | field_simp
  have hpi : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have h0 : 2 * Real.pi *
      ((∑ q ∈ range d, ∑ r ∈ range d, (n (q : ℤ) (r : ℤ) : ℝ)) - 1) = 0 := by
    linear_combination hsum - hsplit - hc
  have hS : ∑ q ∈ range d, ∑ r ∈ range d, (n (q : ℤ) (r : ℤ) : ℝ) = 1 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hpi
    · exact sub_eq_zero.mp h1
  first | exact_mod_cast hS | (apply Int.cast_injective (α := ℝ); push_cast; exact hS)

/-- **B3, total charge one (L4).** For a twisted unit array with `0 < d`, the plaquette integers
over the square `0 ≤ q, r < d` sum to `1`. -/
theorem total_charge_one {d : ℕ} {ζ : ℤ × ℤ → ℂ} (h : IsTwisted d ζ) (hd : 0 < d) :
    ∑ q ∈ range d, ∑ r ∈ range d, plaquetteCharge d ζ (q : ℤ) (r : ℤ) = 1 :=
  sum_plaquette_int_eq_one h hd (plaquetteCharge d ζ) fun q _ r _ =>
    plaquetteCharge_spec d ζ h.norm_eq_one (q : ℤ) (r : ℤ)

end BLT

end
