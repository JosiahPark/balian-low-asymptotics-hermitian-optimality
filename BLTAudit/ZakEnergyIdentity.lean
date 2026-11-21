import BLTAudit.EnergyZakCoordinates
import BLTAudit.ZakSeams

/-!
# A7c. The Zak energy identity

Paper §2: `A_d(ζ) = d² E_N(f)` for `N = d²`, where `ζ` is the array `d · Z_N f` continued to `ℤ²`
by the twisted gluing. Here `energy`, `zak`, `zakEnergy` are those of `BLTAudit/Basic.lean`.

Let `f : ZMod (d * d) → ℂ` and let `ζ : ℤ × ℤ → ℂ` satisfy three named hypotheses:

* `hζ`: `ζ (q, r) = d * zak f q r` for natural numbers `q r < d`;
* `hq`: `ζ (q + d, r) = ζ (q, r)` for all integers `q r` (`shift_q` of `IsTwisted`);
* `hr`: `ζ (q, r + d) = e^{-2πiq/d} ζ (q, r)` for all integers `q r` (`shift_r` of `IsTwisted`).

Then:

* `sum_zmod_eq_sum_range`, `sum_sum_zmod_eq_sum_range`: a sum over `ZMod d` is the sum over
  `range d` of the values at the casts, in one and in two variables;
* `zak_energy_identity`: `d ^ 2 * energy f = zakEnergy d ζ`, from the energy in Zak coordinates
  (A7a) and the two edge identities across the seams (A7b);
* `zak_energy_identity_of_isTwisted`: the same when the gluing is given as `IsTwisted d ζ`.

Unit modulus of `ζ` is not used in `zak_energy_identity`.

What this file does NOT prove: that an array `ζ` with the three properties exists for a given
`f`, or that every twisted unit-modulus array comes from some `f` (inverse Zak transform); so it
does not identify the minimum of `d² E_N` over admissible vectors with the minimum of `A_d` over
twisted unit arrays. It proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and
nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

variable {d : ℕ} [NeZero d]

/-- A sum over `ZMod d` is the sum over `range d` of the values at the casts. -/
theorem sum_zmod_eq_sum_range (F : ZMod d → ℝ) :
    ∑ q : ZMod d, F q = ∑ k ∈ Finset.range d, F (k : ZMod d) := by
  have hi : ∀ q : ZMod d, q.val ∈ Finset.range d := fun q =>
    Finset.mem_range.mpr (ZMod.val_lt q)
  have hl : ∀ q : ZMod d, ((q.val : ℕ) : ZMod d) = q := fun q => ZMod.natCast_zmod_val q
  have hv : ∀ k ∈ Finset.range d, ((k : ℕ) : ZMod d).val = k := fun k hk =>
    zmod_val_natCast_of_lt (Finset.mem_range.mp hk)
  first
    | exact Finset.sum_nbij' (fun q : ZMod d => q.val) (fun k : ℕ => (k : ZMod d))
        (fun q _ => hi q) (fun k _ => Finset.mem_univ _) (fun q _ => hl q) hv
        (fun q _ => congrArg F (hl q).symm)
    | exact Finset.sum_bij' (fun (q : ZMod d) _ => q.val) (fun (k : ℕ) _ => (k : ZMod d))
        (fun q _ => hi q) (fun k _ => Finset.mem_univ _) (fun q _ => hl q) hv
        (fun q _ => congrArg F (hl q).symm)

/-- A double sum over `ZMod d` is the double sum over `range d` of the values at the casts. -/
theorem sum_sum_zmod_eq_sum_range (F : ZMod d → ZMod d → ℝ) :
    ∑ q : ZMod d, ∑ r : ZMod d, F q r =
      ∑ q ∈ Finset.range d, ∑ r ∈ Finset.range d, F (q : ZMod d) (r : ZMod d) :=
  (sum_zmod_eq_sum_range fun q : ZMod d => ∑ r : ZMod d, F q r).trans
    (Finset.sum_congr rfl fun q _ => sum_zmod_eq_sum_range fun r : ZMod d => F (q : ZMod d) r)

/-- **A7c, the Zak energy identity (§2).** If `ζ` equals `d · zak f` on the square
`0 ≤ q, r < d` and satisfies the two gluing relations, then `d² E_N(f) = A_d(ζ)`. -/
theorem zak_energy_identity (f : ZMod (d * d) → ℂ) (ζ : ℤ × ℤ → ℂ)
    (hζ : ∀ q r : ℕ, q < d → r < d →
      ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) * zak f (q : ZMod d) (r : ZMod d))
    (hq : ∀ q r : ℤ, ζ (q + (d : ℤ), r) = ζ (q, r))
    (hr : ∀ q r : ℤ, ζ (q, r + (d : ℤ)) =
      Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) * ζ (q, r)) :
    (d : ℝ) ^ 2 * energy f = zakEnergy d ζ := by
  have hE : energy f = ∑ q ∈ Finset.range d, ∑ r ∈ Finset.range d,
      (‖zak f (q : ZMod d) (r : ZMod d) - zak (transl f) (q : ZMod d) (r : ZMod d)‖ ^ 2 +
        ‖zak f (q : ZMod d) (r : ZMod d) - zak (modul f) (q : ZMod d) (r : ZMod d)‖ ^ 2) :=
    (energy_eq_sum_zak f).trans (sum_sum_zmod_eq_sum_range fun q r : ZMod d =>
      ‖zak f q r - zak (transl f) q r‖ ^ 2 + ‖zak f q r - zak (modul f) q r‖ ^ 2)
  have hZ : zakEnergy d ζ = ∑ q ∈ Finset.range d, ∑ r ∈ Finset.range d, (d : ℝ) ^ 2 *
      (‖zak f (q : ZMod d) (r : ZMod d) - zak (transl f) (q : ZMod d) (r : ZMod d)‖ ^ 2 +
        ‖zak f (q : ZMod d) (r : ZMod d) - zak (modul f) (q : ZMod d) (r : ZMod d)‖ ^ 2) := by
    unfold zakEnergy
    refine Finset.sum_congr rfl fun q hq' => Finset.sum_congr rfl fun r hr' => ?_
    rw [norm_sq_zeta_r_edge f ζ hζ hr (Finset.mem_range.mp hq') (Finset.mem_range.mp hr'),
      norm_sq_zeta_q_edge f ζ hζ hq (Finset.mem_range.mp hq') (Finset.mem_range.mp hr')]
    ring
  rw [hE, hZ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]

/-- **A7c** with the gluing given as `IsTwisted d ζ` (its unit-modulus field is not used). -/
theorem zak_energy_identity_of_isTwisted (f : ZMod (d * d) → ℂ) (ζ : ℤ × ℤ → ℂ)
    (hζ : ∀ q r : ℕ, q < d → r < d →
      ζ ((q : ℤ), (r : ℤ)) = (d : ℂ) * zak f (q : ZMod d) (r : ZMod d))
    (h : IsTwisted d ζ) : (d : ℝ) ^ 2 * energy f = zakEnergy d ζ :=
  zak_energy_identity f ζ hζ h.shift_q h.shift_r

end BLT

end
