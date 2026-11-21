import BLTAudit.FiniteZakUnitary
import BLTAudit.TimeFrequency

/-!
# A7a. The critical energy in Zak coordinates

For `f : ZMod (d * d) → ℂ`, with `energy`, `diffOp`, `dftU`, `transl`, `modul` and `zak` of
`BLTAudit/Basic.lean` (paper §1–§2: `E_N(f) = ‖D f‖² + ‖D F f‖²` with `N = d²`, `D = I − T`):

* `zak_sub`: `zak (f - g) q r = zak f q r - zak g q r`;
* `sum_norm_sq_diffOp_eq_zak`: `‖D f‖² = ∑_{q,r} |zak f q r − zak (T f) q r|²`, from
  `D f = f − T f` and Parseval for the Zak transform (`parseval_zak`, A3a);
* `sum_norm_sq_diffOp_dftU_eq_zak`: `‖D F f‖² = ∑_{q,r} |zak f q r − zak (M f) q r|²`, from
  `D F f = F (f − M f)` (`diffOp_dftU`, A2), Parseval for the DFT (`parseval_dftU`, A1) and
  `parseval_zak`;
* `energy_eq_sum_zak`: `energy f` is the sum over `q r` of these two squared differences.

All sums run over `q r : ZMod d`. No array `ζ` on `ℤ × ℤ` appears, and `zak (transl f)` and
`zak (modul f)` are not evaluated.

What this file does NOT prove: the Zak energy identity `d² E(f) = A_d(ζ)` of §2 (item A7). Two
steps remain: the values of `zak (transl f)` and `zak (modul f)` across the two seams in terms of
a glued array `ζ` (A7b), and the passage from sums over `ZMod d` to the sums over `range d` in
`zakEnergy` (A7c). It proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing
toward the hypotheses [HU] and [HL].
-/

noncomputable section

open Finset

namespace BLT

variable {d : ℕ} [NeZero d]

/-- The finite Zak transform of a difference. -/
theorem zak_sub (f g : ZMod (d * d) → ℂ) (q r : ZMod d) :
    zak (f - g) q r = zak f q r - zak g q r := by
  simp only [zak, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The position half of the energy in Zak coordinates:
`‖D f‖² = ∑_{q,r} |zak f q r − zak (T f) q r|²`. -/
theorem sum_norm_sq_diffOp_eq_zak (f : ZMod (d * d) → ℂ) :
    ∑ j : ZMod (d * d), ‖diffOp f j‖ ^ 2 =
      ∑ q : ZMod d, ∑ r : ZMod d, ‖zak f q r - zak (transl f) q r‖ ^ 2 := by
  have h : ∀ j : ZMod (d * d), diffOp f j = (f - transl f) j := by
    intro j
    simp only [diffOp_apply, Pi.sub_apply, transl_apply]
  calc ∑ j : ZMod (d * d), ‖diffOp f j‖ ^ 2
      = ∑ j : ZMod (d * d), ‖(f - transl f) j‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [h j]
    _ = ∑ q : ZMod d, ∑ r : ZMod d, ‖zak (f - transl f) q r‖ ^ 2 :=
        (parseval_zak (f - transl f)).symm
    _ = ∑ q : ZMod d, ∑ r : ZMod d, ‖zak f q r - zak (transl f) q r‖ ^ 2 :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by rw [zak_sub]

/-- The frequency half of the energy in Zak coordinates:
`‖D F f‖² = ∑_{q,r} |zak f q r − zak (M f) q r|²`. -/
theorem sum_norm_sq_diffOp_dftU_eq_zak (f : ZMod (d * d) → ℂ) :
    ∑ k : ZMod (d * d), ‖diffOp (dftU f) k‖ ^ 2 =
      ∑ q : ZMod d, ∑ r : ZMod d, ‖zak f q r - zak (modul f) q r‖ ^ 2 := by
  calc ∑ k : ZMod (d * d), ‖diffOp (dftU f) k‖ ^ 2
      = ∑ k : ZMod (d * d), ‖dftU (f - modul f) k‖ ^ 2 := by
        rw [diffOp_dftU]
    _ = ∑ j : ZMod (d * d), ‖(f - modul f) j‖ ^ 2 := parseval_dftU (f - modul f)
    _ = ∑ q : ZMod d, ∑ r : ZMod d, ‖zak (f - modul f) q r‖ ^ 2 :=
        (parseval_zak (f - modul f)).symm
    _ = ∑ q : ZMod d, ∑ r : ZMod d, ‖zak f q r - zak (modul f) q r‖ ^ 2 :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by rw [zak_sub]

/-- **A7a.** The critical energy in Zak coordinates, with no array `ζ`: `E_N(f)` is the sum over
`q r : ZMod d` of `|zak f q r − zak (T f) q r|² + |zak f q r − zak (M f) q r|²`. -/
theorem energy_eq_sum_zak (f : ZMod (d * d) → ℂ) :
    energy f = ∑ q : ZMod d, ∑ r : ZMod d,
      (‖zak f q r - zak (transl f) q r‖ ^ 2 + ‖zak f q r - zak (modul f) q r‖ ^ 2) := by
  calc energy f
      = ∑ j : ZMod (d * d), ‖diffOp f j‖ ^ 2 +
          ∑ k : ZMod (d * d), ‖diffOp (dftU f) k‖ ^ 2 := by
        first | rfl | (unfold energy; rfl)
    _ = ∑ q : ZMod d, ∑ r : ZMod d, ‖zak f q r - zak (transl f) q r‖ ^ 2 +
          ∑ q : ZMod d, ∑ r : ZMod d, ‖zak f q r - zak (modul f) q r‖ ^ 2 := by
        rw [sum_norm_sq_diffOp_eq_zak f, sum_norm_sq_diffOp_dftU_eq_zak f]
    _ = ∑ q : ZMod d, ∑ r : ZMod d,
          (‖zak f q r - zak (transl f) q r‖ ^ 2 + ‖zak f q r - zak (modul f) q r‖ ^ 2) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        first | exact Finset.sum_add_distrib.symm | rw [Finset.sum_add_distrib]

end BLT

end
