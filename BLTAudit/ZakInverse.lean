import BLTAudit.Statements
import BLTAudit.FiniteZakUnitary
import BLTAudit.FourierUniqueness
import BLTAudit.ZakCriterionConverse

/-!
# H1. The inverse finite Zak transform, the phase map, and windows with a prescribed Zak array

Tools needed to *instantiate* windows of the paper from Zak data (§1, §2):

* `zakEquiv d`: the index bijection `(b, r) ↦ b d + r` of A3a as an `Equiv`;
* `zakInv G`: the inverse finite Zak transform, `(zakInv G)(b d + r) = d^{-1/2} ∑_x e^{2πi b x / d} G(-x, r)`
  (the substitution `x = -q` of the usual `d^{-1/2} ∑_q e^{-2πi q b / d} G(q, r)`);
* `zak_zakInv`: `zak (zakInv G) q r = G q r`;
* `ph w = w / |w|`, with `norm_ph`: `‖ph w‖ = 1` for `w ≠ 0`;
* `zakInv_admissible`: if `‖u q r‖ = 1` everywhere, the window `zakInv (d⁻¹ • u)` is admissible
  (through the Zak criterion A5c);
* `le_aMin_of_forall`: a lower bound valid on every admissible window bounds `aMin d`, as soon as
  one admissible window exists.

What this file does NOT prove: anything about the size of any energy, about the Gaussian, about the
finite oscillator, or about [HU]/[HL]. Theorem 1.1 and Theorem 4.1 are not proved here.
-/

noncomputable section

open scoped Real

namespace BLT

variable {d : ℕ} [NeZero d]

/-- The Zak index map `(b, r) ↦ b d + r` as an equivalence `ZMod d × ZMod d ≃ ZMod (d * d)`. -/
def zakEquiv (d : ℕ) [NeZero d] : ZMod d × ZMod d ≃ ZMod (d * d) :=
  Equiv.ofBijective (zakIndex d) zakIndex_bijective

/-- **H1.** The inverse finite Zak transform. -/
def zakInv (G : ZMod d → ZMod d → ℂ) (j : ZMod (d * d)) : ℂ :=
  ((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ *
    ∑ x : ZMod d, ZMod.stdAddChar (((zakEquiv d).symm j).1 * x) * G (-x) ((zakEquiv d).symm j).2

theorem zakInv_zakIndex (G : ZMod d → ZMod d → ℂ) (b r : ZMod d) :
    zakInv G (zakIndex d (b, r)) =
      ((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ * ∑ x : ZMod d, ZMod.stdAddChar (b * x) * G (-x) r := by
  have hs : (zakEquiv d).symm (zakIndex d (b, r)) = (b, r) := (zakEquiv d).symm_apply_apply (b, r)
  first
    | (unfold zakInv; rw [hs]; done)
    | simp only [zakInv, hs]
    | (unfold zakInv; simp [hs])

/-- **H1.** `Z (Z⁻¹ G) = G`. -/
theorem zak_zakInv (G : ZMod d → ZMod d → ℂ) (q r : ZMod d) : zak (zakInv G) q r = G q r := by
  rw [zak_eq_dftU]
  show ((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ *
      ∑ b : ZMod d, ZMod.stdAddChar (b * q) * zakInv G (zakIndex d (b, r)) = G q r
  have hinv : ∑ b : ZMod d, ZMod.stdAddChar (-(b * -q)) *
      ∑ x : ZMod d, ZMod.stdAddChar (b * x) * G (-x) r = (d : ℂ) * G (-(-q)) r :=
    sum_stdAddChar_inversion (fun x => G (-x) r) (-q)
  calc ((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ *
        ∑ b : ZMod d, ZMod.stdAddChar (b * q) * zakInv G (zakIndex d (b, r))
      = ((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ * ∑ b : ZMod d, ((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ *
          (ZMod.stdAddChar (-(b * -q)) * ∑ x : ZMod d, ZMod.stdAddChar (b * x) * G (-x) r) := by
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [zakInv_zakIndex, show -(b * -q) = b * q by ring]
        ring
    _ = ((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ * (((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ *
          ∑ b : ZMod d, ZMod.stdAddChar (-(b * -q)) *
            ∑ x : ZMod d, ZMod.stdAddChar (b * x) * G (-x) r) := by
        rw [← Finset.mul_sum]
    _ = ((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ * (((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ *
          ((d : ℂ) * G (-(-q)) r)) := by
        rw [hinv]
    _ = G q r := by
        rw [neg_neg, ← mul_assoc, ← mul_assoc, dft_norm_sq (N := d), one_mul]

/-- **H1.** The phase map `ph w = w / |w|` (and `ph 0 = 0`). -/
def ph (w : ℂ) : ℂ := w / ((‖w‖ : ℝ) : ℂ)

/-- `‖ph w‖ = 1` for `w ≠ 0`. -/
theorem norm_ph {w : ℂ} (hw : w ≠ 0) : ‖ph w‖ = 1 := by
  unfold ph
  have hn : ‖((‖w‖ : ℝ) : ℂ)‖ = ‖w‖ := by
    first
      | exact Complex.norm_of_nonneg (norm_nonneg w)
      | simp
  rw [norm_div, hn]
  exact div_self (norm_ne_zero_iff.mpr hw)

/-- **H1.** A unit-modulus array `u` defines the admissible window `zakInv (d⁻¹ u)`. -/
theorem zakInv_admissible (u : ZMod d → ZMod d → ℂ) (hu : ∀ q r, ‖u q r‖ = 1) :
    Admissible (zakInv (fun q r => (d : ℂ)⁻¹ * u q r)) := by
  unfold Admissible
  refine (ip_gabor_orthonormal_iff_zak_norm _).mpr fun q r => ?_
  rw [zak_zakInv]
  show ‖(d : ℂ)⁻¹ * u q r‖ = 1 / (d : ℝ)
  have hn : ‖(d : ℂ)‖ = (d : ℝ) := by
    first
      | exact Complex.norm_natCast d
      | simp
  rw [norm_mul, norm_inv, hn, hu q r, mul_one, one_div]

/-- **H1.** If some admissible window exists and `L ≤ scaledEnergy f` for every admissible `f`,
then `L ≤ aMin d`. -/
theorem le_aMin_of_forall (L : ℝ) (hne : ∃ f : ZMod (d * d) → ℂ, Admissible f)
    (h : ∀ f : ZMod (d * d) → ℂ, Admissible f → L ≤ scaledEnergy f) : L ≤ aMin d := by
  obtain ⟨f₀, h₀⟩ := hne
  haveI : Nonempty {f : ZMod (d * d) → ℂ // Admissible (d := d) f} := ⟨⟨f₀, h₀⟩⟩
  unfold aMin
  exact le_ciInf fun f => h f.1 f.2

end BLT

end
