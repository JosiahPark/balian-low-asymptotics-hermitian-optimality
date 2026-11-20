import BLTAudit.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# A1. The unitary DFT preserves the inner product

For `f g : ZMod N → ℂ` and the unitary DFT `dftU` of `BLTAudit/Basic.lean`
(`(F f)(k) = N^{-1/2} ∑_j e^{2πijk/N} f(j)`, paper §1):

* `sum_stdAddChar_mul`: orthogonality of characters, `∑_k e^{2πitk/N} = N·[t = 0]`;
* `conj_stdAddChar`: `conj (e^{2πij/N}) = e^{-2πij/N}`;
* `ip_dftU`: `⟨F f, F g⟩ = ⟨f, g⟩`;
* `parseval_dftU`: `∑_k ‖F f k‖² = ∑_j ‖f j‖²`.

What this file does NOT prove: anything about the Zak transform, the Gabor system or the energy
`E_N`; nothing here bears on Theorem 1.1 or Theorem 4.1 of the paper.
-/

noncomputable section

open Finset
open scoped ComplexConjugate

namespace BLT

variable {N : ℕ} [NeZero N]

/-- Orthogonality of the characters `k ↦ e^{2πitk/N}`. -/
theorem sum_stdAddChar_mul (t : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (t * k) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with ht
  · simp only [ht, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ht)

/-- Complex conjugation inverts the standard character. -/
theorem conj_stdAddChar (j : ZMod N) :
    conj (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
  have hR : 0 < ringChar (ZMod N) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne N)
  rw [AddChar.starComp_apply hR, AddChar.inv_apply]

/-- The two normalising factors `N^{-1/2}` multiply to `1/N`. -/
theorem dft_norm_sq :
    ((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹ * (N : ℂ) = 1 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  push_cast
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N))

/-- Products of characters at `j k` and `l k`, summed over `k`, detect `j = l`. -/
theorem sum_conj_stdAddChar_mul (j l : ZMod N) :
    ∑ k : ZMod N, conj (ZMod.stdAddChar (j * k)) * ZMod.stdAddChar (l * k) =
      if l = j then (N : ℂ) else 0 := by
  have h : ∀ k : ZMod N, conj (ZMod.stdAddChar (j * k)) * ZMod.stdAddChar (l * k) =
      ZMod.stdAddChar ((l - j) * k) := by
    intro k
    rw [conj_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [h]
  rw [sum_stdAddChar_mul]
  simp only [sub_eq_zero]

/-- **A1.** The unitary DFT preserves the inner product. -/
theorem ip_dftU (f g : ZMod N → ℂ) : ip (dftU f) (dftU g) = ip f g := by
  set c : ℂ := ((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹ with hc
  have hcc : conj c = c := by
    rw [hc, map_inv₀, Complex.conj_ofReal]
  have hcN : c * c * (N : ℂ) = 1 := dft_norm_sq
  have expand : ∀ k : ZMod N,
      conj (c * ∑ j : ZMod N, ZMod.stdAddChar (j * k) * f j) *
          (c * ∑ l : ZMod N, ZMod.stdAddChar (l * k) * g l) =
        ∑ j : ZMod N, ∑ l : ZMod N, c * c * (conj (f j) * g l) *
          (conj (ZMod.stdAddChar (j * k)) * ZMod.stdAddChar (l * k)) := by
    intro k
    have h1 : conj (c * ∑ j : ZMod N, ZMod.stdAddChar (j * k) * f j) *
        (c * ∑ l : ZMod N, ZMod.stdAddChar (l * k) * g l) =
        c * c * (conj (∑ j : ZMod N, ZMod.stdAddChar (j * k) * f j) *
          ∑ l : ZMod N, ZMod.stdAddChar (l * k) * g l) := by
      rw [map_mul, hcc]
      ring
    rw [h1, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    ring
  calc ip (dftU f) (dftU g)
      = ∑ k : ZMod N, ∑ j : ZMod N, ∑ l : ZMod N, c * c * (conj (f j) * g l) *
          (conj (ZMod.stdAddChar (j * k)) * ZMod.stdAddChar (l * k)) := by
        unfold ip dftU
        exact Finset.sum_congr rfl fun k _ => expand k
    _ = ∑ j : ZMod N, ∑ l : ZMod N, c * c * (conj (f j) * g l) *
          ∑ k : ZMod N, conj (ZMod.stdAddChar (j * k)) * ZMod.stdAddChar (l * k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ j : ZMod N, c * c * (conj (f j) * g j) * (N : ℂ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp_rw [sum_conj_stdAddChar_mul]
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = ip f g := by
        unfold ip
        refine Finset.sum_congr rfl fun j _ => ?_
        linear_combination (conj (f j) * g j) * hcN

/-- **A1, Parseval.** `∑_k ‖F f k‖² = ∑_j ‖f j‖²`. -/
theorem parseval_dftU (f : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖dftU f k‖ ^ 2 = ∑ j : ZMod N, ‖f j‖ ^ 2 := by
  have h := ip_dftU f f
  have hn : ∀ g : ZMod N → ℂ, ip g g = ((∑ j : ZMod N, ‖g j‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    unfold ip
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Complex.conj_mul' (g j)
  rw [hn, hn] at h
  exact_mod_cast h

end BLT

end
