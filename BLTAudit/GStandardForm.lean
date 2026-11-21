import BLTAudit.UnitaryDFT
import BLTAudit.TimeFrequency
import BLTAudit.FiniteZakModulation

/-!
# A6. The standard form of `G_N`

For `f : ZMod N → ℂ`, with `ip`, `energy`, `diffOp`, `dftU`, `gStd` of `BLTAudit/Basic.lean`
(paper §1: `E_N(f) = ‖D f‖² + ‖D F f‖²`, and `G_N = D*D + F*D*D F` acts in standard coordinates
as `(G_N f)(j) = (4 − 2 cos(2πj/N)) f(j) − f(j−1) − f(j+1)`):

* `sum_norm_sq_diffOp`: `‖D f‖² = 2 ∑_j |f(j)|² − 2 ∑_j Re (conj f(j) · f(j+1))`;
* `sum_norm_sq_diffOp_dftU`: `‖D F f‖² = ∑_j (2 − 2 cos(2πj/N)) |f(j)|²`, from
  `D F f = F (f − M f)` (A2), Parseval (A1) and `norm_sq_one_sub_stdAddChar`,
  `|1 − e^{2πij/N}|² = 2 − 2 cos(2πj/N)`;
* `re_ip_gStd`: `Re ⟨f, gStd f⟩ = ∑_j (4 − 2 cos(2πj/N)) |f(j)|² − 2 ∑_j Re (conj f(j) · f(j+1))`;
* `energy_eq_re_ip_gStd`: `energy f = (ip f (gStd f)).re`;
* `im_ip_gStd`: `(ip f (gStd f)).im = 0`.

Helper lemmas: `sum_zmod_add_one` (a real sum over `ZMod N` is invariant under `j ↦ j + 1`),
`complex_norm_sub_sq`, `stdAddChar_eq_exp_ofReal`, `sum_re_conj_mul_sub_one`,
`sum_im_conj_mul_sub_one`.

What this file does NOT prove: the operator identity `gStd f = D*D f + F*D*D F f` (only the
quadratic form `⟨f, G_N f⟩` is identified; the adjoints `D*` and `F*` are not defined), that
`gStd` is self-adjoint, anything about its spectrum or ground state (section D), or anything
about the Zak transform and the Zak energy (A7). It proves nothing toward Theorem 1.1 or
Theorem 4.1 of the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

open scoped ComplexConjugate

namespace BLT

variable {N : ℕ} [NeZero N]

/-- A real sum over `ZMod N` is unchanged by the shift `j ↦ j + 1`. -/
theorem sum_zmod_add_one (g : ZMod N → ℝ) :
    ∑ j : ZMod N, g (j + 1) = ∑ j : ZMod N, g j := by
  first
    | exact (Equiv.addRight (1 : ZMod N)).sum_comp g
    | exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ fun _ => rfl

/-- `|a − b|² = |a|² + |b|² − 2 Re (conj a · b)` in `ℂ`. -/
theorem complex_norm_sub_sq (a b : ℂ) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (conj a * b).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The standard character with a real angle: `e^{2πij/N} = exp (i · 2πj/N)`. -/
theorem stdAddChar_eq_exp_ofReal (j : ZMod N) :
    ZMod.stdAddChar j =
      Complex.exp (((2 * Real.pi * (j.val : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have h := stdAddChar_natCast (N := N) j.val
  rw [ZMod.natCast_zmod_val] at h
  rw [h]
  refine congrArg Complex.exp ?_
  first
    | (push_cast; ring1)
    | (simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_natCast]; ring1)

/-- `|1 − e^{2πij/N}|² = 2 − 2 cos(2πj/N)`. -/
theorem norm_sq_one_sub_stdAddChar (j : ZMod N) :
    ‖1 - ZMod.stdAddChar j‖ ^ 2 = 2 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ)) := by
  rw [stdAddChar_eq_exp_ofReal]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  first
    | linear_combination Real.sin_sq_add_cos_sq (2 * Real.pi * (j.val : ℝ) / (N : ℝ))
    | nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * (j.val : ℝ) / (N : ℝ))]

/-- The frequency half of the energy: `‖D F f‖² = ∑_j (2 − 2 cos(2πj/N)) |f(j)|²`. -/
theorem sum_norm_sq_diffOp_dftU (f : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖diffOp (dftU f) k‖ ^ 2 =
      ∑ j : ZMod N, (2 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))) * ‖f j‖ ^ 2 := by
  rw [diffOp_dftU, parseval_dftU]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (f - modul f) j = (1 - ZMod.stdAddChar j) * f j := by
    simp only [Pi.sub_apply, modul_apply]
    ring
  rw [h, norm_mul, mul_pow, norm_sq_one_sub_stdAddChar]

/-- The position half of the energy: `‖D f‖² = 2 ∑_j |f(j)|² − 2 ∑_j Re (conj f(j) · f(j+1))`. -/
theorem sum_norm_sq_diffOp (f : ZMod N → ℂ) :
    ∑ j : ZMod N, ‖diffOp f j‖ ^ 2 =
      2 * ∑ j : ZMod N, ‖f j‖ ^ 2 - 2 * ∑ j : ZMod N, (conj (f j) * f (j + 1)).re := by
  have hshift : ∑ j : ZMod N, ‖f (j + 1)‖ ^ 2 = ∑ j : ZMod N, ‖f j‖ ^ 2 :=
    sum_zmod_add_one fun j : ZMod N => ‖f j‖ ^ 2
  have hterm : ∀ j : ZMod N, ‖diffOp f j‖ ^ 2 =
      ‖f j‖ ^ 2 + ‖f (j + 1)‖ ^ 2 - 2 * (conj (f j) * f (j + 1)).re := by
    intro j
    rw [diffOp_apply]
    exact complex_norm_sub_sq (f j) (f (j + 1))
  have hsum : ∑ j : ZMod N, ‖diffOp f j‖ ^ 2 =
      ∑ j : ZMod N, ‖f j‖ ^ 2 + ∑ j : ZMod N, ‖f (j + 1)‖ ^ 2 -
        2 * ∑ j : ZMod N, (conj (f j) * f (j + 1)).re := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm j
  linarith [hsum, hshift]

/-- The backward correlation has the same real part as the forward one. -/
theorem sum_re_conj_mul_sub_one (f : ZMod N → ℂ) :
    ∑ j : ZMod N, (conj (f j) * f (j - 1)).re = ∑ j : ZMod N, (conj (f j) * f (j + 1)).re := by
  calc ∑ j : ZMod N, (conj (f j) * f (j - 1)).re
      = ∑ j : ZMod N, (conj (f (j + 1)) * f (j + 1 - 1)).re :=
        (sum_zmod_add_one fun j : ZMod N => (conj (f j) * f (j - 1)).re).symm
    _ = ∑ j : ZMod N, (conj (f j) * f (j + 1)).re := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [add_sub_cancel_right, Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring

/-- The backward correlation has the opposite imaginary part to the forward one. -/
theorem sum_im_conj_mul_sub_one (f : ZMod N → ℂ) :
    ∑ j : ZMod N, (conj (f j) * f (j - 1)).im = -∑ j : ZMod N, (conj (f j) * f (j + 1)).im := by
  calc ∑ j : ZMod N, (conj (f j) * f (j - 1)).im
      = ∑ j : ZMod N, (conj (f (j + 1)) * f (j + 1 - 1)).im :=
        (sum_zmod_add_one fun j : ZMod N => (conj (f j) * f (j - 1)).im).symm
    _ = ∑ j : ZMod N, -(conj (f j) * f (j + 1)).im := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [add_sub_cancel_right, Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
    _ = -∑ j : ZMod N, (conj (f j) * f (j + 1)).im := by
        rw [Finset.sum_neg_distrib]

/-- The real part of `⟨f, G_N f⟩` in standard coordinates. -/
theorem re_ip_gStd (f : ZMod N → ℂ) :
    (ip f (gStd f)).re =
      ∑ j : ZMod N, (4 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))) * ‖f j‖ ^ 2 -
        2 * ∑ j : ZMod N, (conj (f j) * f (j + 1)).re := by
  have hterm : ∀ j : ZMod N, (conj (f j) * gStd f j).re =
      (4 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))) * ‖f j‖ ^ 2 -
        (conj (f j) * f (j - 1)).re - (conj (f j) * f (j + 1)).re := by
    intro j
    simp only [gStd, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hsum : (ip f (gStd f)).re =
      ∑ j : ZMod N, (4 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))) * ‖f j‖ ^ 2 -
        ∑ j : ZMod N, (conj (f j) * f (j - 1)).re -
        ∑ j : ZMod N, (conj (f j) * f (j + 1)).re := by
    unfold ip
    rw [Complex.re_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm j
  linarith [hsum, sum_re_conj_mul_sub_one f]

/-- **A6.** `⟨f, G_N f⟩` is real: `(ip f (gStd f)).im = 0`. -/
theorem im_ip_gStd (f : ZMod N → ℂ) : (ip f (gStd f)).im = 0 := by
  have hterm : ∀ j : ZMod N, (conj (f j) * gStd f j).im =
      -(conj (f j) * f (j - 1)).im - (conj (f j) * f (j + 1)).im := by
    intro j
    simp only [gStd, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsum : (ip f (gStd f)).im =
      -∑ j : ZMod N, (conj (f j) * f (j - 1)).im -
        ∑ j : ZMod N, (conj (f j) * f (j + 1)).im := by
    unfold ip
    rw [Complex.im_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm j
  linarith [hsum, sum_im_conj_mul_sub_one f]

/-- **A6.** `E_N(f) = Re ⟨f, G_N f⟩`, with `G_N` in standard coordinates. -/
theorem energy_eq_re_ip_gStd (f : ZMod N → ℂ) : energy f = (ip f (gStd f)).re := by
  have hsplit : ∑ j : ZMod N,
      (4 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))) * ‖f j‖ ^ 2 =
      2 * ∑ j : ZMod N, ‖f j‖ ^ 2 +
        ∑ j : ZMod N, (2 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))) * ‖f j‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have henergy : energy f =
      ∑ j : ZMod N, ‖diffOp f j‖ ^ 2 + ∑ k : ZMod N, ‖diffOp (dftU f) k‖ ^ 2 := by
    first | rfl | (unfold energy; rfl)
  linarith [hsplit, henergy, re_ip_gStd f, sum_norm_sq_diffOp f, sum_norm_sq_diffOp_dftU f]

end BLT

end
