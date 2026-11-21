import BLTAudit.GStandardForm

/-!
# D2. The Perron–Frobenius step

For a finite type `ι`, a real matrix `A : ι → ι → ℝ` whose off-diagonal entries are `≤ 0`, and
`v : ι → ℂ`:

* `perron_step`: `∑ i, ∑ j, A i j * ‖v i‖ * ‖v j‖ ≤ (∑ i, ∑ j, A i j * conj (v i) * v j).re`;
* `quadFormRe`, `quadFormRe_norm`, `quadFormRe_norm_le`: with `quadFormRe A v` the real part of
  `∑ i, ∑ j, A i j * conj (v i) * v j`, replacing `v` by its entrywise modulus
  `fun i => (‖v i‖ : ℂ)` does not raise `quadFormRe A v`;
* `energy_norm_le`: the same for the paper's quadratic form, `energy |f| ≤ energy f` for
  `f : ZMod N → ℂ` (from `re_ip_gStd` and `energy_eq_re_ip_gStd` of A6: in standard coordinates the
  off-diagonal entries of `G_N` are `−1`).

Helper lemmas: `re_conj_mul_le_norm_mul`, `re_ofReal_mul_conj_mul`, `re_conj_mul_self`.

The roadmap item asks for a real symmetric `A`. Symmetry is not used: the inequality holds term by
term, with equality on the diagonal and `A i j * ‖v i‖ * ‖v j‖ ≤ A i j * Re (conj (v i) * v j)` off
it, so the theorems here are stated without it.

What this file does NOT prove: positivity of a nonnegative eigenvector of `gStd` (D3), existence,
simplicity or positivity of a ground state of `G_N` (D4), or anything about the spectrum of `G_N`.
It proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the
hypotheses [HU] and [HL].
-/

noncomputable section

open scoped ComplexConjugate

namespace BLT

/-- `Re (conj a · b) ≤ |a| |b|`. -/
theorem re_conj_mul_le_norm_mul (a b : ℂ) : (conj a * b).re ≤ ‖a‖ * ‖b‖ := by
  have hw : (conj a * b).re ≤ ‖conj a * b‖ := by
    first
      | exact Complex.re_le_norm _
      | exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
      | (have h := Complex.sq_norm (conj a * b); rw [Complex.normSq_apply] at h;
          nlinarith [sq_nonneg (conj a * b).im, norm_nonneg (conj a * b)])
  calc (conj a * b).re ≤ ‖conj a * b‖ := hw
    _ = ‖a‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]

/-- A real factor comes out of the real part. -/
theorem re_ofReal_mul_conj_mul (r : ℝ) (a b : ℂ) :
    ((r : ℂ) * conj a * b).re = r * (conj a * b).re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- `Re (conj a · a) = |a|²`. -/
theorem re_conj_mul_self (a : ℂ) : (conj a * a).re = ‖a‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **D2, the Perron–Frobenius step.** For a real matrix with nonpositive off-diagonal entries,
the form evaluated on the entrywise moduli is at most the real part of the Hermitian form. -/
theorem perron_step {ι : Type*} [Fintype ι] (A : ι → ι → ℝ)
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) (v : ι → ℂ) :
    ∑ i, ∑ j, A i j * ‖v i‖ * ‖v j‖ ≤ (∑ i, ∑ j, (A i j : ℂ) * conj (v i) * v j).re := by
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [re_ofReal_mul_conj_mul]
  by_cases hij : i = j
  · subst hij
    rw [re_conj_mul_self]
    apply le_of_eq
    ring
  · have hre := re_conj_mul_le_norm_mul (v i) (v j)
    have hAij := hA i j hij
    first
      | (rw [mul_assoc]; exact mul_le_mul_of_nonpos_left hre hAij)
      | nlinarith [hre, hAij]

/-- The real part of the Hermitian form `∑_{i,j} A i j conj (v i) v j` of a real matrix. -/
def quadFormRe {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) (v : ι → ℂ) : ℝ :=
  (∑ i, ∑ j, (A i j : ℂ) * conj (v i) * v j).re

/-- The form on the entrywise moduli. -/
theorem quadFormRe_norm {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) (v : ι → ℂ) :
    quadFormRe A (fun i => (‖v i‖ : ℂ)) = ∑ i, ∑ j, A i j * ‖v i‖ * ‖v j‖ := by
  unfold quadFormRe
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- **D2.** Replacing a vector by its entrywise modulus does not raise the form. -/
theorem quadFormRe_norm_le {ι : Type*} [Fintype ι] (A : ι → ι → ℝ)
    (hA : ∀ i j, i ≠ j → A i j ≤ 0) (v : ι → ℂ) :
    quadFormRe A (fun i => (‖v i‖ : ℂ)) ≤ quadFormRe A v := by
  rw [quadFormRe_norm]
  exact perron_step A hA v

/-- **D2 for `G_N`.** If `g j = |f j|` for every `j`, then `E_N(g) ≤ E_N(f)`. -/
theorem energy_le_of_norm {N : ℕ} [NeZero N] (f g : ZMod N → ℂ)
    (hg : ∀ j, g j = (‖f j‖ : ℂ)) : energy g ≤ energy f := by
  have hn : ∀ j, ‖g j‖ = ‖f j‖ := by
    intro j
    rw [hg j]
    first
      | rw [Complex.norm_real, norm_norm]
      | simp
      | exact Complex.norm_of_nonneg (norm_nonneg _)
  have hc : ∀ j, (conj (g j) * g (j + 1)).re = ‖f j‖ * ‖f (j + 1)‖ := by
    intro j
    rw [hg j, hg (j + 1)]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have e1 : ∑ j : ZMod N, (4 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))) * ‖g j‖ ^ 2 =
      ∑ j : ZMod N, (4 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))) * ‖f j‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [hn j]
  have e2 : ∑ j : ZMod N, (conj (g j) * g (j + 1)).re =
      ∑ j : ZMod N, ‖f j‖ * ‖f (j + 1)‖ :=
    Finset.sum_congr rfl fun j _ => hc j
  have e3 : ∑ j : ZMod N, (conj (f j) * f (j + 1)).re ≤ ∑ j : ZMod N, ‖f j‖ * ‖f (j + 1)‖ :=
    Finset.sum_le_sum fun j _ => re_conj_mul_le_norm_mul (f j) (f (j + 1))
  have hgE := (energy_eq_re_ip_gStd g).trans (re_ip_gStd g)
  have hfE := (energy_eq_re_ip_gStd f).trans (re_ip_gStd f)
  linarith [e1, e2, e3, hgE, hfE]

/-- **D2 for `G_N`.** `E_N(|f|) ≤ E_N(f)`. -/
theorem energy_norm_le {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    energy (fun j => (‖f j‖ : ℂ)) ≤ energy f :=
  energy_le_of_norm f _ fun _ => rfl

end BLT

end
