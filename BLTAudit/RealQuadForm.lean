import BLTAudit.GStandardForm

/-!
# D4a1. The energy of a real vector as a real quadratic form

For `u : ZMod N → ℝ`, read as the complex vector `fun j => (u j : ℂ)`:

* `oscDiag`, `quadR`, `gStdR`: the diagonal `4 − 2 cos(2πj/N)` of `G_N`, the real quadratic form
  `quadR u = ∑ j, oscDiag N j * u j ^ 2 − 2 * ∑ j, u j * u (j + 1)` and the real operator
  `gStdR u j = oscDiag N j * u j − u (j − 1) − u (j + 1)`;
* `energy_ofReal`: `energy (fun j => (u j : ℂ)) = quadR u` (from `re_ip_gStd` of A6);
* `gStd_ofReal`: `gStd (fun i => (u i : ℂ)) j = gStdR u j`;
* `quadR_smul`, `sum_sq_smul`: `quadR` and `∑ j, u j ^ 2` scale by `t ^ 2` under `u ↦ t • u`;
* `quadR_expand`, `sum_sq_expand`: both expanded at `v + t • w` as quadratics in `t`, with the
  cross term `∑ j, 2 * (oscDiag N j * v j * w j) − 2 * ∑ j, (v j * w (j + 1) + w j * v (j + 1))` of
  `quadR`.

Helper lemma: `sum_quad`.

What this file does NOT prove: anything about minimizers of `energy` (D4a2, D4b, D4c). It proves
nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the hypotheses [HU] and
[HL].
-/

noncomputable section

open scoped ComplexConjugate

namespace BLT

variable {N : ℕ} [NeZero N]

/-- The diagonal `4 − 2 cos(2πj/N)` of `G_N` in standard coordinates. -/
def oscDiag (N : ℕ) (j : ZMod N) : ℝ := 4 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))

/-- The energy of a real vector as a real quadratic form. -/
def quadR (u : ZMod N → ℝ) : ℝ :=
  ∑ j : ZMod N, oscDiag N j * u j ^ 2 - 2 * ∑ j : ZMod N, u j * u (j + 1)

/-- `G_N` on real vectors. -/
def gStdR (u : ZMod N → ℝ) (j : ZMod N) : ℝ := oscDiag N j * u j - u (j - 1) - u (j + 1)

theorem energy_ofReal (u : ZMod N → ℝ) : energy (fun j => (u j : ℂ)) = quadR u := by
  have h : energy (fun j => (u j : ℂ)) =
      ∑ j : ZMod N, (4 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))) *
          ‖((u j : ℝ) : ℂ)‖ ^ 2 -
        2 * ∑ j : ZMod N, (conj ((u j : ℝ) : ℂ) * ((u (j + 1) : ℝ) : ℂ)).re :=
    (energy_eq_re_ip_gStd _).trans (re_ip_gStd _)
  have e1 : ∑ j : ZMod N, (4 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ))) *
      ‖((u j : ℝ) : ℂ)‖ ^ 2 = ∑ j : ZMod N, oscDiag N j * u j ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im, oscDiag]
    ring
  have e2 : ∑ j : ZMod N, (conj ((u j : ℝ) : ℂ) * ((u (j + 1) : ℝ) : ℂ)).re =
      ∑ j : ZMod N, u j * u (j + 1) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [h, e1, e2]
  rfl

theorem gStd_ofReal (u : ZMod N → ℝ) (j : ZMod N) :
    gStd (fun i => (u i : ℂ)) j = ((gStdR u j : ℝ) : ℂ) := by
  simp only [gStd, gStdR, oscDiag]
  first
    | (push_cast; ring)
    | push_cast
    | simp

theorem sum_quad (a b c : ZMod N → ℝ) (t : ℝ) :
    ∑ j, (a j + t * b j + t ^ 2 * c j) = ∑ j, a j + t * ∑ j, b j + t ^ 2 * ∑ j, c j := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem sum_sq_smul (t : ℝ) (u : ZMod N → ℝ) : ∑ j, (t * u j) ^ 2 = t ^ 2 * ∑ j, u j ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem quadR_smul (t : ℝ) (u : ZMod N → ℝ) : quadR (fun j => t * u j) = t ^ 2 * quadR u := by
  show ∑ j : ZMod N, oscDiag N j * (t * u j) ^ 2 - 2 * ∑ j : ZMod N, t * u j * (t * u (j + 1)) =
    t ^ 2 * (∑ j : ZMod N, oscDiag N j * u j ^ 2 - 2 * ∑ j : ZMod N, u j * u (j + 1))
  have h1 : ∑ j : ZMod N, oscDiag N j * (t * u j) ^ 2 =
      t ^ 2 * ∑ j : ZMod N, oscDiag N j * u j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j : ZMod N, t * u j * (t * u (j + 1)) = t ^ 2 * ∑ j : ZMod N, u j * u (j + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2]
  ring

theorem quadR_expand (v w : ZMod N → ℝ) (t : ℝ) :
    quadR (fun j => v j + t * w j) = quadR v +
      t * (∑ j, 2 * (oscDiag N j * v j * w j) - 2 * ∑ j, (v j * w (j + 1) + w j * v (j + 1))) +
      t ^ 2 * quadR w := by
  have E1 : ∑ j, oscDiag N j * (v j + t * w j) ^ 2 = ∑ j, oscDiag N j * v j ^ 2 +
      t * ∑ j, 2 * (oscDiag N j * v j * w j) + t ^ 2 * ∑ j, oscDiag N j * w j ^ 2 := by
    rw [← sum_quad]
    exact Finset.sum_congr rfl fun j _ => by ring
  have E2 : ∑ j, (v j + t * w j) * (v (j + 1) + t * w (j + 1)) = ∑ j, v j * v (j + 1) +
      t * ∑ j, (v j * w (j + 1) + w j * v (j + 1)) + t ^ 2 * ∑ j, w j * w (j + 1) := by
    rw [← sum_quad]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∑ j : ZMod N, oscDiag N j * (v j + t * w j) ^ 2 -
      2 * ∑ j : ZMod N, (v j + t * w j) * (v (j + 1) + t * w (j + 1)) =
    (∑ j : ZMod N, oscDiag N j * v j ^ 2 - 2 * ∑ j : ZMod N, v j * v (j + 1)) +
      t * (∑ j, 2 * (oscDiag N j * v j * w j) - 2 * ∑ j, (v j * w (j + 1) + w j * v (j + 1))) +
      t ^ 2 * (∑ j : ZMod N, oscDiag N j * w j ^ 2 - 2 * ∑ j : ZMod N, w j * w (j + 1))
  rw [E1, E2]
  ring

theorem sum_sq_expand (v w : ZMod N → ℝ) (t : ℝ) :
    ∑ j, (v j + t * w j) ^ 2 = ∑ j, v j ^ 2 + t * ∑ j, 2 * (v j * w j) + t ^ 2 * ∑ j, w j ^ 2 := by
  rw [← sum_quad]
  exact Finset.sum_congr rfl fun j _ => by ring

end BLT

end
