import BLTAudit.Basic

/-!
# D3. A nonnegative eigenvector of `G_N` is strictly positive

`G_N` in standard coordinates is `gStd` of `BLTAudit/Basic.lean`:
`(gStd f)(j) = (4 − 2 cos(2πj/N)) f(j) − f(j−1) − f(j+1)`. Let `v : ZMod N → ℝ` be entrywise
nonnegative and satisfy `gStd v = μ v` for a real `μ`, with `v` read as a complex vector, stated
pointwise as `gStd (fun i => (v i : ℂ)) j = μ * v j`. Then:

* `gStd_eigvec_zero_succ`: a zero entry forces the next one to vanish: at a zero `v j = 0` the
  eigenvalue equation reads `−v(j−1) − v(j+1) = 0`, and both terms are `≥ 0`;
* `gStd_eigvec_eq_zero_of_zero`: so one zero entry forces `v = 0`, by going around `ZMod N`
  (every `i` is `j + k` with `k = (i − j).val`);
* `gStd_eigvec_pos`: if `v ≠ 0`, then `0 < v j` for every `j`;
* `gStd_eigvec_pos'`: the same with the eigenvalue equation as an equation of vectors,
  `gStd (fun i => (v i : ℂ)) = (μ : ℂ) • fun i => (v i : ℂ)`.

The value of `μ` and the diagonal of `gStd` play no role; only the off-diagonal entries `−1`
between neighbours on the cycle are used.

What this file does NOT prove: that a nonnegative eigenvector exists, that the bottom of the
spectrum of `G_N` is simple, or that a minimizer of `energy` is an eigenvector (item D4). It
proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the hypotheses
[HU] and [HL].
-/

noncomputable section

namespace BLT

variable {N : ℕ} [NeZero N]

/-- **D3, one step.** At a zero entry of a nonnegative eigenvector of `gStd`, the next entry also
vanishes. -/
theorem gStd_eigvec_zero_succ (v : ZMod N → ℝ) (μ : ℝ) (hnn : ∀ j, 0 ≤ v j)
    (hv : ∀ j, gStd (fun i => (v i : ℂ)) j = (μ : ℂ) * (v j : ℂ)) (j : ZMod N)
    (hj : v j = 0) : v (j + 1) = 0 := by
  have h := congrArg Complex.re (hv j)
  have h1 := hnn (j - 1)
  have h2 := hnn (j + 1)
  first
    | (simp only [gStd, hj, Complex.ofReal_zero, Complex.sub_re, Complex.mul_re,
        Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
        mul_zero, zero_mul, sub_zero, zero_sub] at h; linarith)
    | (simp [gStd, hj] at h; linarith)

/-- **D3, around the cycle.** A nonnegative eigenvector of `gStd` with one zero entry is zero. -/
theorem gStd_eigvec_eq_zero_of_zero (v : ZMod N → ℝ) (μ : ℝ) (hnn : ∀ j, 0 ≤ v j)
    (hv : ∀ j, gStd (fun i => (v i : ℂ)) j = (μ : ℂ) * (v j : ℂ)) (j₀ : ZMod N)
    (h₀ : v j₀ = 0) : ∀ i, v i = 0 := by
  have prop : ∀ k : ℕ, v (j₀ + (k : ZMod N)) = 0 := by
    intro k
    induction k with
    | zero =>
      first
        | (rw [Nat.cast_zero, add_zero]; exact h₀)
        | simpa using h₀
    | succ n ih =>
      have h := gStd_eigvec_zero_succ v μ hnn hv (j₀ + (n : ZMod N)) ih
      first
        | (rw [Nat.cast_succ, ← add_assoc]; exact h)
        | (push_cast; rw [← add_assoc]; exact h)
  intro i
  have e : j₀ + (((i - j₀).val : ℕ) : ZMod N) = i := by
    rw [ZMod.natCast_zmod_val]
    ring
  rw [← e]
  exact prop _

/-- **D3.** A nonzero, entrywise nonnegative eigenvector of `G_N` (in standard coordinates) is
entrywise strictly positive. -/
theorem gStd_eigvec_pos (v : ZMod N → ℝ) (μ : ℝ) (hne : v ≠ 0) (hnn : ∀ j, 0 ≤ v j)
    (hv : ∀ j, gStd (fun i => (v i : ℂ)) j = (μ : ℂ) * (v j : ℂ)) (j : ZMod N) : 0 < v j := by
  rcases lt_or_eq_of_le (hnn j) with h | h
  · exact h
  · exfalso
    apply hne
    funext i
    first
      | exact gStd_eigvec_eq_zero_of_zero v μ hnn hv j h.symm i
      | simp [gStd_eigvec_eq_zero_of_zero v μ hnn hv j h.symm i]

/-- **D3**, with the eigenvalue equation as an equation of vectors. -/
theorem gStd_eigvec_pos' (v : ZMod N → ℝ) (μ : ℝ) (hne : v ≠ 0) (hnn : ∀ j, 0 ≤ v j)
    (hv : gStd (fun i => (v i : ℂ)) = (μ : ℂ) • fun i => (v i : ℂ)) (j : ZMod N) :
    0 < v j := by
  refine gStd_eigvec_pos v μ hne hnn (fun i => ?_) j
  rw [hv, Pi.smul_apply, smul_eq_mul]

end BLT

end
