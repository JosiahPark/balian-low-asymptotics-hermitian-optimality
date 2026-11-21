import BLTAudit.RealQuadForm

/-!
# D4a2. A minimizer of `E_N` on the real unit sphere is an eigenvector of `G_N`

With `quadR`, `gStdR` of `BLTAudit/RealQuadForm.lean` (D4a1):

* `quadR_lower`: if `v` minimizes `quadR` on the real unit sphere `∑ j, u j ^ 2 = 1`, then
  `quadR v * ∑ j, u j ^ 2 ≤ quadR u` for every `u` (normalize `u` by `√(∑ j, u j ^ 2)`);
* `eq_zero_of_forall_quad_nonneg`: if `0 ≤ t * Q + t ^ 2 * K` for every real `t` and `K ≥ 0`, then
  `Q = 0` (take `t = −Q / (K + 1)`);
* `cross_eq`: after the shift `j ↦ j + 1`, the cross term of `quadR_expand` minus
  `μ * ∑ j, 2 * (v j * w j)` is `2 * ∑ j, w j * (gStdR v j − μ * v j)`;
* `gStdR_eq_of_min`: for a minimizer `v`, `gStdR v j = quadR v * v j` (expand at `v + t • w`, then
  take `w = gStdR v − quadR v • v`);
* `ground_eigen`: the statement of D4a, if `∑ j, v j ^ 2 = 1` and
  `energy (fun j => (v j : ℂ)) ≤ energy (fun j => (u j : ℂ))` for every real `u` with
  `∑ j, u j ^ 2 = 1`, then `gStd (fun i => (v i : ℂ)) j = energy (fun i => (v i : ℂ)) * v j` for
  every `j`, in the form of the hypothesis of D3.

What this file does NOT prove: that a minimizer exists (D4b), that it can be taken positive, or that
it is unique up to sign (D4c). It proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper,
and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

variable {N : ℕ} [NeZero N]

/-- A minimizer on the unit sphere bounds the form below on all of `ℝ^N`. -/
theorem quadR_lower (v : ZMod N → ℝ)
    (hmin : ∀ u : ZMod N → ℝ, ∑ j, u j ^ 2 = 1 → quadR v ≤ quadR u) (u : ZMod N → ℝ) :
    quadR v * ∑ j, u j ^ 2 ≤ quadR u := by
  have hs0 : 0 ≤ ∑ j, u j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (u j)
  rcases hs0.lt_or_eq with hs | hs
  · have hsq : Real.sqrt (∑ j, u j ^ 2) ^ 2 = ∑ j, u j ^ 2 := Real.sq_sqrt hs0
    have ht2 : (Real.sqrt (∑ j, u j ^ 2))⁻¹ ^ 2 * ∑ j, u j ^ 2 = 1 := by
      rw [inv_pow, hsq]
      exact inv_mul_cancel₀ hs.ne'
    have hunit : ∑ j, ((Real.sqrt (∑ j, u j ^ 2))⁻¹ * u j) ^ 2 = 1 := by
      rw [sum_sq_smul]
      exact ht2
    have h1 := hmin (fun j => (Real.sqrt (∑ j, u j ^ 2))⁻¹ * u j) hunit
    rw [quadR_smul] at h1
    calc quadR v * ∑ j, u j ^ 2
        ≤ (Real.sqrt (∑ j, u j ^ 2))⁻¹ ^ 2 * quadR u * ∑ j, u j ^ 2 :=
          mul_le_mul_of_nonneg_right h1 hs0
      _ = quadR u := by linear_combination quadR u * ht2
  · have h0 : ∀ j ∈ Finset.univ, u j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (u j)).mp hs.symm
    have hu : ∀ j, u j = 0 := by
      intro j
      first
        | exact (pow_eq_zero_iff two_ne_zero).mp (h0 j (Finset.mem_univ j))
        | nlinarith [h0 j (Finset.mem_univ j), sq_nonneg (u j)]
    have hq : quadR u = 0 := by simp [quadR, hu]
    exact le_of_eq (by rw [← hs, hq, mul_zero])

/-- If `t Q + t² K ≥ 0` for every real `t` and `K ≥ 0`, then `Q = 0`. -/
theorem eq_zero_of_forall_quad_nonneg {Q K : ℝ} (hK : 0 ≤ K)
    (h : ∀ t : ℝ, 0 ≤ t * Q + t ^ 2 * K) : Q = 0 := by
  have hK1 : 0 < K + 1 := by linarith
  have hne : K + 1 ≠ 0 := hK1.ne'
  have ht := h (-Q / (K + 1))
  have hmul : -Q / (K + 1) * (K + 1) = -Q := by
    first
      | exact div_mul_cancel₀ (-Q) hne
      | field_simp
  have e : (-Q / (K + 1) * Q + (-Q / (K + 1)) ^ 2 * K) * (K + 1) ^ 2 = -(Q ^ 2) := by
    linear_combination (K * (-Q / (K + 1) * (K + 1)) + Q) * hmul
  have h2 : 0 ≤ (-Q / (K + 1) * Q + (-Q / (K + 1)) ^ 2 * K) * (K + 1) ^ 2 :=
    mul_nonneg ht (sq_nonneg _)
  have h3 : Q ^ 2 ≤ 0 := by linarith
  first
    | exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h3 (sq_nonneg Q))
    | nlinarith [sq_nonneg Q]

/-- The cross term of the expansion is `2 ∑ w (gStdR v − μ v)`, after the shift `j ↦ j + 1`. -/
theorem cross_eq (v w : ZMod N → ℝ) (μ : ℝ) :
    ∑ j, 2 * (oscDiag N j * v j * w j) - 2 * ∑ j, (v j * w (j + 1) + w j * v (j + 1)) -
      μ * ∑ j, 2 * (v j * w j) = 2 * ∑ j, w j * (gStdR v j - μ * v j) := by
  have hshift : ∑ j, w j * v (j - 1) = ∑ j, w (j + 1) * v j := by
    calc ∑ j, w j * v (j - 1) = ∑ j, w (j + 1) * v (j + 1 - 1) :=
          (sum_zmod_add_one fun j : ZMod N => w j * v (j - 1)).symm
      _ = ∑ j, w (j + 1) * v j :=
          Finset.sum_congr rfl fun j _ => by rw [add_sub_cancel_right]
  have h1 : ∑ j, w j * (gStdR v j - μ * v j) = ∑ j, (oscDiag N j * v j * w j - w j * v (j - 1) -
      w j * v (j + 1) - μ * (v j * w j)) :=
    Finset.sum_congr rfl fun j _ => by simp only [gStdR]; ring
  have h2 : ∑ j, (oscDiag N j * v j * w j - w j * v (j - 1) - w j * v (j + 1) - μ * (v j * w j)) =
      ∑ j, oscDiag N j * v j * w j - ∑ j, w j * v (j - 1) - ∑ j, w j * v (j + 1) -
        μ * ∑ j, v j * w j := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have h3 : ∑ j, 2 * (oscDiag N j * v j * w j) = 2 * ∑ j, oscDiag N j * v j * w j := by
    rw [Finset.mul_sum]
  have h4 : ∑ j, (v j * w (j + 1) + w j * v (j + 1)) =
      ∑ j, w (j + 1) * v j + ∑ j, w j * v (j + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h5 : ∑ j, 2 * (v j * w j) = 2 * ∑ j, v j * w j := by
    rw [Finset.mul_sum]
  have h6 : μ * ∑ j, 2 * (v j * w j) = μ * (2 * ∑ j, v j * w j) := by
    rw [h5]
  linarith [h1, h2, h3, h4, h6, hshift]

/-- The real form of D4a. -/
theorem gStdR_eq_of_min (v : ZMod N → ℝ)
    (hmin : ∀ u : ZMod N → ℝ, ∑ j, u j ^ 2 = 1 → quadR v ≤ quadR u)
    (hv1 : ∑ j, v j ^ 2 = 1) (j : ZMod N) : gStdR v j = quadR v * v j := by
  have hlow := quadR_lower v hmin
  have hzero : ∀ w : ZMod N → ℝ, ∑ i, w i * (gStdR v i - quadR v * v i) = 0 := by
    intro w
    have hK : 0 ≤ quadR w - quadR v * ∑ i, w i ^ 2 := by linarith [hlow w]
    have hQ : ∀ t : ℝ, 0 ≤ t * (∑ i, 2 * (oscDiag N i * v i * w i) -
        2 * ∑ i, (v i * w (i + 1) + w i * v (i + 1)) - quadR v * ∑ i, 2 * (v i * w i)) +
        t ^ 2 * (quadR w - quadR v * ∑ i, w i ^ 2) := by
      intro t
      have h1 := hlow (fun i => v i + t * w i)
      rw [quadR_expand, sum_sq_expand, hv1] at h1
      first
        | linarith [h1]
        | nlinarith [h1]
    have hQ0 := eq_zero_of_forall_quad_nonneg hK hQ
    linarith [cross_eq v w (quadR v), hQ0]
  have hsq := hzero (fun i => gStdR v i - quadR v * v i)
  have h0 : ∀ i ∈ Finset.univ,
      (gStdR v i - quadR v * v i) * (gStdR v i - quadR v * v i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_self_nonneg (gStdR v i - quadR v * v i)).mp hsq
  have h := mul_self_eq_zero.mp (h0 j (Finset.mem_univ j))
  linarith

/-- **D4a.** A minimizer of `E_N` on the real unit sphere is an eigenvector of `G_N`, with
eigenvalue its energy, in the form of the hypothesis of D3. -/
theorem ground_eigen (v : ZMod N → ℝ) (hv1 : ∑ j, v j ^ 2 = 1)
    (hmin : ∀ u : ZMod N → ℝ, ∑ j, u j ^ 2 = 1 →
      energy (fun j => (v j : ℂ)) ≤ energy (fun j => (u j : ℂ))) (j : ZMod N) :
    gStd (fun i => (v i : ℂ)) j = ((energy (fun i => (v i : ℂ)) : ℝ) : ℂ) * (v j : ℂ) := by
  have hminR : ∀ u : ZMod N → ℝ, ∑ j, u j ^ 2 = 1 → quadR v ≤ quadR u := by
    intro u hu
    have h := hmin u hu
    rwa [energy_ofReal, energy_ofReal] at h
  rw [gStd_ofReal, energy_ofReal, gStdR_eq_of_min v hminR hv1 j, Complex.ofReal_mul]

end BLT

end
