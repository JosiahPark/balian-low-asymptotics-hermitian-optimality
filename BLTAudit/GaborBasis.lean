import BLTAudit.ZakCriterion

/-!
# A4e. The critical Gabor system is a basis when `|Z f| = 1/d`

With `ip`, `gabor`, `zak` of `BLTAudit/Basic.lean` (paper §2, the last step of the sufficiency
half of the critical Gabor criterion):

* `ip_zero_right`, `ip_sum_smul_right`: `⟨u, 0⟩ = 0` and
  `⟨u, ∑_{i ∈ s} g i • w i⟩ = ∑_{i ∈ s} g i ⟨u, w i⟩` (linearity of `ip` in its second argument,
  for finite linear combinations);
* `linearIndependent_of_ip_orthonormal`: a family `v : ι → ZMod N → ℂ` with
  `ip (v i) (v j) = if i = j then 1 else 0` is linearly independent over `ℂ` (any index type
  `ι` with decidable equality);
* `linearIndependent_gabor`: if `‖zak f q r‖ = 1 / d` for all `q r`, the family
  `fun p : Fin d × Fin d => gabor f p.1 p.2` is linearly independent over `ℂ` (from A4d);
* `span_gabor_eq_top`: under the same hypothesis this family spans `ZMod (d * d) → ℂ`, because
  it has `d * d = finrank` members.

What this file does NOT prove: it does not package the family as a term of Mathlib's `Basis`
(linear independence and `span = ⊤` are stated separately), it does not prove the converse
"orthonormal implies `|Z f| = 1/d`" (A5), and it says nothing about the energy. It proves
nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the hypotheses
[HU] and [HL].
-/

noncomputable section

namespace BLT

/-- `⟨u, 0⟩ = 0`. -/
theorem ip_zero_right {N : ℕ} [NeZero N] (u : ZMod N → ℂ) : ip u 0 = 0 := by
  unfold ip
  first
    | simp
    | exact Finset.sum_eq_zero fun j _ => mul_zero _

/-- `ip` is linear in its second argument, for finite linear combinations. -/
theorem ip_sum_smul_right {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι) (g : ι → ℂ)
    (u : ZMod N → ℂ) (w : ι → ZMod N → ℂ) :
    ip u (∑ i ∈ s, g i • w i) = ∑ i ∈ s, g i * ip u (w i) := by
  unfold ip
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- A family that is orthonormal for `ip` is linearly independent over `ℂ`. -/
theorem linearIndependent_of_ip_orthonormal {N : ℕ} [NeZero N] {ι : Type*} [DecidableEq ι]
    (v : ι → ZMod N → ℂ) (h : ∀ i j, ip (v i) (v j) = if i = j then (1 : ℂ) else 0) :
    LinearIndependent ℂ v := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have h0 : ip (v i) (∑ j ∈ s, g j • v j) = 0 :=
    (congrArg (ip (v i)) hsum).trans (ip_zero_right (v i))
  have hs : ∑ j ∈ s, g j * ip (v i) (v j) = g i * ip (v i) (v i) :=
    Finset.sum_eq_single i
      (fun j _ hji => by
        show g j * ip (v i) (v j) = 0
        rw [h i j, if_neg (Ne.symm hji), mul_zero])
      (fun hni => absurd hi hni)
  have h1 : ip (v i) (∑ j ∈ s, g j • v j) = g i := by
    rw [ip_sum_smul_right, hs, h i i, if_pos rfl, mul_one]
  exact h1.symm.trans h0

variable {d : ℕ} [NeZero d]

/-- **A4e, independence.** If `|Z f| = 1/d` everywhere, the `d * d` Gabor vectors
`gabor f n m`, `n m < d`, are linearly independent over `ℂ`. -/
theorem linearIndependent_gabor (f : ZMod (d * d) → ℂ)
    (h : ∀ q r : ZMod d, ‖zak f q r‖ = 1 / (d : ℝ)) :
    LinearIndependent ℂ (fun p : Fin d × Fin d => gabor f p.1 p.2) := by
  refine linearIndependent_of_ip_orthonormal _ (fun p p' => ?_)
  have hiff : ((p.1 : ℕ) = (p'.1 : ℕ) ∧ (p.2 : ℕ) = (p'.2 : ℕ)) ↔ p = p' := by
    constructor
    · intro e
      first
        | exact Prod.ext (Fin.ext e.1) (Fin.ext e.2)
        | exact Prod.ext_iff.mpr ⟨Fin.ext e.1, Fin.ext e.2⟩
    · intro e
      first
        | (subst e; exact ⟨rfl, rfl⟩)
        | (rw [e]; exact ⟨rfl, rfl⟩)
  have key := ip_gabor_of_zak_norm f h p.1.isLt p.2.isLt p'.1.isLt p'.2.isLt
  by_cases hp : p = p'
  · rw [if_pos hp]
    rw [if_pos (hiff.mpr hp)] at key
    exact key
  · have hne : ¬ ((p.1 : ℕ) = (p'.1 : ℕ) ∧ (p.2 : ℕ) = (p'.2 : ℕ)) := fun e => hp (hiff.mp e)
    rw [if_neg hp]
    rw [if_neg hne] at key
    exact key

/-- **A4e, span.** If `|Z f| = 1/d` everywhere, the Gabor vectors `gabor f n m`, `n m < d`,
span `ZMod (d * d) → ℂ`: a linearly independent family with `d * d = finrank` members. -/
theorem span_gabor_eq_top (f : ZMod (d * d) → ℂ)
    (h : ∀ q r : ZMod d, ‖zak f q r‖ = 1 / (d : ℝ)) :
    Submodule.span ℂ (Set.range (fun p : Fin d × Fin d => gabor f p.1 p.2)) = ⊤ := by
  have hli := linearIndependent_gabor f h
  first
    | refine hli.span_eq_top_of_card_eq_finrank' ?_
    | refine hli.span_eq_top_of_card_eq_finrank ?_
    | (refine Submodule.eq_top_of_finrank_eq ?_; rw [finrank_span_eq_card hli])
  first
    | simp [ZMod.card]
    | rw [Module.finrank_fintype_fun_eq_card, ZMod.card, Fintype.card_prod, Fintype.card_fin]
    | rw [Module.finrank_pi, ZMod.card, Fintype.card_prod, Fintype.card_fin]

end BLT

end
