import BLTAudit.EdgeEnergy
import BLTAudit.TotalCharge

/-!
# B4. Good plaquettes are neutral and large edges are few (L5)

Paper §4.1, around (L5). With `aQ`, `aR`, `zakEnergy` of `BLTAudit/Basic.lean` and
`plaquetteCharge` of `BLTAudit/TotalCharge.lean`:

* `plaquette_int_eq_zero_of_good`: if the four edge numbers of the plaquette at `(q, r)` have
  modulus `< η`, `4η + 2π / d² < 2π`, and the integer `n` satisfies (L3) there, then `n = 0`
  (no hypothesis on `ζ`); `plaquetteCharge_eq_zero_of_good` is the same for
  `n = plaquetteCharge d ζ q r` and a unit-modulus `ζ`;
* `largeEdgesR d ζ η`, `largeEdgesQ d ζ η`: the pairs `(q, r)` of naturals `q r < d` with
  `η ≤ |aR ζ q r|`, respectively `η ≤ |aQ d ζ q r|` (the large edges of the square);
* `card_large_edges_mul_le_zakEnergy`: for a unit-modulus `ζ` and `0 ≤ η`,
  `(#largeEdgesR + #largeEdgesQ) * (4 sin²(η / 2)) ≤ zakEnergy d ζ`, from (L1) (item B1) and the
  monotonicity of `4 sin²(a / 2)` in `|a| ≤ π`.

Helper lemmas: `cos_eq_one_sub_two_sin_sq_half`, `four_sin_sq_half_le_of_le_abs`,
`abs_aR_le_pi`, `abs_aQ_le_pi`, `int_eq_zero_of_small` (the arithmetic of the first part) and
`card_filter_mul_le_sum` (a count times a lower bound is at most the sum).

The item asks for `0 < η ≤ π` in the count; only `0 ≤ η` is used (for `η > π` there is no large
edge). The gluing of `IsTwisted` is not used anywhere in this file.

What this file does NOT prove: the bound `#{bad plaquettes} ≤ 2 #{large edges}` of (L5), the
division form `#{large edges} ≤ A_d / (4 sin²(η / 2))`, the choice `η = 1 / log d`, or any lower
bound for `zakEnergy`. It proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and
nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

/-- `cos x = 1 - 2 sin²(x / 2)`. -/
theorem cos_eq_one_sub_two_sin_sq_half (x : ℝ) :
    Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
  have h := Real.cos_two_mul_eq_one_sub (x / 2)
  have e : 2 * (x / 2) = x := by ring
  rwa [e] at h

/-- `4 sin²(a / 2)` is monotone in `|a|` for `|a| ≤ π`. -/
theorem four_sin_sq_half_le_of_le_abs {η a : ℝ} (hη : 0 ≤ η) (ha : η ≤ |a|)
    (hπ : |a| ≤ Real.pi) : 4 * Real.sin (η / 2) ^ 2 ≤ 4 * Real.sin (a / 2) ^ 2 := by
  have h1 : Real.cos |a| ≤ Real.cos η := by
    first
      | exact Real.cos_le_cos_of_nonneg_of_le_pi hη hπ ha
      | exact Real.antitoneOn_cos ⟨hη, ha.trans hπ⟩ ⟨hη.trans ha, hπ⟩ ha
  have h2 : Real.cos |a| = Real.cos a := by
    first | exact Real.cos_abs a | (rcases abs_choice a with h | h <;> simp [h])
  have h3 := cos_eq_one_sub_two_sin_sq_half η
  have h4 := cos_eq_one_sub_two_sin_sq_half a
  linarith

/-- The `r`-edge numbers lie in `[-π, π]`. -/
theorem abs_aR_le_pi (ζ : ℤ × ℤ → ℂ) (q r : ℤ) : |aR ζ q r| ≤ Real.pi := by
  unfold aR
  first
    | exact Complex.abs_arg_le_pi _
    | exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩

/-- The `q`-edge numbers lie in `[-π, π]`. -/
theorem abs_aQ_le_pi (d : ℕ) (ζ : ℤ × ℤ → ℂ) (q r : ℤ) : |aQ d ζ q r| ≤ Real.pi := by
  unfold aQ
  first
    | exact Complex.abs_arg_le_pi _
    | exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩

/-- If `s = -(2π / d²) + 2π n` with `|s| < 4η` and `4η + 2π / d² < 2π`, then `n = 0`. -/
theorem int_eq_zero_of_small {d : ℕ} {η s : ℝ} {n : ℤ} (hs : |s| < 4 * η)
    (hη : 4 * η + 2 * Real.pi / (d : ℝ) ^ 2 < 2 * Real.pi)
    (hn : s = -(2 * Real.pi / (d : ℝ) ^ 2) + 2 * Real.pi * (n : ℝ)) : n = 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc : 0 ≤ 2 * Real.pi / (d : ℝ) ^ 2 := by positivity
  obtain ⟨hs1, hs2⟩ := abs_lt.mp hs
  have h1 : n < 1 := by
    by_contra hcon
    have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast not_lt.mp hcon
    have h5 : 0 ≤ Real.pi * ((n : ℝ) - 1) := mul_nonneg hpi.le (sub_nonneg.mpr h2)
    first | linarith | nlinarith
  have h3 : -1 < n := by
    by_contra hcon
    have h4 : (n : ℝ) ≤ -1 := by exact_mod_cast not_lt.mp hcon
    have h5 : 0 ≤ Real.pi * (-1 - (n : ℝ)) := mul_nonneg hpi.le (sub_nonneg.mpr h4)
    first | linarith | nlinarith
  omega

/-- **B4, first part.** If the four edge numbers of a plaquette have modulus `< η` and
`4η + 2π / d² < 2π`, an integer satisfying (L3) at that plaquette is `0`. -/
theorem plaquette_int_eq_zero_of_good {d : ℕ} {ζ : ℤ × ℤ → ℂ} {q r n : ℤ} {η : ℝ}
    (h1 : |aQ d ζ q r| < η) (h2 : |aR ζ (q + 1) r| < η) (h3 : |aQ d ζ q (r + 1)| < η)
    (h4 : |aR ζ q r| < η) (hη : 4 * η + 2 * Real.pi / (d : ℝ) ^ 2 < 2 * Real.pi)
    (hn : aQ d ζ q r + aR ζ (q + 1) r - aQ d ζ q (r + 1) - aR ζ q r =
      -(2 * Real.pi / (d : ℝ) ^ 2) + 2 * Real.pi * (n : ℝ)) : n = 0 := by
  have hs : |aQ d ζ q r + aR ζ (q + 1) r - aQ d ζ q (r + 1) - aR ζ q r| < 4 * η := by
    obtain ⟨a1, a2⟩ := abs_lt.mp h1
    obtain ⟨b1, b2⟩ := abs_lt.mp h2
    obtain ⟨c1, c2⟩ := abs_lt.mp h3
    obtain ⟨e1, e2⟩ := abs_lt.mp h4
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  exact int_eq_zero_of_small hs hη hn

/-- **B4, first part, for the plaquette integer.** For a unit-modulus array, a plaquette whose
four edge numbers have modulus `< η`, with `4η + 2π / d² < 2π`, has `plaquetteCharge = 0`. -/
theorem plaquetteCharge_eq_zero_of_good {d : ℕ} {ζ : ℤ × ℤ → ℂ} (hζ : ∀ p, ‖ζ p‖ = 1)
    {q r : ℤ} {η : ℝ} (h1 : |aQ d ζ q r| < η) (h2 : |aR ζ (q + 1) r| < η)
    (h3 : |aQ d ζ q (r + 1)| < η) (h4 : |aR ζ q r| < η)
    (hη : 4 * η + 2 * Real.pi / (d : ℝ) ^ 2 < 2 * Real.pi) : plaquetteCharge d ζ q r = 0 :=
  plaquette_int_eq_zero_of_good h1 h2 h3 h4 hη (plaquetteCharge_spec d ζ hζ q r)

/-- The `r`-edges of the square, as pairs `(q, r)` with `q r < d`, with `η ≤ |aR ζ q r|`. -/
def largeEdgesR (d : ℕ) (ζ : ℤ × ℤ → ℂ) (η : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range d ×ˢ Finset.range d).filter
    fun p : ℕ × ℕ => η ≤ |aR ζ (p.1 : ℤ) (p.2 : ℤ)|

/-- The `q`-edges of the square, as pairs `(q, r)` with `q r < d`, with `η ≤ |aQ d ζ q r|`. -/
def largeEdgesQ (d : ℕ) (ζ : ℤ × ℤ → ℂ) (η : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range d ×ˢ Finset.range d).filter
    fun p : ℕ × ℕ => η ≤ |aQ d ζ (p.1 : ℤ) (p.2 : ℤ)|

/-- If `0 ≤ f` on `s` and `c ≤ f p` whenever `P p`, then `#{p ∈ s | P p} * c ≤ ∑ p ∈ s, f p`. -/
theorem card_filter_mul_le_sum {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P]
    (f : ι → ℝ) (c : ℝ) (hf : ∀ p ∈ s, 0 ≤ f p) (hc : ∀ p ∈ s, P p → c ≤ f p) :
    ((s.filter P).card : ℝ) * c ≤ ∑ p ∈ s, f p := by
  have h1 : ((s.filter P).card : ℝ) * c = ∑ _p ∈ s.filter P, c := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ _p ∈ s.filter P, c ≤ ∑ p ∈ s.filter P, f p :=
    Finset.sum_le_sum fun p hp =>
      hc p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  have h3 : ∑ p ∈ s.filter P, f p ≤ ∑ p ∈ s, f p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset P s) fun p hp _ => hf p hp
  exact le_of_eq_of_le h1 (h2.trans h3)

/-- **B4, second part (L5).** For a unit-modulus array and `0 ≤ η`, the number of edges of the
square with `|a| ≥ η`, times `4 sin²(η / 2)`, is at most the Zak energy. -/
theorem card_large_edges_mul_le_zakEnergy (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1)
    {η : ℝ} (hη : 0 ≤ η) :
    (((largeEdgesR d ζ η).card + (largeEdgesQ d ζ η).card : ℕ) : ℝ) *
      (4 * Real.sin (η / 2) ^ 2) ≤ zakEnergy d ζ := by
  have hR : ((largeEdgesR d ζ η).card : ℝ) * (4 * Real.sin (η / 2) ^ 2) ≤
      ∑ p ∈ Finset.range d ×ˢ Finset.range d,
        4 * Real.sin (aR ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 :=
    card_filter_mul_le_sum (Finset.range d ×ˢ Finset.range d)
      (fun p : ℕ × ℕ => η ≤ |aR ζ (p.1 : ℤ) (p.2 : ℤ)|)
      (fun p : ℕ × ℕ => 4 * Real.sin (aR ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2)
      (4 * Real.sin (η / 2) ^ 2) (fun p _ => mul_nonneg (by norm_num) (sq_nonneg _))
      (fun p _ hp => four_sin_sq_half_le_of_le_abs hη hp (abs_aR_le_pi ζ _ _))
  have hQ : ((largeEdgesQ d ζ η).card : ℝ) * (4 * Real.sin (η / 2) ^ 2) ≤
      ∑ p ∈ Finset.range d ×ˢ Finset.range d,
        4 * Real.sin (aQ d ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 :=
    card_filter_mul_le_sum (Finset.range d ×ˢ Finset.range d)
      (fun p : ℕ × ℕ => η ≤ |aQ d ζ (p.1 : ℤ) (p.2 : ℤ)|)
      (fun p : ℕ × ℕ => 4 * Real.sin (aQ d ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2)
      (4 * Real.sin (η / 2) ^ 2) (fun p _ => mul_nonneg (by norm_num) (sq_nonneg _))
      (fun p _ hp => four_sin_sq_half_le_of_le_abs hη hp (abs_aQ_le_pi d ζ _ _))
  have hsplit : zakEnergy d ζ =
      ∑ p ∈ Finset.range d ×ˢ Finset.range d,
        4 * Real.sin (aR ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 +
      ∑ p ∈ Finset.range d ×ˢ Finset.range d,
        4 * Real.sin (aQ d ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 := by
    rw [zakEnergy_eq_sum_sin_sq d ζ hζ, ← Finset.sum_add_distrib]
    first
      | exact (Finset.sum_product' _ _ _).symm
      | exact (Finset.sum_product _ _ _).symm
      | rw [Finset.sum_product]
  have hcast : (((largeEdgesR d ζ η).card + (largeEdgesQ d ζ η).card : ℕ) : ℝ) *
      (4 * Real.sin (η / 2) ^ 2) =
      ((largeEdgesR d ζ η).card : ℝ) * (4 * Real.sin (η / 2) ^ 2) +
        ((largeEdgesQ d ζ η).card : ℝ) * (4 * Real.sin (η / 2) ^ 2) := by
    rw [Nat.cast_add, add_mul]
  exact le_of_eq_of_le hcast ((add_le_add hR hQ).trans (le_of_eq hsplit.symm))

end BLT

end
