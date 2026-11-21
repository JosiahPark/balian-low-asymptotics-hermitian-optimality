import BLTAudit.Basic
import BLTAudit.EdgeEnergy
import BLTAudit.TotalCharge

/-!
# B4. Good plaquettes are neutral and large edges are few (§4.1, (L5))

Two consequences of (L1) and (L3) for a unit-modulus array `ζ : ℤ × ℤ → ℂ`, with `aQ`, `aR`,
`zakEnergy` of `BLTAudit/Basic.lean` and the plaquette integer `plaquetteCharge` of B3.

* `plaquetteCharge_eq_zero_of_small`: if the four edge numbers of the plaquette at `(q, r)` have
  modulus `< η` and `4η + 2π/d² < 2π`, then `plaquetteCharge d ζ q r = 0`.
  `plaquette_int_eq_zero_of_small` is the same for any integer `n` that satisfies (L3) at
  `(q, r)`, with no hypothesis on `ζ`.
* `largeEdgesR d ζ η`, `largeEdgesQ d ζ η`: the positions `(q, r)` with `q r < d` whose `r`-edge
  (resp. `q`-edge) number has modulus `≥ η`. Together these are the large edges among the positive
  edges of the `d × d` square, each edge once, as in `zakEnergy`.
* `card_large_edges_mul_le_zakEnergy`: for `0 ≤ η`,
  `(#largeEdgesR + #largeEdgesQ) * (4 sin²(η/2)) ≤ zakEnergy d ζ`;
  `card_large_edges_le_div`: for `0 < η ≤ π`, the paper's form
  `#{large edges} ≤ zakEnergy d ζ / (4 sin²(η/2))`, the first inequality of (L5).

Helpers: `abs_aR_le_pi`, `abs_aQ_le_pi` (edge numbers lie in `[-π, π]`),
`int_eq_zero_of_four_small` (the real arithmetic of neutrality), `four_sin_half_sq`
(`4 sin²(x/2) = 2 - 2 cos x`), `four_sin_half_sq_le_of_le_abs` (the edge weight is monotone on
`0 ≤ η ≤ |a| ≤ π`), `card_filter_mul_le_sum` (a Markov-type count), `zakEnergy_eq_sum_product`
((L1) over `range d ×ˢ range d`), `card_largeEdgesR_mul_le`, `card_largeEdgesQ_mul_le`.

Differences from the roadmap item: the product bound needs only `0 ≤ η`; the bound `η ≤ π` is
used only for the quotient form. Neither the gluing of `IsTwisted` nor `0 < d` is used.

What this file does NOT prove: the rest of (L5), that is `#{large edges} ≤ C₁ log d / η²` and
`#{bad plaquettes} ≤ 2 #{large edges}`; that the four edges of a plaquette at a seam are edges of
the square (this needs the periodicity of B2a); where the nonzero plaquette integers sit. It
proves nothing toward Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the hypotheses
[HU] and [HL].
-/

noncomputable section

open Finset
open scoped ComplexConjugate

namespace BLT

/-- The `r`-edge numbers are principal arguments: `|aR ζ q r| ≤ π`. -/
theorem abs_aR_le_pi (ζ : ℤ × ℤ → ℂ) (q r : ℤ) : |aR ζ q r| ≤ Real.pi := by
  unfold aR
  exact Complex.abs_arg_le_pi _

/-- The `q`-edge numbers are principal arguments: `|aQ d ζ q r| ≤ π`. -/
theorem abs_aQ_le_pi (d : ℕ) (ζ : ℤ × ℤ → ℂ) (q r : ℤ) : |aQ d ζ q r| ≤ Real.pi := by
  unfold aQ
  exact Complex.abs_arg_le_pi _

/-- Real arithmetic behind neutrality: if `a₁ + a₂ - a₃ - a₄ = -c + t * n` for an integer `n`,
with `0 < t`, `0 ≤ c`, the four terms of modulus `< η` and `4η + c < t`, then `n = 0`. -/
theorem int_eq_zero_of_four_small {a₁ a₂ a₃ a₄ c t η : ℝ} {n : ℤ} (ht : 0 < t) (hc : 0 ≤ c)
    (hn : a₁ + a₂ - a₃ - a₄ = -c + t * (n : ℝ)) (hη : 4 * η + c < t)
    (h₁ : |a₁| < η) (h₂ : |a₂| < η) (h₃ : |a₃| < η) (h₄ : |a₄| < η) : n = 0 := by
  obtain ⟨l₁, u₁⟩ := abs_lt.mp h₁
  obtain ⟨l₂, u₂⟩ := abs_lt.mp h₂
  obtain ⟨l₃, u₃⟩ := abs_lt.mp h₃
  obtain ⟨l₄, u₄⟩ := abs_lt.mp h₄
  have hlt : (n : ℝ) < 1 :=
    lt_of_mul_lt_mul_left (by linarith : t * (n : ℝ) < t * 1) ht.le
  have hgt : (0 : ℝ) < (n : ℝ) + 1 :=
    lt_of_mul_lt_mul_left (by linarith : t * (0 : ℝ) < t * ((n : ℝ) + 1)) ht.le
  have h1 : n < 1 := by exact_mod_cast hlt
  have h2 : 0 < n + 1 := by exact_mod_cast hgt
  omega

/-- **B4, neutrality, general form.** An integer that satisfies the plaquette identity (L3) at a
plaquette whose four edge numbers have modulus `< η`, with `4η + 2π/d² < 2π`, is zero. -/
theorem plaquette_int_eq_zero_of_small {d : ℕ} {ζ : ℤ × ℤ → ℂ} {q r n : ℤ} {η : ℝ}
    (hn : aQ d ζ q r + aR ζ (q + 1) r - aQ d ζ q (r + 1) - aR ζ q r =
      -(2 * Real.pi / (d : ℝ) ^ 2) + 2 * Real.pi * (n : ℝ))
    (hη : 4 * η + 2 * Real.pi / (d : ℝ) ^ 2 < 2 * Real.pi)
    (h₁ : |aQ d ζ q r| < η) (h₂ : |aR ζ (q + 1) r| < η)
    (h₃ : |aQ d ζ q (r + 1)| < η) (h₄ : |aR ζ q r| < η) : n = 0 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have hc : (0 : ℝ) ≤ 2 * Real.pi / (d : ℝ) ^ 2 := div_nonneg hpi.le (sq_nonneg _)
  exact int_eq_zero_of_four_small hpi hc hn hη h₁ h₂ h₃ h₄

/-- **B4, good plaquettes are neutral.** For a unit-modulus array, a plaquette whose four edge
numbers have modulus `< η`, with `4η + 2π/d² < 2π`, has plaquette integer zero. -/
theorem plaquetteCharge_eq_zero_of_small (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1)
    (q r : ℤ) {η : ℝ} (hη : 4 * η + 2 * Real.pi / (d : ℝ) ^ 2 < 2 * Real.pi)
    (h₁ : |aQ d ζ q r| < η) (h₂ : |aR ζ (q + 1) r| < η)
    (h₃ : |aQ d ζ q (r + 1)| < η) (h₄ : |aR ζ q r| < η) : plaquetteCharge d ζ q r = 0 :=
  plaquette_int_eq_zero_of_small (plaquetteCharge_spec d ζ hζ q r) hη h₁ h₂ h₃ h₄

/-- The edge weight of (L1): `4 sin²(x/2) = 2 - 2 cos x`. -/
theorem four_sin_half_sq (x : ℝ) : 4 * Real.sin (x / 2) ^ 2 = 2 - 2 * Real.cos x := by
  have h := Real.cos_two_mul_eq_one_sub (x / 2)
  have e : 2 * (x / 2) = x := by ring
  rw [e] at h
  first | linarith | linear_combination (2 : ℝ) * h

/-- The edge weight is monotone in the modulus of the angle on `[0, π]`. -/
theorem four_sin_half_sq_le_of_le_abs {η a : ℝ} (hη : 0 ≤ η) (ha : |a| ≤ Real.pi)
    (h : η ≤ |a|) : 4 * Real.sin (η / 2) ^ 2 ≤ 4 * Real.sin (a / 2) ^ 2 := by
  have hcos : Real.cos |a| ≤ Real.cos η := Real.cos_le_cos_of_nonneg_of_le_pi hη ha h
  rw [Real.cos_abs] at hcos
  rw [four_sin_half_sq η, four_sin_half_sq a]
  linarith

/-- A Markov-type count: if `0 ≤ f` on `s` and `c ≤ f i` wherever `P i`, then
`#{i ∈ s | P i} * c ≤ ∑ i ∈ s, f i`. -/
theorem card_filter_mul_le_sum {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P]
    (f : ι → ℝ) (c : ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (hc : ∀ i ∈ s, P i → c ≤ f i) :
    ((s.filter P).card : ℝ) * c ≤ ∑ i ∈ s, f i := by
  have h1 : ((s.filter P).card : ℝ) * c = ∑ _i ∈ s.filter P, c := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ _i ∈ s.filter P, c ≤ ∑ i ∈ s.filter P, f i :=
    Finset.sum_le_sum fun i hi => hc i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  have h3 : ∑ i ∈ s.filter P, f i ≤ ∑ i ∈ s, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset P s) fun i hi _ => hf i hi
  rw [h1]
  exact h2.trans h3

/-- The large `r`-edges of the `d × d` square: positions `(q, r)`, `q r < d`, with
`η ≤ |aR ζ q r|`. -/
def largeEdgesR (d : ℕ) (ζ : ℤ × ℤ → ℂ) (η : ℝ) : Finset (ℕ × ℕ) :=
  (range d ×ˢ range d).filter fun p => η ≤ |aR ζ (p.1 : ℤ) (p.2 : ℤ)|

/-- The large `q`-edges of the `d × d` square: positions `(q, r)`, `q r < d`, with
`η ≤ |aQ d ζ q r|`. -/
def largeEdgesQ (d : ℕ) (ζ : ℤ × ℤ → ℂ) (η : ℝ) : Finset (ℕ × ℕ) :=
  (range d ×ˢ range d).filter fun p => η ≤ |aQ d ζ (p.1 : ℤ) (p.2 : ℤ)|

/-- (L1) over the product index set, split into `r`-edges and `q`-edges. -/
theorem zakEnergy_eq_sum_product (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1) :
    zakEnergy d ζ =
      ∑ p ∈ range d ×ˢ range d, 4 * Real.sin (aR ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 +
        ∑ p ∈ range d ×ˢ range d, 4 * Real.sin (aQ d ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 := by
  rw [zakEnergy_eq_sum_sin_sq d ζ hζ, ← Finset.sum_add_distrib]
  exact (Finset.sum_product' (range d) (range d) fun q r : ℕ =>
    4 * Real.sin (aR ζ (q : ℤ) (r : ℤ) / 2) ^ 2 +
      4 * Real.sin (aQ d ζ (q : ℤ) (r : ℤ) / 2) ^ 2).symm

/-- Large `r`-edges against the `r`-edge part of the energy. -/
theorem card_largeEdgesR_mul_le (d : ℕ) (ζ : ℤ × ℤ → ℂ) {η : ℝ} (hη : 0 ≤ η) :
    ((largeEdgesR d ζ η).card : ℝ) * (4 * Real.sin (η / 2) ^ 2) ≤
      ∑ p ∈ range d ×ˢ range d, 4 * Real.sin (aR ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 := by
  have hf : ∀ p : ℕ × ℕ, p ∈ range d ×ˢ range d →
      (0 : ℝ) ≤ 4 * Real.sin (aR ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 := fun p _ => by positivity
  have hc : ∀ p : ℕ × ℕ, p ∈ range d ×ˢ range d → η ≤ |aR ζ (p.1 : ℤ) (p.2 : ℤ)| →
      4 * Real.sin (η / 2) ^ 2 ≤ 4 * Real.sin (aR ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 :=
    fun p _ hp => four_sin_half_sq_le_of_le_abs hη (abs_aR_le_pi ζ _ _) hp
  unfold largeEdgesR
  exact card_filter_mul_le_sum (range d ×ˢ range d) (fun p => η ≤ |aR ζ (p.1 : ℤ) (p.2 : ℤ)|)
    (fun p => 4 * Real.sin (aR ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2) (4 * Real.sin (η / 2) ^ 2) hf hc

/-- Large `q`-edges against the `q`-edge part of the energy. -/
theorem card_largeEdgesQ_mul_le (d : ℕ) (ζ : ℤ × ℤ → ℂ) {η : ℝ} (hη : 0 ≤ η) :
    ((largeEdgesQ d ζ η).card : ℝ) * (4 * Real.sin (η / 2) ^ 2) ≤
      ∑ p ∈ range d ×ˢ range d, 4 * Real.sin (aQ d ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 := by
  have hf : ∀ p : ℕ × ℕ, p ∈ range d ×ˢ range d →
      (0 : ℝ) ≤ 4 * Real.sin (aQ d ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 := fun p _ => by positivity
  have hc : ∀ p : ℕ × ℕ, p ∈ range d ×ˢ range d → η ≤ |aQ d ζ (p.1 : ℤ) (p.2 : ℤ)| →
      4 * Real.sin (η / 2) ^ 2 ≤ 4 * Real.sin (aQ d ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2 :=
    fun p _ hp => four_sin_half_sq_le_of_le_abs hη (abs_aQ_le_pi d ζ _ _) hp
  unfold largeEdgesQ
  exact card_filter_mul_le_sum (range d ×ˢ range d)
    (fun p => η ≤ |aQ d ζ (p.1 : ℤ) (p.2 : ℤ)|)
    (fun p => 4 * Real.sin (aQ d ζ (p.1 : ℤ) (p.2 : ℤ) / 2) ^ 2) (4 * Real.sin (η / 2) ^ 2) hf hc

/-- **B4, large edges are few.** For a unit-modulus array and `0 ≤ η`, the number of edges of the
`d × d` square with `|a| ≥ η`, times `4 sin²(η/2)`, is at most the Zak energy. -/
theorem card_large_edges_mul_le_zakEnergy (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1)
    {η : ℝ} (hη : 0 ≤ η) :
    (((largeEdgesR d ζ η).card + (largeEdgesQ d ζ η).card : ℕ) : ℝ) *
      (4 * Real.sin (η / 2) ^ 2) ≤ zakEnergy d ζ := by
  have hR := card_largeEdgesR_mul_le d ζ hη
  have hQ := card_largeEdgesQ_mul_le d ζ hη
  have hcast : (((largeEdgesR d ζ η).card + (largeEdgesQ d ζ η).card : ℕ) : ℝ) =
      ((largeEdgesR d ζ η).card : ℝ) + ((largeEdgesQ d ζ η).card : ℝ) := Nat.cast_add _ _
  rw [hcast, zakEnergy_eq_sum_product d ζ hζ, add_mul]
  exact add_le_add hR hQ

/-- **(L5), first inequality.** For `0 < η ≤ π`,
`#{large edges} ≤ zakEnergy d ζ / (4 sin²(η/2))`. -/
theorem card_large_edges_le_div (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1) {η : ℝ}
    (hη : 0 < η) (hηπ : η ≤ Real.pi) :
    (((largeEdgesR d ζ η).card + (largeEdgesQ d ζ η).card : ℕ) : ℝ) ≤
      zakEnergy d ζ / (4 * Real.sin (η / 2) ^ 2) := by
  have hs : 0 < Real.sin (η / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hpos : 0 < 4 * Real.sin (η / 2) ^ 2 := mul_pos (by norm_num) (pow_pos hs 2)
  rw [le_div_iff₀ hpos]
  exact card_large_edges_mul_le_zakEnergy d ζ hζ hη.le

end BLT

end
