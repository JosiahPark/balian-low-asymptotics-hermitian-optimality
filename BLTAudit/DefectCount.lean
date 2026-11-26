import BLTAudit.Basic
import BLTAudit.GoodPlaquette

/-!
# G2. Defect count: the counting in (L5) and the bound (L14) (§4.1, §4.3)

Paper §4.1: with `η_d = 1 / log d`, an edge is large if `|a_e| ≥ η_d`, and a plaquette is bad if it
is incident to a large edge. (L5) says `#{large edges} ≤ A_d / (4 sin²(η_d/2)) ≤ C₁ log d / η_d²`
and `#{bad plaquettes} ≤ 2 #{large edges}`; (L14) then uses
`S₀ = 10 #{bad plaquettes} ≤ C₂ (log d)³`. This file proves the counting, for abstract finite sets:

* `four_div_pi_sq_mul_sq_le`: for `0 ≤ η ≤ π`, `4 / π ^ 2 * η ^ 2 ≤ 4 * Real.sin (η / 2) ^ 2`
  (Jordan's inequality, Mathlib's `Real.mul_le_sin` at `η / 2`); `four_mul_sq_le_pi_sq_mul` is the
  same without division, `4 η² ≤ π² · 4 sin²(η/2)`;
* `card_biUnion_le_two_mul`: `(L.biUnion inc).card ≤ 2 * L.card` when every `inc e` with `e ∈ L`
  has at most two elements (`L`: the large edges, `inc e`: the plaquettes incident to `e`);
* `defect_count`: for real `d ≥ 2`, `η = 1 / Real.log d`, if
  `(L.card : ℝ) * (4 * Real.sin (η / 2) ^ 2) ≤ A` (the form of `card_large_edges_mul_le_zakEnergy`
  of B4) and `A ≤ C₀ * Real.log d`, then
  `10 * ((L.biUnion inc).card : ℝ) ≤ 5 * π ^ 2 * C₀ * Real.log d ^ 3`: the bound of (L14) with
  `C₂ = 5 π² C₀`, in the form of the hypothesis `hS` of `lower_bound_arithmetic` (E5);
* `four_mul_card_large_edges_le` (not in the roadmap item): for a unit-modulus array `ζ` and a
  natural `d ≥ 2` with `zakEnergy d ζ ≤ C₀ * Real.log d`, the large edges of B4 at `η = 1 / log d`
  satisfy `4 * #{large edges} ≤ π² C₀ (log d)³`: the middle inequality of (L5), `C₁ = π² C₀ / 4`.

Helpers: `half_le_log_two`, `half_le_log_of_two_le` (`log d ≥ 1/2` for `d ≥ 2`, so that
`η = 1 / log d ≤ 2 ≤ π`) and `four_mul_le_pi_sq_mul_log_cube` (the real arithmetic
`4 n ≤ π² C₀ t³` from `n · 4 sin²(1/(2t)) ≤ A ≤ C₀ t`, `t ≥ 1/2`, `n ≥ 0`). The paper asks for `d`
large enough that `η_d < π/4`; only `η_d ≤ π` is used here, and `d ≥ 2` gives it.

What this file does NOT prove: which edges are large and which plaquettes they meet (`L` and `inc`
are arbitrary, and "at most two plaquettes per edge" is a hypothesis); that the plaquettes outside
`L.biUnion inc` are neutral (B4 has this for a single plaquette); the ball construction of §4.3 and
its radius sum; the hypothesis `A ≤ C₀ log d`, which is an assumption of Theorem 4.1. It proves
nothing toward [HU], and neither [HL], Theorem 4.1 nor Theorem 1.1: F4 and H3 keep [HL] as a named
hypothesis.
-/

noncomputable section

open Finset

namespace BLT

/-- Jordan's inequality at `η / 2`, squared and without division:
`4 η² ≤ π² · 4 sin²(η/2)` for `0 ≤ η ≤ π`. -/
theorem four_mul_sq_le_pi_sq_mul {η : ℝ} (h0 : 0 ≤ η) (hπ : η ≤ Real.pi) :
    4 * η ^ 2 ≤ Real.pi ^ 2 * (4 * Real.sin (η / 2) ^ 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 2 / Real.pi * (η / 2) ≤ Real.sin (η / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have e1 : η / Real.pi = 2 / Real.pi * (η / 2) := by ring
  have h2 : η ≤ Real.sin (η / 2) * Real.pi := (div_le_iff₀ hpi).mp (e1.le.trans h1)
  have h3 : η * η ≤ Real.sin (η / 2) * Real.pi * (Real.sin (η / 2) * Real.pi) := by
    first
      | exact mul_self_le_mul_self h0 h2
      | nlinarith [h0, h2]
  first
    | linarith [h3]
    | nlinarith [h3]

/-- **G2, the edge weight from below.** For `0 ≤ η ≤ π`, `(4/π²) η² ≤ 4 sin²(η/2)`. -/
theorem four_div_pi_sq_mul_sq_le {η : ℝ} (h0 : 0 ≤ η) (hπ : η ≤ Real.pi) :
    4 / Real.pi ^ 2 * η ^ 2 ≤ 4 * Real.sin (η / 2) ^ 2 := by
  have hp : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  have hm := four_mul_sq_le_pi_sq_mul h0 hπ
  have e : 4 / Real.pi ^ 2 * η ^ 2 = 4 * η ^ 2 / Real.pi ^ 2 := by ring
  have h' : 4 * η ^ 2 / Real.pi ^ 2 ≤ 4 * Real.sin (η / 2) ^ 2 :=
    (div_le_iff₀ hp).mpr (by linarith [hm])
  exact e.le.trans h'

/-- **G2, bad plaquettes against large edges.** If every `inc e`, `e ∈ L`, has at most two
elements, then `#(⋃ e ∈ L, inc e) ≤ 2 #L`. -/
theorem card_biUnion_le_two_mul {α β : Type*} [DecidableEq β] (L : Finset α)
    (inc : α → Finset β) (hinc : ∀ e ∈ L, (inc e).card ≤ 2) :
    (L.biUnion inc).card ≤ 2 * L.card := by
  have h1 : (L.biUnion inc).card ≤ ∑ e ∈ L, (inc e).card := Finset.card_biUnion_le
  have h2 : ∑ e ∈ L, (inc e).card ≤ ∑ _e ∈ L, 2 := Finset.sum_le_sum hinc
  have h3 : ∑ _e ∈ L, 2 = L.card * 2 := by
    first
      | simp
      | rw [Finset.sum_const, smul_eq_mul]
  calc (L.biUnion inc).card ≤ ∑ e ∈ L, (inc e).card := h1
    _ ≤ ∑ _e ∈ L, 2 := h2
    _ = L.card * 2 := h3
    _ = 2 * L.card := mul_comm _ _

/-- `log 2 ≥ 1/2`. -/
theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have e : (1 : ℝ) - 2⁻¹ = 1 / 2 := by norm_num
  first
    | linarith [Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2), e]
    | linarith [Real.log_two_gt_d9]
    | linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), Real.log_inv (2 : ℝ), e]

/-- `log d ≥ 1/2` for real `d ≥ 2`. -/
theorem half_le_log_of_two_le {d : ℝ} (hd : 2 ≤ d) : 1 / 2 ≤ Real.log d := by
  have h2 := half_le_log_two
  have hmono : Real.log 2 ≤ Real.log d := by
    first
      | exact Real.log_le_log (by norm_num) hd
      | exact (Real.log_le_log_iff (by norm_num) (by linarith)).mpr hd
  linarith

/-- Real arithmetic of the count: if `n · 4 sin²(η/2) ≤ A ≤ C₀ t` with `η = 1/t`, `t ≥ 1/2` and
`n ≥ 0`, then `4 n ≤ π² C₀ t³`. -/
theorem four_mul_le_pi_sq_mul_log_cube {n A C₀ t : ℝ} (hn : 0 ≤ n) (ht : 1 / 2 ≤ t)
    (hL : n * (4 * Real.sin (1 / t / 2) ^ 2) ≤ A) (hA : A ≤ C₀ * t) :
    4 * n ≤ Real.pi ^ 2 * C₀ * t ^ 3 := by
  have htpos : 0 < t := by linarith
  have hne : t ≠ 0 := htpos.ne'
  have hη0 : 0 ≤ 1 / t := (one_div_pos.mpr htpos).le
  have hη2 : 1 / t ≤ 2 := (div_le_iff₀ htpos).mpr (by linarith)
  have hηπ : 1 / t ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hJ := four_mul_sq_le_pi_sq_mul hη0 hηπ
  have hx : 1 / t * t = 1 := by
    first
      | exact one_div_mul_cancel hne
      | exact div_mul_cancel₀ 1 hne
      | field_simp
  have s1 := mul_le_mul_of_nonneg_right hJ (mul_nonneg hn (sq_nonneg t))
  have s2 := mul_le_mul_of_nonneg_right (hL.trans hA)
    (mul_nonneg (sq_nonneg Real.pi) (sq_nonneg t))
  have e : 4 * (1 / t) ^ 2 * (n * t ^ 2) = 4 * n := by
    calc 4 * (1 / t) ^ 2 * (n * t ^ 2) = 4 * n * (1 / t * t) ^ 2 := by ring
      _ = 4 * n := by
        first
          | rw [hx, one_pow, mul_one]
          | simp [hx]
  first
    | linarith [s1, s2, e]
    | nlinarith [s1, s2, e]

/-- **G2, defect count: (L14) from the two counts of (L5).** For real `d ≥ 2`, `η = 1 / log d`: if
the set `L` (large edges) satisfies `#L · 4 sin²(η/2) ≤ A ≤ C₀ log d` and every `inc e`, `e ∈ L`
(plaquettes at `e`), has at most two elements, then `10 #(⋃ inc e) ≤ 5 π² C₀ (log d)³`. -/
theorem defect_count {α β : Type*} [DecidableEq β] (L : Finset α) (inc : α → Finset β)
    (hinc : ∀ e ∈ L, (inc e).card ≤ 2) {d A C₀ : ℝ} (hd : 2 ≤ d)
    (hL : (L.card : ℝ) * (4 * Real.sin (1 / Real.log d / 2) ^ 2) ≤ A)
    (hA : A ≤ C₀ * Real.log d) :
    10 * ((L.biUnion inc).card : ℝ) ≤ 5 * Real.pi ^ 2 * C₀ * Real.log d ^ 3 := by
  have h4 : 4 * (L.card : ℝ) ≤ Real.pi ^ 2 * C₀ * Real.log d ^ 3 :=
    four_mul_le_pi_sq_mul_log_cube (Nat.cast_nonneg _) (half_le_log_of_two_le hd) hL hA
  have hbi : ((L.biUnion inc).card : ℝ) ≤ 2 * (L.card : ℝ) := by
    exact_mod_cast card_biUnion_le_two_mul L inc hinc
  linarith [h4, hbi]

/-- **(L5), middle inequality, for the large edges of B4.** For a unit-modulus array and a natural
`d ≥ 2` with `zakEnergy d ζ ≤ C₀ log d`, at `η = 1 / log d`:
`4 #{large edges} ≤ π² C₀ (log d)³`. -/
theorem four_mul_card_large_edges_le (d : ℕ) (ζ : ℤ × ℤ → ℂ) (hζ : ∀ p, ‖ζ p‖ = 1)
    (hd : 2 ≤ d) {C₀ : ℝ} (hA : zakEnergy d ζ ≤ C₀ * Real.log d) :
    4 * (((largeEdgesR d ζ (1 / Real.log d)).card +
      (largeEdgesQ d ζ (1 / Real.log d)).card : ℕ) : ℝ) ≤
      Real.pi ^ 2 * C₀ * Real.log d ^ 3 := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ht : 1 / 2 ≤ Real.log (d : ℝ) := half_le_log_of_two_le hd'
  have htpos : 0 < Real.log (d : ℝ) := by linarith
  have hη0 : (0 : ℝ) ≤ 1 / Real.log (d : ℝ) := (one_div_pos.mpr htpos).le
  have hL := card_large_edges_mul_le_zakEnergy d ζ hζ hη0
  exact four_mul_le_pi_sq_mul_log_cube (Nat.cast_nonneg _) ht hL hA

end BLT

end
