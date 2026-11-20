import BLTAudit.UnitaryDFT

/-!
# A5b. Two-variable Fourier uniqueness on `ZMod d`

Finite Fourier analysis on `ZMod d` with the characters `ZMod.stdAddChar` (`e^{2πi a x / d}`),
used for the necessity half of the critical Gabor criterion (paper §2):

* `sum_stdAddChar_inversion`: for `g : ZMod d → ℂ`,
  `∑_a e^{-2πi a x₀ / d} ∑_x e^{2πi a x / d} g x = d · g x₀` (from `sum_stdAddChar_mul` of A1);
* `sum_sum_stdAddChar_inversion`: for `W : ZMod d → ZMod d → ℂ`,
  `∑_a e^{-2πi a q₀ / d} ∑_c e^{-2πi c r₀ / d} ∑_r ∑_q e^{2πi c r / d} e^{2πi a q / d} W q r
  = d · (d · W q₀ r₀)` (the one-variable inversion in each variable);
* `sum_sum_ite_zero`: `∑_a u a ∑_c v c · [a = 0 ∧ c = 0] = u 0 · v 0`;
* `fourier_uniqueness_two`: if
  `∑_r ∑_q e^{2πi c r / d} e^{2πi a q / d} W q r = if a = 0 ∧ c = 0 then 1 else 0` for all
  `a c : ZMod d`, then `W q r = 1 / d²` for all `q r`.

What this file does NOT prove: anything about `zak`, `gabor` or `ip`. It does not apply the
uniqueness statement to `W q r = ‖zak f q r‖²`, so it does not prove that orthonormality of the
Gabor vectors forces `‖zak f q r‖ = 1 / d` (A5c, the statement of A5). It proves nothing toward
Theorem 1.1 or Theorem 4.1 of the paper, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

variable {d : ℕ} [NeZero d]

/-- One-variable Fourier inversion on `ZMod d`. -/
theorem sum_stdAddChar_inversion (g : ZMod d → ℂ) (x₀ : ZMod d) :
    ∑ a : ZMod d, ZMod.stdAddChar (-(a * x₀)) * ∑ x : ZMod d, ZMod.stdAddChar (a * x) * g x =
      (d : ℂ) * g x₀ := by
  have h1 : ∀ a x : ZMod d, ZMod.stdAddChar (-(a * x₀)) * (ZMod.stdAddChar (a * x) * g x) =
      ZMod.stdAddChar ((x - x₀) * a) * g x := by
    intro a x
    have e : -(a * x₀) + a * x = (x - x₀) * a := by ring
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, e]
  have h3 : ∀ a : ZMod d,
      ZMod.stdAddChar (-(a * x₀)) * ∑ x : ZMod d, ZMod.stdAddChar (a * x) * g x =
        ∑ x : ZMod d, ZMod.stdAddChar ((x - x₀) * a) * g x := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => h1 a x
  calc ∑ a : ZMod d, ZMod.stdAddChar (-(a * x₀)) * ∑ x : ZMod d, ZMod.stdAddChar (a * x) * g x
      = ∑ a : ZMod d, ∑ x : ZMod d, ZMod.stdAddChar ((x - x₀) * a) * g x :=
        Finset.sum_congr rfl fun a _ => h3 a
    _ = ∑ x : ZMod d, ∑ a : ZMod d, ZMod.stdAddChar ((x - x₀) * a) * g x := Finset.sum_comm
    _ = (d : ℂ) * g x₀ := by
        rw [Finset.sum_eq_single x₀]
        · rw [← Finset.sum_mul, sum_stdAddChar_mul, if_pos (sub_self x₀)]
        · intro x _ hx
          rw [← Finset.sum_mul, sum_stdAddChar_mul,
            if_neg (fun h : x - x₀ = 0 => hx (sub_eq_zero.mp h)), zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h

/-- Two-variable Fourier inversion on `ZMod d`. -/
theorem sum_sum_stdAddChar_inversion (W : ZMod d → ZMod d → ℂ) (q₀ r₀ : ZMod d) :
    ∑ a : ZMod d, ZMod.stdAddChar (-(a * q₀)) *
        ∑ c : ZMod d, ZMod.stdAddChar (-(c * r₀)) *
          ∑ r : ZMod d, ∑ q : ZMod d,
            ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) * W q r =
      (d : ℂ) * ((d : ℂ) * W q₀ r₀) := by
  have hin : ∀ a c : ZMod d,
      ∑ r : ZMod d, ∑ q : ZMod d, ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) * W q r =
        ∑ r : ZMod d, ZMod.stdAddChar (c * r) *
          ∑ q : ZMod d, ZMod.stdAddChar (a * q) * W q r := by
    intro a c
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => mul_assoc _ _ _
  have hc : ∀ a : ZMod d,
      ∑ c : ZMod d, ZMod.stdAddChar (-(c * r₀)) *
          ∑ r : ZMod d, ∑ q : ZMod d,
            ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) * W q r =
        (d : ℂ) * ∑ q : ZMod d, ZMod.stdAddChar (a * q) * W q r₀ := by
    intro a
    calc ∑ c : ZMod d, ZMod.stdAddChar (-(c * r₀)) *
          ∑ r : ZMod d, ∑ q : ZMod d,
            ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) * W q r
        = ∑ c : ZMod d, ZMod.stdAddChar (-(c * r₀)) *
            ∑ r : ZMod d, ZMod.stdAddChar (c * r) *
              ∑ q : ZMod d, ZMod.stdAddChar (a * q) * W q r :=
          Finset.sum_congr rfl fun (c : ZMod d) _ =>
            congrArg (fun z : ℂ => ZMod.stdAddChar (-(c * r₀)) * z) (hin a c)
      _ = (d : ℂ) * ∑ q : ZMod d, ZMod.stdAddChar (a * q) * W q r₀ :=
          sum_stdAddChar_inversion
            (fun r : ZMod d => ∑ q : ZMod d, ZMod.stdAddChar (a * q) * W q r) r₀
  calc ∑ a : ZMod d, ZMod.stdAddChar (-(a * q₀)) *
        ∑ c : ZMod d, ZMod.stdAddChar (-(c * r₀)) *
          ∑ r : ZMod d, ∑ q : ZMod d,
            ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) * W q r
      = ∑ a : ZMod d, ZMod.stdAddChar (-(a * q₀)) *
          ((d : ℂ) * ∑ q : ZMod d, ZMod.stdAddChar (a * q) * W q r₀) :=
        Finset.sum_congr rfl fun (a : ZMod d) _ =>
          congrArg (fun z : ℂ => ZMod.stdAddChar (-(a * q₀)) * z) (hc a)
    _ = (d : ℂ) * ∑ a : ZMod d, ZMod.stdAddChar (-(a * q₀)) *
          ∑ q : ZMod d, ZMod.stdAddChar (a * q) * W q r₀ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _
    _ = (d : ℂ) * ((d : ℂ) * W q₀ r₀) :=
        congrArg (fun z : ℂ => (d : ℂ) * z)
          (sum_stdAddChar_inversion (fun q : ZMod d => W q r₀) q₀)

/-- A double sum against the indicator of `(0, 0)` picks out the term at `(0, 0)`. -/
theorem sum_sum_ite_zero (u v : ZMod d → ℂ) :
    ∑ a : ZMod d, u a * ∑ c : ZMod d, v c * (if a = 0 ∧ c = 0 then (1 : ℂ) else 0) =
      u 0 * v 0 := by
  rw [Finset.sum_eq_single (0 : ZMod d)]
  · rw [Finset.sum_eq_single (0 : ZMod d)]
    · rw [if_pos (And.intro (rfl : (0 : ZMod d) = 0) (rfl : (0 : ZMod d) = 0)), mul_one]
    · intro c _ hc
      rw [if_neg (fun h : (0 : ZMod d) = 0 ∧ c = 0 => hc h.2), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    have hz : ∑ c : ZMod d, v c * (if a = 0 ∧ c = 0 then (1 : ℂ) else 0) = 0 :=
      Finset.sum_eq_zero fun c _ => by
        rw [if_neg (fun h : a = 0 ∧ c = 0 => ha h.1), mul_zero]
    rw [hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **A5b.** Two-variable Fourier uniqueness on `ZMod d`: an array whose two-variable discrete
Fourier transform is the indicator of `(0, 0)` is the constant `1 / d²`. -/
theorem fourier_uniqueness_two (W : ZMod d → ZMod d → ℂ)
    (h : ∀ a c : ZMod d,
      ∑ r : ZMod d, ∑ q : ZMod d, ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) * W q r =
        if a = 0 ∧ c = 0 then (1 : ℂ) else 0)
    (q₀ r₀ : ZMod d) : W q₀ r₀ = 1 / (d : ℂ) ^ 2 := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h1 : ∑ a : ZMod d, ZMod.stdAddChar (-(a * q₀)) *
        ∑ c : ZMod d, ZMod.stdAddChar (-(c * r₀)) *
          ∑ r : ZMod d, ∑ q : ZMod d,
            ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) * W q r =
      ∑ a : ZMod d, ZMod.stdAddChar (-(a * q₀)) *
        ∑ c : ZMod d, ZMod.stdAddChar (-(c * r₀)) * (if a = 0 ∧ c = 0 then (1 : ℂ) else 0) :=
    Finset.sum_congr rfl fun (a : ZMod d) _ =>
      congrArg (fun z : ℂ => ZMod.stdAddChar (-(a * q₀)) * z)
        (Finset.sum_congr rfl fun (c : ZMod d) _ =>
          congrArg (fun z : ℂ => ZMod.stdAddChar (-(c * r₀)) * z) (h a c))
  have h2 : ∑ a : ZMod d, ZMod.stdAddChar (-(a * q₀)) *
        ∑ c : ZMod d, ZMod.stdAddChar (-(c * r₀)) * (if a = 0 ∧ c = 0 then (1 : ℂ) else 0) =
      ZMod.stdAddChar (-((0 : ZMod d) * q₀)) * ZMod.stdAddChar (-((0 : ZMod d) * r₀)) :=
    sum_sum_ite_zero (fun a : ZMod d => ZMod.stdAddChar (-(a * q₀)))
      (fun c : ZMod d => ZMod.stdAddChar (-(c * r₀)))
  have h3 : ZMod.stdAddChar (-((0 : ZMod d) * q₀)) * ZMod.stdAddChar (-((0 : ZMod d) * r₀)) =
      (1 : ℂ) := by
    first
      | rw [zero_mul, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
      | simp [AddChar.map_zero_eq_one]
  have key : (d : ℂ) * ((d : ℂ) * W q₀ r₀) = 1 :=
    ((sum_sum_stdAddChar_inversion W q₀ r₀).symm.trans h1).trans (h2.trans h3)
  rw [eq_div_iff (pow_ne_zero 2 hd)]
  linear_combination key

end BLT

end
