import Mathlib

/-!
# Shared definitions for the finite Balian–Low project

Definitions (with definitional unfolding lemmas and two nonnegativity facts) following §1–§4 of
J. Park, "Relative asymptotic optimality of finite Hermite Gabor windows" (25 Sep 2026).
Other files in `BLTAudit/` should `import BLTAudit.Basic` and reuse these definitions instead of
redefining them.

Conventions: vectors in `ℂ^N` are functions `ZMod N → ℂ`; `ZMod.stdAddChar j` is
`exp (2πi j.val / N)`, so `dftU` is the unitary DFT with the paper's sign.

What this file does NOT prove: unitarity of `dftU` or `zak`, the critical Gabor criterion
`|Z_N f| = 1/d`, any property of `gaussZak` (not even summability), the standard form of `G_N`,
or any energy estimate. In particular it proves nothing toward Theorem 1.1, Theorem 4.1,
(U4), (U14) or (L19) of the paper.
-/

noncomputable section

open Finset
open scoped ComplexConjugate

namespace BLT

/-! ### Operators that need no finiteness -/

section Shifts

variable {N : ℕ}

/-- Translation `(T_N f)(j) = f (j + 1)`. -/
def transl (f : ZMod N → ℂ) : ZMod N → ℂ := fun j => f (j + 1)

/-- Forward difference `D_N = I - T_N`, i.e. `(D_N f)(j) = f j - f (j + 1)`. -/
def diffOp (f : ZMod N → ℂ) : ZMod N → ℂ := fun j => f j - f (j + 1)

@[simp] theorem transl_apply (f : ZMod N → ℂ) (j : ZMod N) : transl f j = f (j + 1) := rfl

@[simp] theorem diffOp_apply (f : ZMod N → ℂ) (j : ZMod N) : diffOp f j = f j - f (j + 1) := rfl

end Shifts

/-! ### Finite time–frequency operators on `ℂ^N` -/

section Finite

variable {N : ℕ} [NeZero N]

/-- Modulation `(M_N f)(j) = e^{2πij/N} f(j)`. -/
def modul (f : ZMod N → ℂ) : ZMod N → ℂ := fun j => ZMod.stdAddChar j * f j

/-- The unitary DFT `(F_N f)(k) = N^{-1/2} ∑_j e^{2πijk/N} f(j)`. -/
def dftU (f : ZMod N → ℂ) : ZMod N → ℂ :=
  fun k => ((Real.sqrt (N : ℝ) : ℝ) : ℂ)⁻¹ * ∑ j : ZMod N, ZMod.stdAddChar (j * k) * f j

/-- The Euclidean inner product `⟨f, g⟩ = ∑_j conj (f j) * g j`. -/
def ip (f g : ZMod N → ℂ) : ℂ := ∑ j : ZMod N, conj (f j) * g j

/-- The critical difference energy `E_N(f) = ⟨f, G_N f⟩ = ‖D_N f‖² + ‖D_N F_N f‖²`. -/
def energy (f : ZMod N → ℂ) : ℝ :=
  ∑ j : ZMod N, ‖diffOp f j‖ ^ 2 + ∑ k : ZMod N, ‖diffOp (dftU f) k‖ ^ 2

/-- `G_N` in standard coordinates (paper §1):
`(G_N f)(j) = (4 - 2 cos(2πj/N)) f(j) - f(j-1) - f(j+1)`. -/
def gStd (f : ZMod N → ℂ) : ZMod N → ℂ := fun j =>
  ((4 - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / (N : ℝ)) : ℝ) : ℂ) * f j - f (j - 1) - f (j + 1)

@[simp] theorem modul_apply (f : ZMod N → ℂ) (j : ZMod N) :
    modul f j = ZMod.stdAddChar j * f j := rfl

theorem energy_nonneg (f : ZMod N → ℂ) : 0 ≤ energy f := by
  unfold energy
  exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end Finite

/-! ### The finite Zak transform and the Gabor system, `N = d²` (paper §1–§2) -/

section Zak

variable {d : ℕ} [NeZero d]

/-- `(Z_N f)(q, r) = d^{-1/2} ∑_{b<d} e^{2πiqb/d} f(b d + r)`, in coordinates `j = b d + r`
with `0 ≤ r < d`. -/
def zak (f : ZMod (d * d) → ℂ) (q r : ZMod d) : ℂ :=
  ((Real.sqrt (d : ℝ) : ℝ) : ℂ)⁻¹ *
    ∑ b : ZMod d, ZMod.stdAddChar (q * b) * f ((b.val * d + r.val : ℕ) : ZMod (d * d))

end Zak

/-- The Gabor system element `T_N^{n d} M_N^{m d} f` for `N = d²`. -/
def gabor {d : ℕ} [NeZero (d * d)] (f : ZMod (d * d) → ℂ) (n m : ℕ) : ZMod (d * d) → ℂ :=
  (transl (N := d * d))^[n * d] ((modul (N := d * d))^[m * d] f)

/-! ### Twisted unit arrays and the Zak energy (paper §2, §4) -/

/-- Unit-modulus arrays on `ℤ²` with the twisted gluing of §2:
`ζ(q + d, r) = ζ(q, r)` and `ζ(q, r + d) = e^{-2πiq/d} ζ(q, r)`. -/
structure IsTwisted (d : ℕ) (ζ : ℤ × ℤ → ℂ) : Prop where
  norm_eq_one : ∀ p, ‖ζ p‖ = 1
  shift_q : ∀ q r : ℤ, ζ (q + (d : ℤ), r) = ζ (q, r)
  shift_r : ∀ q r : ℤ,
    ζ (q, r + (d : ℤ)) = Complex.exp (-2 * Real.pi * Complex.I * (q : ℂ) / (d : ℂ)) * ζ (q, r)

/-- The magnetic multiplier `e^{2πir/d²}` carried by `q`-edges. -/
def mag (d : ℕ) (r : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) / ((d : ℂ) ^ 2))

/-- Covariant `q`-edge number `a^q_{q,r} = Arg(e^{2πir/d²} ζ(q+1,r) conj ζ(q,r))` in `(-π, π]`. -/
def aQ (d : ℕ) (ζ : ℤ × ℤ → ℂ) (q r : ℤ) : ℝ :=
  Complex.arg (mag d r * ζ (q + 1, r) * conj (ζ (q, r)))

/-- Covariant `r`-edge number `a^r_{q,r} = Arg(ζ(q,r+1) conj ζ(q,r))` in `(-π, π]`. -/
def aR (ζ : ℤ × ℤ → ℂ) (q r : ℤ) : ℝ :=
  Complex.arg (ζ (q, r + 1) * conj (ζ (q, r)))

/-- The Zak energy `A_d(ζ)` of §2: every positive edge of the `d × d` square once, both seams
included through the gluing, no factor `1/2`. -/
def zakEnergy (d : ℕ) (ζ : ℤ × ℤ → ℂ) : ℝ :=
  ∑ q ∈ range d, ∑ r ∈ range d,
    (‖ζ ((q : ℤ), (r : ℤ) + 1) - ζ ((q : ℤ), (r : ℤ))‖ ^ 2 +
      ‖mag d (r : ℤ) * ζ ((q : ℤ) + 1, (r : ℤ)) - ζ ((q : ℤ), (r : ℤ))‖ ^ 2)

theorem zakEnergy_nonneg (d : ℕ) (ζ : ℤ × ℤ → ℂ) : 0 ≤ zakEnergy d ζ := by
  unfold zakEnergy
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ### The Gaussian and its Zak transform (paper §3.1) -/

/-- `φ(x) = 2^{1/4} e^{-πx²}`. -/
def gauss (x : ℝ) : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-Real.pi * x ^ 2)

/-- `F(x, y) = ∑_{r ∈ ℤ} φ(x - r) e^{2πiry}` as a `tsum` (summability is roadmap item C1). -/
def gaussZak (x y : ℝ) : ℂ :=
  ∑' r : ℤ, ((gauss (x - (r : ℝ)) : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (y : ℂ))

end BLT

end
