import BLTAudit.Basic

/-!
# D1. Gaussian eigenfunctions of `H₀ = -∂² + 4π²x²` (Appendix A.1)

Appendix A.1 of the paper compares the finite operator with the oscillator
`H₀ = -∂ₓ² + 4π²x²` on the line. This file proves the two statements of roadmap item D1,
pointwise in `x : ℝ` and as `HasDerivAt` statements, for `φ(x) = e^{-πx²}` (`oscPhi`) and
`ψ(x) = x φ(x)` (`oscPsi`):

* `oscPhi_eigenfunction`: `φ' = oscPhiD`, `φ'' = oscPhiDD` and `-φ'' + 4π²x²φ = 2πφ`, where
  `oscPhiD x = -(2πx) φ(x)` and `oscPhiDD x = (4π²x² - 2π) φ(x)`.
* `oscPsi_eigenfunction`: `ψ' = oscPsiD`, `ψ'' = oscPsiDD` and `-ψ'' + 4π²x²ψ = 6πψ`, where
  `oscPsiD x = (1 - 2πx²) φ(x)` and `oscPsiDD x = (4π²x³ - 6πx) φ(x)`.

The four derivatives are `hasDerivAt_oscPhi`, `hasDerivAt_oscPhiD`, `hasDerivAt_oscPsi` and
`hasDerivAt_oscPsiD`; the two algebraic identities are `oscPhi_eigen` and `oscPsi_eigen`.

Conventions: the roadmap item takes `φ(x) = e^{-πx²}`; the paper's Gaussian is the normalised
`ϕ = 2^{1/4} e^{-πx²}`, which is `gauss` of `BLTAudit/Basic.lean` and equals `2^{1/4} * oscPhi`
(`gauss_eq_mul_oscPhi`). The equations are linear, so nothing changes:
`const_mul_oscPhi_eigenfunction` and `const_mul_oscPsi_eigenfunction` are the two statements for
`c φ` and `c ψ` with any real `c`; the paper's `ϕ` and `xϕ` are the case `c = 2^{1/4}`.

What this file does NOT prove: `H₀` is not defined as an operator on a function space, so
"eigenfunction" means only the pointwise differential equation, and the equations are not
restated with Mathlib's `deriv`; that `φ` and `ψ` are in `L²`, that `ϕ` has norm one, or that
`ϕ` and `xϕ` are orthogonal; that `2π` and `6π` are the two lowest eigenvalues of `H₀`; anything
about the finite operator `G_N` or the spectral convergence (A4). It proves nothing toward
Theorem 1.1 or Theorem 4.1, and nothing toward the hypotheses [HU] and [HL].
-/

noncomputable section

namespace BLT

/-- `φ(x) = e^{-πx²}`, the unnormalised Gaussian. -/
def oscPhi (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

/-- `φ'(x) = -(2πx) φ(x)`. -/
def oscPhiD (x : ℝ) : ℝ := -(2 * Real.pi * x) * oscPhi x

/-- `φ''(x) = (4π²x² - 2π) φ(x)`. -/
def oscPhiDD (x : ℝ) : ℝ := (4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * oscPhi x

/-- `ψ(x) = x φ(x)`. -/
def oscPsi (x : ℝ) : ℝ := x * oscPhi x

/-- `ψ'(x) = (1 - 2πx²) φ(x)`. -/
def oscPsiD (x : ℝ) : ℝ := (1 - 2 * Real.pi * x ^ 2) * oscPhi x

/-- `ψ''(x) = (4π²x³ - 6πx) φ(x)`. -/
def oscPsiDD (x : ℝ) : ℝ := (4 * Real.pi ^ 2 * x ^ 3 - 6 * Real.pi * x) * oscPhi x

/-- `φ' = -(2πx) φ`. -/
theorem hasDerivAt_oscPhi (x : ℝ) : HasDerivAt oscPhi (oscPhiD x) x := by
  have h00 : HasDerivAt (fun s : ℝ => -Real.pi * (s * s)) (-Real.pi * (1 * x + x * 1)) x :=
    ((hasDerivAt_id' x).mul (hasDerivAt_id' x)).const_mul (-Real.pi)
  have h0 : HasDerivAt (fun s : ℝ => -Real.pi * s ^ 2) (-Real.pi * (2 * x)) x := by
    have hf : (fun s : ℝ => -Real.pi * s ^ 2) = fun s : ℝ => -Real.pi * (s * s) :=
      funext fun s => by rw [pow_two]
    rw [hf]
    exact h00.congr_deriv (by ring)
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-Real.pi * s ^ 2))
      (Real.exp (-Real.pi * x ^ 2) * (-Real.pi * (2 * x))) x := h0.exp
  have hval : Real.exp (-Real.pi * x ^ 2) * (-Real.pi * (2 * x)) = oscPhiD x := by
    unfold oscPhiD oscPhi
    ring
  first
    | exact h1.congr_deriv hval
    | (have hf' : oscPhi = fun s : ℝ => Real.exp (-Real.pi * s ^ 2) := funext fun s => rfl
       rw [hf']
       exact h1.congr_deriv hval)

/-- `φ'' = (4π²x² - 2π) φ`. -/
theorem hasDerivAt_oscPhiD (x : ℝ) : HasDerivAt oscPhiD (oscPhiDD x) x := by
  have hl : HasDerivAt (fun s : ℝ => -(2 * Real.pi) * s) (-(2 * Real.pi) * 1) x :=
    (hasDerivAt_id' x).const_mul (-(2 * Real.pi))
  have h1 : HasDerivAt (fun s : ℝ => -(2 * Real.pi) * s * oscPhi s)
      (-(2 * Real.pi) * 1 * oscPhi x + -(2 * Real.pi) * x * oscPhiD x) x :=
    hl.mul (hasDerivAt_oscPhi x)
  have hf : oscPhiD = fun s : ℝ => -(2 * Real.pi) * s * oscPhi s :=
    funext fun s => by
      show oscPhiD s = -(2 * Real.pi) * s * oscPhi s
      unfold oscPhiD
      ring
  have hval : -(2 * Real.pi) * 1 * oscPhi x + -(2 * Real.pi) * x * oscPhiD x = oscPhiDD x := by
    unfold oscPhiDD oscPhiD
    ring
  first
    | (rw [hf]
       exact h1.congr_deriv hval)
    | exact hf ▸ h1.congr_deriv hval

/-- `ψ' = (1 - 2πx²) φ`. -/
theorem hasDerivAt_oscPsi (x : ℝ) : HasDerivAt oscPsi (oscPsiD x) x := by
  have h1 : HasDerivAt (fun s : ℝ => s * oscPhi s) (1 * oscPhi x + x * oscPhiD x) x :=
    (hasDerivAt_id' x).mul (hasDerivAt_oscPhi x)
  have hf : oscPsi = fun s : ℝ => s * oscPhi s := funext fun s => rfl
  have hval : 1 * oscPhi x + x * oscPhiD x = oscPsiD x := by
    unfold oscPsiD oscPhiD
    ring
  first
    | (rw [hf]
       exact h1.congr_deriv hval)
    | exact hf ▸ h1.congr_deriv hval

/-- `ψ'' = (4π²x³ - 6πx) φ`, from `ψ' = φ + x φ'`. -/
theorem hasDerivAt_oscPsiD (x : ℝ) : HasDerivAt oscPsiD (oscPsiDD x) x := by
  have h2 : HasDerivAt (fun s : ℝ => s * oscPhiD s) (1 * oscPhiD x + x * oscPhiDD x) x :=
    (hasDerivAt_id' x).mul (hasDerivAt_oscPhiD x)
  have h1 : HasDerivAt (fun s : ℝ => oscPhi s + s * oscPhiD s)
      (oscPhiD x + (1 * oscPhiD x + x * oscPhiDD x)) x := (hasDerivAt_oscPhi x).add h2
  have hf : oscPsiD = fun s : ℝ => oscPhi s + s * oscPhiD s :=
    funext fun s => by
      show oscPsiD s = oscPhi s + s * oscPhiD s
      unfold oscPsiD oscPhiD
      ring
  have hval : oscPhiD x + (1 * oscPhiD x + x * oscPhiDD x) = oscPsiDD x := by
    unfold oscPsiDD oscPhiDD oscPhiD
    ring
  first
    | (rw [hf]
       exact h1.congr_deriv hval)
    | exact hf ▸ h1.congr_deriv hval

/-- `-φ'' + 4π²x²φ = 2πφ`, with `φ''` written out. -/
theorem oscPhi_eigen (x : ℝ) :
    -oscPhiDD x + 4 * Real.pi ^ 2 * x ^ 2 * oscPhi x = 2 * Real.pi * oscPhi x := by
  unfold oscPhiDD
  ring

/-- `-ψ'' + 4π²x²ψ = 6πψ`, with `ψ''` written out. -/
theorem oscPsi_eigen (x : ℝ) :
    -oscPsiDD x + 4 * Real.pi ^ 2 * x ^ 2 * oscPsi x = 6 * Real.pi * oscPsi x := by
  unfold oscPsiDD oscPsi
  ring

/-- Roadmap item D1 for `φ = e^{-πx²}`: `-φ'' + 4π²x²φ = 2πφ`, as `HasDerivAt` statements. -/
theorem oscPhi_eigenfunction (x : ℝ) :
    HasDerivAt oscPhi (oscPhiD x) x ∧ HasDerivAt oscPhiD (oscPhiDD x) x ∧
      -oscPhiDD x + 4 * Real.pi ^ 2 * x ^ 2 * oscPhi x = 2 * Real.pi * oscPhi x :=
  ⟨hasDerivAt_oscPhi x, hasDerivAt_oscPhiD x, oscPhi_eigen x⟩

/-- Roadmap item D1 for `ψ = xφ`: `-ψ'' + 4π²x²ψ = 6πψ`, as `HasDerivAt` statements. -/
theorem oscPsi_eigenfunction (x : ℝ) :
    HasDerivAt oscPsi (oscPsiD x) x ∧ HasDerivAt oscPsiD (oscPsiDD x) x ∧
      -oscPsiDD x + 4 * Real.pi ^ 2 * x ^ 2 * oscPsi x = 6 * Real.pi * oscPsi x :=
  ⟨hasDerivAt_oscPsi x, hasDerivAt_oscPsiD x, oscPsi_eigen x⟩

/-- The paper's normalised Gaussian `ϕ = 2^{1/4} e^{-πx²}` (`gauss`) is `2^{1/4} φ`. -/
theorem gauss_eq_mul_oscPhi (x : ℝ) : gauss x = (2 : ℝ) ^ ((1 : ℝ) / 4) * oscPhi x := by
  first
    | rfl
    | (unfold gauss oscPhi
       rfl)

/-- The statement for `c φ`, any real `c`; the paper's `ϕ` is the case `c = 2^{1/4}`. -/
theorem const_mul_oscPhi_eigenfunction (c x : ℝ) :
    HasDerivAt (fun s : ℝ => c * oscPhi s) (c * oscPhiD x) x ∧
      HasDerivAt (fun s : ℝ => c * oscPhiD s) (c * oscPhiDD x) x ∧
      -(c * oscPhiDD x) + 4 * Real.pi ^ 2 * x ^ 2 * (c * oscPhi x) =
        2 * Real.pi * (c * oscPhi x) := by
  refine ⟨(hasDerivAt_oscPhi x).const_mul c, (hasDerivAt_oscPhiD x).const_mul c, ?_⟩
  unfold oscPhiDD
  ring

/-- The statement for `c ψ`, any real `c`; the paper's `xϕ` is the case `c = 2^{1/4}`. -/
theorem const_mul_oscPsi_eigenfunction (c x : ℝ) :
    HasDerivAt (fun s : ℝ => c * oscPsi s) (c * oscPsiD x) x ∧
      HasDerivAt (fun s : ℝ => c * oscPsiD s) (c * oscPsiDD x) x ∧
      -(c * oscPsiDD x) + 4 * Real.pi ^ 2 * x ^ 2 * (c * oscPsi x) =
        6 * Real.pi * (c * oscPsi x) := by
  refine ⟨(hasDerivAt_oscPsi x).const_mul c, (hasDerivAt_oscPsiD x).const_mul c, ?_⟩
  unfold oscPsiDD oscPsi
  ring

end BLT

end
