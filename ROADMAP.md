# Roadmap: Lean companion to "Relative asymptotic optimality of finite Hermite Gabor windows"

Paper: J. Park, 25 Sep 2026, [`relative_asymptotic_optimality.pdf`](relative_asymptotic_optimality.pdf).
Theorem 1.1 says that the minimal rescaled critical Gabor energy satisfies
`2π log d − 7π log log d − C ≤ a_d ≤ 2π log d + C`, so the optimal discrete limit constant is
`lim a_d / log d = 2π`, and the finite-Hermite window `f_d` attains it to relative order
`O(log log d / log d)` along odd `d`.

The hourly formalize task takes the FIRST unchecked item (`- [ ]`), writes it in the file the item
names, and ticks it (`- [x]`) only after CI shows it compiled. `- [-]` marks an item that is skipped.
[docs/roadmap.html](docs/roadmap.html) is an interactive map of this file; CI redraws its snapshot after
every verification run, and the page also reads this file live from main when opened in a browser.
[verification/STATUS.md](verification/STATUS.md) lists every theorem with its axioms.

Layout: `BLTAudit.lean` (root, imports Mathlib only), `BLTAudit/Basic.lean` (shared definitions:
`transl`, `modul`, `dftU`, `diffOp`, `ip`, `energy`, `gStd`, `zak`, `gabor`, `IsTwisted`, `mag`, `aQ`,
`aR`, `zakEnergy`, `gauss`, `gaussZak`), then one file per item, `BLTAudit/<Name>.lean`. Every file
under `BLTAudit/` is built automatically. CI (`.github/workflows/lean.yml`) runs `lake build` with
Lean 4.35.0 + Mathlib v4.35.0, then `axiom_audit.py`.

Rules: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`, `extern` or
heartbeat options. Each file starts with a `/-! ... -/` docstring saying what it proves and what it does
NOT prove. An estimate of the paper that is not proved in Lean may enter only as an explicit, named
hypothesis. Nothing here may be described as a proof of Theorem 1.1 or Theorem 4.1 unless it has no
such hypothesis.

## A. Finite Gabor and Zak analysis

Exact finite statements of §1–§2. Mathlib has the discrete Fourier transform on `ZMod N` but no Gabor
systems and no Zak transform.

- [x] A1. Unitary DFT: `ip (dftU f) (dftU g) = ip f g` for all `f g : ZMod N → ℂ`, hence Parseval
  `∑ k, ‖dftU f k‖ ^ 2 = ∑ j, ‖f j‖ ^ 2`, by orthogonality of the characters `ZMod.stdAddChar`.
  File `BLTAudit/UnitaryDFT.lean`.
  - Done 2026-11-20 04:12 UTC at 4f24a6c: `ip_dftU`, `parseval_dftU`, `sum_stdAddChar_mul`, `conj_stdAddChar`, `dft_norm_sq`, `sum_conj_stdAddChar_mul`
- [x] A2. Time–frequency relations: `transl (modul f) j = ZMod.stdAddChar 1 * modul (transl f) j`
  (that is, `T M = e^{2πi/N} M T`) and `transl (dftU f) = dftU (modul f)` (that is, `F* T F = M`).
  File `BLTAudit/TimeFrequency.lean`.
  - Done 2026-11-20 15:11 UTC at 43d02d6: `transl_modul`, `transl_dftU`, `dftU_sub`, `diffOp_dftU`
- [-] A3. Finite Zak transform for `N = d²`: `∑ q, ∑ r, ‖zak f q r‖ ^ 2 = ∑ j, ‖f j‖ ^ 2`;
  `zak (transl f) q r = zak f q (r + 1)` when `r.val + 1 < d`, and
  `zak (transl f) q r = ZMod.stdAddChar (-q) * zak f q 0` when `r.val + 1 = d` (the seam);
  `zak (modul f) q r = Complex.exp (2πi r.val / d²) * zak f (q + 1) r`.
  File `BLTAudit/FiniteZak.lean`. (split into A3a, A3b, A3c)
  - Split 2026-11-20: three separate index computations in `ZMod (d * d)`, too large for one file of about 150 lines. Nothing was attempted and `BLTAudit/FiniteZak.lean` was not written.
- [x] A3a. The finite Zak transform is unitary: for `f : ZMod (d * d) → ℂ`,
  `∑ q, ∑ r, ‖zak f q r‖ ^ 2 = ∑ j, ‖f j‖ ^ 2`, by Parseval (A1) on `ZMod d` in the variable `b` for
  each fixed `r`, and the bijection `(b, r) ↦ b.val * d + r.val` from `ZMod d × ZMod d` onto
  `ZMod (d * d)`. File `BLTAudit/FiniteZakUnitary.lean`.
  - Done 2026-11-20 17:37 UTC at 3403199: `parseval_zak`, `zak_eq_dftU`, `zakIndex_bijective`, `zakIndex_injective`, `zakIndex_lt`
- [ ] A3b. Zak transform of a translate: for `f : ZMod (d * d) → ℂ` and `q r : ZMod d`,
  `zak (transl f) q r = zak f q (r + 1)` when `r.val + 1 < d`, and
  `zak (transl f) q r = ZMod.stdAddChar (-q) * zak f q 0` when `r.val + 1 = d` (the seam: reindex
  `b ↦ b + 1`; the term with `b.val + 1 = d` wraps around because `d * d = 0` in `ZMod (d * d)`).
  File `BLTAudit/FiniteZakTranslation.lean`.
- [ ] A3c. Zak transform of a modulate:
  `zak (modul f) q r = Complex.exp (2πi r.val / d²) * zak f (q + 1) r`, where the factor is
  `mag d r.val` (the character of `ZMod (d * d)` at `b.val * d + r.val` is
  `e^{2πi b.val / d} · e^{2πi r.val / d²}`). File `BLTAudit/FiniteZakModulation.lean`.
- [ ] A4. Critical Gabor criterion, sufficiency (§2): if `‖zak f q r‖ = 1 / d` for all `q r`, then the
  `d²` vectors `gabor f n m` (`n m < d`) are orthonormal for `ip`, hence a basis of `ℂ^{d²}`.
  File `BLTAudit/ZakCriterion.lean`.
- [ ] A5. Critical Gabor criterion, necessity: orthonormality of `{gabor f n m : n m < d}` forces
  `‖zak f q r‖ = 1 / d` for all `q r`, so admissible vectors correspond exactly to unit-modulus arrays
  `ζ = d • zak f`. File `BLTAudit/ZakCriterionConverse.lean`.
- [ ] A6. Standard form of `G_N` (§1): `energy f = (ip f (gStd f)).re` and `(ip f (gStd f)).im = 0`,
  that is, `D*D + F*D*DF` acts as `(4 − 2cos(2πj/N)) f(j) − f(j−1) − f(j+1)` (uses A1, A2).
  File `BLTAudit/GStandardForm.lean`.
- [ ] A7. Zak energy identity (§2): for `f : ZMod (d * d) → ℂ` and any `ζ : ℤ × ℤ → ℂ` with
  `ζ (q, r) = d * zak f q r` on `0 ≤ q, r < d` and the gluing `shift_q`, `shift_r` of `IsTwisted`,
  `d ^ 2 * energy f = zakEnergy d ζ` (uses A1–A3). Unit modulus is not needed. A numerical check of
  this identity for `d ≤ 7` passed on 2026-11-19; if a convention still fails in Lean, prove the
  corrected identity and record the difference in the docstring and in a note under this item.
  File `BLTAudit/ZakEnergyIdentity.lean`.

## B. Discrete phase topology

§4.1: the twisted boundary condition forces total integer charge one. Nothing like this is in Mathlib.

- [ ] B1. Edge energy (L1): for `‖u‖ = ‖v‖ = 1`, `‖v − u‖ ^ 2 = 4 * sin (arg (v * conj u) / 2) ^ 2`;
  hence for unit-modulus `ζ`,
  `zakEnergy d ζ = ∑ q r < d, (4 sin²(aR ζ q r / 2) + 4 sin²(aQ d ζ q r / 2))`.
  File `BLTAudit/EdgeEnergy.lean`.
- [ ] B2. Plaquette identity (L3): for `IsTwisted d ζ` with `0 < d`, the edge numbers `aQ d ζ` and
  `aR ζ` are `d`-periodic in `q` and in `r`, and
  `aQ d ζ q r + aR ζ (q+1) r − aQ d ζ q (r+1) − aR ζ q r = −2π/d² + 2π n` for some `n : ℤ`.
  File `BLTAudit/PlaquetteCharge.lean`.
- [ ] B3. Total charge one (L4): for `IsTwisted d ζ` with `0 < d`, the plaquette integers of B2 over
  `0 ≤ q, r < d` sum to `1` (the oriented edge sums telescope by the periodicity of B2).
  File `BLTAudit/TotalCharge.lean`.
- [ ] B4. Good plaquettes are neutral and large edges are few (§4.1, (L5)): if the four edge numbers of
  a plaquette have modulus `< η` and `4η + 2π/d² < 2π`, its integer is `0`; and for `0 < η ≤ π`,
  `#{edges with |a| ≥ η} * (4 sin²(η/2)) ≤ zakEnergy d ζ`. File `BLTAudit/GoodPlaquette.lean`.

## C. The Zak transform of the Gaussian

§3.1 and Appendix A.3. Mathlib has `jacobiTheta₂`; it has no Zak transform.

- [ ] C1. Theta representation: `r ↦ gauss (x − r) * exp (2πi r y)` is summable over `ℤ`, and
  `gaussZak x y = 2^{1/4} e^{−πx²} * jacobiTheta₂ (y − x * I) I` (Mathlib's convention is
  `jacobiTheta₂ z τ = ∑ exp (2πi n z + πi n² τ)`). File `BLTAudit/ZakTheta.lean`.
- [ ] C2. Quasi-periodicity (U1): `gaussZak (x + 1) y = exp (2πi y) * gaussZak x y` and
  `gaussZak x (y + 1) = gaussZak x y`. File `BLTAudit/ZakGluing.lean`.
- [ ] C3. The Zak zero (A10, first part): `gaussZak (1/2) (1/2) = 0`, by pairing `r ↔ 1 − r` in the sum.
  File `BLTAudit/ZakZero.lean`.
- [ ] C4. Conformality at the zero (A10): `exp (πx²) * gaussZak x y` is a holomorphic function of
  `y − x * I` (from C1), hence `∂_y gaussZak = I * ∂_x gaussZak` at `(1/2, 1/2)`.
  File `BLTAudit/ZakConformal.lean`.
- [ ] C5. Nonvanishing derivative (A10): with `A₀ = ∂ₓ gaussZak` at `(1/2, 1/2)`,
  `A₀ = −4π ∑_{k ≥ 0} (−1)^k (k + 1/2) gauss (k + 1/2)`, and this alternating series has strictly
  decreasing terms, so `A₀ ≠ 0`. File `BLTAudit/ZakDerivNonzero.lean`.

## D. The finite oscillator and its ground state

§1 and Appendix A.1: `G_N` has a simple, strictly positive ground vector.

- [ ] D1. Gaussian eigenfunctions of `H₀ = −∂² + 4π²x²` (Appendix A.1): `φ(x) = exp (−πx²)` satisfies
  `−φ'' + 4π²x²φ = 2πφ`, and `ψ = xφ` satisfies `−ψ'' + 4π²x²ψ = 6πψ`, as `HasDerivAt` statements.
  File `BLTAudit/OscillatorGaussian.lean`.
- [ ] D2. Perron–Frobenius step: for a real symmetric matrix `A` with nonpositive off-diagonal entries
  and `v : ι → ℂ`, `∑ i j, A i j * ‖v i‖ * ‖v j‖ ≤ (∑ i j, A i j * conj (v i) * v j).re`; so replacing
  a vector by its entrywise modulus does not raise the quadratic form. File `BLTAudit/PerronStep.lean`.
- [ ] D3. Positivity on the cycle: if `v : ZMod N → ℝ` is nonzero, entrywise nonnegative and
  `gStd` (applied to `v` as a complex vector) equals `λ • v` for a real `λ`, then `0 < v j` for every
  `j` (a zero entry forces its two neighbours to vanish, all the way around `ZMod N`).
  File `BLTAudit/GStdPositive.lean`.
- [ ] D4. Simple positive ground state (§1): among real vectors, the minimizers of `energy` on the unit
  sphere form a line spanned by an entrywise strictly positive vector (a minimizer's modulus is a
  minimizer by D2 and A6, hence strictly positive by D3; two orthogonal vectors cannot both have
  constant sign). File `BLTAudit/GroundState.lean`.

## E. Tools for the vortex lower bound

§4.2–§4.3. One-variable and model versions of the steps of Theorem 4.1; the degree lemma on the twisted
torus and the ball growth as a whole are listed under "Not attempted here".

- [ ] E1. Circle energy: if `θ` is `C¹` on `[0, 2π]` and `θ (2π) − θ 0 = 2π Q`, then
  `2π Q² ≤ ∫ φ in 0..2π, (deriv θ φ) ^ 2` (expand `∫ (θ' − Q)² ≥ 0`). File `BLTAudit/CircleEnergy.lean`.
- [ ] E2. Annulus logarithm (L13): for `0 < r < s` and `g` interval-integrable on `[r, s]` with
  `2π Q² ≤ g ρ` there, `2π Q² * log (s / r) ≤ ∫ ρ in r..s, g ρ / ρ`. File `BLTAudit/AnnulusEnergy.lean`.
- [ ] E3. Bilinear interpolation (L8)–(L10) with zero gauge error: for corner values
  `θ₀₀ θ₁₀ θ₀₁ θ₁₁` and the bilinear interpolant `θ` on `[0,1]²`,
  `(∂ₓθ)² + (∂ᵧθ)² ≤ W x y := (1−y) b_bot² + y b_top² + (1−x) b_left² + x b_right²`, and
  `∫∫ W = (b_bot² + b_top² + b_left² + b_right²) / 2`. File `BLTAudit/BilinearInterp.lean`.
- [ ] E4. Ball merging (§4.3): in a real normed space, if `‖c₁ − c₂‖ ≤ r₁ + r₂` with `0 < r₁`, `0 < r₂`,
  then `c = c₁ + (r₂ / (r₁ + r₂)) • (c₂ − c₁)` has `‖c − c₁‖ ≤ r₂`, `‖c − c₂‖ ≤ r₁`,
  `ball c₁ r₁ ∪ ball c₂ r₂ ⊆ ball c (r₁ + r₂)`, and `r₁ − ‖x − c₁‖ ≤ (r₁ + r₂) − ‖x − c‖` for all `x`.
  File `BLTAudit/BallMerge.lean`.
- [ ] E5. Final arithmetic of Theorem 4.1, (L17)–(L19), from named real hypotheses only: for real
  `d ≥ 3` and `0 ≤ C`, if `2π log T ≤ (1 + C / log d) * A + K`, `T = d / √(log d) / S₀`,
  `0 < S₀ ≤ C₂ (log d)³` and `A ≤ C₀ log d`, then
  `2π log d − 7π log (log d) − (2π log C₂ + C * C₀ + K) ≤ A`. File `BLTAudit/LowerBoundArithmetic.lean`.

## F. Assembly: Theorem 1.1 from named hypotheses

§5. The statement layer and the last step of the proof, in the style of a hypothesis ledger: the two
analytic halves enter as named hypotheses, and Lean checks what follows from them.

- [ ] F1. Statement layer: `Admissible f` (the vectors `gabor f n m`, `n m < d`, are orthonormal for
  `ip`), `scaledEnergy f = d ^ 2 * energy f` and `aMin d = ⨅ f : {f // Admissible f}, scaledEnergy f`,
  with `0 ≤ aMin d` and `aMin d ≤ scaledEnergy f` for admissible `f`. Definitions and these two facts
  only. File `BLTAudit/Statements.lean`.
- [ ] F2. Relative optimality from two named bounds (§5): for real sequences `A a : ℕ → ℝ` with
  `a d ≤ A d`, `[HU] A d ≤ 2π log d + C₁` and `[HL] 2π log d − 7π log (log d) − C₂ ≤ a d` for all large
  `d`, conclude `0 ≤ A d − a d ≤ 7π log (log d) + C₁ + C₂` eventually and
  `Tendsto (fun d => A d / a d) atTop (𝓝 1)`. File `BLTAudit/RelativeOptimality.lean`.
- [ ] F3. The limit constant from the same two bounds: if eventually
  `2π log d − 7π log (log d) − C ≤ a d ≤ 2π log d + C`, then
  `Tendsto (fun d => a d / log d) atTop (𝓝 (2π))`. File `BLTAudit/LimitConstant.lean`.
- [ ] F4. Conditional main theorem: combine F1–F3 into one statement about `aMin` and a candidate family
  `f_d`, whose only hypotheses are `[HU]` (the trial bound (U4) with (U14)) and `[HL]` (the lower bound
  (L19)), each a named structure field tagged `/-- [HU] ... -/`, `/-- [HL] ... -/`.
  File `BLTAudit/MainConditional.lean`.

## Not attempted here

- Uniqueness and simplicity of the Gaussian Zak zero in the unit square (Jacobi triple product, Appendix A.3), unless Mathlib already has the triple product.
- Spectral convergence `λ₀,d → 2π`, `λ₁,d → 6π` (A4), the fourth-order approximate ground vector (A5)–(A7), and the uniform Zak approximation (A9).
- The trial-energy asymptotic (U4) and its transfer to the finite-Hermite phase (U12)–(U14): hypothesis `[HU]`.
- The cellular degree lemma on the twisted torus (L12) and the ball-growth argument (L14)–(L16) as a whole, hence Theorem 4.1: hypothesis `[HL]`.
- Theorem 1.1 without hypotheses.
