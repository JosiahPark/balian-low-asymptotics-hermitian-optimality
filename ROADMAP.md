# ROADMAP — Lean companion to "Relative asymptotic optimality of finite Hermite Gabor windows"

Paper: J. Park, 25 Sep 2026, `relative_asymptotic_optimality.pdf` in this repository. Its Theorem 1.1
says that the minimal rescaled critical Gabor energy satisfies
`2π log d − 7π log log d − C ≤ a_d ≤ 2π log d + C`, so the optimal discrete limit constant is
`lim a_d / log d = 2π`, and the finite-Hermite window `f_d` attains it to relative order
`O(log log d / log d)`.

Layout: `BLTAudit.lean` (root, imports Mathlib only), `BLTAudit/Foundations/Basic.lean` (shared
definitions: `transl`, `modul`, `dftU`, `diffOp`, `energy`, `gStd`, `ip`, `zak`, `gabor`, `IsTwisted`,
`mag`, `aQ`, `aR`, `zakEnergy`, `gauss`, `gaussZak`), one new file per item in `BLTAudit/Foundations/`.
Every file under `BLTAudit/` is built automatically. CI (`.github/workflows/lean.yml`) runs
`lake build` with Lean 4.35.0 + Mathlib v4.35.0, then `axiom_audit.py`, and writes
`verification/STATUS.md` / `STATUS.json`.

Rules: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`, `extern`,
or heartbeat options. Every file has a `/-! ... -/` docstring saying what it proves and what it does
NOT prove. Nothing in this repository proves Theorem 1.1 or Theorem 4.1.

## Foundations (long-term)

Machinery that Mathlib lacks and that Theorem 1.1 needs: (G1) finite Gabor and Zak analysis,
(G2) discrete phase topology (covariant edge angles, integer plaquette charges), (G3) the Zak
transform of the Gaussian and its zero, (G4) the finite oscillator `G_N` and its positive ground
state, (G5) vortex-energy lower-bound tools. Worked by an hourly scheduled foundations task, one item
per run. Each item is a new file `BLTAudit/Foundations/<Name>.lean` that imports
`BLTAudit.Foundations.Basic` (or Mathlib) and states exactly what it proves. Items are either exact
finite statements from the paper or one-dimensional / model versions of its analytic steps; none of
them proves Theorem 1.1, Theorem 4.1, (U4), (U14) or (L19).

- [ ] F1.1 Unitary DFT: `ip (dftU f) (dftU g) = ip f g` for all `f g : ZMod N → ℂ` (hence Parseval `∑ ‖dftU f k‖² = ∑ ‖f j‖²`), via character orthogonality — file BLTAudit/Foundations/UnitaryDFT.lean
- [ ] F1.2 Time–frequency relations: `transl (modul f) j = ZMod.stdAddChar 1 * modul (transl f) j` (i.e. `T_N M_N = e^{2πi/N} M_N T_N`) and `transl (dftU f) = dftU (modul f)` (i.e. `F_N* T_N F_N = M_N`) — file BLTAudit/Foundations/TimeFrequency.lean
- [ ] F1.3 Finite Zak transform for `N = d²`: `∑_{q,r} ‖zak f q r‖² = ∑_j ‖f j‖²`, `zak (transl^[d] f) q r = ZMod.stdAddChar (-q) * zak f q r` and `zak (modul^[d] f) q r = ZMod.stdAddChar r * zak f q r` — file BLTAudit/Foundations/FiniteZak.lean
- [ ] F1.4 Critical Gabor criterion (⇐), §2: if `‖zak f q r‖ = 1/d` for all `q r`, then the `d²` vectors `gabor f n m` (`n m < d`) are orthonormal for `ip`, hence an orthonormal basis of `ℂ^{d²}` — file BLTAudit/Foundations/ZakCriterion.lean
- [ ] F1.5 Critical Gabor criterion (⇒): orthonormality of `{gabor f n m : n m < d}` forces `‖zak f q r‖ = 1/d` for all `q r`, so admissible vectors correspond exactly to unit arrays `ζ = d · zak f` — file BLTAudit/Foundations/ZakCriterionConverse.lean
- [ ] F2.1 Edge energy identity (L1): for `‖u‖ = ‖v‖ = 1`, `‖v − u‖² = 4 sin²(arg(v · conj u)/2)`; hence `zakEnergy d ζ = ∑_{q,r<d} (4 sin²(aR ζ q r / 2) + 4 sin²(aQ d ζ q r / 2))` for unit-modulus `ζ` — file BLTAudit/Foundations/EdgeEnergy.lean
- [ ] F2.2 Plaquette identity (L3): for `IsTwisted d ζ` with `d ≥ 1`, `aQ d ζ` and `aR ζ` are `d`-periodic in `q` and in `r`, and `aQ d ζ q r + aR ζ (q+1) r − aQ d ζ q (r+1) − aR ζ q r = −2π/d² + 2π n` for some `n : ℤ` — file BLTAudit/Foundations/PlaquetteCharge.lean
- [ ] F2.3 Total charge one (L4): for `IsTwisted d ζ`, the plaquette integers of F2.2 over `0 ≤ q, r < d` sum to `1` (telescoping with the periodicity of F2.2) — file BLTAudit/Foundations/TotalCharge.lean
- [ ] F2.4 Good plaquettes are neutral, large edges are few (§4.1, (L5)): if the four edge numbers of a plaquette have modulus `< η` with `4η + 2π/d² < 2π`, its integer is `0`; and for `0 < η ≤ π`, `#{edges with |a| ≥ η} · 4 sin²(η/2) ≤ zakEnergy d ζ` — file BLTAudit/Foundations/GoodPlaquette.lean
- [ ] F3.1 Theta representation: `r ↦ gauss (x − r) · e^{2πiry}` is summable over `ℤ` and `gaussZak x y = 2^{1/4} e^{−πx²} · jacobiTheta₂ (y − x·I) I` (Mathlib convention `jacobiTheta₂ z τ = ∑ exp(2πinz + πin²τ)`) — file BLTAudit/Foundations/ZakTheta.lean
- [ ] F3.2 Quasi-periodicity (U1): `gaussZak (x + 1) y = e^{2πiy} gaussZak x y` and `gaussZak x (y + 1) = gaussZak x y` — file BLTAudit/Foundations/ZakGluing.lean
- [ ] F3.3 The Zak zero (A10, first part): `gaussZak (1/2) (1/2) = 0`, by pairing `r ↔ 1 − r` in the sum — file BLTAudit/Foundations/ZakZero.lean
- [ ] F3.4 Conformality at the zero (A10): `e^{πx²} gaussZak x y` is a holomorphic function of `y − x·I` (from F3.1), hence `∂_y gaussZak = I · ∂_x gaussZak` at `(1/2, 1/2)` — file BLTAudit/Foundations/ZakConformal.lean
- [ ] F4.1 Gaussian eigenfunctions of `H₀ = −∂² + 4π²x²` (Appendix A.1): `φ(x) = e^{−πx²}` has `−φ'' + 4π²x²φ = 2πφ` and `ψ = xφ` has `−ψ'' + 4π²x²ψ = 6πψ`, as `HasDerivAt` statements — file BLTAudit/Foundations/OscillatorGaussian.lean
- [ ] F4.2 Standard form of `G_N` (§1): `energy f = (ip f (gStd f)).re` and `(ip f (gStd f)).im = 0`, i.e. `D*D + F*D*DF` acts as `(4 − 2cos(2πj/N)) f(j) − f(j−1) − f(j+1)` (uses F1.1, F1.2) — file BLTAudit/Foundations/GStandardForm.lean
- [ ] F4.3 Perron–Frobenius step: for a real symmetric matrix `A` with nonpositive off-diagonal entries and `v : ι → ℂ`, `∑ A i j |v i| |v j| ≤ Re ∑ A i j conj(v i) v j`; so a Rayleigh minimizer can be taken entrywise nonnegative — file BLTAudit/Foundations/PerronStep.lean
- [ ] F4.4 Positivity on the cycle: a nonzero real eigenvector `v ≥ 0` of `gStd` (any `N ≥ 1`) has `v j > 0` for every `j` (a zero entry propagates to its neighbours around `ZMod N`) — file BLTAudit/Foundations/GStdPositive.lean
- [ ] F5.1 Circle energy: if `θ` is `C¹` on `[0, 2π]` with `θ(2π) − θ(0) = 2πQ`, then `∫₀^{2π} θ'(φ)² dφ ≥ 2πQ²` (expand `∫ (θ' − Q)² ≥ 0`) — file BLTAudit/Foundations/CircleEnergy.lean
- [ ] F5.2 Annulus logarithm (L13): for `0 < r < s` and `g` integrable on `[r, s]` with `g ρ ≥ 2πQ²` there, `∫_r^s g ρ / ρ dρ ≥ 2πQ² log(s/r)`; then the same for `g ρ = ∫₀^{2π} (∂_φ θ(ρ, φ))² dφ` using F5.1 — file BLTAudit/Foundations/AnnulusEnergy.lean
- [ ] F5.3 Bilinear interpolation (L8)–(L10), zero gauge error: for corner values `θ₀₀ θ₁₀ θ₀₁ θ₁₁` and the bilinear interpolant on `[0,1]²`, `|∇θ(x,y)|² ≤ W(x,y) = (1−y) b_bot² + y b_top² + (1−x) b_left² + x b_right²`, and `∫∫_{[0,1]²} W = (b_bot² + b_top² + b_left² + b_right²)/2` — file BLTAudit/Foundations/BilinearInterp.lean
- [ ] F5.4 Ball merging (§4.3): in a real normed space, if `‖c₁ − c₂‖ ≤ r₁ + r₂` with `r₁ r₂ > 0`, then `c = c₁ + (r₂/(r₁+r₂)) • (c₂ − c₁)` has `‖c − c₁‖ ≤ r₂`, `‖c − c₂‖ ≤ r₁`, `ball c₁ r₁ ∪ ball c₂ r₂ ⊆ ball c (r₁ + r₂)`, and `(r₁ + r₂) − ‖x − c‖ ≥ r₁ − ‖x − c₁‖` for all `x` — file BLTAudit/Foundations/BallMerge.lean
- [ ] F5.5 Final arithmetic of Theorem 4.1 (L17)–(L19), from named real hypotheses only: for `d ≥ 3`, `C ≥ 0`, if `2π log T ≤ (1 + C/log d)·A + K`, `T = (d/√(log d))/S₀`, `0 < S₀ ≤ C₂ (log d)³` and `A ≤ C₀ log d`, then `A ≥ 2π log d − 7π log log d − (2π log C₂ + C·C₀ + K)` — file BLTAudit/Foundations/LowerBoundArithmetic.lean

## Not attempted here

- Uniqueness and simplicity of the Gaussian Zak zero in the unit square (Jacobi triple product, Appendix A.3), unless Mathlib already has the triple product.
- Spectral convergence `λ₀,d → 2π`, `λ₁,d → 6π` (A4), the fourth-order approximate ground vector (A5)–(A7), and the uniform Zak approximation (A9).
- The trial-energy asymptotic (U4) and its transfer to the finite-Hermite phase (U12)–(U14).
- The cellular degree lemma on the twisted torus (L12), the ball-growth argument (L14)–(L16) as a whole, Theorem 4.1, and Theorem 1.1.
