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
- [x] A3b. Zak transform of a translate: for `f : ZMod (d * d) → ℂ` and `q r : ZMod d`,
  `zak (transl f) q r = zak f q (r + 1)` when `r.val + 1 < d`, and
  `zak (transl f) q r = ZMod.stdAddChar (-q) * zak f q 0` when `r.val + 1 = d` (the seam: reindex
  `b ↦ b + 1`; the term with `b.val + 1 = d` wraps around because `d * d = 0` in `ZMod (d * d)`).
  File `BLTAudit/FiniteZakTranslation.lean`.
  - Done 2026-11-20 17:50 UTC at 3579b28: `zak_transl_of_lt`, `zak_transl_seam`
- [x] A3c. Zak transform of a modulate:
  `zak (modul f) q r = Complex.exp (2πi r.val / d²) * zak f (q + 1) r`, where the factor is
  `mag d r.val` (the character of `ZMod (d * d)` at `b.val * d + r.val` is
  `e^{2πi b.val / d} · e^{2πi r.val / d²}`). File `BLTAudit/FiniteZakModulation.lean`.
  - Done 2026-11-20 18:05 UTC at 2917950: `zak_modul`, `stdAddChar_natCast`. The factor is stated as `Complex.exp (2 * π * I * r.val / d ^ 2)`; its identification with `mag d r.val` is not stated as a lemma.
- [-] A4. Critical Gabor criterion, sufficiency (§2): if `‖zak f q r‖ = 1 / d` for all `q r`, then the
  `d²` vectors `gabor f n m` (`n m < d`) are orthonormal for `ip`, hence a basis of `ℂ^{d²}`.
  File `BLTAudit/ZakCriterion.lean`. (split into A4a, A4b, A4c, A4d, A4e)
  - Split 2026-11-20: five separate steps (closed form of `gabor`, two index computations in `ZMod (d * d)`, a correlation identity on `ZMod d`, the orthonormality sum, linear independence with span), about 220 lines in all, too large for one file of about 150 lines. Nothing was attempted and no Lean file was written; `BLTAudit/ZakCriterion.lean` is now the file of A4d. The five statements below passed a numerical check for `d ≤ 5` on 2026-11-20.
- [x] A4a. Closed form of the Gabor vectors: for `f : ZMod N → ℂ`, `k : ℕ` and `j : ZMod N`,
  `(transl^[k] f) j = f (j + k)` and `(modul^[k] f) j = ZMod.stdAddChar (k * j) * f j`; hence for
  `f : ZMod (d * d) → ℂ` and all `n m : ℕ`,
  `gabor f n m j = ZMod.stdAddChar ((m * d : ℕ) * j) * f (j + (n * d : ℕ))` (the cross term
  `(m d)(n d)` vanishes because `d * d = 0` in `ZMod (d * d)`). File `BLTAudit/GaborFormula.lean`.
  - Done 2026-11-20 18:19 UTC at b615ca4: `gabor_apply`, `transl_iterate_apply`, `modul_iterate_apply`
- [x] A4b. Gabor vectors in Zak coordinates: for `b r : ZMod d` and `n m : ℕ`,
  `gabor f n m (zakIndex d (b, r)) = ZMod.stdAddChar ((m : ZMod d) * r) * f (zakIndex d (b + n, r))`,
  from A4a and the two index facts `zakIndex d (b, r) + (n * d : ℕ) = zakIndex d (b + n, r)` and
  `ZMod.stdAddChar ((m * d : ℕ) * zakIndex d (b, r)) = ZMod.stdAddChar ((m : ZMod d) * r)` (the first
  character is on `ZMod (d * d)`, the second on `ZMod d`). File `BLTAudit/GaborZakCoordinates.lean`.
  - Done 2026-11-20 18:37 UTC at 8735e2c: `gabor_zakIndex`, `zakIndex_add_natCast_mul`, `stdAddChar_mul_zakIndex`, `stdAddChar_natCast_mul_self`
- [x] A4c. Zak correlation identity: for `f : ZMod (d * d) → ℂ` and `r s t : ZMod d`, in `ℂ`,
  `∑ b, conj (f (zakIndex d (b + s, r))) * f (zakIndex d (b + t, r))`
  `= ∑ q, ZMod.stdAddChar ((s - t) * q) * ‖zak f q r‖ ^ 2`; hence, if `‖zak f q r‖ = 1 / d` for all
  `q`, the left side is `1 / d` when `s = t` and `0` otherwise (the DFT of `b ↦ g (b + s)` is
  `q ↦ ZMod.stdAddChar (-(s * q)) * dftU g q`; then A1 and the identification of `zak` with `dftU`
  in A3a). File `BLTAudit/ZakCorrelation.lean`.
  - Done 2026-11-20 18:46 UTC at 0014bf4: `zak_correlation`, `zak_correlation_of_norm`, `dftU_shift`. The right side is stated with `(‖zak f q r‖ : ℂ) ^ 2`.
- [x] A4d. Orthonormality, the statement of A4 without "basis": if `‖zak f q r‖ = 1 / d` for all `q r`,
  then for `n m n' m' < d`, `ip (gabor f n m) (gabor f n' m') = if n = n' ∧ m = m' then 1 else 0` (sum
  over `ZMod (d * d)` through the bijection of A3a, then A4b, A4c, and orthogonality of characters in
  `r`). File `BLTAudit/ZakCriterion.lean`.
  - Done 2026-11-20 19:57 UTC at c24ed5d: `ip_gabor_of_zak_norm`, `ip_gabor_eq_sum`, `ip_eq_sum_zakIndex`, `natCast_zmod_eq_iff_of_lt`
- [x] A4e. Basis: a family `v : ι → ZMod N → ℂ` with `ip (v i) (v j) = if i = j then 1 else 0` is
  linearly independent over `ℂ`; hence, under the hypothesis of A4, the family
  `fun p : Fin d × Fin d => gabor f p.1 p.2` is linearly independent and spans `ZMod (d * d) → ℂ`
  (it has `d * d = finrank` members; uses A4d). File `BLTAudit/GaborBasis.lean`.
  - Done 2026-11-20 20:22 UTC at 81f9fe1: `linearIndependent_gabor`, `span_gabor_eq_top`, `linearIndependent_of_ip_orthonormal`, `ip_sum_smul_right`, `ip_zero_right`. Linear independence and `span = ⊤` are two theorems; the family is not packaged as a Mathlib `Basis`.
- [-] A5. Critical Gabor criterion, necessity: orthonormality of `{gabor f n m : n m < d}` forces
  `‖zak f q r‖ = 1 / d` for all `q r`, so admissible vectors correspond exactly to unit-modulus arrays
  `ζ = d • zak f`. File `BLTAudit/ZakCriterionConverse.lean`. (split into A5a, A5b, A5c)
  - Split 2026-11-20: three separate steps (Gabor inner products through `‖zak f q r‖ ^ 2`, a two-variable Fourier uniqueness statement on `ZMod d`, the conclusion with the equivalence), about 200 lines in all, too large for one file of about 150 lines. Nothing was attempted and no Lean file was written; `BLTAudit/ZakCriterionConverse.lean` is now the file of A5c. The three statements below passed a numerical check for `d ≤ 5` on 2026-11-20.
- [x] A5a. Gabor inner products through the Zak modulus, with no hypothesis on `f`: for
  `f : ZMod (d * d) → ℂ` and all `n m n' m' : ℕ`, `ip (gabor f n m) (gabor f n' m')`
  `= ∑ r, conj (ZMod.stdAddChar ((m : ZMod d) * r)) * ZMod.stdAddChar ((m' : ZMod d) * r)`
  `* ∑ q, ZMod.stdAddChar (((n : ZMod d) - n') * q) * ‖zak f q r‖ ^ 2` (`ip_gabor_eq_sum` of A4d, then
  `zak_correlation` of A4c); hence for `a c : ZMod d`, `ip (gabor f a.val 0) (gabor f 0 c.val)`
  `= ∑ r, ∑ q, ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) * ‖zak f q r‖ ^ 2`.
  File `BLTAudit/GaborZakModulus.lean`.
  - Done 2026-11-20 20:35 UTC at 85ee9d4: `ip_gabor_eq_sum_zak`, `ip_gabor_val_zero`. The right sides are stated with `(‖zak f q r‖ : ℂ) ^ 2`.
- [x] A5b. Two-variable Fourier uniqueness on `ZMod d`: if `W : ZMod d → ZMod d → ℂ` satisfies
  `∑ r, ∑ q, ZMod.stdAddChar (c * r) * ZMod.stdAddChar (a * q) * W q r = if a = 0 ∧ c = 0 then 1 else 0`
  for all `a c : ZMod d`, then `W q r = 1 / d ^ 2` for all `q r` (multiply by
  `ZMod.stdAddChar (-(c * r₀)) * ZMod.stdAddChar (-(a * q₀))`, sum over `a c`, and use
  `sum_stdAddChar_mul` of A1 in each variable). File `BLTAudit/FourierUniqueness.lean`.
  - Done 2026-11-20 21:58 UTC at 5013a3b: `fourier_uniqueness_two`, `sum_sum_stdAddChar_inversion`, `sum_stdAddChar_inversion`, `sum_sum_ite_zero`
- [x] A5c. Necessity, the statement of A5: if
  `ip (gabor f n m) (gabor f n' m') = if n = n' ∧ m = m' then 1 else 0` for all `n m n' m' < d`, then
  `‖zak f q r‖ = 1 / d` for all `q r` (A5a at `n = a.val`, `m = 0`, `n' = 0`, `m' = c.val`, then A5b
  with `W q r = ‖zak f q r‖ ^ 2`); hence, with A4d, orthonormality of the Gabor vectors is equivalent to
  `‖zak f q r‖ = 1 / d` for all `q r`, that is, to `‖d * zak f q r‖ = 1` for all `q r` (unit modulus of
  `ζ = d • zak f`). File `BLTAudit/ZakCriterionConverse.lean`.
  - Done 2026-11-20 23:45 UTC at 14316bd: `zak_norm_of_ip_gabor`, `ip_gabor_orthonormal_iff_zak_norm`, `ip_gabor_orthonormal_iff_unit_modulus`, `norm_natCast_mul_zak_eq_one_iff`, `zmod_val_eq_zero_iff`. The correspondence with unit-modulus arrays is proved as this equivalence only; that every unit-modulus array is `d • zak f` for some `f` (inverse Zak transform) is not stated.
- [x] A6. Standard form of `G_N` (§1): `energy f = (ip f (gStd f)).re` and `(ip f (gStd f)).im = 0`,
  that is, `D*D + F*D*DF` acts as `(4 − 2cos(2πj/N)) f(j) − f(j−1) − f(j+1)` (uses A1, A2).
  File `BLTAudit/GStandardForm.lean`.
  - Done 2026-11-21 00:35 UTC at ad4e270: `energy_eq_re_ip_gStd`, `im_ip_gStd`, `re_ip_gStd`, `sum_norm_sq_diffOp`, `sum_norm_sq_diffOp_dftU`, `norm_sq_one_sub_stdAddChar`, `stdAddChar_eq_exp_ofReal`, `sum_re_conj_mul_sub_one`, `sum_im_conj_mul_sub_one`, `complex_norm_sub_sq`, `sum_zmod_add_one`. Proved as an identity of quadratic forms; the operator identity `gStd f = D*D f + F*D*D F f` is not stated (the adjoints `D*`, `F*` are not defined). Also uses `stdAddChar_natCast` of A3c.
- [-] A7. Zak energy identity (§2): for `f : ZMod (d * d) → ℂ` and any `ζ : ℤ × ℤ → ℂ` with
  `ζ (q, r) = d * zak f q r` on `0 ≤ q, r < d` and the gluing `shift_q`, `shift_r` of `IsTwisted`,
  `d ^ 2 * energy f = zakEnergy d ζ` (uses A1–A3). Unit modulus is not needed. A numerical check of
  this identity for `d ≤ 7` passed on 2026-11-19; if a convention still fails in Lean, prove the
  corrected identity and record the difference in the docstring and in a note under this item.
  File `BLTAudit/ZakEnergyIdentity.lean`. (split into A7a, A7b, A7c)
  - Split 2026-11-21: three separate steps (the two halves of `energy` in Zak coordinates, the array `ζ` across the two seams, the sum over `ZMod d` as a sum over `range d` with the assembly), about 190 lines in all, too large for one file of about 150 lines. Nothing was attempted and no Lean file was written; `BLTAudit/ZakEnergyIdentity.lean` is now the file of A7c. The three statements below passed a numerical check for `d ≤ 6` on 2026-11-21.
- [x] A7a. Energy in Zak coordinates, with no array `ζ`: for `f g : ZMod (d * d) → ℂ` and
  `q r : ZMod d`, `zak (f - g) q r = zak f q r - zak g q r`;
  `∑ j, ‖diffOp f j‖ ^ 2 = ∑ q, ∑ r, ‖zak f q r - zak (transl f) q r‖ ^ 2` (`parseval_zak` of A3a at
  `f - transl f`); `∑ k, ‖diffOp (dftU f) k‖ ^ 2 = ∑ q, ∑ r, ‖zak f q r - zak (modul f) q r‖ ^ 2`
  (`diffOp_dftU` of A2, `parseval_dftU` of A1, then `parseval_zak` at `f - modul f`); hence
  `energy f = ∑ q, ∑ r, (‖zak f q r - zak (transl f) q r‖ ^ 2 + ‖zak f q r - zak (modul f) q r‖ ^ 2)`,
  all sums over `q r : ZMod d`. File `BLTAudit/EnergyZakCoordinates.lean`.
  - Done 2026-11-21 01:39 UTC at f9d12f1: `energy_eq_sum_zak`, `sum_norm_sq_diffOp_eq_zak`, `sum_norm_sq_diffOp_dftU_eq_zak`, `zak_sub`
- [x] A7b. The array `ζ` across the two seams: let `f : ZMod (d * d) → ℂ` and `ζ : ℤ × ℤ → ℂ` satisfy
  `ζ (q, r) = d * zak f q r` for naturals `q r < d`, `ζ (q + d, r) = ζ (q, r)` and
  `ζ (q, r + d) = Complex.exp (-2πi q / d) * ζ (q, r)` for integers `q r` (`shift_q` and `shift_r` of
  `IsTwisted`; unit modulus is not assumed). Then for naturals `q r < d`,
  `ζ (q, r + 1) = d * zak (transl f) q r` (A3b; at `r + 1 = d` by `shift_r` and
  `ZMod.stdAddChar (-(q : ZMod d)) = Complex.exp (-2πi q / d)`) and
  `mag d r * ζ (q + 1, r) = d * zak (modul f) q r` (A3c, whose factor is `mag d r`; at `q + 1 = d` by
  `shift_q`); hence `‖ζ (q, r + 1) - ζ (q, r)‖ ^ 2 = d ^ 2 * ‖zak f q r - zak (transl f) q r‖ ^ 2` and
  `‖mag d r * ζ (q + 1, r) - ζ (q, r)‖ ^ 2 = d ^ 2 * ‖zak f q r - zak (modul f) q r‖ ^ 2`.
  File `BLTAudit/ZakSeams.lean`.
  - Done 2026-11-21 01:57 UTC at 0abbc79: `zeta_r_succ`, `mag_mul_zeta_q_succ`, `norm_sq_zeta_r_edge`, `norm_sq_zeta_q_edge`, `stdAddChar_neg_natCast`, `zmod_val_natCast_of_lt`, `norm_sq_natCast_mul`. The gluing enters as two explicit hypotheses with the statements of `shift_q` and `shift_r`, not as `IsTwisted`; that an array `ζ` with the three properties exists is not stated.
- [x] A7c. The identity, the statement of A7: `∑ q : ZMod d, F q = ∑ k ∈ range d, F (k : ZMod d)` for
  `F : ZMod d → ℝ`; hence, under the hypotheses of A7b, `d ^ 2 * energy f = zakEnergy d ζ` (A7a, the
  reindexing in both variables, then A7b edge by edge). If a convention still fails in Lean, prove the
  corrected identity and record the difference in the docstring and in a note under this item.
  File `BLTAudit/ZakEnergyIdentity.lean`.
  - Done 2026-11-21 02:08 UTC at 1c05ccb: `zak_energy_identity`, `zak_energy_identity_of_isTwisted`, `sum_sum_zmod_eq_sum_range`, `sum_zmod_eq_sum_range`. No convention failed: the identity holds as stated in A7, with `ζ (q, r) = d * zak f q r` assumed for naturals `q r < d` and the gluing as the two hypotheses of A7b or as `IsTwisted d ζ`. That such an array `ζ` exists for a given `f` is not stated.

## B. Discrete phase topology

§4.1: the twisted boundary condition forces total integer charge one. Nothing like this is in Mathlib.

- [x] B1. Edge energy (L1): for `‖u‖ = ‖v‖ = 1`, `‖v − u‖ ^ 2 = 4 * sin (arg (v * conj u) / 2) ^ 2`;
  hence for unit-modulus `ζ`,
  `zakEnergy d ζ = ∑ q r < d, (4 sin²(aR ζ q r / 2) + 4 sin²(aQ d ζ q r / 2))`.
  File `BLTAudit/EdgeEnergy.lean`.
  - Done 2026-11-21 03:54 UTC at ffa15cb: `zakEnergy_eq_sum_sin_sq`, `zakEnergy_eq_sum_sin_sq_of_isTwisted`, `norm_sub_sq_eq_four_sin_sq`, `norm_sub_one_sq_of_norm_eq_one`, `norm_mag`, `norm_sq_edgeR`, `norm_sq_edgeQ`. Only unit modulus is used. The sum is over naturals `q r < d`, as in the definition of `zakEnergy`; the paper's sum over `q, r (mod d)` is the same once the periodicity of B2 is known.
- [-] B2. Plaquette identity (L3): for `IsTwisted d ζ` with `0 < d`, the edge numbers `aQ d ζ` and
  `aR ζ` are `d`-periodic in `q` and in `r`, and
  `aQ d ζ q r + aR ζ (q+1) r − aQ d ζ q (r+1) − aR ζ q r = −2π/d² + 2π n` for some `n : ℤ`.
  File `BLTAudit/PlaquetteCharge.lean`. (split into B2a, B2b)
  - Split 2026-11-21: two separate steps (four periodicity statements, two of which need the twist factors and the magnetic factor to cancel across the seam, and the plaquette identity through the product of the four edge phases), about 215 lines in all, too large for one file of about 150 lines. A draft was written but not committed, and no Lean file is on main; `BLTAudit/PlaquetteCharge.lean` is now the file of B2b.
- [x] B2a. Periodic edge numbers: for `IsTwisted d ζ` and integers `q r`, `aR ζ (q + d) r = aR ζ q r`,
  `aR ζ q (r + d) = aR ζ q r`, `aQ d ζ (q + d) r = aQ d ζ q r` and, if `0 < d`,
  `aQ d ζ q (r + d) = aQ d ζ q r` (in `r` the twist factor `e^{−2πiq/d}` meets its conjugate; for `aQ`,
  `mag d (r + d) = mag d r * e^{2πi/d}` and `e^{−2πi(q+1)/d} = e^{−2πiq/d} * e^{−2πi/d}`).
  File `BLTAudit/EdgePeriodicity.lean`.
  - Done 2026-11-21 05:19 UTC at ea468fb: `aR_add_period_q`, `aR_add_period_r`, `aQ_add_period_q`, `aQ_add_period_r`, `mag_add_period_mul_twist`, `norm_twist_factor`, `mag_twist_cancel`, `unit_mul_mul_conj`, `mul_conj_of_norm_eq_one`. Each periodicity is proved as an equality of the complex numbers under `Complex.arg`. The two factor identities of the hint are proved only in the combined form `mag d (r + d) * e^{-2πi(q+1)/d} = mag d r * e^{-2πiq/d}` (`mag_add_period_mul_twist`, for `0 < d`); shifts by integer multiples of `d` are not stated.
- [x] B2b. Plaquette identity (L3): for a unit-modulus `ζ : ℤ × ℤ → ℂ` (in particular under
  `IsTwisted d ζ`) and integers `q r`, there is `n : ℤ` with
  `aQ d ζ q r + aR ζ (q+1) r − aQ d ζ q (r+1) − aR ζ q r = −2π/d² + 2π n` (`exp (a * I) = w` for each
  unit edge phase `w` with `a = arg w`; the four phases multiply to
  `mag d r * conj (mag d (r + 1)) = e^{−2πi/d²}`; then `Complex.exp_eq_exp_iff_exists_int`). Neither
  the gluing nor `0 < d` is needed. File `BLTAudit/PlaquetteCharge.lean`.
  - Done 2026-11-21 10:20 UTC at 6533028: `plaquette_identity`, `plaquette_identity_of_isTwisted`, `arg_add_arg_sub_of_mul_eq`, `exists_int_of_exp_mul_I_eq`, `exp_arg_mul_I_of_norm_eq_one`, `mag_succ`, `plaquette_phase_algebra`, `norm_mul_conj_eq_one`. The right side is stated as `-(2 * π / d ^ 2) + 2 * π * n`. The integer `n` is only shown to exist for each `(q, r)`; it is not defined as a function of the plaquette. The phase product is used in the form `mag d (r + 1) = mag d r * exp ((2π / d²) * I)` (`mag_succ`), not with `conj (mag d (r + 1))`. Uses `norm_mag` of B1 and `mul_conj_of_norm_eq_one` of B2a.
- [x] B3. Total charge one (L4): for `IsTwisted d ζ` with `0 < d`, the plaquette integers of B2 over
  `0 ≤ q, r < d` sum to `1` (the oriented edge sums telescope by the periodicity of B2).
  File `BLTAudit/TotalCharge.lean`.
  - Done 2026-11-21 11:12 UTC at f640d86: `total_charge_one`, `sum_plaquette_int_eq_one`, `sum_plaquette_edges_eq_zero`, `plaquetteCharge_spec`, `plaquetteCharge_eq_of_identity`, `sum_range_int_telescope`, `sum_range_aQ_r_edge`, `sum_range_aR_q_edge`, `sum_range_const_add_mul`, `sum_sum_range_const_add_mul`. The plaquette integer is defined in this file as `plaquetteCharge d ζ q r` (the oriented sum of the four edge numbers plus `2π / d²`, divided by `2π` and rounded): for a unit-modulus array it satisfies (L3), and any integer that satisfies (L3) at `(q, r)` equals it. `sum_plaquette_int_eq_one` is the same statement for any integers `n q r` that satisfy (L3) on the square. The sum is over naturals `q r < d`. Of B2a only `aQ_add_period_r` and `aR_add_period_q` are used. That `plaquetteCharge d ζ` is `d`-periodic is not stated.
- [x] B4. Good plaquettes are neutral and large edges are few (§4.1, (L5)): if the four edge numbers of
  a plaquette have modulus `< η` and `4η + 2π/d² < 2π`, its integer is `0`; and for `0 < η ≤ π`,
  `#{edges with |a| ≥ η} * (4 sin²(η/2)) ≤ zakEnergy d ζ`. File `BLTAudit/GoodPlaquette.lean`.
  - Done 2026-11-21 15:11 UTC at 751049e: `plaquetteCharge_eq_zero_of_small`, `plaquette_int_eq_zero_of_small`, `card_large_edges_mul_le_zakEnergy`, `card_large_edges_le_div`, `card_largeEdgesR_mul_le`, `card_largeEdgesQ_mul_le`, `zakEnergy_eq_sum_product`, `card_filter_mul_le_sum`, `four_sin_half_sq_le_of_le_abs`, `four_sin_half_sq`, `int_eq_zero_of_four_small`, `abs_aR_le_pi`, `abs_aQ_le_pi`. Both statements are for a unit-modulus array; neither the gluing of `IsTwisted` nor `0 < d` is used. The integer is `plaquetteCharge d ζ q r` of B3 (`plaquette_int_eq_zero_of_small`: any integer that satisfies (L3) at `(q, r)`, with no hypothesis on `ζ`). The large edges are counted as `largeEdgesR d ζ η` and `largeEdgesQ d ζ η`, the positions `q r < d` whose `r`-edge or `q`-edge number has modulus `≥ η`: each positive edge of the square once, as in `zakEnergy`. The product bound holds for `0 ≤ η`; `η ≤ π` is used only for the quotient form `card_large_edges_le_div`. The rest of (L5), `#{large edges} ≤ C₁ log d / η²` and `#{bad plaquettes} ≤ 2 #{large edges}`, is not stated, nor that the four edges of a plaquette at a seam are edges of the square. Uses `zakEnergy_eq_sum_sin_sq` of B1 and `plaquetteCharge_spec` of B3.

## C. The Zak transform of the Gaussian

§3.1 and Appendix A.3. Mathlib has `jacobiTheta₂`; it has no Zak transform.

- [x] C1. Theta representation: `r ↦ gauss (x − r) * exp (2πi r y)` is summable over `ℤ`, and
  `gaussZak x y = 2^{1/4} e^{−πx²} * jacobiTheta₂ (y − x * I) I` (Mathlib's convention is
  `jacobiTheta₂ z τ = ∑ exp (2πi n z + πi n² τ)`). File `BLTAudit/ZakTheta.lean`.
  - Done 2026-11-21 16:36 UTC at 6b1be5d: `gaussZak_eq_theta`, `summable_gaussZak_term`, `hasSum_gaussZak_term`, `gaussZak_eq_gauss_mul_theta`, `hasSum_gaussZak_term_theta`, `gaussZak_term_eq`, `gaussZak_term_aux`, `ofReal_mul_exp_mul_exp_eq`. The constant is the real number `(2 : ℝ) ^ ((1 : ℝ) / 4) * Real.exp (-Real.pi * x ^ 2)` (that is, `gauss x`) cast to `ℂ`, and the theta function is taken at `z = y - x * I`, `τ = I`. Both statements follow from the termwise identity `gaussZak_term_eq` (complete the square) and Mathlib's `hasSum_jacobiTheta₂_term`; `hasSum_gaussZak_term` says that the series sums to `gaussZak x y`. Continuity or differentiability of `gaussZak` is not stated.
- [x] C2. Quasi-periodicity (U1): `gaussZak (x + 1) y = exp (2πi y) * gaussZak x y` and
  `gaussZak x (y + 1) = gaussZak x y`. File `BLTAudit/ZakGluing.lean`.
  - Done 2026-11-21 16:58 UTC at 2f275d1: `gaussZak_add_one_left`, `gaussZak_add_one_right`, `gaussZak_term_shift`, `exp_two_pi_int_mul_add_one`. The factor is stated as `Complex.exp (2 * π * I * y)`. Both statements are proved termwise from `hasSum_gaussZak_term` of C1 (in `x` after the reindexing `r = s + 1`); the theta representation itself is not used. Shifts by other integers are not stated, nor that the samples of `gaussZak` on a grid satisfy the gluing of `IsTwisted`.
- [x] C3. The Zak zero (A10, first part): `gaussZak (1/2) (1/2) = 0`, by pairing `r ↔ 1 − r` in the sum.
  File `BLTAudit/ZakZero.lean`.
  - Done 2026-11-21 17:19 UTC at 4803e98: `gaussZak_half_half`, `gaussZak_half_term_reflect`, `exp_reflect_half`, `gauss_neg`, `gauss_pos`, `jacobiTheta_zakZero`. Proved by reindexing the series of C1 (`hasSum_gaussZak_term`) with `r ↦ 1 − r` (`Equiv.subLeft 1` on `ℤ`): at `x = y = 1/2` the summand at `1 − r` is minus the summand at `r`, so the sum equals its own negative. `jacobiTheta_zakZero` is the same zero in Mathlib's notation, `jacobiTheta₂ (1/2 − (1/2) * I) I = 0` (through `gaussZak_eq_gauss_mul_theta` of C1; the two numbers `1/2` are real numbers cast to `ℂ`). That `(1/2, 1/2)` is the only zero in the unit square, that the zero is simple, and the zeros at the other half-integer points are not stated.
- [x] C4. Conformality at the zero (A10): `exp (πx²) * gaussZak x y` is a holomorphic function of
  `y − x * I` (from C1), hence `∂_y gaussZak = I * ∂_x gaussZak` at `(1/2, 1/2)`.
  File `BLTAudit/ZakConformal.lean`.
  - Done 2026-11-21 17:44 UTC at cb5e057: `deriv_gaussZak_snd_zero`, `hasDerivAt_gaussZak_fst_zero`, `hasDerivAt_gaussZak_snd_zero`, `exp_mul_gaussZak`, `exp_mul_gaussZak_holomorphic`, `hasDerivAt_gaussZak_fst`, `hasDerivAt_gaussZak_snd`, `hasDerivAt_gauss`, `im_I_pos`. The holomorphic statement is `e^{πx²} * gaussZak x y = Θ (y − x * I)` for all real `x y`, with the entire function `Θ z = 2^{1/4} * jacobiTheta₂ z I`. The conformality is stated for the two one-variable derivatives `deriv (fun t : ℝ => gaussZak (1/2) t) (1/2)` and `deriv (fun s : ℝ => gaussZak s (1/2)) (1/2)`, both of which exist (as `HasDerivAt`). The `x`-derivative at the zero is `zakA0 = gauss (1/2) * (jacobiTheta₂' (1/2 − (1/2) * I) I * (−I))`, defined in this file with Mathlib's `jacobiTheta₂'`; it is the number `A₀` of (A10), and the `y`-derivative is `I * zakA0`. The two partial derivatives are computed at every point; at the zero the term with `gauss'` vanishes by `jacobiTheta_zakZero` of C3. Joint differentiability of `gaussZak` on `ℝ²`, the expansion (U2) and `zakA0 ≠ 0` (C5) are not stated.
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
