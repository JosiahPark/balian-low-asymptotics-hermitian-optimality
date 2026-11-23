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
- [-] C5. Nonvanishing derivative (A10): with `A₀ = ∂ₓ gaussZak` at `(1/2, 1/2)`,
  `A₀ = −4π ∑_{k ≥ 0} (−1)^k (k + 1/2) gauss (k + 1/2)`, and this alternating series has strictly
  decreasing terms, so `A₀ ≠ 0`. File `BLTAudit/ZakDerivNonzero.lean`. (split into C5a, C5b, C5c, C5d)
  - Split 2026-11-21: four separate steps (the series of `A₀` over `ℤ` from Mathlib's series of `jacobiTheta₂'`, its folding to a series over `ℕ` by pairing `n ↔ 1 − n`, the positivity and strict decrease of the terms, the alternating-series bound with the conclusion), about 400 lines in all, too large for one file of about 150 lines. Nothing was attempted and no Lean file was written; `BLTAudit/ZakDerivNonzero.lean` is now the file of C5d. The four statements below passed a numerical check on 2026-11-21 (`zakA0 ≈ −3.38769`).
- [x] C5a. Series of `A₀` over `ℤ`: with `zakA0` of C4 (so that `∂ₓ gaussZak = zakA0` at `(1/2, 1/2)`),
  `HasSum (fun n : ℤ => 2 * π * n * (gauss (1/2 − n) * Complex.exp (2πi n (1/2)))) zakA0` in `ℂ`: the
  summand is `2πn` times the summand of `gaussZak (1/2) (1/2)` (Mathlib's `hasSum_jacobiTheta₂'_term`
  with `jacobiTheta₂'_term n z τ = 2πi n * jacobiTheta₂_term n z τ`, multiplied by
  `gauss (1/2) * (−I)`, then `gaussZak_term_eq` of C1). File `BLTAudit/ZakDerivSeries.lean`.
  - Done 2026-11-21 18:18 UTC at c80ecaa: `hasSum_zakA0`, `hasSum_deriv_gaussZak_fst_zero`, `summable_zakA0_term`, `zakA0_eq_tsum`, `zakA0_term_eq`, `hasSum_thetaDerivTerm`, `thetaDerivTerm_eq`. The summand is stated as `2 * π * n * (gauss (1/2 − n) * Complex.exp (2 * π * I * n * (1/2)))`, with `π`, `n` and the `1/2` of the exponent cast to `ℂ` (the `1/2` is a real number cast to `ℂ`, as in the summand of `gaussZak`). The series is Mathlib's series of `jacobiTheta₂'` at `1/2 − (1/2) * I`, multiplied by `gauss (1/2) * (−I)`; it is not obtained by differentiating the series of `gaussZak` term by term. `hasSum_deriv_gaussZak_fst_zero` is the same series with the sum written `deriv (fun s : ℝ => gaussZak s (1/2)) (1/2)` (`hasDerivAt_gaussZak_fst_zero` of C4). `Complex.exp (2πi n (1/2)) = (−1) ^ n` is not stated (C5b). Uses `gaussZak_term_eq` of C1 and `im_I_pos` of C4.
- [x] C5b. Folding to a series over `ℕ`: `Complex.exp (2πi n (1/2)) = (−1) ^ n` for `n : ℤ`, and
  `HasSum (fun k : ℕ => −(4π) * ((−1) ^ k * ((k + 1/2) * gauss (k + 1/2)))) zakA0`, each term a real
  number cast to `ℂ`; that is, `A₀ = −4π ∑_{k ≥ 0} (−1)^k (k + 1/2) gauss (k + 1/2)` (reindex the series
  of C5a by `n = m + 1`, split `ℤ` into `m = k` and `m = −(k + 1)` with `HasSum.of_nat_of_neg_add_one`
  and `Summable.comp_injective`; the terms at `n = k + 1` and `n = −k` add up to
  `−4π (−1)^k (k + 1/2) gauss (k + 1/2)` because `gauss` is even, `gauss_neg` of C3; uses C5a).
  File `BLTAudit/ZakDerivFold.lean`.
  - Done 2026-11-21 20:24 UTC at 6c0ffc0: `exp_half_int`, `hasSum_zakA0_nat`, `zakA0Term_fold`, `hasSum_zakA0Term`, `exp_half_succ`, `exp_half_neg`, `exp_nat_mul_pi_I`, `zakA0_eq_tsum_nat`, `hasSum_zakA0_re`. `exp_half_int` is stated with the `1/2` of the exponent a real number cast to `ℂ`, as in the summand of C5a, and with `(-1) ^ n` an integer power in `ℂ`. The term of the folded series is the real number `-(4 * π) * ((-1) ^ k * ((k + 1/2) * gauss (k + 1/2)))` cast to `ℂ`. The series of C5a is reindexed by `n = m + 1` and folded with Mathlib's `HasSum.nat_add_neg_add_one`, which pairs `n = k + 1` with `n = -k`; `HasSum.of_nat_of_neg_add_one` and `Summable.comp_injective` of the hint are not used. `zakA0Term n`, defined in this file, is the summand of the series of C5a. `hasSum_zakA0_re` is the same series of real numbers with sum `zakA0.re` (for C5d); that the imaginary part of `zakA0` is `0` is not stated. Uses `gauss_neg` of C3 and `hasSum_zakA0` of C5a.
- [x] C5c. The terms are positive and strictly decreasing: for `k : ℕ`, with
  `a k = (k + 1/2) * gauss (k + 1/2)`, `0 < a k` and `a (k + 1) < a k`
  (`gauss (t + 1) = exp (−π (2t + 1)) * gauss t`, and `exp (−2π (k + 1)) ≤ exp (−2π) < 1/3` because
  `1 + x ≤ exp x` and `3 < π`; then `(k + 3/2) / 3 ≤ k + 1/2`). File `BLTAudit/ZakDerivTerms.lean`.
  - Done 2026-11-21 20:42 UTC at e924783: `zakA0Coeff_pos`, `zakA0Coeff_succ_lt`, `zakA0Coeff_succ_le`, `strictAnti_zakA0Coeff`, `gauss_add_one`, `exp_neg_two_pi_lt`, `hasSum_zakA0_re_coeff`. The term `a k` is defined in this file as `zakA0Coeff k = (k + 1/2) * gauss (k + 1/2)`, a real number, with `k` cast from `ℕ`. `exp_neg_two_pi_lt` is `Real.exp (-(2 * π)) < 1/3`, and `gauss_add_one` holds for every real `t`. `strictAnti_zakA0Coeff` is the strict decrease as Mathlib's `StrictAnti`. `hasSum_zakA0_re_coeff` is `hasSum_zakA0_re` of C5b written with `zakA0Coeff`: `HasSum (fun k : ℕ => -(4 * π) * ((-1) ^ k * zakA0Coeff k)) zakA0.re` (for C5d). No numerical bound for `zakA0` is stated. Uses `gauss_pos` of C3 and `hasSum_zakA0_re` of C5b.
- [x] C5d. Alternating series and the statement of C5: if `a : ℕ → ℝ` satisfies `a (k + 1) ≤ a k` for
  all `k` and `HasSum (fun k => (−1) ^ k * a k) S`, then `a 0 − a 1 ≤ S` (the even partial sums are
  `∑_{j < m} (a (2j) − a (2j + 1))`, and they tend to `S`); hence, with the real parts of the series
  of C5b and with C5c, `zakA0 ≠ 0`. File `BLTAudit/ZakDerivNonzero.lean`.
  - Done 2026-11-21 21:21 UTC at f28752b: `le_hasSum_alternating`, `zakA0_ne_zero`, `hasSum_pairs`, `hasSum_alternating_zakA0Coeff`, `zakA0_re_le`, `zakA0_re_neg`, `deriv_gaussZak_fst_zero_ne_zero`, `deriv_gaussZak_snd_zero_ne_zero`. The bound is proved by summing the series in consecutive pairs (`hasSum_pairs`: `HasSum f S → HasSum (fun k => f (2 * k) + f (2 * k + 1)) S`, from Mathlib's `Summable.comp_injective` and `HasSum.even_add_odd`) and Mathlib's `le_hasSum`, not through the even partial sums of the hint; `HasSum` on `ℝ` is unconditional summation, so the regrouping is available. `zakA0_re_le` is `zakA0.re ≤ -(4 * π) * (zakA0Coeff 0 - zakA0Coeff 1)` and `zakA0_re_neg` is `zakA0.re < 0`; `zakA0 ≠ 0` follows from the real part alone. The last two theorems say that the one-variable derivatives of `gaussZak` at `(1/2, 1/2)` in `x` and in `y` are nonzero (they are `zakA0` and `I * zakA0` by C4). The upper bound `S ≤ a 0`, that `zakA0` is a real number, and any numerical value of `zakA0` are not stated. Uses `zakA0Coeff_succ_le`, `zakA0Coeff_succ_lt` and `hasSum_zakA0_re_coeff` of C5c, and `hasDerivAt_gaussZak_fst_zero`, `hasDerivAt_gaussZak_snd_zero` of C4.

## D. The finite oscillator and its ground state

§1 and Appendix A.1: `G_N` has a simple, strictly positive ground vector.

- [x] D1. Gaussian eigenfunctions of `H₀ = −∂² + 4π²x²` (Appendix A.1): `φ(x) = exp (−πx²)` satisfies
  `−φ'' + 4π²x²φ = 2πφ`, and `ψ = xφ` satisfies `−ψ'' + 4π²x²ψ = 6πψ`, as `HasDerivAt` statements.
  File `BLTAudit/OscillatorGaussian.lean`.
  - Done 2026-11-21 21:46 UTC at 2aa008f: `oscPhi_eigenfunction`, `oscPsi_eigenfunction`, `hasDerivAt_oscPhi`, `hasDerivAt_oscPhiD`, `hasDerivAt_oscPsi`, `hasDerivAt_oscPsiD`, `oscPhi_eigen`, `oscPsi_eigen`, `gauss_eq_mul_oscPhi`, `const_mul_oscPhi_eigenfunction`, `const_mul_oscPsi_eigenfunction`. Defined in this file: `oscPhi x = Real.exp (-π * x ^ 2)` and `oscPsi x = x * oscPhi x`, with their derivatives written out, `oscPhiD x = -(2πx) * oscPhi x`, `oscPhiDD x = (4π²x² − 2π) * oscPhi x`, `oscPsiD x = (1 − 2πx²) * oscPhi x` and `oscPsiDD x = (4π²x³ − 6πx) * oscPhi x`. Each of the two main theorems is a conjunction at a point `x`: two `HasDerivAt` statements (first and second derivative) and the equation with the second derivative written out, `-oscPhiDD x + 4π²x² * oscPhi x = 2π * oscPhi x` and `-oscPsiDD x + 4π²x² * oscPsi x = 6π * oscPsi x`. The paper's Gaussian in Appendix A.1 is the normalised `ϕ = 2^{1/4} e^{−πx²}`, that is `gauss`, not the `e^{−πx²}` of this item: `gauss_eq_mul_oscPhi` is `gauss x = 2^{1/4} * oscPhi x`, and the two `const_mul` theorems are the same statements for `c * oscPhi` and `c * oscPsi` with any real `c`. `H₀` is not defined as an operator, so "eigenfunction" means only the pointwise equation; the equations are not restated with Mathlib's `deriv`; that `ϕ` has norm one, that `ϕ` and `xϕ` are orthogonal, and that `2π` and `6π` are the two lowest eigenvalues of `H₀` are not stated.
- [x] D2. Perron–Frobenius step: for a real symmetric matrix `A` with nonpositive off-diagonal entries
  and `v : ι → ℂ`, `∑ i j, A i j * ‖v i‖ * ‖v j‖ ≤ (∑ i j, A i j * conj (v i) * v j).re`; so replacing
  a vector by its entrywise modulus does not raise the quadratic form. File `BLTAudit/PerronStep.lean`.
  - Done 2026-11-21 22:43 UTC at 1c55849: `perron_step`, `quadFormRe_norm_le`, `quadFormRe_norm`, `energy_norm_le`, `energy_le_of_norm`, `re_conj_mul_le_norm_mul`, `re_ofReal_mul_conj_mul`, `re_conj_mul_self`. Proved without the symmetry hypothesis, which the term-by-term argument does not need. Also proved for `G_N` itself: `energy (fun j => (‖f j‖ : ℂ)) ≤ energy f`.
- [x] D3. Positivity on the cycle: if `v : ZMod N → ℝ` is nonzero, entrywise nonnegative and
  `gStd` (applied to `v` as a complex vector) equals `λ • v` for a real `λ`, then `0 < v j` for every
  `j` (a zero entry forces its two neighbours to vanish, all the way around `ZMod N`).
  File `BLTAudit/GStdPositive.lean`.
  - Done 2026-11-21 22:48 UTC at 0f6ab65: `gStd_eigvec_pos`, `gStd_eigvec_pos'`, `gStd_eigvec_eq_zero_of_zero`, `gStd_eigvec_zero_succ`. The eigenvalue equation is stated pointwise, `gStd (fun i => (v i : ℂ)) j = μ * v j`, and as an equation of vectors in the primed version.
- [-] D4. Simple positive ground state (§1): among real vectors, the minimizers of `energy` on the unit
  sphere form a line spanned by an entrywise strictly positive vector (a minimizer's modulus is a
  minimizer by D2 and A6, hence strictly positive by D3; two orthogonal vectors cannot both have
  constant sign). File `BLTAudit/GroundState.lean`. (split into D4a, D4b, D4c)
  - Split 2026-11-21: three separate steps (a minimizer is an eigenvector, a minimizer exists, positivity with uniqueness up to sign), about 300 lines in all, too large for one file of about 150 lines. Nothing was attempted and no Lean file was written; `BLTAudit/GroundState.lean` is now the file of D4c. Below, "real unit vector" means `v : ZMod N → ℝ` with `∑ j, v j ^ 2 = 1`, and "minimizer" means a real unit vector `v` with `energy (fun j => (v j : ℂ)) ≤ energy (fun j => (u j : ℂ))` for every real unit vector `u`.
- [x] D4a. A minimizer is an eigenvector: if `v` is a minimizer and `λ = energy (fun j => (v j : ℂ))`, then
  `gStd (fun i => (v i : ℂ)) j = λ * v j` for every `j` (in the form of the hypothesis of D3). Route: by
  `re_ip_gStd` of A6, for real `u` the energy is the real quadratic form
  `∑ j, (4 − 2 cos(2πj/N)) * u j ^ 2 − 2 * ∑ j, u j * u (j + 1)`; it scales by `t ^ 2`, so
  `B u = energy u − λ ∑ j, u j ^ 2 ≥ 0` with `B v = 0`; expanding `B (v + t • w) ≥ 0` in `t` gives
  `∑ j, w j * ((gStd v) j − λ v j) = 0` for all `w`, and `w = gStd v − λ v` ends it.
  File `BLTAudit/GroundEigen.lean`.
  - Done 2026-11-21 23:07 UTC at f6310c2: `ground_eigen`, `gStdR_eq_of_min`, `cross_eq`, `eq_zero_of_forall_quad_nonneg`, `quadR_lower`, and in the helper file `BLTAudit/RealQuadForm.lean` (imported by `BLTAudit/GroundEigen.lean`; the two files together were about 270 lines, too long for one): `energy_ofReal`, `gStd_ofReal`, `quadR_expand`, `sum_sq_expand`, `quadR_smul`, `sum_sq_smul`, `sum_quad`. Defined there: `oscDiag N j = 4 − 2 cos(2πj/N)`, `quadR u = ∑ j, oscDiag N j * u j ^ 2 − 2 * ∑ j, u j * u (j + 1)` (the energy of a real vector, `energy_ofReal`) and `gStdR u j = oscDiag N j * u j − u (j − 1) − u (j + 1)` (`gStd` on real vectors, `gStd_ofReal`). The eigenvalue is `energy (fun i => (v i : ℂ))`, cast to `ℂ`. The minimizer hypothesis is over real unit vectors only, as in the item.
- [x] D4b. A minimizer exists: for `0 < N` there is a minimizer (the real unit sphere in
  `ZMod N → ℝ` is closed, bounded and nonempty, hence compact, and `u ↦ energy (fun j => (u j : ℂ))`
  is continuous, being the real quadratic form of D4a; then `IsCompact.exists_isMinOn`).
  File `BLTAudit/GroundExists.lean`.
  - Done 2026-11-21 23:18 UTC at 5981bce: `exists_minimizer`, `exists_minimizer_quadR`, `isCompact_unitSphereR`, `unitSphereR_nonempty`, `continuous_quadR`. `0 < N` is the instance `[NeZero N]`. Compactness is for the sup norm of `ZMod N → ℝ`: the sphere is closed and lies in the closed ball of radius `1`.
- [x] D4c. Simple positive ground state, the statement of D4: there is a minimizer `w` with `0 < w j`
  for every `j`, and every minimizer `v` is `w` or `−w`. Route: for a minimizer `v`, `j ↦ |v j|` is a
  minimizer (`energy_norm_le` of D2), hence an eigenvector (D4a), hence strictly positive
  (`gStd_eigvec_pos` of D3), so no minimizer has a zero entry; for two minimizers `v`, `w`, the vector
  `v 0 • w − w 0 • v` lies in the same eigenspace and vanishes at `0`, so it is zero (otherwise its
  normalization would be a minimizer with a zero entry), and unit length leaves `v = ± w`.
  File `BLTAudit/GroundState.lean`.
  - Done 2026-11-21 23:23 UTC at a21c7ef: `ground_state`, `isGround_unique`, `isGround_ne_zero`, `ne_zero_of_eig`, `isGround_abs`, `quadR_abs_le`, `quadR_eq_sum_mul_gStdR`, `gStdR_comb`. `IsGround v` (defined in this file) says that `v` minimizes `quadR` on the real unit sphere. That `j ↦ |v j|` is again a minimizer is proved directly (`quadR_abs_le`: `v j * v (j + 1) ≤ |v j| * |v (j + 1)|`), not through `energy_norm_le` of D2. `ground_state` is a single statement: a minimizer `w` with `0 < w j` for every `j`, and every minimizer is `w` or `-w`. Only real vectors are compared, as in the item.

## E. Tools for the vortex lower bound

§4.2–§4.3. One-variable and model versions of the steps of Theorem 4.1; the degree lemma on the twisted
torus and the ball growth as a whole are listed under "Not attempted here".

- [x] E1. Circle energy: if `θ` is `C¹` on `[0, 2π]` and `θ (2π) − θ 0 = 2π Q`, then
  `2π Q² ≤ ∫ φ in 0..2π, (deriv θ φ) ^ 2` (expand `∫ (θ' − Q)² ≥ 0`). File `BLTAudit/CircleEnergy.lean`.
  - Done 2026-11-22 00:21 UTC at c1c8eca: `circle_energy`, `interval_energy_lower`, `integral_sq_sub_const`. "`θ` is `C¹` on `[0, 2π]`" is read as: `θ : ℝ → ℝ` is differentiable at every point of the closed interval and `deriv θ` is continuous on it. `interval_energy_lower` is the same bound on any `[a, b]` with `a ≤ b`: `(b − a) Q² ≤ ∫ x in a..b, (deriv θ x) ^ 2` when `θ b − θ a = (b − a) Q`. `Q` is any real number.
- [x] E2. Annulus logarithm (L13): for `0 < r < s` and `g` interval-integrable on `[r, s]` with
  `2π Q² ≤ g ρ` there, `2π Q² * log (s / r) ≤ ∫ ρ in r..s, g ρ / ρ`. File `BLTAudit/AnnulusEnergy.lean`.
  - Done 2026-11-22 00:25 UTC at 0cf0fcb: `annulus_energy`, `annulus_log_lower`, `integral_const_mul_inv`, `inv_continuousOn_of_pos`. `annulus_log_lower` is the same bound with any real constant `c` in place of `2π Q²`; the lower bound `c ≤ g ρ` is assumed on the closed interval `[r, s]`.
- [x] E3. Bilinear interpolation (L8)–(L10) with zero gauge error: for corner values
  `θ₀₀ θ₁₀ θ₀₁ θ₁₁` and the bilinear interpolant `θ` on `[0,1]²`,
  `(∂ₓθ)² + (∂ᵧθ)² ≤ W x y := (1−y) b_bot² + y b_top² + (1−x) b_left² + x b_right²`, and
  `∫∫ W = (b_bot² + b_top² + b_left² + b_right²) / 2`. File `BLTAudit/BilinearInterp.lean`.
  - Done 2026-11-22 00:30 UTC at be37af2: `bilinInterp_energy`, `bilinInterp_grad_le`, `integral_bilinW`, `integral_zero_one_affine`, `sq_convex_comb_le`, `hasDerivAt_bilinInterp_x`, `hasDerivAt_bilinInterp_y`, `bilinInterp_corners`. `bilinInterp` and `bilinW` are defined in this file, with `b_bot = θ₁₀ − θ₀₀`, `b_top = θ₁₁ − θ₀₁`, `b_left = θ₀₁ − θ₀₀`, `b_right = θ₁₁ − θ₁₀`. `∂ₓθ` and `∂ᵧθ` are `deriv` of the one-variable slices, and `∫∫ W` is the iterated interval integral `∫ y in 0..1, ∫ x in 0..1, W x y`.
- [x] E4. Ball merging (§4.3): in a real normed space, if `‖c₁ − c₂‖ ≤ r₁ + r₂` with `0 < r₁`, `0 < r₂`,
  then `c = c₁ + (r₂ / (r₁ + r₂)) • (c₂ − c₁)` has `‖c − c₁‖ ≤ r₂`, `‖c − c₂‖ ≤ r₁`,
  `ball c₁ r₁ ∪ ball c₂ r₂ ⊆ ball c (r₁ + r₂)`, and `r₁ − ‖x − c₁‖ ≤ (r₁ + r₂) − ‖x − c‖` for all `x`.
  File `BLTAudit/BallMerge.lean`.
  - Done 2026-11-22 00:35 UTC at 3a0dc8f: `ball_merge`, `ball_union_subset_merge`, `merge_margin_left`, `merge_margin_right`, `norm_sub_le_of_left`, `norm_mergeCenter_sub_left`, `norm_mergeCenter_sub_right`. The center `c` is `mergeCenter c₁ c₂ r₁ r₂`, defined in this file as in the item. `merge_margin_right` is the same margin inequality for the second ball, `r₂ − ‖x − c₂‖ ≤ (r₁ + r₂) − ‖x − c‖`.
- [x] E5. Final arithmetic of Theorem 4.1, (L17)–(L19), from named real hypotheses only: for real
  `d ≥ 3` and `0 ≤ C`, if `2π log T ≤ (1 + C / log d) * A + K`, `T = d / √(log d) / S₀`,
  `0 < S₀ ≤ C₂ (log d)³` and `A ≤ C₀ log d`, then
  `2π log d − 7π log (log d) − (2π log C₂ + C * C₀ + K) ≤ A`. File `BLTAudit/LowerBoundArithmetic.lean`.
  - Done 2026-11-22 00:35 UTC at e59f6ae: `lower_bound_arithmetic`, `log_T_eq`, `pos_of_le_mul_pow`, `log_S₀_le`, `div_mul_le_of_le_mul`. The four inputs of the item are hypotheses of `lower_bound_arithmetic` (`hT`, `hTdef`, `hS₀` with `hS`, `hA`); `0 < C₂` is derived from `0 < S₀ ≤ C₂ (log d)³`. Nothing about where these inputs come from is proved.

## F. Assembly: Theorem 1.1 from named hypotheses

§5. The statement layer and the last step of the proof, in the style of a hypothesis ledger: the two
analytic halves enter as named hypotheses, and Lean checks what follows from them.

- [x] F1. Statement layer: `Admissible f` (the vectors `gabor f n m`, `n m < d`, are orthonormal for
  `ip`), `scaledEnergy f = d ^ 2 * energy f` and `aMin d = ⨅ f : {f // Admissible f}, scaledEnergy f`,
  with `0 ≤ aMin d` and `aMin d ≤ scaledEnergy f` for admissible `f`. Definitions and these two facts
  only. File `BLTAudit/Statements.lean`.
  - Done 2026-11-22 01:01 UTC at 3cf8c2c: `aMin_nonneg`, `aMin_le`, `bddBelow_scaledEnergy`, `scaledEnergy_nonneg`. `Admissible f` is the orthonormality hypothesis of A5c, for naturals `n m n' m' < d`; `aMin d` is Mathlib's `iInf` on `ℝ`, which is `0` for an empty family. That admissible windows exist, that the infimum is attained, and the link with `‖zak f q r‖ = 1 / d` (A4d, A5c) are not stated.
- [x] F2. Relative optimality from two named bounds (§5): for real sequences `A a : ℕ → ℝ` with
  `a d ≤ A d`, `[HU] A d ≤ 2π log d + C₁` and `[HL] 2π log d − 7π log (log d) − C₂ ≤ a d` for all large
  `d`, conclude `0 ≤ A d − a d ≤ 7π log (log d) + C₁ + C₂` eventually and
  `Tendsto (fun d => A d / a d) atTop (𝓝 1)`. File `BLTAudit/RelativeOptimality.lean`.
  - Done 2026-11-22 01:25 UTC at 20f3344: `relative_optimality`, `tendsto_div_log_of_bounds`, `tendsto_loglog_div_log`, `tendsto_log_div_self`, `tendsto_inv_log_nat`, `tendsto_log_nat`. "For all large `d`" is `∀ᶠ d in atTop` on `ℕ`, with `log d` the real logarithm of `(d : ℝ)`; `a d ≤ A d` is also assumed only for large `d`. `A d / a d → 1` is proved through `A d / log d → 2π` and `a d / log d → 2π` (`tendsto_div_log_of_bounds`, reused by F3). [HU] and [HL] are hypotheses of the theorem; neither is proved.
- [x] F3. The limit constant from the same two bounds: if eventually
  `2π log d − 7π log (log d) − C ≤ a d ≤ 2π log d + C`, then
  `Tendsto (fun d => a d / log d) atTop (𝓝 (2π))`. File `BLTAudit/LimitConstant.lean`.
  - Done 2026-11-22 01:29 UTC at b8cc459: `limit_constant`, `limit_constant_of_bounds`. Both follow from `tendsto_div_log_of_bounds` of F2 with `C₁ = C₂ = C`; the two bounds are hypotheses.
- [x] F4. Conditional main theorem: combine F1–F3 into one statement about `aMin` and a candidate family
  `f_d`, whose only hypotheses are `[HU]` (the trial bound (U4) with (U14)) and `[HL]` (the lower bound
  (L19)), each a named structure field tagged `/-- [HU] ... -/`, `/-- [HL] ... -/`.
  File `BLTAudit/MainConditional.lean`.
  - Done 2026-11-22 01:30 UTC at 018bb61: `main_conditional`, `main_bounds`, `aSeq_eq`, `ASeq_eq`. The two named hypotheses are the fields `HU` and `HL` of the structure `MainHypotheses f C₁ C₂` (defined in this file, with docstrings tagged [HU] and [HL]); neither is proved, so Theorem 1.1 is not proved: `main_conditional` derives its shape (the two-sided bound, `aMin d / log d → 2π`, and `scaledEnergy (f d) / aMin d → 1`) from [HU] and [HL] only. `aSeq d` and `ASeq f d`, defined in this file, are `aMin d` and `scaledEnergy (f d)` of F1 as real sequences, `0` at `d = 0`. [HU] is assumed for all large `d`; the paper's use of `f_d` along odd `d` is not modelled.

## G. Toward [HU] and [HL]: one-run model steps

§3.2–§3.3 and §4.1–§4.3. Model statements of single steps in the proofs of (U4), (U14) and (L19), each
small enough for one file. None of them proves [HU] or [HL], and F4 keeps both as named hypotheses.

- [x] G1. Edge-angle comparison (L10): `edge_angle_sq_le`: for real `a η` with `|a| ≤ η` and `η ≤ 1`,
  `a ^ 2 ≤ (1 + η ^ 2) * (4 * Real.sin (a / 2) ^ 2)`; hence for a finset `s` and `a : ι → ℝ` with
  `|a e| ≤ η ≤ 1` on `s`, `∑ e ∈ s, a e ^ 2 ≤ (1 + η ^ 2) * ∑ e ∈ s, 4 * Real.sin (a e / 2) ^ 2`
  (`four_sin_half_sq` of B4 gives `4 sin²(a/2) = 2 − 2 cos a`, and Mathlib's `Real.cos_bound` gives
  `cos a ≤ 1 − a²/2 + (5/96) a⁴` for `|a| ≤ 1`; then `(1 + η²)(1 − (5/48) a²) ≥ 1` when `a² ≤ η² ≤ 1`).
  The paper's constant `C` is `1` here. File `BLTAudit/EdgeAngleComparison.lean`.
  - Done 2026-11-23 04:10 UTC at 098586a: `edge_angle_sq_le`, `sum_edge_angle_sq_le`, `weighted_edge_angle_sq_le`, `edge_angle_sq_le_self`, `sq_sub_quartic_le_four_sin_half_sq`, `cos_le_quartic` (verified 363/363). Proved with `C = 1` as stated; `weighted_edge_angle_sq_le` (weights `0 ≤ w e ≤ 1`, the coefficients with which (L8) counts an edge) and `edge_angle_sq_le_self` (`η = |a|`) are extra. (L10) itself, which edges are good, and the identification of `∑ 4 sin²(a_e/2)` with `zakEnergy` are not stated. Uses `four_sin_half_sq` of B4 and Mathlib's `Real.cos_bound`.
- [ ] G2. Defect count (L5), (L14): `defect_count`: for `0 ≤ η ≤ π`,
  `4 / π ^ 2 * η ^ 2 ≤ 4 * Real.sin (η / 2) ^ 2` (Mathlib's `Real.mul_le_sin` at `η / 2`); for finsets,
  `(L.biUnion inc).card ≤ 2 * L.card` when every `inc e` with `e ∈ L` has at most two elements
  (`Finset.card_biUnion_le`); hence for real `d ≥ 2`, `η = 1 / Real.log d`,
  `(L.card : ℝ) * (4 * Real.sin (η / 2) ^ 2) ≤ A` (the form of `card_large_edges_mul_le_zakEnergy` of B4)
  and `A ≤ C₀ * Real.log d`, `10 * ((L.biUnion inc).card : ℝ) ≤ 5 * π ^ 2 * C₀ * Real.log d ^ 3`: the bound
  `S₀ ≤ C₂ (log d)³` of (L14) with `C₂ = 5π² C₀`, in the form that `lower_bound_arithmetic` of E5 takes.
  Which edges are large and which plaquettes they meet is not modelled. File `BLTAudit/DefectCount.lean`.
- [ ] G3. Discrete Stokes on a rectangle, the rectangular case of the computation in (L12):
  `stokes_rect`: for `bq br : ℤ → ℤ → ℝ`, integers `q₀ r₀` and naturals `m n`,
  `∑ i ∈ range m, ∑ j ∈ range n, (bq (q₀+i) (r₀+j) + br (q₀+i+1) (r₀+j) − bq (q₀+i) (r₀+j+1) − br (q₀+i) (r₀+j))`
  `= ∑ i ∈ range m, (bq (q₀+i) r₀ − bq (q₀+i) (r₀+n)) + ∑ j ∈ range n, (br (q₀+m) (r₀+j) − br q₀ (r₀+j))`
  (telescope in each variable, `Finset.sum_range_sub`); hence if `aq ar : ℤ → ℤ → ℝ` and `n : ℤ → ℤ → ℤ`
  satisfy (L3), `aq q r + ar (q+1) r − aq q (r+1) − ar q r = −2π/d² + 2π * n q r` with `d : ℕ`, on the
  plaquettes of the rectangle, then for the local gauge `A′q q r = 2π (r − c) / d²`, `A′r = 0` (any real
  `c`, as in (L7)) the boundary sum of `bq = aq − A′q`, `br = ar` equals
  `2π * ∑ i ∈ range m, ∑ j ∈ range n, n (q₀+i) (r₀+j)`. The cellular chain of a disk, the degree of the
  interpolated map and Lemma 4.2 itself are not attempted. File `BLTAudit/DiscreteStokes.lean`.
- [ ] G4. Cell step of the singular Riemann sum (U10): `inv_sq_cell`: for `z w : ℂ` and `0 < h` with
  `4 * h ≤ ‖z‖` and `‖w − z‖ ≤ h`, `|(‖w‖ ^ 2)⁻¹ − (‖z‖ ^ 2)⁻¹| ≤ 4 * h / ‖z‖ ^ 3` (`‖w‖` lies between
  `3‖z‖/4` and `5‖z‖/4`); hence for a measurable `Q ⊆ Metric.closedBall z h` with `volume Q < ⊤`,
  `|∫ w in Q, (‖w‖ ^ 2)⁻¹ − (volume Q).toReal * (‖z‖ ^ 2)⁻¹| ≤ 4 * h / ‖z‖ ^ 3 * (volume Q).toReal`
  (the zero `z₀` of (U10) is moved to `0`; a grid square of side `h` centred at `z` lies in
  `closedBall z h` and has measure `h²`). The shell count, the strips at the two circles and (U10) itself
  are not attempted. File `BLTAudit/SingularCell.lean`.
- [ ] G5. Transfer estimate (U14), abstract form: `transfer_estimate`: in a normed additive group `V`,
  for additive maps `S₁ S₂ : V →+ V` with `‖S₁ x‖ = ‖x‖` and `‖S₂ x‖ = ‖x‖` for all `x`, put
  `E v = ‖S₁ v − v‖ ^ 2 + ‖S₂ v − v‖ ^ 2`; then `E δ ≤ 8 * ‖δ‖ ^ 2` and
  `|E (u + δ) − E u| ≤ 2 * Real.sqrt (E u) * Real.sqrt (E δ) + E δ` (from
  `|‖x‖ − ‖y‖| ≤ ‖x + y‖ ≤ ‖x‖ + ‖y‖` in each component and Cauchy–Schwarz in `ℝ²`); hence if
  `E u ≤ K * L`, `‖δ‖ ^ 2 ≤ K * h ^ 2 * L`, `0 ≤ K`, `0 ≤ L` and `0 ≤ h ≤ 1`, then
  `|E (u + δ) − E u| ≤ (4 * Real.sqrt 2 + 8) * K * h * L`, the shape `O(h log(1/h))` of (U14) with
  `L = log (1/h)`. The twisted shifts of (U3), the bound (U13) on `‖W − U‖` and (U4) are not attempted.
  File `BLTAudit/TransferEstimate.lean`.

## H. The milestone along odd `d` and the actual candidate

Added 2026-11-23 at the author's request (interactive session, not the hourly task). Goal: the
milestone `a_d / log d → 2π` along odd `d` from the Gaussian trial upper bound and the universal
lower bound, before the oscillator approximation; and a final statement aligned with the paper (the
actual candidate `f_d`, odd `d` only, and its `2π log d + O(1)` energy recorded separately). F4 stays
as it was; H3 is the ledger to shrink from now on. Its five inputs are [HZ], [HV], [HL] (enough
for the milestone) and [HN], [HE] (for `f_d`).
After H4–H10 (2026-11-23) the ledger reads: milestone from [HZ], [HV] (equivalently a bound on
`zakEnergy d (zakExt d (gaussPhase d))`, H5) and [HLζ] (Theorem 4.1 for twisted arrays, H4); for `f_d`
add [HA] (uniform Zak approximation, H10, which with [HZ] gives [HN]) and [HE]. Under [HZ],
`|F(x,y)| ≥ c · dist((x,y), z₀)` on the square (H7) and `|F| ≥ c/(2d)` on the odd grid (H9) are proved.
After H11–H14: `main_odd_reduced` derives Theorem 1.1 along odd `d` for `f_d` from [HZ], [HA], [HV₂]
(two-sided (3.3) for the explicit Gaussian phase array), [HW] (an `ℓ²` bound on `W − u₀ U`) and [HLζ].

- [x] H1. Inverse Zak transform and windows with a prescribed Zak array: `zakEquiv`, `zakInv`,
  `zak_zakInv` (`Z (Z⁻¹ G) = G`), `ph`, `norm_ph`, `zakInv_admissible` (a unit-modulus array `u` gives
  the admissible window `Z⁻¹ (d⁻¹ u)`), `le_aMin_of_forall`. File `BLTAudit/ZakInverse.lean`.
  - Done 2026-11-23 02:43 UTC at 2d31964 (verified 295/295).
- [x] H2. The actual windows: `groundR` (the positive unit ground vector of D4c, with
  `groundR_sq_sum`, `groundR_pos`, `groundR_min`), `hermiteCand d = Z⁻¹ (d⁻¹ ph (Z g_d))`, `hermiteFam`,
  `gaussPhase`, `gaussCand`; `hermiteCand_admissible` (no zero of `Z g_d` ⇒ admissible),
  `GaussZeroUnique`, `gaussZak_grid_ne_zero` and `gaussCand_admissible` (odd `d` and [HZ] ⇒
  admissible). File `BLTAudit/Candidates.lean`. A numerical check of these exact definitions gave
  `d² E − 2π log d = 0.29, 0.15, 0.047, −0.020, −0.037` at `d = 5, 7, 11, 21, 31` for both windows.
  - Done 2026-11-23 02:43 UTC at 2d31964 (verified 295/295).
- [x] H3. The odd-`d` ledger: structures `GaussianTrialHyp C` (fields [HZ] `zero_unique`, [HV]
  `vortex`), `LowerBoundHyp` ([HL], Theorem 4.1 window by window under `scaledEnergy f ≤ K log d`),
  `HermiteHyp C` ([HN] `nonvanish`, [HE] `energy_asymp`); `tendsto_odd_of_bounds`,
  `milestone_odd_bounds`, `milestone_odd` (`aSeq (2k+1) / log (2k+1) → 2π` from [HZ], [HV], [HL]
  only), `main_odd_conditional` (adds [HN], [HE]: `f_d` admissible, `|d² E(f_d) − 2π log d| ≤ C_H`,
  the bounds on `a_d`, `0 ≤ d² E(f_d) − a_d ≤ 7π log log d + O(1)`, both limits along odd `d`).
  File `BLTAudit/MainOdd.lean`.
  - Done 2026-11-23 02:43 UTC at 2d31964 (verified 295/295). Nothing here proves the milestone, Theorem 1.1 or Theorem 4.1: all five inputs are named hypotheses.
- [x] H4. [HL] in Zak coordinates: `lowerBound_of_zak`: let [HLζ] be the statement "for every `K`
  there are `C`, `D` such that for `d ≥ D` every `ζ` with `IsTwisted d ζ` and
  `zakEnergy d ζ ≤ K log d` has `2π log d − 7π log log d − C ≤ zakEnergy d ζ`" (Theorem 4.1 exactly as
  §4 states it); prove `[HLζ] → LowerBoundHyp`. For admissible `f`, build `ζ` from `d * zak f` by the
  two gluing rules (define `zakExt d u : ℤ × ℤ → ℂ` by `q ↦ q mod d` and the factor
  `exp (−2πi q ⌊r/d⌋ / d)`), show `IsTwisted d (zakExt ...)` using A5c (unit modulus), and use
  `zak_energy_identity_of_isTwisted` of A7c. File `BLTAudit/LowerBoundZak.lean`.
  - Done 2026-11-23 03:07 UTC at a11b7e1 (verified 309/309): `zakExt`, `twistFactor`, `isTwisted_zakExt`, `zakExt_of_lt`, `scaledEnergy_eq_zakEnergy`, `ZakLowerBoundHyp`, `lowerBound_of_zak`. The input [HL] of H3 may now be replaced by [HLζ].
- [x] H5. [HV] as a statement about the explicit phase array: `scaledEnergy_zakInv`: for
  unit-modulus `u`, `scaledEnergy (zakInv (fun q r => d⁻¹ * u q r)) = zakEnergy d (zakExt d u)` (H1,
  H4's `zakExt`, A7c); hence `vortex` of H3 is equivalent to a bound on
  `zakEnergy d (zakExt d (gaussPhase d))`, with no Fourier transform left. `vortex_iff_zakEnergy`.
  File `BLTAudit/GaussVortexZak.lean`.
  - Done 2026-11-23 03:07 UTC at a11b7e1 (verified 309/309): `scaledEnergy_zakInv`, `gaussCand_scaledEnergy_eq`, `vortex_iff_zakEnergy`, `zakEnergy_eq_sum_range`.
- [x] H6. Linear lower bound near the zero, the local half of `|F(z)| ≥ c |z − z₀|`: from C4 and C5
  (`hasDerivAt_gaussZak_fst`, `deriv_gaussZak_fst_zero_ne_zero`), there are `ρ > 0`, `c > 0` with
  `c * ‖(x − 1/2, y − 1/2)‖ ≤ ‖gaussZak x y‖` for `‖(x − 1/2, y − 1/2)‖ ≤ ρ` (differentiability of the
  holomorphic `Θ` of C4 at the zero, `HasDerivAt.isLittleO`). `gaussZak_ge_linear_near_zero`.
  File `BLTAudit/GaussLinearNearZero.lean`.
  - Done 2026-11-23 03:12 UTC at 95e8ecc (verified 317/317): `zakZeroPt`, `thetaI`, `thetaI_zakZeroPt`, `thetaI'_zakZeroPt_ne_zero`, `thetaI_ge_linear_near_zero`, `gauss_ge_of_abs_le`, `gaussZak_ge_linear_near_zero`, `norm_sub_zakZeroPt_sq`. The bound is stated with `‖(y − x i) − z₀‖` in `ℂ`; the constant is `(‖θ'(z₀)‖/2) · 2^{1/4} e^{−4π}`.
- [x] H7. The global half under [HZ]: `gaussZak_ge_linear`: assuming `GaussZeroUnique`, there is
  `c > 0` with `c * dist (x, y) (1/2, 1/2) ≤ ‖gaussZak x y‖` on `[0,1]²` (continuity of `gaussZak`
  from C1, compactness of `[0,1]² \ ball z₀ ρ`, H6 inside the ball; points with `x = 1` or `y = 1`
  through C2). File `BLTAudit/GaussLinearGlobal.lean`.
  - Done 2026-11-23 03:21 UTC at c453ac5 (verified 329/329): `gaussZak_ne_zero_of_closed`, `continuous_gaussZak_pair`, `continuous_thetaI`, `continuous_gauss`, `norm_sub_zakZeroPt_le_two`, `gaussZak_ge_linear`. On the closed square `[0,1]²`, with `GaussZeroUnique` as the hypothesis.
- [x] H8. [HZ] as a statement about `jacobiTheta₂`: `gaussZeroUnique_iff_theta`: by C1,
  `GaussZeroUnique` holds iff `jacobiTheta₂ z I ≠ 0` for every `z = y − x I` with `x y ∈ [0,1)`,
  `(x, y) ≠ (1/2, 1/2)` (the prefactor `gauss x` is positive, `gauss_pos` of C3). This isolates the
  Jacobi-triple-product input as a single statement about Mathlib's theta function.
  File `BLTAudit/GaussZeroTheta.lean`.
  - Done 2026-11-23 03:21 UTC at c453ac5 (verified 329/329): `gaussZak_eq_zero_iff`, `gaussZeroUnique_iff_theta`, `jacobiTheta₂_zakZeroPt`. Stated with `¬ (x = 1/2 ∧ y = 1/2)`.
- [x] H9. The grid lower bound under [HZ]: `odd_grid_abs_sub_half` (`|a/d − 1/2| ≥ 1/(2d)` for odd `d`),
  `odd_grid_norm_sub_zakZeroPt`, `gaussZak_grid_lower` (there is `c > 0` with `c/(2d) ≤ |F(r/d, (−q)/d)|`
  for every odd `d` and all `q r`), the quantitative form of `gaussZak_grid_ne_zero` of H2.
  File `BLTAudit/GaussGridLower.lean`.
  - Done 2026-11-23 03:27 UTC at 56398d6 (verified 332/332). The constant is `1/2` in place of the paper's `1/√2`.
- [x] H10. [HN] from the uniform Zak approximation: structure `ZakApproxHyp C` ([HA]: for large odd `d`
  there is `c_d ≠ 0` with `‖c_d⁻¹ · d · zak g_d q r − F(r/d, (−q)/d)‖ ≤ C/d²`, Lemma 3.1 with (3.4));
  `nonvanish_of_approx : [HZ] → [HA] → nonvanish`, `hermiteHyp_of_approx`.
  File `BLTAudit/NonvanishFromApprox.lean`.
  - Done 2026-11-23 03:31 UTC at 10fe472 (verified 334/334). The input [HN] of H3 is now replaced by [HA] (plus [HZ]).
- [x] H11. Phase perturbation: `norm_ph_sub_ph_le`: for `a b : ℂ` with `b ≠ 0`,
  `‖ph a − ph b‖ ≤ 2 * ‖a − b‖ / ‖b‖` (write `ph a − ph b = (a − b)/‖a‖ + b (1/‖a‖ − 1/‖b‖)` and use
  `|‖a‖ − ‖b‖| ≤ ‖a − b‖`; the case `a = 0` gives `‖ph a − ph b‖ = 1 ≤ 2‖b‖/‖b‖`). Hence
  `norm_ph_sub_ph_le_of_approx`: if `‖a − b‖ ≤ ε` and `m ≤ ‖b‖` with `0 < m`, then
  `‖ph a − ph b‖ ≤ 2 ε / m`; and `ph_mul_pos`: `ph (c * a) = ph c * ph a` for `c ≠ 0`, so a nonzero
  scalar `c_d` changes `ph` by a constant unimodular factor. File `BLTAudit/PhasePerturbation.lean`.
  - Done 2026-11-23 03:58 UTC at ec9f03f (verified 357/357): `ph_zero`, `norm_ph_le_one`, `ph_mul` (for all `c a`, not only `c ≠ 0`), `ph_natCast_mul`, `norm_ph_sub_ph_le`, `norm_ph_sub_ph_le_of_approx`.
- [x] H12. Energy of a constant phase change: `zakEnergy_const_mul`: for unimodular `u₀`,
  `zakEnergy d (fun p => u₀ * ζ p) = zakEnergy d ζ` (`‖u₀ (a − b)‖ = ‖a − b‖` edge by edge); and
  `scaledEnergy_const_mul` for windows: `scaledEnergy (fun j => u₀ * f j) = scaledEnergy f`. Hence
  the scalar `c_d` of [HA] does not change the energy of `hermiteCand d`. File `BLTAudit/EnergyConstPhase.lean`.
  - Done 2026-11-23 03:58 UTC at ec9f03f (verified 357/357), in `BLTAudit/ZakEnergyCompare.lean` together with H13: `zakEnergy_const_mul`, `zakExt_const_mul`, `zakExt_add`, `zakExt_neg`. The window form `scaledEnergy_const_mul` was not needed and is not stated.
- [x] H13. Zak-energy comparison, the concrete form of G5 for twisted arrays: `zakEnergy_sqrt_sub_le`:
  for `ζ ζ' : ℤ × ℤ → ℂ`, `|√(zakEnergy d ζ) − √(zakEnergy d ζ')| ≤ √(zakEnergy d (ζ − ζ'))` (the energy is
  the squared `ℓ²` norm of the edge-difference vector, which is linear in `ζ`; triangle inequality for
  the `ℓ²` norm on `Fin (2 d²) → ℂ` or `EuclideanSpace`), and `zakEnergy_le_eight_sum`:
  `zakEnergy d δ ≤ 8 * ∑ q ∈ range (d+1), ∑ r ∈ range (d+1), ‖δ (q, r)‖ ^ 2` from `‖a − b‖² ≤ 2‖a‖² + 2‖b‖²`
  (`mag` is unimodular). File `BLTAudit/ZakEnergyCompare.lean`.
  - Done 2026-11-23 03:58 UTC at ec9f03f (verified 357/357): `sq_norm_add_le_mul` (`‖x+y‖² ≤ (1+t)‖x‖² + (1+t⁻¹)‖y‖²`), `zakEnergy_add_le` (the same for `zakEnergy`, in place of the square-root triangle inequality), `sq_norm_sub_le`, `norm_zakExt_eq`, `zakEnergy_zakExt_le` (`A(zakExt u) ≤ 8 ∑ ‖u‖²` over `ZMod d`, not over `range (d+1)`). `norm_mag` is reused from `BLTAudit/EdgeEnergy.lean`.
- [x] H14. [HE] from [HV], [HA], [HZ] and a named pointwise phase bound: with `W = ph (d · zak g_d)` and
  `U = gaussPhase d`, H11 and H9 give `‖W q r − U q r‖ ≤ (4 C/c) / d` for large odd `d`; combine with
  H12, H13 and `vortex` to show `|scaledEnergy (hermiteCand d) − 2π log d| ≤ C'` requires the
  `O(h √log d)` bound on `‖W − U‖_{ℓ²}` (dyadic summation, §3.2). State that bound as the named input
  `[HW] : ∑ q r, ‖W q r − U q r‖² ≤ C h² log d` and prove `energy_asymp_of_W : [HV] → [HW] → [HA] →
  [HZ] → energy_asymp` (the field [HE] of H3), using H13 and `√(a) ≤ √(2π log d + C)`. The lower half
  `2π log d − C ≤ scaledEnergy (hermiteCand d)` comes from `milestone_odd_bounds` and `aMin_le` of F1.
  File `BLTAudit/EnergyFromTransfer.lean`.
  - Done 2026-11-23 03:58 UTC at ec9f03f (verified 357/357): `hermiteCand_scaledEnergy_eq`, `zakEnergy_compare`, `div_le_of_le_two_pi_log`, `energy_close_arith`, structure `TransferHyp C₁ C` ([HV₂] `vortex2`: two-sided (3.3) for the Gaussian phase; [HW] `phase_l2`: `∃ u₀` unimodular with `∑ ‖ph (zak g_d) − u₀ U‖² ≤ C log d / d²`), `energy_asymp_of_transfer` ([HV₂] + [HW] → [HE] with constant `3C₁ + 4π + 32|C|`; [HA] and [HZ] are not needed for this step), `gaussianTrialHyp_of_transfer`, `hermiteHyp_of_transfer`, `main_odd_reduced` (Theorem 1.1 along odd `d` for `f_d` from [HZ], [HA], [HV₂], [HW], [HLζ]). The one-sided [HV] of H3 is not enough for [HE]: the lower half needs (3.3) two-sided. A numerical check with `u₀ = 1` gives `d² ∑ ‖W − U‖² / log d ≈ 6e-5, 3e-5, 2.2e-5` at `d = 5, 15, 41`.

- [ ] H15. The Gaussian phase near the zero, the first step of (3.3): `gaussPhase_near_zero`: with
  `z = y − x i` and `V(z) = ph (z − z₀)`, there are a unimodular `κ`, `ρ > 0` and `K` with
  `‖ph (gaussZak x y) − κ · V(z)‖ ≤ K ‖z − z₀‖` for `0 < ‖z − z₀‖ < ρ` (`V` or its conjugate)
  (from `thetaI_ge_linear_near_zero` of H6, `norm_ph_sub_ph_le` of H11 and the second-order Taylor bound
  of `θ` at `z₀`, `HasDerivAt` of `θ'`). Fix the exact unimodular constant and the orientation (`V` or
  its conjugate) by a numerical check first and record it in the docstring.
  File `BLTAudit/GaussPhaseNearZero.lean`.
- [ ] H16. The lattice sum of the model vortex, the main term of (3.3): `vortex_grid_sum`: for odd `d`,
  the Zak energy of the pure model phase `V` sampled on the odd grid around `z₀` (with the gauge of
  `zakExt`) restricted to the annulus `4h ≤ |z − z₀| ≤ R` equals `2π log (R/(4h)) + O(1)`; first state
  and prove only the cell step `inv_sq_cell` of G4 and the shell count `#{grid points with
  ρ ≤ |z − z₀| < 2ρ} ≤ C (ρ/h)²`. File `BLTAudit/VortexGridSum.lean`.
- [ ] H17. [HW] from [HA], [HZ] and a pointwise phase bound with the `1/r` profile: state
  [HWpt] `‖ph (zak g_d q r) − u₀ U q r‖ ≤ K h² / dist(grid point, z₀)` and prove
  `phase_l2_of_pointwise : [HWpt] → [HW]` from the dyadic count `∑_{grid} h²/dist² ≤ C log d` (the same
  shell count as H16). File `BLTAudit/PhaseL2FromPointwise.lean`.

## Not attempted here

- Uniqueness and simplicity of the Gaussian Zak zero in the unit square (Jacobi triple product, Appendix A.3), unless Mathlib already has the triple product.
- Spectral convergence `λ₀,d → 2π`, `λ₁,d → 6π` (A4), the fourth-order approximate ground vector (A5)–(A7), and the uniform Zak approximation (A9).
- The trial-energy asymptotic (U4) and its transfer to the finite-Hermite phase (U12)–(U14): hypothesis `[HU]`.
- The cellular degree lemma on the twisted torus (L12) and the ball-growth argument (L14)–(L16) as a whole, hence Theorem 4.1: hypothesis `[HL]`.
- Theorem 1.1 without hypotheses.
