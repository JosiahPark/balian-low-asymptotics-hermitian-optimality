# Lean verification status: PASS

Checked 2026-11-20 21:58 UTC at commit `5013a3bbce07`.

- Build: ok
- Theorems verified with standard axioms only: 49 of 49
- Nothing here proves Theorem 1.1 or Theorem 4.1 of the paper.

## Theorems

| file | theorem | status |
|---|---|---|
| BLTAudit/Basic.lean | `BLT.transl_apply` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.diffOp_apply` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.modul_apply` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.energy_nonneg` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.zakEnergy_nonneg` | verified (standard axioms only) |
| BLTAudit/FiniteZakModulation.lean | `BLT.stdAddChar_natCast` | verified (standard axioms only) |
| BLTAudit/FiniteZakModulation.lean | `BLT.zak_modul` | verified (standard axioms only) |
| BLTAudit/FiniteZakTranslation.lean | `BLT.zak_transl_of_lt` | verified (standard axioms only) |
| BLTAudit/FiniteZakTranslation.lean | `BLT.zak_transl_seam` | verified (standard axioms only) |
| BLTAudit/FiniteZakUnitary.lean | `BLT.zakIndex_lt` | verified (standard axioms only) |
| BLTAudit/FiniteZakUnitary.lean | `BLT.zakIndex_injective` | verified (standard axioms only) |
| BLTAudit/FiniteZakUnitary.lean | `BLT.zakIndex_bijective` | verified (standard axioms only) |
| BLTAudit/FiniteZakUnitary.lean | `BLT.zak_eq_dftU` | verified (standard axioms only) |
| BLTAudit/FiniteZakUnitary.lean | `BLT.parseval_zak` | verified (standard axioms only) |
| BLTAudit/FourierUniqueness.lean | `BLT.sum_stdAddChar_inversion` | verified (standard axioms only) |
| BLTAudit/FourierUniqueness.lean | `BLT.sum_sum_stdAddChar_inversion` | verified (standard axioms only) |
| BLTAudit/FourierUniqueness.lean | `BLT.sum_sum_ite_zero` | verified (standard axioms only) |
| BLTAudit/FourierUniqueness.lean | `BLT.fourier_uniqueness_two` | verified (standard axioms only) |
| BLTAudit/GaborBasis.lean | `BLT.ip_zero_right` | verified (standard axioms only) |
| BLTAudit/GaborBasis.lean | `BLT.ip_sum_smul_right` | verified (standard axioms only) |
| BLTAudit/GaborBasis.lean | `BLT.linearIndependent_of_ip_orthonormal` | verified (standard axioms only) |
| BLTAudit/GaborBasis.lean | `BLT.linearIndependent_gabor` | verified (standard axioms only) |
| BLTAudit/GaborBasis.lean | `BLT.span_gabor_eq_top` | verified (standard axioms only) |
| BLTAudit/GaborFormula.lean | `BLT.transl_iterate_apply` | verified (standard axioms only) |
| BLTAudit/GaborFormula.lean | `BLT.modul_iterate_apply` | verified (standard axioms only) |
| BLTAudit/GaborFormula.lean | `BLT.gabor_apply` | verified (standard axioms only) |
| BLTAudit/GaborZakCoordinates.lean | `BLT.zakIndex_add_natCast_mul` | verified (standard axioms only) |
| BLTAudit/GaborZakCoordinates.lean | `BLT.stdAddChar_natCast_mul_self` | verified (standard axioms only) |
| BLTAudit/GaborZakCoordinates.lean | `BLT.stdAddChar_mul_zakIndex` | verified (standard axioms only) |
| BLTAudit/GaborZakCoordinates.lean | `BLT.gabor_zakIndex` | verified (standard axioms only) |
| BLTAudit/GaborZakModulus.lean | `BLT.ip_gabor_eq_sum_zak` | verified (standard axioms only) |
| BLTAudit/GaborZakModulus.lean | `BLT.ip_gabor_val_zero` | verified (standard axioms only) |
| BLTAudit/TimeFrequency.lean | `BLT.transl_modul` | verified (standard axioms only) |
| BLTAudit/TimeFrequency.lean | `BLT.transl_dftU` | verified (standard axioms only) |
| BLTAudit/TimeFrequency.lean | `BLT.dftU_sub` | verified (standard axioms only) |
| BLTAudit/TimeFrequency.lean | `BLT.diffOp_dftU` | verified (standard axioms only) |
| BLTAudit/UnitaryDFT.lean | `BLT.sum_stdAddChar_mul` | verified (standard axioms only) |
| BLTAudit/UnitaryDFT.lean | `BLT.conj_stdAddChar` | verified (standard axioms only) |
| BLTAudit/UnitaryDFT.lean | `BLT.dft_norm_sq` | verified (standard axioms only) |
| BLTAudit/UnitaryDFT.lean | `BLT.sum_conj_stdAddChar_mul` | verified (standard axioms only) |
| BLTAudit/UnitaryDFT.lean | `BLT.ip_dftU` | verified (standard axioms only) |
| BLTAudit/UnitaryDFT.lean | `BLT.parseval_dftU` | verified (standard axioms only) |
| BLTAudit/ZakCorrelation.lean | `BLT.dftU_shift` | verified (standard axioms only) |
| BLTAudit/ZakCorrelation.lean | `BLT.zak_correlation` | verified (standard axioms only) |
| BLTAudit/ZakCorrelation.lean | `BLT.zak_correlation_of_norm` | verified (standard axioms only) |
| BLTAudit/ZakCriterion.lean | `BLT.natCast_zmod_eq_iff_of_lt` | verified (standard axioms only) |
| BLTAudit/ZakCriterion.lean | `BLT.ip_eq_sum_zakIndex` | verified (standard axioms only) |
| BLTAudit/ZakCriterion.lean | `BLT.ip_gabor_eq_sum` | verified (standard axioms only) |
| BLTAudit/ZakCriterion.lean | `BLT.ip_gabor_of_zak_norm` | verified (standard axioms only) |
