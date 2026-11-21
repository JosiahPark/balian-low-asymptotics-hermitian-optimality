# Lean verification status: PASS

Checked 2026-11-21 02:07 UTC at commit `1c05ccb674f4`.

- Build: ok
- Theorems verified with standard axioms only: 80 of 80
- Nothing here proves Theorem 1.1 or Theorem 4.1 of the paper.

## Theorems

| file | theorem | status |
|---|---|---|
| BLTAudit/Basic.lean | `BLT.transl_apply` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.diffOp_apply` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.modul_apply` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.energy_nonneg` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.zakEnergy_nonneg` | verified (standard axioms only) |
| BLTAudit/EnergyZakCoordinates.lean | `BLT.zak_sub` | verified (standard axioms only) |
| BLTAudit/EnergyZakCoordinates.lean | `BLT.sum_norm_sq_diffOp_eq_zak` | verified (standard axioms only) |
| BLTAudit/EnergyZakCoordinates.lean | `BLT.sum_norm_sq_diffOp_dftU_eq_zak` | verified (standard axioms only) |
| BLTAudit/EnergyZakCoordinates.lean | `BLT.energy_eq_sum_zak` | verified (standard axioms only) |
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
| BLTAudit/GStandardForm.lean | `BLT.sum_zmod_add_one` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.complex_norm_sub_sq` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.stdAddChar_eq_exp_ofReal` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.norm_sq_one_sub_stdAddChar` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.sum_norm_sq_diffOp_dftU` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.sum_norm_sq_diffOp` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.sum_re_conj_mul_sub_one` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.sum_im_conj_mul_sub_one` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.re_ip_gStd` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.im_ip_gStd` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.energy_eq_re_ip_gStd` | verified (standard axioms only) |
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
| BLTAudit/ZakCriterionConverse.lean | `BLT.zmod_val_eq_zero_iff` | verified (standard axioms only) |
| BLTAudit/ZakCriterionConverse.lean | `BLT.zak_norm_of_ip_gabor` | verified (standard axioms only) |
| BLTAudit/ZakCriterionConverse.lean | `BLT.ip_gabor_orthonormal_iff_zak_norm` | verified (standard axioms only) |
| BLTAudit/ZakCriterionConverse.lean | `BLT.norm_natCast_mul_zak_eq_one_iff` | verified (standard axioms only) |
| BLTAudit/ZakCriterionConverse.lean | `BLT.ip_gabor_orthonormal_iff_unit_modulus` | verified (standard axioms only) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.sum_zmod_eq_sum_range` | verified (standard axioms only) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.sum_sum_zmod_eq_sum_range` | verified (standard axioms only) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.zak_energy_identity` | verified (standard axioms only) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.zak_energy_identity_of_isTwisted` | verified (standard axioms only) |
| BLTAudit/ZakSeams.lean | `BLT.zmod_val_natCast_of_lt` | verified (standard axioms only) |
| BLTAudit/ZakSeams.lean | `BLT.norm_sq_natCast_mul` | verified (standard axioms only) |
| BLTAudit/ZakSeams.lean | `BLT.stdAddChar_neg_natCast` | verified (standard axioms only) |
| BLTAudit/ZakSeams.lean | `BLT.zeta_r_succ` | verified (standard axioms only) |
| BLTAudit/ZakSeams.lean | `BLT.mag_mul_zeta_q_succ` | verified (standard axioms only) |
| BLTAudit/ZakSeams.lean | `BLT.norm_sq_zeta_r_edge` | verified (standard axioms only) |
| BLTAudit/ZakSeams.lean | `BLT.norm_sq_zeta_q_edge` | verified (standard axioms only) |
