# Lean verification status: PASS

Checked 2026-11-20 03:59 UTC at commit `fad127e4f3ee`.

- Build: ok
- Theorems verified with standard axioms only: 52 of 52
- Nothing here proves Theorem 1.1 or Theorem 4.1 of the paper.

## Theorems

| file | theorem | status |
|---|---|---|
| BLTAudit/BallMerge.lean | `BLT.norm_mergeCenter_sub_left` | verified (standard axioms only) |
| BLTAudit/BallMerge.lean | `BLT.norm_mergeCenter_sub_right` | verified (standard axioms only) |
| BLTAudit/BallMerge.lean | `BLT.margin_mergeBall_left` | verified (standard axioms only) |
| BLTAudit/BallMerge.lean | `BLT.margin_mergeBall_right` | verified (standard axioms only) |
| BLTAudit/BallMerge.lean | `BLT.ball_union_subset_mergeBall` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.transl_apply` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.diffOp_apply` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.modul_apply` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.energy_nonneg` | verified (standard axioms only) |
| BLTAudit/Basic.lean | `BLT.zakEnergy_nonneg` | verified (standard axioms only) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_exp_sub_one_sq` | verified (standard axioms only) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_sub_sq_eq_four_sin_sq` | verified (standard axioms only) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_mag` | verified (standard axioms only) |
| BLTAudit/EdgeEnergy.lean | `BLT.zakEnergy_eq_sin_sq` | verified (standard axioms only) |
| BLTAudit/FiniteZak.lean | `BLT.stdAddChar_natCast` | verified (standard axioms only) |
| BLTAudit/FiniteZak.lean | `BLT.zakIndex_lt` | verified (standard axioms only) |
| BLTAudit/FiniteZak.lean | `BLT.zakIndex_injective` | verified (standard axioms only) |
| BLTAudit/FiniteZak.lean | `BLT.zakIndex_bijective` | verified (standard axioms only) |
| BLTAudit/FiniteZak.lean | `BLT.zak_eq_dftU` | verified (standard axioms only) |
| BLTAudit/FiniteZak.lean | `BLT.parseval_zak` | verified (standard axioms only) |
| BLTAudit/FiniteZak.lean | `BLT.zak_transl_of_lt` | verified (standard axioms only) |
| BLTAudit/FiniteZak.lean | `BLT.zak_transl_seam` | verified (standard axioms only) |
| BLTAudit/FiniteZak.lean | `BLT.zak_modul` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.stdAddChar_add_neg` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.normSq_one_sub_stdAddChar` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.sum_norm_sq_eq` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.energy_eq_ip_gStd` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.energy_eq_re_ip_gStd` | verified (standard axioms only) |
| BLTAudit/GStandardForm.lean | `BLT.im_ip_gStd` | verified (standard axioms only) |
| BLTAudit/LimitConstant.lean | `BLT.tendsto_loglog_div_log` | verified (standard axioms only) |
| BLTAudit/LimitConstant.lean | `BLT.limit_constant` | verified (standard axioms only) |
| BLTAudit/LowerBoundArithmetic.lean | `BLT.log_stopTime` | verified (standard axioms only) |
| BLTAudit/LowerBoundArithmetic.lean | `BLT.lower_bound_arithmetic` | verified (standard axioms only) |
| BLTAudit/RelativeOptimality.lean | `BLT.gap_bound` | verified (standard axioms only) |
| BLTAudit/RelativeOptimality.lean | `BLT.relative_optimality` | verified (standard axioms only) |
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
| BLTAudit/ZakEnergyIdentity.lean | `BLT.zak_sub` | verified (standard axioms only) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.sum_range_eq_sum_zmod` | verified (standard axioms only) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.exp_neg_eq_stdAddChar` | verified (standard axioms only) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.zeta_r_succ` | verified (standard axioms only) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.zeta_q_succ` | verified (standard axioms only) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.mag_eq_exp` | verified (standard axioms only) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.zak_energy_identity` | verified (standard axioms only) |
