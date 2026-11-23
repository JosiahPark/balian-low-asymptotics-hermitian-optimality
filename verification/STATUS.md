# Lean verification status: FAIL

Checked 2026-11-23 03:53 UTC at commit `764b6fe360e7`.

- Build: ok
- Theorems verified with standard axioms only: 0 of 358
- Nothing here proves Theorem 1.1 or Theorem 4.1 of the paper.

## Problems

- `BLT.inv_continuousOn_of_pos`
- `BLT.integral_const_mul_inv`
- `BLT.annulus_log_lower`
- `BLT.annulus_energy`
- `BLT.norm_mergeCenter_sub_left`
- `BLT.norm_mergeCenter_sub_right`
- `BLT.norm_sub_le_of_left`
- `BLT.merge_margin_left`
- `BLT.merge_margin_right`
- `BLT.ball_union_subset_merge`
- `BLT.ball_merge`
- `BLT.transl_apply`
- `BLT.diffOp_apply`
- `BLT.modul_apply`
- `BLT.energy_nonneg`
- `BLT.zakEnergy_nonneg`
- `BLT.bilinInterp_corners`
- `BLT.hasDerivAt_bilinInterp_x`
- `BLT.hasDerivAt_bilinInterp_y`
- `BLT.sq_convex_comb_le`
- `BLT.bilinInterp_grad_le`
- `BLT.integral_zero_one_affine`
- `BLT.integral_bilinW`
- `BLT.bilinInterp_energy`
- `BLT.hermiteFam_eq`
- `BLT.groundR_sq_sum`
- `BLT.groundR_pos`
- `BLT.groundR_min`
- `BLT.hermiteCand_admissible`
- `BLT.val_div_lt_one`
- `BLT.val_div_ne_half`
- `BLT.gaussZak_grid_ne_zero`
- `BLT.gaussCand_admissible`
- `BLT.integral_sq_sub_const`
- `BLT.interval_energy_lower`
- `BLT.circle_energy`
- `BLT.norm_sub_one_sq_of_norm_eq_one`
- `BLT.norm_sub_sq_eq_four_sin_sq`
- `BLT.norm_mag`
- `BLT.norm_sq_edgeR`
- `BLT.norm_sq_edgeQ`
- `BLT.zakEnergy_eq_sum_sin_sq`
- `BLT.zakEnergy_eq_sum_sin_sq_of_isTwisted`
- `BLT.mul_conj_of_norm_eq_one`
- `BLT.unit_mul_mul_conj`
- `BLT.mag_twist_cancel`
- `BLT.norm_twist_factor`
- `BLT.mag_add_period_mul_twist`
- `BLT.aR_add_period_q`
- `BLT.aR_add_period_r`
- `BLT.aQ_add_period_q`
- `BLT.aQ_add_period_r`
- `BLT.hermiteCand_scaledEnergy_eq`
- `BLT.zakEnergy_compare`
- `BLT.div_le_of_le_two_pi_log`
- `BLT.energy_close_arith`
- `BLT.energy_asymp_of_transfer`
- `BLT.gaussianTrialHyp_of_transfer`
- `BLT.hermiteHyp_of_transfer`
- `BLT.main_odd_reduced`
- `BLT.zak_sub`
- `BLT.sum_norm_sq_diffOp_eq_zak`
- `BLT.sum_norm_sq_diffOp_dftU_eq_zak`
- `BLT.energy_eq_sum_zak`
- `BLT.stdAddChar_natCast`
- `BLT.zak_modul`
- `BLT.zak_transl_of_lt`
- `BLT.zak_transl_seam`
- `BLT.zakIndex_lt`
- `BLT.zakIndex_injective`
- `BLT.zakIndex_bijective`
- `BLT.zak_eq_dftU`
- `BLT.parseval_zak`
- `BLT.sum_stdAddChar_inversion`
- `BLT.sum_sum_stdAddChar_inversion`
- `BLT.sum_sum_ite_zero`
- `BLT.fourier_uniqueness_two`
- `BLT.sum_zmod_add_one`
- `BLT.complex_norm_sub_sq`
- `BLT.stdAddChar_eq_exp_ofReal`
- `BLT.norm_sq_one_sub_stdAddChar`
- `BLT.sum_norm_sq_diffOp_dftU`
- `BLT.sum_norm_sq_diffOp`
- `BLT.sum_re_conj_mul_sub_one`
- `BLT.sum_im_conj_mul_sub_one`
- `BLT.re_ip_gStd`
- `BLT.im_ip_gStd`
- `BLT.energy_eq_re_ip_gStd`
- `BLT.gStd_eigvec_zero_succ`
- `BLT.gStd_eigvec_eq_zero_of_zero`
- `BLT.gStd_eigvec_pos`
- `BLT.gStd_eigvec_pos'`
- `BLT.ip_zero_right`
- `BLT.ip_sum_smul_right`
- `BLT.linearIndependent_of_ip_orthonormal`
- `BLT.linearIndependent_gabor`
- `BLT.span_gabor_eq_top`
- `BLT.transl_iterate_apply`
- `BLT.modul_iterate_apply`
- `BLT.gabor_apply`
- `BLT.zakIndex_add_natCast_mul`
- `BLT.stdAddChar_natCast_mul_self`
- `BLT.stdAddChar_mul_zakIndex`
- `BLT.gabor_zakIndex`
- `BLT.ip_gabor_eq_sum_zak`
- `BLT.ip_gabor_val_zero`
- `BLT.odd_grid_abs_sub_half`
- `BLT.odd_grid_norm_sub_zakZeroPt`
- `BLT.gaussZak_grid_lower`
- `BLT.gaussZak_ne_zero_of_lt`
- `BLT.gaussZak_one_left`
- `BLT.gaussZak_one_right`
- `BLT.gaussZak_ne_zero_of_closed`
- `BLT.continuous_gauss`
- `BLT.continuous_thetaI`
- `BLT.continuous_gaussZak_pair`
- `BLT.norm_sub_zakZeroPt_le_two`
- `BLT.gaussZak_ge_linear`
- `BLT.gaussZak_eq_gauss_mul_thetaI`
- `BLT.thetaI_zakZeroPt`
- `BLT.thetaI'_zakZeroPt_ne_zero`
- `BLT.hasDerivAt_thetaI`
- `BLT.thetaI_ge_linear_near_zero`
- `BLT.gauss_ge_of_abs_le`
- `BLT.gaussZak_ge_linear_near_zero`
- `BLT.norm_sub_zakZeroPt_sq`
- `BLT.scaledEnergy_zakInv`
- `BLT.gaussCand_scaledEnergy_eq`
- `BLT.vortex_iff_zakEnergy`
- `BLT.zakEnergy_eq_sum_range`
- `BLT.gaussZak_eq_zero_iff`
- `BLT.gaussZeroUnique_iff_theta`
- `BLT.jacobiTheta₂_zakZeroPt`
- `BLT.abs_aR_le_pi`
- `BLT.abs_aQ_le_pi`
- `BLT.int_eq_zero_of_four_small`
- `BLT.plaquette_int_eq_zero_of_small`
- `BLT.plaquetteCharge_eq_zero_of_small`
- `BLT.four_sin_half_sq`
- `BLT.four_sin_half_sq_le_of_le_abs`
- `BLT.card_filter_mul_le_sum`
- `BLT.zakEnergy_eq_sum_product`
- `BLT.card_largeEdgesR_mul_le`
- `BLT.card_largeEdgesQ_mul_le`
- `BLT.card_large_edges_mul_le_zakEnergy`
- `BLT.card_large_edges_le_div`
- `BLT.quadR_lower`
- `BLT.eq_zero_of_forall_quad_nonneg`
- `BLT.cross_eq`
- `BLT.gStdR_eq_of_min`
- `BLT.ground_eigen`
- `BLT.continuous_quadR`
- `BLT.isCompact_unitSphereR`
- `BLT.unitSphereR_nonempty`
- `BLT.exists_minimizer_quadR`
- `BLT.exists_minimizer`
- `BLT.quadR_abs_le`
- `BLT.isGround_abs`
- `BLT.isGround_ne_zero`
- `BLT.quadR_eq_sum_mul_gStdR`
- `BLT.gStdR_comb`
- `BLT.ne_zero_of_eig`
- `BLT.isGround_unique`
- `BLT.ground_state`
- `BLT.limit_constant_of_bounds`
- `BLT.limit_constant`
- `BLT.log_T_eq`
- `BLT.pos_of_le_mul_pow`
- `BLT.log_S₀_le`
- `BLT.div_mul_le_of_le_mul`
- `BLT.lower_bound_arithmetic`
- `BLT.norm_twistFactor`
- `BLT.twistFactor_shift_q`
- `BLT.twistFactor_shift_k`
- `BLT.zakExt_shift_q`
- `BLT.zakExt_shift_r`
- `BLT.norm_zakExt`
- `BLT.isTwisted_zakExt`
- `BLT.zakExt_of_lt`
- `BLT.scaledEnergy_eq_zakEnergy`
- `BLT.lowerBound_of_zak`
- `BLT.aSeq_eq`
- `BLT.ASeq_eq`
- `BLT.main_bounds`
- `BLT.main_conditional`
- `BLT.exists_le_log`
- `BLT.tendsto_odd_of_bounds`
- `BLT.milestone_odd_bounds`
- `BLT.milestone_odd`
- `BLT.main_odd_conditional`
- `BLT.nonvanish_of_approx`
- `BLT.hermiteHyp_of_approx`
- `BLT.hasDerivAt_oscPhi`
- `BLT.hasDerivAt_oscPhiD`
- `BLT.hasDerivAt_oscPsi`
- `BLT.hasDerivAt_oscPsiD`
- `BLT.oscPhi_eigen`
- `BLT.oscPsi_eigen`
- `BLT.oscPhi_eigenfunction`
- `BLT.oscPsi_eigenfunction`
- `BLT.gauss_eq_mul_oscPhi`
- `BLT.const_mul_oscPhi_eigenfunction`
- `BLT.const_mul_oscPsi_eigenfunction`
- `BLT.re_conj_mul_le_norm_mul`
- `BLT.re_ofReal_mul_conj_mul`
- `BLT.re_conj_mul_self`
- `BLT.perron_step`
- `BLT.quadFormRe_norm`
- `BLT.quadFormRe_norm_le`
- `BLT.energy_le_of_norm`
- `BLT.energy_norm_le`
- `BLT.ph_zero`
- `BLT.norm_ph_le_one`
- `BLT.ph_mul`
- `BLT.ph_natCast_mul`
- `BLT.norm_ph_sub_ph_le`
- `BLT.norm_ph_sub_ph_le_of_approx`
- `BLT.exp_arg_mul_I_of_norm_eq_one`
- `BLT.exists_int_of_exp_mul_I_eq`
- `BLT.arg_add_arg_sub_of_mul_eq`
- `BLT.mag_succ`
- `BLT.plaquette_phase_algebra`
- `BLT.norm_mul_conj_eq_one`
- `BLT.plaquette_identity`
- `BLT.plaquette_identity_of_isTwisted`
- `BLT.energy_ofReal`
- `BLT.gStd_ofReal`
- `BLT.sum_quad`
- `BLT.sum_sq_smul`
- `BLT.quadR_smul`
- `BLT.quadR_expand`
- `BLT.sum_sq_expand`
- `BLT.tendsto_log_nat`
- `BLT.tendsto_inv_log_nat`
- `BLT.tendsto_log_div_self`
- `BLT.tendsto_loglog_div_log`
- `BLT.tendsto_div_log_of_bounds`
- `BLT.relative_optimality`
- `BLT.scaledEnergy_nonneg`
- `BLT.bddBelow_scaledEnergy`
- `BLT.aMin_nonneg`
- `BLT.aMin_le`
- `BLT.transl_modul`
- `BLT.transl_dftU`
- `BLT.dftU_sub`
- `BLT.diffOp_dftU`
- `BLT.plaquetteCharge_eq_of_identity`
- `BLT.plaquetteCharge_spec`
- `BLT.sum_range_int_telescope`
- `BLT.sum_range_aQ_r_edge`
- `BLT.sum_range_aR_q_edge`
- `BLT.sum_plaquette_edges_eq_zero`
- `BLT.sum_range_const_add_mul`
- `BLT.sum_sum_range_const_add_mul`
- `BLT.sum_plaquette_int_eq_one`
- `BLT.total_charge_one`
- `BLT.sum_stdAddChar_mul`
- `BLT.conj_stdAddChar`
- `BLT.dft_norm_sq`
- `BLT.sum_conj_stdAddChar_mul`
- `BLT.ip_dftU`
- `BLT.parseval_dftU`
- `BLT.im_I_pos`
- `BLT.exp_mul_gaussZak`
- `BLT.exp_mul_gaussZak_holomorphic`
- `BLT.hasDerivAt_gauss`
- `BLT.hasDerivAt_gaussZak_snd`
- `BLT.hasDerivAt_gaussZak_fst`
- `BLT.hasDerivAt_gaussZak_fst_zero`
- `BLT.hasDerivAt_gaussZak_snd_zero`
- `BLT.deriv_gaussZak_snd_zero`
- `BLT.dftU_shift`
- `BLT.zak_correlation`
- `BLT.zak_correlation_of_norm`
- `BLT.natCast_zmod_eq_iff_of_lt`
- `BLT.ip_eq_sum_zakIndex`
- `BLT.ip_gabor_eq_sum`
- `BLT.ip_gabor_of_zak_norm`
- `BLT.zmod_val_eq_zero_iff`
- `BLT.zak_norm_of_ip_gabor`
- `BLT.ip_gabor_orthonormal_iff_zak_norm`
- `BLT.norm_natCast_mul_zak_eq_one_iff`
- `BLT.ip_gabor_orthonormal_iff_unit_modulus`
- `BLT.exp_nat_mul_pi_I`
- `BLT.exp_half_int`
- `BLT.exp_half_succ`
- `BLT.exp_half_neg`
- `BLT.hasSum_zakA0Term`
- `BLT.zakA0Term_fold`
- `BLT.hasSum_zakA0_nat`
- `BLT.zakA0_eq_tsum_nat`
- `BLT.hasSum_zakA0_re`
- `BLT.hasSum_pairs`
- `BLT.le_hasSum_alternating`
- `BLT.hasSum_alternating_zakA0Coeff`
- `BLT.zakA0_re_le`
- `BLT.zakA0_re_neg`
- `BLT.zakA0_ne_zero`
- `BLT.deriv_gaussZak_fst_zero_ne_zero`
- `BLT.deriv_gaussZak_snd_zero_ne_zero`
- `BLT.thetaDerivTerm_eq`
- `BLT.hasSum_thetaDerivTerm`
- `BLT.zakA0_term_eq`
- `BLT.hasSum_zakA0`
- `BLT.summable_zakA0_term`
- `BLT.zakA0_eq_tsum`
- `BLT.hasSum_deriv_gaussZak_fst_zero`
- `BLT.gauss_add_one`
- `BLT.exp_neg_two_pi_lt`
- `BLT.zakA0Coeff_pos`
- `BLT.zakA0Coeff_succ_lt`
- `BLT.zakA0Coeff_succ_le`
- `BLT.strictAnti_zakA0Coeff`
- `BLT.hasSum_zakA0_re_coeff`
- `BLT.norm_mag`
- `BLT.zakExt_add`
- `BLT.zakExt_const_mul`
- `BLT.zakExt_neg`
- `BLT.zakEnergy_const_mul`
- `BLT.sq_norm_add_le_mul`
- `BLT.zakEnergy_add_le`
- `BLT.sq_norm_sub_le`
- `BLT.norm_zakExt_eq`
- `BLT.zakEnergy_zakExt_le`
- `BLT.sum_zmod_eq_sum_range`
- `BLT.sum_sum_zmod_eq_sum_range`
- `BLT.zak_energy_identity`
- `BLT.zak_energy_identity_of_isTwisted`
- `BLT.exp_two_pi_int_mul_add_one`
- `BLT.gaussZak_term_shift`
- `BLT.gaussZak_add_one_left`
- `BLT.gaussZak_add_one_right`
- `BLT.zakInv_zakIndex`
- `BLT.zak_zakInv`
- `BLT.norm_ph`
- `BLT.zakInv_admissible`
- `BLT.le_aMin_of_forall`
- `BLT.zmod_val_natCast_of_lt`
- `BLT.norm_sq_natCast_mul`
- `BLT.stdAddChar_neg_natCast`
- `BLT.zeta_r_succ`
- `BLT.mag_mul_zeta_q_succ`
- `BLT.norm_sq_zeta_r_edge`
- `BLT.norm_sq_zeta_q_edge`
- `BLT.ofReal_mul_exp_mul_exp_eq`
- `BLT.gaussZak_term_aux`
- `BLT.gaussZak_term_eq`
- `BLT.hasSum_gaussZak_term_theta`
- `BLT.summable_gaussZak_term`
- `BLT.gaussZak_eq_gauss_mul_theta`
- `BLT.gaussZak_eq_theta`
- `BLT.hasSum_gaussZak_term`
- `BLT.gauss_neg`
- `BLT.gauss_pos`
- `BLT.exp_reflect_half`
- `BLT.gaussZak_half_term_reflect`
- `BLT.gaussZak_half_half`
- `BLT.jacobiTheta_zakZero`

## Build errors

```
/home/runner/work/balian-low-asymptotics-hermitian-optimality/balian-low-asymptotics-hermitian-optimality/AxiomAudit.lean:1:0: error: import BLTAudit.ZakEnergyCompare failed, environment already contains 'BLT.norm_mag' from BLTAudit.EdgeEnergy
```

## Theorems

| file | theorem | status |
|---|---|---|
| BLTAudit/AnnulusEnergy.lean | `BLT.inv_continuousOn_of_pos` | NOT CHECKED (name not found by Lean) |
| BLTAudit/AnnulusEnergy.lean | `BLT.integral_const_mul_inv` | NOT CHECKED (name not found by Lean) |
| BLTAudit/AnnulusEnergy.lean | `BLT.annulus_log_lower` | NOT CHECKED (name not found by Lean) |
| BLTAudit/AnnulusEnergy.lean | `BLT.annulus_energy` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.norm_mergeCenter_sub_left` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.norm_mergeCenter_sub_right` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.norm_sub_le_of_left` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.merge_margin_left` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.merge_margin_right` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.ball_union_subset_merge` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.ball_merge` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Basic.lean | `BLT.transl_apply` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Basic.lean | `BLT.diffOp_apply` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Basic.lean | `BLT.modul_apply` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Basic.lean | `BLT.energy_nonneg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Basic.lean | `BLT.zakEnergy_nonneg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BilinearInterp.lean | `BLT.bilinInterp_corners` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BilinearInterp.lean | `BLT.hasDerivAt_bilinInterp_x` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BilinearInterp.lean | `BLT.hasDerivAt_bilinInterp_y` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BilinearInterp.lean | `BLT.sq_convex_comb_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BilinearInterp.lean | `BLT.bilinInterp_grad_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BilinearInterp.lean | `BLT.integral_zero_one_affine` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BilinearInterp.lean | `BLT.integral_bilinW` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BilinearInterp.lean | `BLT.bilinInterp_energy` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Candidates.lean | `BLT.hermiteFam_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Candidates.lean | `BLT.groundR_sq_sum` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Candidates.lean | `BLT.groundR_pos` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Candidates.lean | `BLT.groundR_min` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Candidates.lean | `BLT.hermiteCand_admissible` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Candidates.lean | `BLT.val_div_lt_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Candidates.lean | `BLT.val_div_ne_half` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Candidates.lean | `BLT.gaussZak_grid_ne_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Candidates.lean | `BLT.gaussCand_admissible` | NOT CHECKED (name not found by Lean) |
| BLTAudit/CircleEnergy.lean | `BLT.integral_sq_sub_const` | NOT CHECKED (name not found by Lean) |
| BLTAudit/CircleEnergy.lean | `BLT.interval_energy_lower` | NOT CHECKED (name not found by Lean) |
| BLTAudit/CircleEnergy.lean | `BLT.circle_energy` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_sub_one_sq_of_norm_eq_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_sub_sq_eq_four_sin_sq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_mag` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_sq_edgeR` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_sq_edgeQ` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.zakEnergy_eq_sum_sin_sq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.zakEnergy_eq_sum_sin_sq_of_isTwisted` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgePeriodicity.lean | `BLT.mul_conj_of_norm_eq_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgePeriodicity.lean | `BLT.unit_mul_mul_conj` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgePeriodicity.lean | `BLT.mag_twist_cancel` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgePeriodicity.lean | `BLT.norm_twist_factor` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgePeriodicity.lean | `BLT.mag_add_period_mul_twist` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgePeriodicity.lean | `BLT.aR_add_period_q` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgePeriodicity.lean | `BLT.aR_add_period_r` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgePeriodicity.lean | `BLT.aQ_add_period_q` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgePeriodicity.lean | `BLT.aQ_add_period_r` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyFromTransfer.lean | `BLT.hermiteCand_scaledEnergy_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyFromTransfer.lean | `BLT.zakEnergy_compare` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyFromTransfer.lean | `BLT.div_le_of_le_two_pi_log` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyFromTransfer.lean | `BLT.energy_close_arith` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyFromTransfer.lean | `BLT.energy_asymp_of_transfer` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyFromTransfer.lean | `BLT.gaussianTrialHyp_of_transfer` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyFromTransfer.lean | `BLT.hermiteHyp_of_transfer` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyFromTransfer.lean | `BLT.main_odd_reduced` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyZakCoordinates.lean | `BLT.zak_sub` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyZakCoordinates.lean | `BLT.sum_norm_sq_diffOp_eq_zak` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyZakCoordinates.lean | `BLT.sum_norm_sq_diffOp_dftU_eq_zak` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EnergyZakCoordinates.lean | `BLT.energy_eq_sum_zak` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZakModulation.lean | `BLT.stdAddChar_natCast` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZakModulation.lean | `BLT.zak_modul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZakTranslation.lean | `BLT.zak_transl_of_lt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZakTranslation.lean | `BLT.zak_transl_seam` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZakUnitary.lean | `BLT.zakIndex_lt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZakUnitary.lean | `BLT.zakIndex_injective` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZakUnitary.lean | `BLT.zakIndex_bijective` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZakUnitary.lean | `BLT.zak_eq_dftU` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZakUnitary.lean | `BLT.parseval_zak` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FourierUniqueness.lean | `BLT.sum_stdAddChar_inversion` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FourierUniqueness.lean | `BLT.sum_sum_stdAddChar_inversion` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FourierUniqueness.lean | `BLT.sum_sum_ite_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FourierUniqueness.lean | `BLT.fourier_uniqueness_two` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.sum_zmod_add_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.complex_norm_sub_sq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.stdAddChar_eq_exp_ofReal` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.norm_sq_one_sub_stdAddChar` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.sum_norm_sq_diffOp_dftU` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.sum_norm_sq_diffOp` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.sum_re_conj_mul_sub_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.sum_im_conj_mul_sub_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.re_ip_gStd` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.im_ip_gStd` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.energy_eq_re_ip_gStd` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStdPositive.lean | `BLT.gStd_eigvec_zero_succ` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStdPositive.lean | `BLT.gStd_eigvec_eq_zero_of_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStdPositive.lean | `BLT.gStd_eigvec_pos` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStdPositive.lean | `BLT.gStd_eigvec_pos'` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborBasis.lean | `BLT.ip_zero_right` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborBasis.lean | `BLT.ip_sum_smul_right` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborBasis.lean | `BLT.linearIndependent_of_ip_orthonormal` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborBasis.lean | `BLT.linearIndependent_gabor` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborBasis.lean | `BLT.span_gabor_eq_top` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborFormula.lean | `BLT.transl_iterate_apply` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborFormula.lean | `BLT.modul_iterate_apply` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborFormula.lean | `BLT.gabor_apply` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborZakCoordinates.lean | `BLT.zakIndex_add_natCast_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborZakCoordinates.lean | `BLT.stdAddChar_natCast_mul_self` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborZakCoordinates.lean | `BLT.stdAddChar_mul_zakIndex` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborZakCoordinates.lean | `BLT.gabor_zakIndex` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborZakModulus.lean | `BLT.ip_gabor_eq_sum_zak` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaborZakModulus.lean | `BLT.ip_gabor_val_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussGridLower.lean | `BLT.odd_grid_abs_sub_half` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussGridLower.lean | `BLT.odd_grid_norm_sub_zakZeroPt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussGridLower.lean | `BLT.gaussZak_grid_lower` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearGlobal.lean | `BLT.gaussZak_ne_zero_of_lt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearGlobal.lean | `BLT.gaussZak_one_left` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearGlobal.lean | `BLT.gaussZak_one_right` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearGlobal.lean | `BLT.gaussZak_ne_zero_of_closed` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearGlobal.lean | `BLT.continuous_gauss` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearGlobal.lean | `BLT.continuous_thetaI` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearGlobal.lean | `BLT.continuous_gaussZak_pair` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearGlobal.lean | `BLT.norm_sub_zakZeroPt_le_two` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearGlobal.lean | `BLT.gaussZak_ge_linear` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearNearZero.lean | `BLT.gaussZak_eq_gauss_mul_thetaI` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearNearZero.lean | `BLT.thetaI_zakZeroPt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearNearZero.lean | `BLT.thetaI'_zakZeroPt_ne_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearNearZero.lean | `BLT.hasDerivAt_thetaI` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearNearZero.lean | `BLT.thetaI_ge_linear_near_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearNearZero.lean | `BLT.gauss_ge_of_abs_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearNearZero.lean | `BLT.gaussZak_ge_linear_near_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussLinearNearZero.lean | `BLT.norm_sub_zakZeroPt_sq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussVortexZak.lean | `BLT.scaledEnergy_zakInv` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussVortexZak.lean | `BLT.gaussCand_scaledEnergy_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussVortexZak.lean | `BLT.vortex_iff_zakEnergy` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussVortexZak.lean | `BLT.zakEnergy_eq_sum_range` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussZeroTheta.lean | `BLT.gaussZak_eq_zero_iff` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussZeroTheta.lean | `BLT.gaussZeroUnique_iff_theta` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GaussZeroTheta.lean | `BLT.jacobiTheta₂_zakZeroPt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.abs_aR_le_pi` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.abs_aQ_le_pi` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.int_eq_zero_of_four_small` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.plaquette_int_eq_zero_of_small` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.plaquetteCharge_eq_zero_of_small` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.four_sin_half_sq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.four_sin_half_sq_le_of_le_abs` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.card_filter_mul_le_sum` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.zakEnergy_eq_sum_product` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.card_largeEdgesR_mul_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.card_largeEdgesQ_mul_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.card_large_edges_mul_le_zakEnergy` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GoodPlaquette.lean | `BLT.card_large_edges_le_div` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundEigen.lean | `BLT.quadR_lower` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundEigen.lean | `BLT.eq_zero_of_forall_quad_nonneg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundEigen.lean | `BLT.cross_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundEigen.lean | `BLT.gStdR_eq_of_min` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundEigen.lean | `BLT.ground_eigen` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundExists.lean | `BLT.continuous_quadR` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundExists.lean | `BLT.isCompact_unitSphereR` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundExists.lean | `BLT.unitSphereR_nonempty` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundExists.lean | `BLT.exists_minimizer_quadR` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundExists.lean | `BLT.exists_minimizer` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundState.lean | `BLT.quadR_abs_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundState.lean | `BLT.isGround_abs` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundState.lean | `BLT.isGround_ne_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundState.lean | `BLT.quadR_eq_sum_mul_gStdR` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundState.lean | `BLT.gStdR_comb` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundState.lean | `BLT.ne_zero_of_eig` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundState.lean | `BLT.isGround_unique` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GroundState.lean | `BLT.ground_state` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LimitConstant.lean | `BLT.limit_constant_of_bounds` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LimitConstant.lean | `BLT.limit_constant` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundArithmetic.lean | `BLT.log_T_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundArithmetic.lean | `BLT.pos_of_le_mul_pow` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundArithmetic.lean | `BLT.log_S₀_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundArithmetic.lean | `BLT.div_mul_le_of_le_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundArithmetic.lean | `BLT.lower_bound_arithmetic` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundZak.lean | `BLT.norm_twistFactor` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundZak.lean | `BLT.twistFactor_shift_q` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundZak.lean | `BLT.twistFactor_shift_k` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundZak.lean | `BLT.zakExt_shift_q` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundZak.lean | `BLT.zakExt_shift_r` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundZak.lean | `BLT.norm_zakExt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundZak.lean | `BLT.isTwisted_zakExt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundZak.lean | `BLT.zakExt_of_lt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundZak.lean | `BLT.scaledEnergy_eq_zakEnergy` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundZak.lean | `BLT.lowerBound_of_zak` | NOT CHECKED (name not found by Lean) |
| BLTAudit/MainConditional.lean | `BLT.aSeq_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/MainConditional.lean | `BLT.ASeq_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/MainConditional.lean | `BLT.main_bounds` | NOT CHECKED (name not found by Lean) |
| BLTAudit/MainConditional.lean | `BLT.main_conditional` | NOT CHECKED (name not found by Lean) |
| BLTAudit/MainOdd.lean | `BLT.exists_le_log` | NOT CHECKED (name not found by Lean) |
| BLTAudit/MainOdd.lean | `BLT.tendsto_odd_of_bounds` | NOT CHECKED (name not found by Lean) |
| BLTAudit/MainOdd.lean | `BLT.milestone_odd_bounds` | NOT CHECKED (name not found by Lean) |
| BLTAudit/MainOdd.lean | `BLT.milestone_odd` | NOT CHECKED (name not found by Lean) |
| BLTAudit/MainOdd.lean | `BLT.main_odd_conditional` | NOT CHECKED (name not found by Lean) |
| BLTAudit/NonvanishFromApprox.lean | `BLT.nonvanish_of_approx` | NOT CHECKED (name not found by Lean) |
| BLTAudit/NonvanishFromApprox.lean | `BLT.hermiteHyp_of_approx` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.hasDerivAt_oscPhi` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.hasDerivAt_oscPhiD` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.hasDerivAt_oscPsi` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.hasDerivAt_oscPsiD` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.oscPhi_eigen` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.oscPsi_eigen` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.oscPhi_eigenfunction` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.oscPsi_eigenfunction` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.gauss_eq_mul_oscPhi` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.const_mul_oscPhi_eigenfunction` | NOT CHECKED (name not found by Lean) |
| BLTAudit/OscillatorGaussian.lean | `BLT.const_mul_oscPsi_eigenfunction` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PerronStep.lean | `BLT.re_conj_mul_le_norm_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PerronStep.lean | `BLT.re_ofReal_mul_conj_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PerronStep.lean | `BLT.re_conj_mul_self` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PerronStep.lean | `BLT.perron_step` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PerronStep.lean | `BLT.quadFormRe_norm` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PerronStep.lean | `BLT.quadFormRe_norm_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PerronStep.lean | `BLT.energy_le_of_norm` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PerronStep.lean | `BLT.energy_norm_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PhasePerturbation.lean | `BLT.ph_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PhasePerturbation.lean | `BLT.norm_ph_le_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PhasePerturbation.lean | `BLT.ph_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PhasePerturbation.lean | `BLT.ph_natCast_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PhasePerturbation.lean | `BLT.norm_ph_sub_ph_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PhasePerturbation.lean | `BLT.norm_ph_sub_ph_le_of_approx` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PlaquetteCharge.lean | `BLT.exp_arg_mul_I_of_norm_eq_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PlaquetteCharge.lean | `BLT.exists_int_of_exp_mul_I_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PlaquetteCharge.lean | `BLT.arg_add_arg_sub_of_mul_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PlaquetteCharge.lean | `BLT.mag_succ` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PlaquetteCharge.lean | `BLT.plaquette_phase_algebra` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PlaquetteCharge.lean | `BLT.norm_mul_conj_eq_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PlaquetteCharge.lean | `BLT.plaquette_identity` | NOT CHECKED (name not found by Lean) |
| BLTAudit/PlaquetteCharge.lean | `BLT.plaquette_identity_of_isTwisted` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RealQuadForm.lean | `BLT.energy_ofReal` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RealQuadForm.lean | `BLT.gStd_ofReal` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RealQuadForm.lean | `BLT.sum_quad` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RealQuadForm.lean | `BLT.sum_sq_smul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RealQuadForm.lean | `BLT.quadR_smul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RealQuadForm.lean | `BLT.quadR_expand` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RealQuadForm.lean | `BLT.sum_sq_expand` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RelativeOptimality.lean | `BLT.tendsto_log_nat` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RelativeOptimality.lean | `BLT.tendsto_inv_log_nat` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RelativeOptimality.lean | `BLT.tendsto_log_div_self` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RelativeOptimality.lean | `BLT.tendsto_loglog_div_log` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RelativeOptimality.lean | `BLT.tendsto_div_log_of_bounds` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RelativeOptimality.lean | `BLT.relative_optimality` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Statements.lean | `BLT.scaledEnergy_nonneg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Statements.lean | `BLT.bddBelow_scaledEnergy` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Statements.lean | `BLT.aMin_nonneg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Statements.lean | `BLT.aMin_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TimeFrequency.lean | `BLT.transl_modul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TimeFrequency.lean | `BLT.transl_dftU` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TimeFrequency.lean | `BLT.dftU_sub` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TimeFrequency.lean | `BLT.diffOp_dftU` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TotalCharge.lean | `BLT.plaquetteCharge_eq_of_identity` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TotalCharge.lean | `BLT.plaquetteCharge_spec` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TotalCharge.lean | `BLT.sum_range_int_telescope` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TotalCharge.lean | `BLT.sum_range_aQ_r_edge` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TotalCharge.lean | `BLT.sum_range_aR_q_edge` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TotalCharge.lean | `BLT.sum_plaquette_edges_eq_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TotalCharge.lean | `BLT.sum_range_const_add_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TotalCharge.lean | `BLT.sum_sum_range_const_add_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TotalCharge.lean | `BLT.sum_plaquette_int_eq_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TotalCharge.lean | `BLT.total_charge_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.sum_stdAddChar_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.conj_stdAddChar` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.dft_norm_sq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.sum_conj_stdAddChar_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.ip_dftU` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.parseval_dftU` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakConformal.lean | `BLT.im_I_pos` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakConformal.lean | `BLT.exp_mul_gaussZak` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakConformal.lean | `BLT.exp_mul_gaussZak_holomorphic` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakConformal.lean | `BLT.hasDerivAt_gauss` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakConformal.lean | `BLT.hasDerivAt_gaussZak_snd` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakConformal.lean | `BLT.hasDerivAt_gaussZak_fst` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakConformal.lean | `BLT.hasDerivAt_gaussZak_fst_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakConformal.lean | `BLT.hasDerivAt_gaussZak_snd_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakConformal.lean | `BLT.deriv_gaussZak_snd_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCorrelation.lean | `BLT.dftU_shift` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCorrelation.lean | `BLT.zak_correlation` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCorrelation.lean | `BLT.zak_correlation_of_norm` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCriterion.lean | `BLT.natCast_zmod_eq_iff_of_lt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCriterion.lean | `BLT.ip_eq_sum_zakIndex` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCriterion.lean | `BLT.ip_gabor_eq_sum` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCriterion.lean | `BLT.ip_gabor_of_zak_norm` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCriterionConverse.lean | `BLT.zmod_val_eq_zero_iff` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCriterionConverse.lean | `BLT.zak_norm_of_ip_gabor` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCriterionConverse.lean | `BLT.ip_gabor_orthonormal_iff_zak_norm` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCriterionConverse.lean | `BLT.norm_natCast_mul_zak_eq_one_iff` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakCriterionConverse.lean | `BLT.ip_gabor_orthonormal_iff_unit_modulus` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivFold.lean | `BLT.exp_nat_mul_pi_I` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivFold.lean | `BLT.exp_half_int` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivFold.lean | `BLT.exp_half_succ` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivFold.lean | `BLT.exp_half_neg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivFold.lean | `BLT.hasSum_zakA0Term` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivFold.lean | `BLT.zakA0Term_fold` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivFold.lean | `BLT.hasSum_zakA0_nat` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivFold.lean | `BLT.zakA0_eq_tsum_nat` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivFold.lean | `BLT.hasSum_zakA0_re` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivNonzero.lean | `BLT.hasSum_pairs` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivNonzero.lean | `BLT.le_hasSum_alternating` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivNonzero.lean | `BLT.hasSum_alternating_zakA0Coeff` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivNonzero.lean | `BLT.zakA0_re_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivNonzero.lean | `BLT.zakA0_re_neg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivNonzero.lean | `BLT.zakA0_ne_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivNonzero.lean | `BLT.deriv_gaussZak_fst_zero_ne_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivNonzero.lean | `BLT.deriv_gaussZak_snd_zero_ne_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivSeries.lean | `BLT.thetaDerivTerm_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivSeries.lean | `BLT.hasSum_thetaDerivTerm` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivSeries.lean | `BLT.zakA0_term_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivSeries.lean | `BLT.hasSum_zakA0` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivSeries.lean | `BLT.summable_zakA0_term` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivSeries.lean | `BLT.zakA0_eq_tsum` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivSeries.lean | `BLT.hasSum_deriv_gaussZak_fst_zero` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivTerms.lean | `BLT.gauss_add_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivTerms.lean | `BLT.exp_neg_two_pi_lt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivTerms.lean | `BLT.zakA0Coeff_pos` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivTerms.lean | `BLT.zakA0Coeff_succ_lt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivTerms.lean | `BLT.zakA0Coeff_succ_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivTerms.lean | `BLT.strictAnti_zakA0Coeff` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakDerivTerms.lean | `BLT.hasSum_zakA0_re_coeff` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyCompare.lean | `BLT.norm_mag` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyCompare.lean | `BLT.zakExt_add` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyCompare.lean | `BLT.zakExt_const_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyCompare.lean | `BLT.zakExt_neg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyCompare.lean | `BLT.zakEnergy_const_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyCompare.lean | `BLT.sq_norm_add_le_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyCompare.lean | `BLT.zakEnergy_add_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyCompare.lean | `BLT.sq_norm_sub_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyCompare.lean | `BLT.norm_zakExt_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyCompare.lean | `BLT.zakEnergy_zakExt_le` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.sum_zmod_eq_sum_range` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.sum_sum_zmod_eq_sum_range` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.zak_energy_identity` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakEnergyIdentity.lean | `BLT.zak_energy_identity_of_isTwisted` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakGluing.lean | `BLT.exp_two_pi_int_mul_add_one` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakGluing.lean | `BLT.gaussZak_term_shift` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakGluing.lean | `BLT.gaussZak_add_one_left` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakGluing.lean | `BLT.gaussZak_add_one_right` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakInverse.lean | `BLT.zakInv_zakIndex` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakInverse.lean | `BLT.zak_zakInv` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakInverse.lean | `BLT.norm_ph` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakInverse.lean | `BLT.zakInv_admissible` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakInverse.lean | `BLT.le_aMin_of_forall` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakSeams.lean | `BLT.zmod_val_natCast_of_lt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakSeams.lean | `BLT.norm_sq_natCast_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakSeams.lean | `BLT.stdAddChar_neg_natCast` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakSeams.lean | `BLT.zeta_r_succ` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakSeams.lean | `BLT.mag_mul_zeta_q_succ` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakSeams.lean | `BLT.norm_sq_zeta_r_edge` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakSeams.lean | `BLT.norm_sq_zeta_q_edge` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakTheta.lean | `BLT.ofReal_mul_exp_mul_exp_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakTheta.lean | `BLT.gaussZak_term_aux` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakTheta.lean | `BLT.gaussZak_term_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakTheta.lean | `BLT.hasSum_gaussZak_term_theta` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakTheta.lean | `BLT.summable_gaussZak_term` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakTheta.lean | `BLT.gaussZak_eq_gauss_mul_theta` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakTheta.lean | `BLT.gaussZak_eq_theta` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakTheta.lean | `BLT.hasSum_gaussZak_term` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakZero.lean | `BLT.gauss_neg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakZero.lean | `BLT.gauss_pos` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakZero.lean | `BLT.exp_reflect_half` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakZero.lean | `BLT.gaussZak_half_term_reflect` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakZero.lean | `BLT.gaussZak_half_half` | NOT CHECKED (name not found by Lean) |
| BLTAudit/ZakZero.lean | `BLT.jacobiTheta_zakZero` | NOT CHECKED (name not found by Lean) |
