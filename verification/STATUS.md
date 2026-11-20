# Lean verification status: FAIL

Checked 2026-11-20 03:52 UTC at commit `ebbd00c332fd`.

- Build: FAILED
- Theorems verified with standard axioms only: 0 of 45
- Nothing here proves Theorem 1.1 or Theorem 4.1 of the paper.

## Problems

- `BLT.norm_mergeCenter_sub_left`
- `BLT.norm_mergeCenter_sub_right`
- `BLT.margin_mergeBall_left`
- `BLT.margin_mergeBall_right`
- `BLT.ball_union_subset_mergeBall`
- `BLT.transl_apply`
- `BLT.diffOp_apply`
- `BLT.modul_apply`
- `BLT.energy_nonneg`
- `BLT.zakEnergy_nonneg`
- `BLT.norm_exp_sub_one_sq`
- `BLT.norm_sub_sq_eq_four_sin_sq`
- `BLT.norm_mag`
- `BLT.zakEnergy_eq_sin_sq`
- `BLT.stdAddChar_natCast`
- `BLT.zakIndex_lt`
- `BLT.zakIndex_injective`
- `BLT.zakIndex_bijective`
- `BLT.zak_eq_dftU`
- `BLT.parseval_zak`
- `BLT.zak_transl_of_lt`
- `BLT.zak_transl_seam`
- `BLT.zak_modul`
- `BLT.stdAddChar_add_neg`
- `BLT.normSq_one_sub_stdAddChar`
- `BLT.sum_norm_sq_eq`
- `BLT.energy_eq_ip_gStd`
- `BLT.energy_eq_re_ip_gStd`
- `BLT.im_ip_gStd`
- `BLT.tendsto_loglog_div_log`
- `BLT.limit_constant`
- `BLT.log_stopTime`
- `BLT.lower_bound_arithmetic`
- `BLT.gap_bound`
- `BLT.relative_optimality`
- `BLT.transl_modul`
- `BLT.transl_dftU`
- `BLT.dftU_sub`
- `BLT.diffOp_dftU`
- `BLT.sum_stdAddChar_mul`
- `BLT.conj_stdAddChar`
- `BLT.dft_norm_sq`
- `BLT.sum_conj_stdAddChar_mul`
- `BLT.ip_dftU`
- `BLT.parseval_dftU`

## Build errors

```
error: BLTAudit/LowerBoundArithmetic.lean:34:2: No goals to be solved
error: BLTAudit/RelativeOptimality.lean:55:35: failed to prove positivity/nonnegativity/nonzeroness
error: BLTAudit/UnitaryDFT.lean:77:74: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (∑ i ∈ ?s, ?f i) * ∑ j ∈ ?t, ?g j
in the target expression
  c * ∑ i, (∑ x, (starRingEnd ℂ) (ZMod.stdAddChar (x * k) * f x)) * (c * (ZMod.stdAddChar (i * k) * g i)) =
    ∑ j,
      ∑ l, c * c * ((starRingEnd ℂ) (f j) * g l) * ((starRingEnd ℂ) (ZMod.stdAddChar (j * k)) * ZMod.stdAddChar (l * k))

N : ℕ
inst✝ : NeZero N
f g : ZMod N → ℂ
c : ℂ := (↑√↑N)⁻¹
hc : c = (↑√↑N)⁻¹
hcc : (starRingEnd ℂ) c = c
hcN : c * c * ↑N = 1
k : ZMod N
⊢ c * ∑ i, (∑ x, (starRingEnd ℂ) (ZMod.stdAddChar (x * k) * f x)) * (c * (ZMod.stdAddChar (i * k) * g i)) =
    ∑ j,
      ∑ l, c * c * ((starRingEnd ℂ) (f j) * g l) * ((starRingEnd ℂ) (ZMod.stdAddChar (j * k)) * ZMod.stdAddChar (l * k))
error: BLTAudit/TimeFrequency.lean:26:41: typeclass instance problem is stuck
  OfNat (ZMod ?m.6) 1

Note: Lean will not try to resolve this typeclass instance problem because the first type argument to `OfNat` contains metavariables. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  ZMod ?m.6
due to the absence of the instance above
error: build failed
/home/runner/work/balian-low-asymptotics-hermitian-optimality/balian-low-asymptotics-hermitian-optimality/AxiomAudit.lean:1:0: error: object file '/home/runner/work/balian-low-asymptotics-hermitian-optimality/balian-low-asymptotics-hermitian-optimality/.lake/build/lib/lean/BLTAudit/FiniteZak.olean' of module BLTAudit.FiniteZak does not exist
```

## Theorems

| file | theorem | status |
|---|---|---|
| BLTAudit/BallMerge.lean | `BLT.norm_mergeCenter_sub_left` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.norm_mergeCenter_sub_right` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.margin_mergeBall_left` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.margin_mergeBall_right` | NOT CHECKED (name not found by Lean) |
| BLTAudit/BallMerge.lean | `BLT.ball_union_subset_mergeBall` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Basic.lean | `BLT.transl_apply` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Basic.lean | `BLT.diffOp_apply` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Basic.lean | `BLT.modul_apply` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Basic.lean | `BLT.energy_nonneg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/Basic.lean | `BLT.zakEnergy_nonneg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_exp_sub_one_sq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_sub_sq_eq_four_sin_sq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.norm_mag` | NOT CHECKED (name not found by Lean) |
| BLTAudit/EdgeEnergy.lean | `BLT.zakEnergy_eq_sin_sq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZak.lean | `BLT.stdAddChar_natCast` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZak.lean | `BLT.zakIndex_lt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZak.lean | `BLT.zakIndex_injective` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZak.lean | `BLT.zakIndex_bijective` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZak.lean | `BLT.zak_eq_dftU` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZak.lean | `BLT.parseval_zak` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZak.lean | `BLT.zak_transl_of_lt` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZak.lean | `BLT.zak_transl_seam` | NOT CHECKED (name not found by Lean) |
| BLTAudit/FiniteZak.lean | `BLT.zak_modul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.stdAddChar_add_neg` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.normSq_one_sub_stdAddChar` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.sum_norm_sq_eq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.energy_eq_ip_gStd` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.energy_eq_re_ip_gStd` | NOT CHECKED (name not found by Lean) |
| BLTAudit/GStandardForm.lean | `BLT.im_ip_gStd` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LimitConstant.lean | `BLT.tendsto_loglog_div_log` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LimitConstant.lean | `BLT.limit_constant` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundArithmetic.lean | `BLT.log_stopTime` | NOT CHECKED (name not found by Lean) |
| BLTAudit/LowerBoundArithmetic.lean | `BLT.lower_bound_arithmetic` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RelativeOptimality.lean | `BLT.gap_bound` | NOT CHECKED (name not found by Lean) |
| BLTAudit/RelativeOptimality.lean | `BLT.relative_optimality` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TimeFrequency.lean | `BLT.transl_modul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TimeFrequency.lean | `BLT.transl_dftU` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TimeFrequency.lean | `BLT.dftU_sub` | NOT CHECKED (name not found by Lean) |
| BLTAudit/TimeFrequency.lean | `BLT.diffOp_dftU` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.sum_stdAddChar_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.conj_stdAddChar` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.dft_norm_sq` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.sum_conj_stdAddChar_mul` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.ip_dftU` | NOT CHECKED (name not found by Lean) |
| BLTAudit/UnitaryDFT.lean | `BLT.parseval_dftU` | NOT CHECKED (name not found by Lean) |
