import BLTAudit.Basic

/-!
# A2. Time–frequency relations on `ℂ^N`

With `T = transl`, `M = modul`, `D = diffOp` and the unitary DFT `F = dftU` of
`BLTAudit/Basic.lean`, for every `f : ZMod N → ℂ`:

* `transl_modul`: `T M f = e^{2πi/N} M T f`, pointwise in `j`;
* `transl_dftU`: `T F f = F M f`. With the unitarity of `F` (A1) this is the paper's
  `F* T F = M`; the conjugated form itself is not stated here;
* `dftU_sub`: `F (f − g) = F f − F g`;
* `diffOp_dftU`: `D F f = F (f − M f)`, the forward difference of the DFT.

What this file does NOT prove: unitarity of `F` (that is A1, `BLTAudit/UnitaryDFT.lean`), the
identity `F* T F = M` as an equation between operators, any statement about the Zak transform,
the Gabor system or the energy `E_N`; nothing here bears on Theorem 1.1 or Theorem 4.1.
-/

noncomputable section

open Finset

namespace BLT

variable {N : ℕ} [NeZero N]

/-- **A2.** `T M = e^{2πi/N} M T`. -/
theorem transl_modul (f : ZMod N → ℂ) (j : ZMod N) :
    transl (modul f) j = ZMod.stdAddChar (1 : ZMod N) * modul (transl f) j := by
  simp only [transl_apply, modul_apply, AddChar.map_add_eq_mul]
  ring

/-- **A2.** `T F = F M`: translating the DFT is the DFT of the modulated vector. -/
theorem transl_dftU (f : ZMod N → ℂ) : transl (dftU f) = dftU (modul f) := by
  funext k
  simp only [transl_apply, dftU, modul_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_add, mul_one, AddChar.map_add_eq_mul]
  ring

/-- The DFT of a difference. -/
theorem dftU_sub (f g : ZMod N → ℂ) : dftU (f - g) = dftU f - dftU g := by
  funext k
  simp only [dftU, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- `D F f = F (f − M f)`: the forward difference of the DFT. -/
theorem diffOp_dftU (f : ZMod N → ℂ) : diffOp (dftU f) = dftU (f - modul f) := by
  rw [dftU_sub, ← transl_dftU]
  funext k
  simp only [diffOp_apply, Pi.sub_apply, transl_apply]

end BLT

end
