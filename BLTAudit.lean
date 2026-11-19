import Mathlib

/-!
# BLTAudit

Lean 4 + Mathlib companion to J. Park, "Relative asymptotic optimality of finite Hermite Gabor
windows" (25 Sep 2026; `relative_asymptotic_optimality.pdf` in this repository).

Every file under `BLTAudit/` is built automatically (lakefile globs `BLTAudit.+`), so this root
file imports nothing beyond Mathlib. Shared definitions are in `BLTAudit/Basic.lean`. The work
list is `ROADMAP.md`; CI writes `verification/STATUS.md` and redraws `docs/roadmap.html`.

Nothing in this library proves Theorem 1.1 (relative asymptotic optimality) or Theorem 4.1
(the universal lower bound `a_d ≥ 2π log d - 7π log log d - C`) of the paper.
-/
