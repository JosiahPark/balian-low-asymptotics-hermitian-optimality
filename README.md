# Sharp finite Balian–Low asymptotics for finite Hermite Gabor windows

This repository holds the note
[*Relative asymptotic optimality of finite Hermite Gabor windows*](relative_asymptotic_optimality.pdf)
(J. Park, 25 September 2026) and a Lean 4 + Mathlib (v4.35.0) project, `BLTAudit`, that checks the parts of
it that can be checked today.

[Live roadmap page](https://josiahpark.github.io/balian-low-asymptotics-hermitian-optimality/docs/roadmap.html):
the interactive map of the work list, with the state of each item and of CI.

The note's Theorem 1.1: for the critical orthonormal Gabor problem on `ℂ^{d²}`, the minimal rescaled
difference energy satisfies `2π log d − 7π log log d − C ≤ a_d ≤ 2π log d + C`. So the optimal discrete
limit constant is `lim a_d / log d = 2π`, and the finite-Hermite window attains it to relative order
`O(log log d / log d)` along odd `d`.

## What is and is not verified

- **Checked by CI:** every theorem under `BLTAudit/` compiles with only Lean's three standard axioms.
  [`verification/STATUS.md`](verification/STATUS.md) lists them and is rewritten after every build.
- **Not verified: Theorem 1.1 and Theorem 4.1.** The trial-energy asymptotic (U4)/(U14) and the vortex
  lower bound (L19) are not attempted. The roadmap's last section proves the main statement only from
  those two bounds, taken as named hypotheses `[HU]` and `[HL]`.
- A numerical check of the paper's conventions (the Zak energy identity `d² E(f) = A_d(ζ)` with both
  seams, total plaquette charge one, the Gaussian Zak zero) passed for `d ≤ 7` on 2026-11-19. It is a
  sanity check of the definitions in `BLTAudit/Basic.lean`, not a proof.

## Roadmap

[`ROADMAP.md`](ROADMAP.md) is the ordered work list: finite Gabor and Zak analysis (A), discrete phase
topology (B), the Zak transform of the Gaussian (C), the finite oscillator (D), tools for the vortex
lower bound (E), and the assembly of Theorem 1.1 from named hypotheses (F).

[`docs/roadmap.html`](docs/roadmap.html) draws it as an interactive map, in the style of the
[steklov-lean](https://github.com/JosiahPark/steklov-lean) dependency map: sections as bands, one box per
item, the paper's results as a spine on the right. Select a box for its statement, file, verified theorems,
and what it needs and unlocks. CI refreshes the page's snapshot after every verification run; opened in a
browser, the page also reads `ROADMAP.md` and the status live from `main`.

## How the loop works

An hourly scheduled task takes the first unticked roadmap item, writes one Lean file for it, and commits.
GitHub Actions builds the project, audits the axioms, and updates the status and the roadmap page. The
task ticks the item only after that build passes; if it fails, it fixes the file or withdraws it.

## Layout

- `relative_asymptotic_optimality.pdf`: the note.
- `BLTAudit.lean`, `BLTAudit/Basic.lean`: root file and shared definitions (shifts, modulation, unitary
  DFT, energy, finite Zak transform, twisted phase arrays, Zak energy, Gaussian Zak transform).
- `BLTAudit/<Name>.lean`: one file per roadmap item. Every file under `BLTAudit/` is built automatically.
- `axiom_audit.py`: after `lake build`, runs `#print axioms` on every theorem and fails on `sorry`,
  non-standard axioms, escape hatches, or a proof that is just one of its own hypotheses. It writes
  `verification/STATUS.md` and `verification/STATUS.json`.
- `tools/build_roadmap.py`: refreshes the snapshot inside `docs/roadmap.html`.
- `.github/workflows/lean.yml`: builds, audits, then commits status and roadmap page when they change.

The setup follows [steklov-lean](https://github.com/JosiahPark/steklov-lean) (CI, axiom audit, status
files) and [entropy-quotients-lean](https://github.com/JosiahPark/entropy-quotients-lean) (roadmap page).
The note was prepared with OpenAI Astra, as its acknowledgment says; the Lean scaffold and roadmap were
written with Claude Fable 5.2 (`claude-fable-5-2`), 2026-11-19.
