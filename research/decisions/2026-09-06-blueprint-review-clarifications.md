# Blueprint review clarifications

**Date:** 2026-09-06 (Asia/Shanghai). **Authorization:** after the screenshot review and the
independent assessment of its five points, the owner instructed “fill in the gaps according to your assessment”. Work is
local on `main`, based on `70ca1c19c4d207a31716c2e589c0b096521a5490`.

This record follows [analytic bridge resolution](2026-09-06-analytic-bridge-resolution.md),
which followed [comparison proof acceptance](2026-09-06-poincare-comparison-proofs.md).
Both earlier records remain unchanged. Their counts describe successive validation snapshots:

| Stage | Blueprint labels | PDF pages |
| --- | --- | --- |
| Comparison proof acceptance | 77 | 27 |
| Analytic bridge resolution | 86 | 33 |
| This review clarification | 86 | 34 |

The current reading order is also linked from the root `HANDOFF.md`.

## Corrections

1. **Fiber-form density.** The structural lemma now uses only the fiber-form definition.
   Its proof applies the independent-copy variance identity to a globally Lipschitz test,
   giving `D(f) ≤ d Lip(f)^2`. Finite second moment supplies `f ∈ L²`; exceptional fibers
   follow the existing zero-contribution convention. This puts compactly supported smooth
   tests in the domain without a one-dimensional Poincaré input. The imported statement's
   scope is retained; the proof explicitly identifies the weaker assumptions needed for
   density. The distinct integrated-gradient comparison still uses its finite input `κ`.
2. **Cheeger conventions.** The Cheeger--Buser proof names the BV/Minkowski relaxation
   result, explains equality of the Cheeger infima, and accounts for restriction to the
   closed intrinsic support and the half-mass convention. The bibliography now points to
   all the ADMG results used here. The source is
   [ADMG, Lemma 2.1 and Theorem 3.6](https://arxiv.org/pdf/1603.08412).
3. **Numerical wording.** Removed the unsupported description of `π` as a sharp coefficient.
   The proof records the Rayleigh energy normalization and the stronger zero-curvature
   bound in [De Ponti--Mondino, equation (2) and Corollary 1.2](https://arxiv.org/pdf/1902.03835).
   The displayed inequalities retain their valid constants `4` and `π`.
4. **Direct dependency.** The parameterized fiber-energy comparison now explicitly uses
   `def:literature-poincare-constant`.
5. **Lean navigation.** The two relaxation comparison docstrings cross-reference one another.
   They distinguish exact test lifts through continuous maps between topological spaces
   from recovery-sequence comparison in one pseudometric space. Both declarations remain.

## Mathematical and certification scope

All displayed theorem hypotheses and conclusions, all status markers, and all Lean executable
source are unchanged. The Lean edits are confined to the two docstrings. The six certificates,
foundation axiom guards, production ledger, route sidecar, and pre-existing decision and
exploration records are byte-identical to the start-of-turn snapshot.

The analytic bridge nodes retain `notready`. This follow-up adds proof explanations and source
alignment, not new Lean proofs of disintegration, BV theory, Cheeger--Buser, or KLS. No commit
or push was performed.

## Validation

- `lake build` passed: 3241 jobs, including the foundation audit and existing certificates.
- Ledger checker: six nodes, zero errors.
- Blueprint checker: eight chapter files, 86 labels, four active routes, zero errors.
- Existing Python suite: all 63 tests passed.
- Blueprint PDF, web, and `checkdecls` passed after the Lean build completed.
- The final PDF has 34 pages, no overfull boxes, no unresolved references or bibliography
  warnings. Nine existing underfull-box notices remain. PDF pages 18--20, 26--29, and 33--34
  were rendered and visually checked, including both edited proofs and the bibliography.
- Source comparisons verified unchanged Lean code outside docstrings, unchanged displayed
  mathematical statements and status markers, and the two exact dependency corrections.
- `git diff --check` passed; the turn preserved all pre-existing unrelated changes.

The first combined Blueprint run reached `checkdecls` while the concurrent Lean rebuild had
not yet recreated `SmoothGradient.olean`. PDF and web generation had completed. After the
default Lean build finished, rerunning the full Blueprint command passed. This was a check
ordering issue and required no mathematical or implementation change.

The local evidence snapshot is
`/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-review-cleanup-559ywf39/`,
with source hashes, the final Lean output chunk, both Blueprint logs, scope checks, and rendered
pages. These temporary files are validation evidence, not committed repository artifacts.
