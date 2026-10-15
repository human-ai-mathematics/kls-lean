# N11d weak third Hessian derivatives: canonical integration

Date: 2026-10-14. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)). Codex froze four small contracts N11d.1-N11d.4 and accepted
each candidate independently (`build/reviews/2026-10-14-letwin-constant-eight-goal/independent/N11d1..4`). The complete package passed
Codex's isolated placement prototype (`N11d-placement-prototype/RESULT.json`, CODEX_COMPLETE_N11D_PLACEMENT_PROTOTYPE_PASS) and placement
acceptance (`N11d-integration/PLACEMENT-ACCEPTANCE.json`, CODEX_PLACEMENT_ACCEPT). Claude integrated the exact prototype bytes
(`N11d-integration/SOURCE-MANIFEST.json`) as sole canonical writer. No commit, push, tag, remote CI or release is authorized.

## Target and exact scope

The original L-N11d statement `FunctionalInequalities.Analysis.exists_weak_third_derivative` (weak Letwin route toward Theorem 2.5,
consumed through Theorem 1.2 by BKL Lemma 4.2) is proved with its original docstring, header and complete type (type hash 2055644421).

The hypotheses are unchanged:
- C1 convex u with G-Lipschitz gradient;
- C1 convex V;
- a globally LF-Lipschitz exponent -u + V(gradient u);
- K > 0;
- almost everywhere positive definite Hessian with log det = -u + V(gradient u) and the cap Hess u <= K;
- the global centered-difference bound u(x+h) + u(x-h) - 2u(x) <= D|h|^2 for all x and h;
- every finite dimension, including zero.

The conclusion produces an actual tensor T. For all coordinate indices k, i, j, the Hessian entry (i, j) has the weak derivative
T(., k, i, j) along the k-th basis vector, and T(., k, i, j) is L2 on every compact set. There is no cutoff or test-function input, and
no given tensor, H1 or cutoff square-difference-energy conclusion or C2 hypothesis is assumed; the original global centered-difference
bound is an input, distinct from the global L2 translation bound C t^2 produced by N11d.3.

It is a supporting result. Applying it to the actual R0 regular source law still requires closing the two original inputs, the global
centered-difference bound and the global Lipschitz exponent, from R0 data. The current source proves the centered-difference bound
with coefficient 4/kappa only as an internal step (`hsd`) of `lipschitzWith_gradient_of_map_gradient`
(`Analysis/Convex/GradientLipschitz.lean`), and exports no declaration or consumer for it. The result is the original weak, locally L2 tensor support; it does not establish global
C2 or smooth regularity, smooth Letwin Lemma 2.2, Theorem 2.5, Theorem 1.2, compact constant 8, unconditional BKL or KLS. Paper
coverage, the 30 ledger certificates and the covered ADM-G/BGL targets are unchanged.

## Placement (all accepted bodies verbatim)

| Accepted part | Declarations | Owner |
| --- | --- | --- |
| N11d.1 | `Analysis.exists_smooth_compact_translate_majorant` | `Analysis/Cutoff/Translation.lean` (new leaf in the existing cutoff family; three Mathlib imports) |
| N11d.2 | `Probability.Stein.memLp_hessianMatrix_entry_of_isCompact`, `Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry` | `Probability/Stein/HessianKernel.lean` (extended; old file an exact byte prefix; no new import) |
| N11d.3 | `Analysis.exists_hessian_cutoff_sq_difference_bound` (+ private `n11d3_entry_sq_le_total`) | `Analysis/Convex/HessianIncrement.lean` (extended; one new header import `Analysis.Cutoff.Translation`, otherwise the old file is an exact prefix; accepted local `maxHeartbeats 800000` kept, no linter/type/axiom/kernel override) |
| N11d.4 | `Analysis.exists_weak_third_derivative` | `Analysis/Convex/HessianRegularity.lean` (new; imports `Analysis.Convex.HessianIncrement` and `Analysis.WeakDerivative`) |

API and import changes:
- Public names and namespaces are exactly the accepted ones: five new public declarations, and no namespace migration, alias or change
  to an existing public declaration.
- Import map:
  - each scratch `CandidateN11d1/2/3` import was replaced by its canonical owner;
  - the original `CandidateLN11b` import of the L-N11d statement was replaced by canonical `HessianIncrement`;
  - the root aggregate gains the imports of `Analysis.Cutoff.Translation` and `Analysis.Convex.HessianRegularity`.
- Nothing low-level imports `HessianRegularity`.

The generic N11e theorem `ae_weak_third_derivative_symm` consumes a given tensor and does not depend on this producer. No logical edge is
drawn from the producer to it.

## Audit

The new audit `research/audits/BKL/WeakHessianRegularityAudit.lean` contains Codex's eight genuine client bodies. They are placed in the
audit-only namespaces `WeakHessianRegularityAudit.{Geometry,EntryLp,DifferenceEnergy,Tensor}`:
- the uniform majorant as an original energy test;
- the global criterion and cutoff gluing consumers of the entry L2 interfaces;
- the difference energy feeding both weak-derivative criteria;
- the produced tensor with its N11e almost-everywhere symmetry, local L2 bounds and weak testing identity.

The audit imports only canonical modules and prints thirteen standard axiom reports.

## Validation

Local canonical checks:
- `lake build` completed (9514 jobs).
- Strict `-DwarningAsError=true` compilation of the four owners, the aggregate and the audit produced empty logs.
- All five complete types equal the accepted hashes: 2719651189, 2068056844, 425888721, 3629892747, 2055644421.
- All public axiom reports and the thirteen audit reports use only propext, Classical.choice and Quot.sound.
- `leanchecker` replay of the four changed or new modules passed.
- The original L-N11d header, opens and context are present verbatim.

Metadata changes:
- The Blueprint chapter `45-shared-analytic-bridges.tex` gains four lemmas, appended so that the old chapter is an exact prefix.
- `nodes.json`, `tasks.json` (pinned evidence hashes of the extended files refreshed), `literature.json`, the proof path, `HANDOFF.md`
  and the root summary are synchronized.

At this documentation freeze a fresh full `research/verify.py` run is required and pending. Its exact report will be recorded in the
ignored `N11d-integration/CLAUDE-INTEGRATION-REPORT.md` and `STATE.json`. Codex's independent canonical acceptance is also pending.

## Next

1. Close the actual R0 source-law inputs (the global centered-difference bound and the global exponent Lipschitz constant) from the
   regular-class data, without changing the R0 normalization.
2. Then local H1 and the chain rule, weak Hessian evolution and the integrated trace estimate, weak Brascamp-Lieb, Stein/H^-1 transport,
   and the spectral constant-8 assembly.

No proof task is dispatched by this integration.
