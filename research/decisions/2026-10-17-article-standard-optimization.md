# Article-standard optimization

Date: 2026-10-17. The owner authorized an optimization of the KLS formalization against article standards after the BKL
file organization. Codex planned and independently accepted each step; the original Claude session wrote the candidates.
No theorem statement, certificate, ledger node, coverage or progress status changed.

## Findings addressed

Codex's read-only article-standard audit found six items:

| Finding | Problem | Resolution |
| --- | --- | --- |
| REVIEW-01 | The strongest Mathlib-only classical KLS specification and client lived only in ignored local evidence | Persisted as a tracked gate (A) |
| REVIEW-02 | No license for project-owned code | Apache-2.0, chosen by the owner (E) |
| REVIEW-03 | The matrix trace-integral extension hard-coded the coefficient 2 | Arbitrary real coefficient (B) |
| REVIEW-04 | The closed cutoff-energy and cumulant assembly was repeated in two certificates and in `Theorem41.lean` | One shared producer, thin certificates (C) |
| REVIEW-05 | The Letwin regular-class proof consumed the moment witness through deep positional projections | A flat named-property theorem at the same witness (D) |
| REVIEW-06 | The Letwin `remaining` text began with superseded chronology | Concise current scope, history archived (E) |

## Changes

**A — classical specification gate** (`research/audits/KLS/Classical/`).
- **Templates.** Byte copies of the second review's Mathlib-only specification (`f52663e2398d7eb45433dbad4edd808ae02a03fb8167467f937a9e12205a8d0f`)
  and client (`d7e762f9ddd616d37a98d5e80f8fea40b5972507b76989dad8b4a12055b8f864`), pinned in `config.json`.
- **Driver.** `check.py` reuses the verifier's axiom parser.
- **Gate.** `classical-kls` in `research/verify.py`, in both modes; the lean-only snapshot binds every file of the
  directory.
- **Mutations.** Each mutated specification must be rejected by a specific client elaboration error, calibrated from the
  first preserved run:
  - dropped log-concavity: `Application type mismatch`;
  - dropped gradient energy: `Type mismatch`;
  - strict inequality: a `change` that is not definitionally equal.
- **Records.** [Gate guide](../audits/KLS/Classical/README.md) and [review record](2026-10-17-classical-kls-specification.md).

**B — `Analysis/Matrix/Integral.lean`.**
- `symmetric_trace_integral_extension_mul_of_ae_posSemidef` (a.e. PSD field) and `symmetric_trace_integral_extension_mul`
  (pointwise) take an implicit real `C` with no sign condition.
- The a.e. proof is the existing proof with the coefficient replaced.
- `symmetric_trace_integral_extension` and `symmetric_trace_integral_extension_of_ae_posSemidef` keep their exact types as
  `C = 2` specializations.
- Client: `research/audits/MatrixTraceIntegralCoefficientAudit.lean`, with a scalar field of coefficient `c²` on an
  indefinite `B`, and an empty index with `C = −1`.

**C — BKL cumulant closure.**
- **`KLS/BKL/Theorem41.lean`** (conditional, explicit compact Letwin hypothesis) adds:
  - `cutoffEnergyClaim_of_letwinCompact`, the single assembly of the cutoff induction;
  - `cumulantBound_of_letwinCompact`.

  `theorem41Compact` now consumes the shared producer, with its type unchanged.
- **New `KLS/BKL/CumulantBound.lean`**, importing exactly `Theorem41` and `Letwin.CompactBound`, holds the closed
  `cutoffEnergyClaim_153` and `cumulantBound_153`.
- **`Poincare.lean`** imports it with `Reduction`. `theorem11` consumes `cumulantBound_153`, with its type unchanged.
- **Certificates.** `LemBklCutoffEnergy.bound` and `ThmBklCumulantBound.bound` are thin clients of the closed producers and
  import neither Poincare nor Reduction. Their types are unchanged.

**D — `KLS/CEK/MomentRegularity.lean`.**
- `exists_regular_moment_hessian_trace_bound` returns a flat conjunction at the same actual witness:
  - convexity, the Lipschitz bound, normalization and pushforward;
  - `C¹` with a `16/κ`-Lipschitz gradient;
  - the a.e. Hessian data;
  - the Hessian mean `Id`;
  - the weak Theorem 2.5 bound.

  Its hypotheses are exactly those of `exists_regular_moment_weak_stein_coupling`.
- `regularClass_matrix_variance_le_eight` consumes it through one `obtain`; its type is unchanged.

**E — documentation and license.**
- **Letwin `remaining`.** Rewritten to its current scope; the previous string is preserved byte for byte in the
  [register notes](2026-10-17-pre-article-optimization-register-notes.md).
- **Current guides.** HANDOFF (archived [here](2026-10-17-pre-article-optimization-handoff.md)), the root README,
  certificates guide, naming guide, Lean design, BKL module guide and generated filename directory.
- **Metadata.** The Blueprint `\lean` lists of the affected nodes gain the new names, and the evidence pins of changed
  sources are refreshed.
- **License.** The root `LICENSE` is the Apache License 2.0 text, byte-identical to
  `formalization/vendor/BrownianMotion/LICENSE`. Vendored libraries keep their own licenses, notices and copyright lines.

## Validation (scratch evidence under the ignored `build/reviews/2026-10-17-article-standard-optimization/`)

**Source (B–D).**
- 15 changed and descendant modules were rebuilt strictly on a fresh copy of the organization receipt view.
- The 18 dependent audits and the new client compile.
- All 65 declarations of the rebuilt modules use the standard axioms only.
- 572 modules were replayed.
- Full elaborated types are unchanged for all 46 pre-existing declarations checked, including 21 public roots. Codex's
  comparison used untruncated printing.
- Accepted in `CODEX-SOURCE-ACCEPTANCE.json` (`56a9b9e92524aa8454bba601bad49bc331d580b2c156d7ae6ff49a51c5eb5f15`).

**Gate (A).**
- On the accepted view: four standard-axiom reports, both runtime modules replayed, three mutations rejected.
- The full Python suite of 180 tests passed with the candidate verifier.
- Accepted in `CODEX-AUDIT-ACCEPTANCE.json` (`420255ad1f4ea77cdf516d06b7235492619d9ad229a4848f6da57c6f536e3e64`).

**Snapshot.** The integrated snapshot is accepted only with a passed full local verification report for that exact
snapshot and its independent acceptance, recorded in the optimization's control checkpoint.
