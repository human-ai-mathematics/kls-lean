# N10b weak generator identities: canonical integration

Date: 2026-10-14. The owner authorized a Codex/Claude/API division of work for the minimal N10b chain: Codex froze six small contracts, controlled dependency order and accepted each candidate independently; Claude ran one existing gpt-6-astra/high loop per contract in ignored scratch and integrated only after Codex acceptance and a Codex-accepted placement plan. No other large task, worker, controller or Goal was started; no commit, push, tag, publication or remote CI is authorized.

## Target and scope

Pinned consumer: Letwin arXiv:2607.24164v1, equation (2.2), weak C^{1,1} counterpart, toward Theorem 2.5 and the compact constant-8 Theorem 1.2 on the BKL path. The two declarations of the original `L-N10b-generator-symmetry` frozen statement are proved exactly as frozen: `FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy` and `FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy'`. Hypotheses: u in C1 with Lipschitz gradient, V in C1, Lipschitz exponent -u + V(gradient u), det Hess u = exp(-u + V(gradient u)) almost everywhere, w in C1 with Lipschitz gradient, eta in C2 with compact support; every dimension. No C2 hypothesis on u or w, positive dimension, pointwise determinant, positive definiteness or added integrability premise. These are supports; Letwin Theorems 2.5/1.2, BKL Theorems 4.1/1.1 and KLS remain open, and no paper coverage changes.

## Accepted chain

| Contract | Statement | Accepted candidate sha256 | Type hash |
| --- | --- | --- | --- |
| N10b.1 | `exists_lipschitz_compact_exp_gradient_test` | `94b9b011…5ecf2` | 3888316748 |
| N10b.2 | `ae_fderiv_exp_gradient_test` | `25ba58ee…b89e2` | 1308585157 |
| N10b.3 | `ae_fderiv_mongeAmpere_exponent` | `36e3f854…d4537` | 2739830079 |
| N10b.4 | `integrable_inv_hessianMatrix_mul_of_bounded_compact` | `d5fad992…bd4c36` | 1022078404 |
| N10b.5 | `sum_inv_gradient_test_sub_chain_eq` | `e29cc165…17911e` | 526362223 |
| N10b.6 | the two original identities | `a168c44c…d977e7` | 700686545 / 4130481219 |

Independent acceptance receipts: `build/reviews/2026-10-13-codex-claude-n10-controller/independent/N10b{1..6}/ACCEPTANCE.json`. The earlier failed 18-round N10b loop and its diagnostics are unchanged.

## Placement

Following `PLACEMENT.json` (`CODEX_PLACEMENT_ACCEPT`):

- `Analysis/Matrix/Piola.lean` (extended): the public interface `integrable_inv_hessianMatrix_mul_of_bounded_compact` is added at the end of the weak inverse-Hessian divergence section. Its body is the accepted N10b.4 body with the scratch helpers replaced by the existing `n10_cofactor_bound` and `n10_measurable_cofactor` (the accepted copies were identical to them up to the name prefix); two comments were made location-independent. The prior file text is unchanged (46 lines added, none removed).
- `Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean` (new, namespace `FunctionalInequalities.Analysis`): the weak inverse-metric integration property, kept apart from the classical `InverseHessian` (different regularity and dependencies) and from the mean-Hessian `LipschitzHessian`. It holds the two public identities and, private, the one-use supports N10b.1/2/3/5 and all helpers of N10b.2/3/6, with bodies verbatim from the accepted candidates; each source keeps its original `open` lines in its own section. N10b.2 reuses privately the two gradient-only coordinate lemmas whose verified bodies are private in `Probability/Stein/HessianKernel.lean` (provenance N11e), because the public C1 bridge does not supply the weaker premise; no existing N11e/R0 API was altered, exported or renamed. The trailing N10b.3 client example and `#print` were omitted.
- Imports: `Analysis.Matrix.Piola`, `Probability.Diffusion.Cutoff`, `Probability.Stein.HessianKernel`, Mathlib `Calculus.Rademacher` and the low-level matrix imports of N10b.5; no scratch module.
- Root aggregate: one import line added after `IntegrationByParts.LipschitzHessian`.

API impact: three new public declarations; the two original names and types are unchanged; the four scratch-public supports are now private (`_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakInverseHessian.0.FunctionalInequalities.Analysis.<name>`). No existing public declaration moved or was renamed; no aliases. The full map is `build/reviews/2026-10-13-codex-claude-n10-controller/integration/NAME-TYPE-MAP.json`.

## Validation

Strict compilation (`-DwarningAsError=true`) of both changed modules and of the new audit client `research/audits/BKL/WeakInverseHessianAudit.lean` (canonical imports only) is clean; the full library build passes. All seven declarations keep their accepted elaborated type hashes, with standard axioms only (`propext`, `Classical.choice`, `Quot.sound`); both original theorem headers and the Piola interface header are byte-identical to their frozen sources. The audit covers both original statements, the actual compact-test generator symmetry consumer, the integrability interface and a compactly supported Lipschitz test derivative consumer. Blueprint `lem:letwin-weak-inverse-hessian-integrability` and `lem:letwin-weak-generator-symmetry` were appended to `45-shared-analytic-bridges.tex` (old chapter text an exact prefix); the Letwin T25 paper-map entry lists the new declarations and stays partial. The final complete verifier receipt is recorded in the controller's `STATE.json` and `CLAUDE-INTEGRATION-REPORT.md`.
