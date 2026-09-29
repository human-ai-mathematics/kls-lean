# Weighted Smooth Approximation: Statement and Claude Proof Handoff

Date: 2026-09-06. User request: "Advance the first mathematical task, write only statement, leave sorry, I'll have Claude handle sorry". This batch contains only `lem:covariance-test-core-density`'s four candidate statements; no proofs are written or tasks sent to other Agents. Node is **`drafted / checked_by: null`**, all four proof bodies are `by sorry`. This is not proof verification, nor does it require prior interface freezing.

## Reading Entry and Source

1. First read the repository [HANDOFF](../../HANDOFF.md), especially the authority hierarchy, interface evolution, and append-only record rules.
2. The mathematical origin is local [Blueprint Appendix A](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex)
   of `lem:covariance-test-core-density` and its immediately following proof. It is an existing local analytical argument,
   `tasks.json` will still mark the mathematical state as `local_argument`, without attributing it to a paper that has not been checked.
3. The main contract and four proof holes are located at
   [LipschitzApproximation.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/LipschitzApproximation.lean).
4. Default build entry
   [LemCovarianceTestCoreDensity.lean](../../solutions/LemCovarianceTestCoreDensity.lean)
   only imports this module and `#check` four complete signatures, without `certificate` wrapping.

Statements are located in the `FunctionalInequalities.Energy.Euclidean.LipschitzApproximation` namespace.
First read the main result `exists_smooth_weighted_L2_approximation`, and proceed with the proof in the following order.

## Four proof obligations

| Order | Statement | Input and output | Suggested route |
| --- | --- | --- | --- |
| 1 | `exists_compactSupport_weighted_L2_approximation` | Locally Lipschitz g, with g and B∇g in L²(ν); obtain a compactly supported, globally Lipschitz sequence with function and weighted gradient converging in L² | Smooth cutoff χ_R g; estimate the cutoff gradient error and L² tail term |
| 2 | `exists_smooth_compactSupport_L2_approximation` | Compactly supported g with Lipschitz constant K; obtain a compactly supported C∞ sequence preserving K, with function and full gradient converging in L² | Nonnegative normalized compactly supported convolution kernel, a.e. gradient convergence, bounded dominated convergence |
| 3 | `exists_smooth_weighted_L2_approximation` | Same input as step 1; obtain a compactly supported C∞ sequence approximating g and B∇g simultaneously | Use continuity of B to turn step 2 into a weighted estimate, then combine with step 1 by diagonal selection |
| 4 | `exists_smooth_bounded_L1_approximation` | Globally K-Lipschitz with a ≤ g ≤ b; obtain a C∞ sequence in the same interval with the same K, with function and gradient converging in L¹ | No cutoff; directly use nonnegative normalized convolution; no compact-support requirement |

Steps 2 and 4 also conclude `MemLp` for the original function and gradient, deriving these from global Lipschitzness,
boundedness, and the probability measure. Every step explicitly requires the corresponding `MemLp` for approximation terms.
Convergence is expressed by the `eLpNorm` of the difference tending to zero, rather than by a real integral that may be totalized to zero.

## Mathematical scope and usage

E is any finite-dimensional complete real inner product space with a Borel measurable structure and second-countable topology; ν is a probability law.
The reference measure m satisfies `Measure.IsAddHaarMeasure m`, and ν ≪ m is assumed. Any positive normalization of Lebesgue/Haar measure is allowed,
so the statement is not restricted to coordinate implementations. The convolution kernel must be normalized relative to the actual m.
Dimension zero is included, without adding a positive-dimension assumption.

The main L² statement requires only square integrability of B∇g. B is an arbitrary continuous linear endomorphism, including zero and operators with nontrivial kernel;
in finite dimensions this covers the linear maps in the mathematical source. Do not add an L² assumption on the full gradient merely to apply an existing smooth-test interface,
and do not require B to be invertible or positive definite. No log-concavity, finite second moments, or positive lower density bound is required for ν;
the proof does not rely on comparing densities before and after translation.

Taking B to be the identity gives ordinary function-and-gradient L² approximation; orthogonal projections retain degenerate weights.
Taking a=0 and b=1 in step 4 gives Blueprint's range-preserving version. Any bounded globally Lipschitz function has its range in some closed interval.
Preserving the same K and allowing arbitrary [a,b] states the convolution step's local specification explicitly, without adding stronger input assumptions to the main conclusion.

`gradient` is Mathlib's standard Hilbert gradient, defined to be zero at nondifferentiable points. Almost-everywhere differentiability of locally Lipschitz functions
and its connection with convolution/weak derivatives remain proof obligations.
Under `open scoped ContDiff`, `ContDiff ℝ ∞` means ordinary C∞; do not replace it with analyticity,
`ContDiff ℝ ⊤`. This batch introduces no new gradient, energy, or test class.

## Mathlib starting points and missing connections

Current toolchain is Lean/Mathlib v4.33.0, Mathlib commit is
`db584cd6d46c92f209a44c0f1c829460d327499d`. The following names have been verified in local source code for reference and localization:
They are not among the four target statements that already have existing proofs.

- `Mathlib/Analysis/Calculus/Rademacher.lean`: `LipschitzWith.ae_differentiableAt`,
  together with the `integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul` series.
- `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`:
  `ContDiffBump.convolution_tendsto_right_of_continuous` and
  `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`.
- `Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`:
  The differentiability conclusion of `HasCompactSupport.hasFDerivAt_convolution_right` rests on its own regularity assumptions;
  invoking it alone cannot substitute for an analysis argument that transfers derivatives to functions with only Lipschitz continuity.
- `Mathlib/Analysis/Calculus/BumpFunction/` provides the infrastructure for smooth truncation and normalization kernels;
  the function value approximation in `SmoothApprox.lean` does not inherently provide the required gradient approximation.

Key work includes: global Lipschitz control of truncation functions, measurability and a.e, gradient identity, gradient convergence under Lipschitz smoothing, transfer of zero-measure sets via ν ≪ m, and dominated convergence in weighted L²/L¹ norms.
This is not an exhaustive enumeration of missing theorems in the entire Mathlib; further exploration of more direct existing APIs is warranted.
The infrastructure for `tasks.json` remains `missing`, with only additional annotations added for the current handover position.

## Task Boundary for Claude

Complete the four theorem bodies by adding proof-aiding lemmas with clear stated purposes. Do not reframe "existence of a required approximating sequence" as an input assumption. Do not weaken the main statements to ensure compilation success. If it is actually discovered that the statement must be modified, record the mathematical rationale, the updated input-output specification, and whether the original goal remains covered, and synchronize the ledger. Interfaces are not required to be permanently frozen.

This batch does not process the next `lem:covariance-core-closure`, nor does it prove the correspondence between local slopes and gradients, comparison of Poincaré constants, Dirichlet properties, or KLS. This module does not include aggregated imports from certified libraries. Six certificate declarations and imports remain unchanged. Blueprint labels, route status, mathematical classification, and golden are unchanged.

After proof completion, compile the relevant modules and default target, verify the transitive axioms of new declarations and certificates, remove the four `sorry`, then establish node certificates and append verification records according to the actual coverage scope. Draft entry access is navigated via ledger and the default Lake target; currently, no draft Blueprint `\lean{}` anchor point has been added. The validator will audit all such anchors and must not ignore its `sorryAx` after linking draft declarations, nor relax the checker for this task.

## Local Check Record

Git HEAD: `70ca1c19c4d207a31716c2e589c0b096521a5490`. The following check targets the working tree with existing uncommitted modifications, plus the batch statement/registration/guide modifications, recording the source SHA256 of the file prior to its write as
`56a786c6abb35d83567e06c801005c59afb011b6e0eb8e23f44ee170101dd965`.
Hashes are saved file by file in `build/draft-statements/20260906-weighted-approximation/checked-source.json`.

| Check | Actual Result |
| --- | --- |
| `lake build solutions.LemCovarianceTestCoreDensity` (under formalization) | Final pass, 2889 jobs; four complete signatures preserved with expected parameters: finite-dimensional, Haar, and absolutely continuous |
| `python3 research/check_ledger.py` | Passed, 7 ledger nodes, of which 6 were proved, 1 were drafted |
| `python3 research/check_blueprint.py` | Passed, 86 labels, 4 active routes |
| `python3 research/atlas.py check` | Passed, 73 mathematical nodes, 6 certificates, acyclic |
| `python3 -m unittest discover -s research/tests -p 'test_*.py'` | 97 items passed |
| `lake build` (under formalization) | Passed, 3247 jobs; exactly four `declaration uses sorry` warnings in this batch |
| Execution of `#print axioms` on four statements | All included `sorryAx`, explicitly marked as unproven |
| `python3 research/statement_snapshot.py check` | Passed, public statements and definitions of closure consistent with the original golden version |

Log located at `build/draft-statements/20260906-weighted-approximation/`, considered local output to be ignored.
Initial module compilation revealed issues with the Haar namespace and C∞ notation scope; these have been resolved, and subsequent runs of the target and default builds passed.
Passing in this batch only indicates successful elaboration of statements.

The full `verify.py` was not executed, full module leanchecker replay, isolated rebuild, or remote CI was not run.
The previous full verification receipt `build/verification/20260906T115425.436083Z/report.json`'s source snapshot
pre-dates the current modifications and cannot be used to certify the current working tree. No commit/push was present, and no prior stash was updated.
Historical decisions/explorations remains unchanged.
