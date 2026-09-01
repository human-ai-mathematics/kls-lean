# Authorize Issue 2 Stage 5 Run 1 final assembly

Date: 2026-09-01

## Human authorization

The user authorizes exactly one Stage 5 Run 1 after committing the Stage 4B acceptance separately
as commit `cb05ea3` (`experiment: accept stage4b under statement-level ruling`). Stage 5 is the
final layer of the staged Issue 2 reconstruction. It packages the already accepted abstract lower
bound, certificate surface, and Euclidean specialization; it adds no new mathematics.

The standing acceptance policy from the Stage 4B decision remains binding: every definition,
lemma, and theorem statement must be semantically aligned with the frozen specification and
production reference. Proof construction is unconstrained when kernel-valid, assumption-
preserving, silent under the exact pinned compiler command, and free of every prohibited escape
hatch, attribute, option, or diagnostic suppression. Mechanism descriptions are descriptive, not
proof-correspondence requirements. The Stage 5 checklist is authored under this ruling.

## Frozen three-theorem surface

Stage 5 adds exactly these production `Project/LinearTestLower.lean` theorem statements, in
production order, inside the accepted experimental namespace
`Issue2Autoformalization.Stage1A` and under the same complete real Hilbert/measurable/Borel
ambient block:

1. `linearTestLower`, with local `[FiniteDimensional ℝ E]` and
   `[IsProbabilityMeasure μ]`, explicit `MemLp (id : E → E) 2 μ`, and conclusion
   `lambdaMaxCovariance μ ≤ optimalPoincareConstant μ`;
2. `linearTestLowerCertificate`, with the same hypotheses and the exact conjunction of the
   universal admissible-test Rayleigh bound and covariance lower bound, including the frozen
   strict-implicit binder `⦃f : E → ℝ⦄`; and
3. `euclideanLinearTestLower`, with free `{D : ℕ}`, canonical
   `EuclideanSpace ℝ (Fin D)` instances, the probability and second-moment hypotheses, and the
   same extended covariance lower bound.

No attribute, definition, fourth declaration, namespace, section, option, syntax, notation,
macro, manual instance, Gaussian formula, KLS target, or other mathematical content is
authorized.

The finite-dimensional and probability instances on the first two theorems are deliberate
hypothesis redundancy for statement and ledger fidelity: the `lem:linear-test-lower` statement
quantifies over finite-dimensional probability measures even though the accepted underlying
theorems need fewer assumptions. The packaging statements are frozen to that surface rather than
to hypothesis minimality. The actor must preserve the instances exactly, and human review must
not classify them as smuggled assumptions.

The Euclidean theorem includes `D = 0`. Every Hilbert, measurable, Borel, and finite-dimensional
instance comes from Mathlib; none may be added by hand. The accepted zero-dimensional convention
continues to give `lambdaMaxCovariance μ = 0`.

## Import, oracle, and actor boundary

A hidden known-good compile established that `EuclideanSpace` is transitively reachable through
the accepted chain. The exact import surface is therefore only:

```lean
import AcceptedStage4B
```

No extra Mathlib import or harness/API-surface adjustment is needed. The fail-closed verifier
rejects an extra or replacement import. The exact hidden production three-declaration surface is
pinned at
`08583f55632c3a199dcb71b33828539602d922b4cdcfc8cf1913eebd99bd17f9`.

The actor specification, prompt, and sixteen-item human checklist expose no production proof,
oracle material, ledger content, or reviewer finding. The fixture has exactly seventeen entries:
`AGENTS.md`, `TASK.md`, the seven accepted source/compiled pairs from Stage 1A through Stage 4B,
and `CandidateStage5.lean`. All fourteen accepted artifacts are physically read-only and only the
candidate may mutate. The accepted Stage 4B source pin is
`610e9006ffe2e03beb83ec6ec811cfb58ae67621867e191c371264b2066a3188`; its deterministic compiled
dependency hash under Lean 4.33.0 is
`2070b15306e3af609b85e88e80841353b4cb55fbb882d5afc38a903e820646ef`.
`pins/stage_5.sha256` freezes the complete fifty-file actor-facing harness.

## Model-free validation and live-run authorization

Before any model call, the complete Stage 5 model-free suite passed:

- deterministic source-to-`.olean` rebuild of all seven accepted layers;
- exact seventeen-entry reset, immutable accepted dependencies, and compiler-failing sentinel;
- silent compilation of the hidden known-good exact three-theorem surface;
- fail-closed rejection of extra/replacement imports, missing `BorelSpace`, a weakened strict-
  implicit binder, removed deliberate probability hypotheses, and every attribute;
- rejection of an added axiom and diagnostic suppression;
- deny-default Seatbelt enforcement with candidate-only writes and hidden repository, oracle,
  review, client state, and production source;
- one-session, one-turn, zero-descendant complete-trace policy tests; and
- fail-closed acknowledgement and fresh subscription-login gates.

Exactly one fresh subscription-authenticated `gpt-5.6-sol` Run 1 at `high` effort is authorized
under `/private/tmp/humanize2-kls-issue2-stage5-run1`. The exact command
`lean CandidateStage5.lean` must exit zero with empty standard output and standard error. Zero
diagnostics, no escape hatch, no attribute, exact hypotheses, the strict-implicit binder, and the
zero-dimensional Euclidean boundary are mandatory.

After the actor stops, independent verification, hidden oracle verification, complete trace
audit, and post-stop semantic comparison are required. The exact stopped output must be preserved
under `review/pending/`; a new append-only Stage 5 Run 1 exploration must record the attempt; and
the Claude 5 Fable interactive review prompt must follow the Stage 4B template with dedicated
checks for the deliberate hypothesis redundancy and strict-implicit binder.

`mechanical-pass` is not acceptance. The stopped candidate must wait for a separate explicit
human decision. Even later Stage 5 acceptance would complete only the staged reconstruction; the
experiment wrap-up is a separate decision. This authorization promotes no production code,
certifies no dossier, and changes no ledger, manuscript, certificate metadata, or mathematical
status.
