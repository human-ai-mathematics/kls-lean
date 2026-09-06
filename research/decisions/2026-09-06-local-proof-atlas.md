# Local proof atlas and literal KLS target

Date: 2026-09-06 (Asia/Shanghai). The owner approved local implementation of the architecture
review with “这个工作我们先在本地进行，开始吧”. Work remains on the existing local checkout;
no commit, push, branch change, remote dispatch or publication is part of this change.

## Change and provenance

The Chen-project comparison motivated a bounded extension of the existing Blueprint, route
sidecar and certification ledger. Their authorities are retained. `research/tasks.json` adds
explicit mathematical classifications and execution notes; `research/atlas.py` derives the
mathematical task graph and checks cycles, missing classifications, retained assumptions and
certificate coverage. AND/OR route composition and repository adapters are not conflated.
Existing historical source records, ledger statements and route metadata are preserved.

The KLS target now has definition-only Lean modules `KLS/Definitions.lean` and
`KLS/Statement.lean`, with default-build checks in `solutions/StatementChecks.lean`. The target
is the Blueprint's literature/covariance formulation, represented on `EuclideanSpace ℝ (Fin n)`
for every natural n, including zero. A finite `NNReal` constant precedes the dimension and law.
The law is bundled as a probability; compact-set log-concavity and `MemLp id 2` are explicit.

The literature test energy integrates the square of the pointwise local slope on the direction
space of the affine support. The slope is the infimum over positive radii of centered secant
suprema, not the two-moving-point asymptotic Lipschitz constant. The zero center quotient is
harmless and constant functions have zero slope. Extended variance avoids assigning an infinite
real integral the value zero; it is finite on the explicit L² domain. Finite constants are
infimized in `ENNReal`. No smooth/literature equivalence, affine whitening or Cheeger identity
is built into these definitions.

The existing `Covariance.operator` and `operator_inner` declarations are moved intact from
`Poincare/LinearTest.lean` to `Probability/Covariance.lean`. The public names and bodies are
preserved and LinearTest imports the new definition module. This allows the literal statement
to share the covariance definition without importing a proof of a related bound or duplicating
the covariance API. The root aggregate exports the target as a proposition, not a proved theorem.

The three earlier certificates now have the same default-build axiom guards as the Gaussian
and two comparison certificates. `research/verify.py` audits every Blueprint Lean anchor and
all six mapped certificates, checks that no reports are missing, and replays all local source
modules under the explicit library/solutions/examples prefixes. The current Lean checker
assumes the capitalized package name when no prefix is given; that assumption is wrong for this
package, so the runner always supplies prefixes.

A broad-prefix replay initially exposed obsolete compiled modules, including a `Hardy 2` copy
whose old differentiability index no longer matches the current imports. The runner now prepares
a source-manifest-filtered view of current compiled modules, records the copied parts' hashes,
and replays using that local search-path entry. Original build artifacts are retained. Missing
current compiled modules and extra or missing replay reports fail; the old duplicate is not an
accepted dependency or a claimed failure of the current Gaussian proof.

## Evidence and scheduling boundary

Verification hashes tracked and nonignored untracked source files before and after a run.
Successful receipts are usable only against matching content; Git HEAD alone is not enough
for this dirty workspace. Reports include the generated audit source, declaration output,
kernel replay coverage, source manifest and logs. A fresh export supplies dispatch actions.
The change-diff command reports source and declaration changes without imposing an API freeze.

The pilot is the weighted smooth-approximation and literature-comparison chain. It remains
unformalized; the atlas exposes its actual prerequisites and does not replace its missing
analytic proofs by assumptions presented as unconditional results. The KLS declaration is open,
the Cheeger-definition choice remains unresolved, and the six existing ledger nodes retain their
claims. Local kernel replay still trusts compiled third-party imports. Comparator, full fresh
replay, isolated rebuilding and automatic worker dispatch remain later work.

Validation commands and the current receipt are documented in
[verification.md](../verification.md). Generated receipts live in `build/verification/`; they
are evidence for their own exact content snapshot and do not assert a remote CI result.
