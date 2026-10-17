# Cutoff and weak-derivative responsibility layout (2026-10-17)

This is the first source-layout batch after the documentation correction. It supports the
existing Letwin arXiv:2607.24164v1 weak regular-class chain and BKL arXiv:2610.05474v1 cutoff
localization infrastructure. No mathematical target, proof payload, hypothesis, normalization,
dimensional scope, public declaration name or certificate status changes.

## Placement

- Extend `Analysis/Lipschitz/Gradient.lean` with the existing generic gradient/fderiv norm facts.
- Move the actual smooth scaled cutoff to `Analysis/Cutoff/SmoothBall.lean` and the distinct
  Lipschitz norm-ball cutoff/localization to `Analysis/Cutoff/LipschitzBall.lean`.
  The former is one on radius R and zero outside 2R; the latter is clamp(R+1-norm).
- Split `Analysis/WeakDerivative.lean` into the substantive `WeakDerivative/` family:
  `Basic` (definition, uniqueness, classical/a.e. identification and the C1 cutoff product),
  `Mollification` (convolution and difference bounds), `Approximation` (cutoff gluing and smooth
  compact approximations), and `Calculus` (rough products, exponential chain rule, rough testing
  and integrable weak divergence).
- Keep rough products, chain rule and testing together: bounded products use the chain rule
  private compact-test helper, while rough testing uses the product proof private L2 pairing
  helper. The attempted finer split was rejected by those actual shared private dependencies.
  The C1 cutoff product stays in Basic, so Approximation does not depend on rough Calculus.
  Neither visibility changes nor duplicate proofs are introduced.

The generic tools retain their existing namespaces, including Energy/Probability-qualified
names. A namespace migration is a separate API change and is not part of this batch. No old-path
wrappers or aliases remain. Energy, Probability and KLS consumers import the generic owners.

The complete [source and declaration map](../api-migration/2026-10-17-cutoff-weak-derivative-map.json)
records the one-to-many split, private/compiler identifier correspondence and actual imports.

## Proof provenance and validation

The weak-calculus source provenance remains the Letwin controller's L-W3a/W3b1 and subsequent
weak-route supporting work; the Lipschitz cutoff provenance remains BKL S5cd. Existing declaration
and proof text is compared with the captured source spans. Repeated namespace/section/open
context is scaffolding only; necessary private supports remain with their consumers.

Independent acceptance compares the elaborated types and local definition closures, preserves
source declaration payloads, updates real clients and metadata source owners, regenerates views
from a private index, and requires a full local build, strict audit clients, axiom checks and
local-module replay. Evidence hashes are refreshed only after source/interface comparison.
Batch diagnostics and receipts are retained under
`build/file-management/2026-10-17-other-families-optimization/batch-01-cutoff-weak-derivative/`.
Historical records and the user's real index/staging are preserved. There is no commit, push,
remote CI, API/Claude run or proof/certificate status advancement.
