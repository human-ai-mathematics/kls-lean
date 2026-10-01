# Current KLS handoff

Updated 2026-10-02. Work from the current source and this handoff; previous execution
windows and instructions are preserved in the [history](research/decisions/2026-10-01-handoff-history.md).

## Verified baseline

Commit `6ca1824f18e81b7409fd6e5aafdc0df53b14678e` is on `main` and `origin/main`.
The full local verifier passed 184 gates, including 173 independent audit clients and
352 replayed modules. [Remote Lean certification](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/36846629874)
passed 180 gates for that exact commit, auditing 5,660 local declarations.
Subsequent documentation changes are not covered by that full-source local receipt.

The ledger has 26 certificates. Auxiliary proofs do not create certificates automatically.
The exact open declaration `FunctionalInequalities.KLS.kls` is the sole intentional hole;
its dependent wrappers are rejected by the whole-library axiom audit. Dimension-free KLS is open.

## Current mathematical scope

- Both numerical Cheeger–Buser comparisons hold for finite-dimensional log-concave laws:
  `C_P^lit ≤ 4 Ψ²` and `Ψ² ≤ π C_P^lit`, including affine-support dimension zero and infinite optima.
- The one-dimensional certificate proves the `4 Var` upper bound; it does not certify universal sharpness.
- ADMG Theorem 3.6's relaxed lower and upper Minkowski identities are proved for finite-mass
  Borel targets under measures finite on bounded Borel sets, using global indicator `L¹` convergence.
  Definition 3.3's globally Lipschitz test class agrees with bounded-support perimeter.
  Lemma 2.1's equality of the two relaxed contents needs only a Borel measure at finite-mass targets.
- Locally Lipschitz variants agree on proper metric spaces at finite-mass targets for every
  Borel measure. Nonproper variants, nonconvex support transfer and general RCD comparisons remain gaps.

For declarations, certificates and exact scopes use the [literature register](research/progress/LITERATURE.md)
and [node register](research/progress/STATUS.md), rather than historical prose.

## Current work and next source review

The user confirmed on 2026-10-02 that future work follows published literature, as requested
by [issue #8](https://github.com/numina-functional-inequalities/kls-lean/issues/8).
The primary plan is the [paper register](research/progress/LITERATURE.md#current-literature-priorities).
The four exploratory branches are retained separately as non-targets. Blueprint/atlas pending
entries do not override this source-led task-selection policy.

Next, audit and pin the strong-curvature Bakry–Émery Poincaré theorem `C_P ≤ 1/ρ`,
then select the Brascamp–Lieb source statement separately. Retain every regularity,
measure, Hessian-positivity and normalization hypothesis; compare the exact statement with
existing Γ₂/semigroup APIs before adding a theorem or promising that the proof is immediate.
Name the published theorem supported by each infrastructure task. Later priorities are KLS
localization, Milman's concentration-to-Cheeger theorem and source-specific stochastic localization.

For stochastic localization, reuse Mathlib foundations and assess pinned external APIs
through a small audited client before introducing a dependency or building missing bridges.
The [implementation record](research/decisions/2026-10-01-issue-8.md) records repository policy,
source assessments and deferred CI optimizations. No new mathematical theorem or certificate
is claimed by the progress reorganization.

## Delivery

Run change-appropriate checks in [research/workflow.md](research/workflow.md).
Stage intended canonical metadata, then regenerate progress with
`python3 research/progress/update.py`; use `--check` to detect drift.
Remote CI is Lean-only and runs only by manual dispatch or `milestone/**` tags.
The full local verifier retains metadata, Python and statement checks. Do not rerun the
already successful unchanged baseline or use `[skip ci]`.
