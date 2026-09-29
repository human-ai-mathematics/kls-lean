# Lean foundation cleanup and Blueprint boundary corrections

Date: 2026-09-05. The user authorized corrections to review findings and cleanup of existing
Lean code, preserving mathematical correctness and generality and following formech's
presentation style. This record covers only this round, following earlier Blueprint-fix records.

Starting HEAD: `70ca1c19c4d207a31716c2e589c0b096521a5490`. Uncommitted Blueprint, checker, and
test changes already existed and were preserved in the working tree. No commit, push, or
remote CI run was performed in this round.

## Corrected mathematical interfaces

The conditional-fiber route in `formalization/blueprint/src/chapters/50-kls-routes.tex` now states:

1. Frame construction requires `d ≥ 1`. The zero-dimensional unit sphere is empty, so it has no probability frame; zero-dimensional KLS is handled directly by zero variance.
2. Quantifiers specify one finite constant for all dimensions and measures, then a frame independent of the test function for each measure: `∃ C ≥ 0, ∀ d ≥ 1, ∀ μ, ∃ ρμ, ∀ f`.
3. The fiber-energy integral is extended nonnegative; its maximal form domain consists of finite-energy `L²` classes. Locally Lipschitz tests with finite gradient energy belong to that domain, allowing the form gap to apply to every test in the literature Poincaré definition.
4. The form and factor-four bound retain their general finite-second-moment/log-concave measure scope, without adding isotropy of `μ`. Directional averaging needs isotropy of the frame; only the route's existence question concerns isotropic `μ`.
5. The named affine/isotropic bridge transfers the positive-dimensional isotropic conclusion to all affine supports; the sidecar includes it in the conditional-fiber branch's `all_of`.

These correct Blueprint statements and dependencies, without changing the upstream source pin,
upstream ledger status, local `leanok` or `notready` status, or claiming a new local Lean proof.
The fiber-form formula's source and local interface clarifications are identified separately.

The smooth-gradient heading “quadratic dense core” becomes “quadratic pre-energy with dense
realization”, to avoid interpreting `L²` density as a graph-norm core. The linear-lower-bound
proof description uses the covariance Rayleigh characterization actually used; it does not
claim a local API identifying the largest eigenvalue with the operator norm.

The PDF previously rendered some references sharing the theorem counter as “Theorem”.
The print macros now retain shared numbering while setting the correct cleveref type within
each environment, so Assumption, Lemma, and other references match their targets.

## Lean cleanup

New `Energy/RelaxationApproximation.lean` extracts only two steps reused by existing proofs:

- `PreEnergy.exists_test_near_of_relaxation_lt`: choose a test within any positive radius with energy below a strict upper bound. Strictness avoids requiring an optimal test.
- `PreEnergy.DenseRealization.nonempty_approximatingSequence`: obtain an approximating sequence from dense realization and Mathlib's `mem_closure_iff_seq_limit`.

Lower semicontinuity and finite-energy recovery share the first step; infinite-energy recovery
shares the second. Finite/infinite branches, density premises, nonquadratic cases, and
pseudometric generality are retained. Existing public declarations keep their names,
parameters, typeclass premises, and conclusions. Legacy and relaxed-energy constants are
not merged, and no unproved mathematical bridge is introduced.

`TestFamily` field documentation is completed, and a comment incorrectly calling the extended
Rayleigh quotient finite is corrected. Foundation remains an explicit application aggregate;
reusable lower-level modules do not import it back.

## Presentation and continuous verification

The presentation references are the README and two Lean entry points of
`lyw-ops/formech@d0bb1913acc1f710ba6eadf1244b633abbc75fb9`. Adopt their approach of starting
from mathematical meaning, giving concrete examples, and stating model boundaries and build
commands, without importing their domain model or global notation.

- Rewrite the Poincaré foundation guide with entry points and a usable interface first, followed by generality, closure, affine support, four constant interfaces, and unproved boundaries. Keep the complete file tree in `formalization/README.md`.
- Add 12 compiling examples in `examples/PoincareFoundation.lean`, covering energy comparison, arbitrary probability laws, zero-dimensional Euclidean instances, the Dirac raw-energy counterexample, empty test classes, and Gaussian values. They enter the default `Examples` target without new public theorems or ledger nodes.
- Add `solutions/FoundationAxiomAudit.lean` to fix the transitive axiom sets of eight core declarations in the default build, supplementing the Gaussian audit and four node certificates.
- Synchronize Lake targets, current documentation, and the CI cache scan for direct Mathlib imports in examples. Lean, Mathlib, and checkdecls version pins are unchanged.

## Verification results

| Check | Result |
| --- | --- |
| Full `lake build` | Passed, 3234 jobs |
| 8 added or modified Lean modules, `-DwarningAsError=true` | All passed |
| Type and axiom comparison for existing project-namespace declarations | All 665 retained; printed types unchanged; no additional axiom dependencies |
| New public declarations | Only the two approximation lemmas above; 667 declarations after comparison |
| Default usage examples | All 12 compiled |
| Foundation axiom guards | All 8 passed; only `propext`, `Classical.choice`, `Quot.sound` |
| Ledger checker | 4 nodes, 0 errors |
| Blueprint checker | 73 labels, 4 active routes, 0 errors |
| Python tests | 63 passed |
| Blueprint PDF, web, checkdecls | All built; 27-page PDF |
| Final PDF log | No undefined references/citations, duplicate labels, or overfull boxes; 8 underfull notices |
| Modified PDF pages | Physical pages 9, 14, 24, 25 individually rendered and inspected |
| Relative Markdown links after editing | No missing targets |
| `git diff --check` | Passed |

The declaration comparison imports the library aggregate and four certificates before and
after editing, prints types with `Meta.ppExpr`, collects transitive axioms with
`Lean.collectAxioms`, and compares by full declaration name. The 665 declarations include
structure fields and generated public declarations; they are not 665 independent mathematical
theorems. The comparator requires nonempty input with at least 400 records to prevent a false
pass from an empty parse. Type comparison and itemwise source-diff review together check the
existing mathematical interfaces; Lean compilation verifies the modified proofs.

Local verification artifacts for this round are in:

```text
/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-cleanup-20260905-y_qb33wj/
```

`api-before.txt` and `api-after.txt` are declaration-text snapshots;
`api-comparison.json` is the structured comparison. Their SHA-256 values are:

```text
before  9ece29407b9e96c146940be9b076db60d99c95e571aa86fb23b9c2fec03305e4
after   df74034328b375e459f79b1f5edc475c9d519565d4d335b658ed89e8569e9be4
```

All 49 protected files present at the start (historical records, four certificates, ledger,
toolchain/manifest, and unrelated ` 2` copies) were individually checked by SHA-256 and remained
unchanged. These temporary verification artifacts are not new production control files.

Subsequent KLS statements, constant bridges, whitening, and long-route proofs continue within
the original mathematical boundaries.
