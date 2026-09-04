# Gaussian Poincaré: statement-stage validation

Date: 2026-09-04 (Asia/Shanghai).
Baseline: `10e4c707491830ebe9d07f7bfc5e65efeddc7e2e` on `main`, with the local candidate changes.
Node: `lem:poincare-gaussian-one-dimensional`, **drafted / checked_by: null**.

## Result and scope

The statement preparation is complete for human review. All 20 new theorem declarations
elaborate, their source notes and semantic boundaries were reviewed, and the solution entry
point is included in the default Lake build. Every new mathematical obligation remains
`by sorry`. There is no human freeze, completed Gaussian proof, named Gaussian certificate,
GitHub Issue creation, commit, push or CI claim in this stage.

The [reading guide](../../formalization/FunctionalInequalities/Poincare/Gaussian/README.md)
introduces the mathematics and examples. The [candidate package](../decisions/2026-09-04-gaussian-poincare-candidate.md)
contains all source signatures and the exact ledger node; the
[source/API audit](2026-09-04-gaussian-poincare-design.md) records origins and the proof route.

## Checks performed

| Check | Result |
| --- | --- |
| `python3 research/check_ledger.py` | 1 ledger, 4 nodes, 0 errors; the new node is drafted and the three previous nodes remain proved. |
| `python3 -m unittest discover -s research/tests -p 'test_*.py'` | All 24 existing regression tests passed. |
| `cd formalization && lake build` | Successful default build, 3130 jobs. Exactly 20 expected proof-placeholder warnings, all from the new Gaussian declarations; no other warning or error. |
| `lake env lean ../solutions/LemPoincareGaussianOneDimensional.lean` | Exit 0; 20 named signature checks, 7 typed applications, and 1 future-certificate proposition-type check. |
| Dedicated signature extraction using the same 20 `#check @...` lines and printer options | Exit 0; complete output saved in `2026-09-04-gaussian-poincare-signatures.txt`. |
| Protected-file comparison with the pre-edit baseline | All 45 protected tracked files unchanged, including every pre-existing Lean source, historical decision/exploration, checker/tests, CI workflow, toolchain and dependency manifest. |
| Existing ledger node comparison | All three accepted node objects are unchanged. Only the Gaussian node and current program-scope description were added/updated. |
| Placeholder structure | `Density.lean`: 7 theorems/7 proof placeholders; `Real.lean`: 13 theorems/13 proof placeholders. The solution adds no theorem, definition, axiom or duplicate proof obligation. |

The default build was rerun after the final Lean docstring clarification. The documentation
and configuration changes update the current reading paths and status; historical records
were preserved. These are local statement checks using the pinned dependencies, not a clean
published-commit or CI acceptance run. That later evidence belongs to the final proof stage.

## Axiom boundary

A separate Lean probe imported all three accepted solution modules and the new Gaussian
module, then printed the transitive axioms of their main declarations.

| Declaration | Reported axioms |
| --- | --- |
| `Solutions.LemLinearTestLower.certificate` | `propext`, `Classical.choice`, `Quot.sound` |
| `Solutions.LemPoincareTensorization.certificate` | `propext`, `Classical.choice`, `Quot.sound` |
| `Solutions.LemPoincareFiniteTensorization.certificate` | `propext`, `Classical.choice`, `Quot.sound` |
| `FunctionalInequalities.Poincare.holds_gaussianReal` | The same standard axioms plus `sorryAx` |
| `FunctionalInequalities.Poincare.constant_gaussianReal` | The same standard axioms plus `sorryAx` |

The new declarations therefore remain explicitly unproved even though their types compile.
The accepted certificates retain their original proof dependencies when the draft module is
loaded alongside them. The proved aggregate is unchanged and does not import Gaussian.

## Semantic review

The primary reviewer and an independent reviewer checked all 20 candidate declarations.
The positive-variance density derivative has coefficient −(x−m)/v. Both one-sided first-moment
tails equal v times the density; the left integral uses m−x and the left half-line. Signed
integrability supplies the absolute-integrability obligations for improper FTC.

The nonnegative triangle identities retain their correct integration regions and allow
`g : ℝ → ENNReal` to take infinity without a finiteness premise. Each real half-line estimate
uses only its own half-line energy; their sum gives v times the whole energy. Density-weighted
integrability is a separate contract, not inferred solely from totalized real-integral
equalities. The finite-interval C¹ helper does not require global Lebesgue L² membership of f′.

Both main targets include every mean and nonnegative variance. The zero-variance branch uses
a Dirac law on the real line. The identity test has variance v and energy one, so every finite
valid constant is at least v; the existing extended-infimum interfaces give the final equality
without an attainment assumption. No change to `Admissible`, `energy`, `Holds` or `constant`
was made. One source note was clarified to distinguish the local `ENNReal` encoding from
Definition 2.1 itself. No mathematical signature change was needed by the review.

## Reproducible candidate identifiers

The signature snapshot uses these options and all 20 `#check @...` lines from the solution:

```lean
import FunctionalInequalities.Poincare.Gaussian.Real
set_option pp.universes true
set_option pp.funBinderTypes true
set_option format.width 100
```

Run that temporary probe with `lake env lean` from `formalization/` and compare its complete
standard output with the saved signature file. The two identifiers are:

- Complete signature output, SHA-256 including final newline:
  `8103fa2acdfa4f2ed7df32b3d72496c65863de9c34da8b3c8c3148a893c763ca`.
- Ledger `statement` string, UTF-8 without an added newline, SHA-256:
  `07fa78f7a1a97217da6726a4f09fe043191413447e9a01715f850d9a38625574`.

These identify the reviewed candidate version; they are not a substitute for human approval.
After approval, a separate freeze record must preserve the chosen full signatures and ledger
claim before the independent proof stage begins.
