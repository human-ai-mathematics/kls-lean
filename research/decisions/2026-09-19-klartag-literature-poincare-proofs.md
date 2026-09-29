# Literature Poincaré clause of Klartag frontend identification: implementation round

2026-09-19, the thirteenth round of the day, following the [route round](2026-09-19-klartag-literature-poincare-route.md).
`Q1`, `Q2`, and `Q0` are **all proved**; `Q3` follows directly from the existing definition.
All three conclusions of `thm:klartag-density-frontend-identification` now have local Lean proofs, and the node is marked `\leanok`.
Direct holes remain **0**, certificates **26** (this clause belongs to an existing node; no new certificate). No commit or push.

Starting point: `HEAD = 2a882c8` (one commit ahead of `origin/main`).

## Results

New module `formalization/FunctionalInequalities/Poincare/LocalSlope/Gradient.lean`, with three public declarations:

| Obligation | Declaration | Description |
| --- | --- | --- |
| `Q1` | `Poincare.LocalSlope.holds_iff_memLp_gradient` | Under `ν ≪ m`, valid constants for the slope and gradient formulations coincide |
| `Q2` | `Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient` | Equality of infima for any absolutely continuous intrinsic law |
| `Q0` | `Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient_of_logConcave` | **Goal**: the literature Poincaré clause for log-concave laws |

As planned, **no new definition is added**: validity in the gradient formulation is written inline,
and the optimal constant remains `Poincare.LocalSlope.Intrinsic.constant`.
All analytic work reuses the four proved declarations in `Energy/LocalSlope/Gradient.lean`;
this round only transports the validity predicate and its infimum.

## `Q3`: follows from the definition, with no lemma needed

The route asked for an explicit record of how `Q3` (independence of affine origin) is obtained.
**It is the first option**: `Probability.intrinsicMeasure` already carries no choice of origin,
so the Blueprint sentence follows directly from the existing definition. No lemma was written for it this round.

There is slightly more than expected: **the statement of `Q0` contains no reference measure either**.
Haar measure is constructed inside the proof: the direction submodule is a finite-dimensional normed space,
hence weakly locally compact, giving a `PositiveCompacts` instance. Then use `Measure.addHaarMeasure K₀`
with `Measure.isAddHaarMeasure_addHaarMeasure`.
The constant therefore depends on neither an origin nor a reference measure.
This is the repository's first **internal construction** of Haar measure: existing formulations
(`constant_eq_localSlope`, `ThmSmoothLipschitzConstantEquivalence`) take `m` as an explicit parameter.

## Departures from the route

The route estimated 55–70 lines; the module has 114 lines, including 22 lines of module documentation and three docstrings.
The proof bodies total about 30 lines. The route's “only substantive risk”, matching the test classes on both sides of the
`Q1` equivalence literally, **did not arise**: the triple in `admissible_iff_memLp_gradient` matches the three premises
of the gradient formulation exactly. Each direction takes three lines.

The only implementation obstacle was `unusedSectionVars`: `Q2` and `Q0` do not use `[CompleteSpace E]`.
Following repository convention, add `omit [CompleteSpace E] in`, **before the docstring**;
placing it between the docstring and `theorem` gives `unexpected token 'omit'`.

## Bookkeeping

* Blueprint `thm:klartag-density-frontend-identification`: add two `\lean{}` names,
  `Solutions.LemRelativePerimeterCheegerInfimum.intrinsic` and this round's `Q0`; add `\leanok` to both theorem and proof.
  Rewrite the closing prose: its former claim that the `C_P^lit` clause was uncertified, hence the node lacked leanok, no longer holds.
  **Explicitly state** that this does not certify `thm:logconcave-cheeger-poincare-comparison`.
* Import the new module in aggregate root `FunctionalInequalities.lean`, making it reachable by `lake exe checkdecls`.
* `research/tasks.json`: rewrite the node note; change `infrastructure.status` from `unchecked` to `available`
  (three evidence entries with sha256, `gaps: []`). Also refresh the evidence hash for
  `45-shared-analytic-bridges.tex` under `lem:relative-perimeter-smoothing`, since this round changes that file.
* Audit client `research/audits/KlartagLiteraturePoincareAudit.lean`: restate and prove `Q1`/`Q2`/`Q0` verbatim,
  plus two boundary cases (zero-dimensional direction and transport of a single valid constant).

## Scheduling effect

In `atlas.py ready`, `thm:logconcave-cheeger-poincare-comparison` moves from **`blocked`** to
**`inspect_infrastructure`**: the uncertified-dependency blocker is removed.
It **still does not** receive `\leanok`: the Buser half for `n ≥ 2` remains imported mathematics.
`thm:klartag-density-frontend-identification` becomes `verify_recorded`.

## Validation

`lake build` passes (3515 jobs). The new module and audit client pass `lake env lean -DwarningAsError=true`
with **0 errors and 0 warnings**. **All 8 audit `#print axioms` reports contain only
`propext, Classical.choice, Quot.sound`, with 0 occurrences of `sorryAx`**;
log: `build/audit/klartag-literature-poincare-proofs/scope-audit.log`.
`check_ledger.py`: 26 nodes, 0 errors; `check_blueprint.py`: 88 labels, 0 errors;
`atlas.py check`: 75 nodes, 26 certificates, acyclic; all 104 `research/tests` pass.
`lake exe checkdecls` passes for all **326** `\lean{}` names regenerated from `.tex`, including the 2 added this round.
Direct holes: 0; no WIP modules. The receipt is bound by rerunning `research/verify.py` at the end of this round.
