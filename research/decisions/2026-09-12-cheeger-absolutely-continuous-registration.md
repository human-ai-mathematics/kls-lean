# 2026-09-12 — `cor:absolutely-continuous-relaxation-two-cheeger`: Register as Certificate 24

Take over [statement record](2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md),
[proof record](2026-09-11-smooth-gradient-relaxation-two-cheeger-proofs.md) and
[metadata record](2026-09-12-smooth-gradient-relaxation-two-cheeger-metadata.md), according to
[this round's prompt](2026-09-12-cheeger-absolutely-continuous-scope-prompt.md).
Not `git commit`, not `git push`.

## Decision

Take out and make positive the absolutely continuous/log-concave range that is already without `sorry` in `Energy/WIP/Cheeger.lean`, and establish it as a new Blueprint node
`cor:absolutely-continuous-relaxation-two-cheeger` and register as certificate number twenty-four.
**The statement for the unconditional node `thm:smooth-gradient-relaxation-two-cheeger` has not been modified or added `\lean{}`/`\leanok`, and remains unauthenticated.**

## Module Splitting

Originally a single WIP module in row 584 is split into three:

| File | Content | Status |
|---|---|---|
| `Energy/LocalSlope/Relaxation.lean` | `AsymptoticLipschitz.{apply,energy,Admissible,preEnergy,relaxation}`, `LocalSlope.{preEnergy,relaxation}` and their unconditional `sorry` lemma, unconditional comparison `relaxation_le_asymptoticLipschitz` | Registered, no `sorry` |
| `Energy/Cheeger.lean` | `Cheeger.{ofLocalSlope,ofAsymptoticLipschitz,energy,Intrinsic.energy}`, `SmoothGradient.Test.*`, `localSlope_relaxation_le`, two `_of_absolutelyContinuous`, `Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous`, `KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` | Registered, no `sorry` |
| `Energy/WIP/Cheeger.lean` | **Only** five open obligations for singular cases (two true obligations + three three-line implications) | Unregistered |

"The absence of `sorry` in dependency closure is not asserted manually, but rather enforced by the compiler: five declarations were removed from two registered modules. If any remaining declaration (transitively) references them, `lake env lean` will fail with unknown identifier. The build passes successfully."

The types of all declarations have not been changed; only their positions have been moved and module docstrings have been added according to the new modules.

## New and Modifications

- Certificate `solutions/CorAbsolutelyContinuousRelaxationTwoCheeger.lean`:
  `certificate μ m hac` package (1) `SmoothGradient.relaxation (intrinsicMeasure μ) = LocalSlope.relaxation (intrinsicMeasure μ)`;
  (2) For each `f : L²(μ)`, `SmoothGradient.Intrinsic.energy μ f = 2 * Cheeger.Intrinsic.energy μ f`.
  Five `example`: log-concave law automatically satisfies the premise, convention `2·Ch = LocalSlope.relaxation`, unconditional inequality
  `LocalSlope.relaxation ≤ SmoothGradient.relaxation`, a point space with Cheeger energy zero, standard applications of Euclidean family.
  Three axioms are guarded, all being `propext / Classical.choice / Quot.sound`.
- Blueprint `30-open-canonical-bridges.tex`: Add a lemma block after the unconditional theorem (`\uses{def:selected-canonical-frontend,
  lem:logconcave-intrinsic-absolute-continuity}`,  six \lean{} names, one statement and one proof block each (\leanok)
  And rewrite the preceding explanatory paragraph to specify that the entire content of the open obligation is the WIP module, with the absolutely continuous range already listed and certified.
- `formalization/lakefile.toml`'s `Solutions` roots; `formalization/FunctionalInequalities.lean` adds two imports and a section of documentation.
- `research/a-series/ledger.yaml`: Add the 24th node (`proved / lean`), `meta.scope` appended.
- `research/check_blueprint.py`'s `CERTIFICATES` new mapping.
- `research/tasks.json`: **unchanged**. Nodes recorded in the ledger do not require task entries (`atlas.py` only applies to
  (`not recorded and not in records` error), there was no evidence of expired hash in this round either.
- `formalization/blueprint/route-composition.yaml`: **unmodified**. This node belongs to the open bridge of Chapter 30, and is not part of any route
  `all_of` member; unconditional nodes are also not in sidecar. `atlas.py check` passed, without entries.
- Guidelines: `HANDOFF.md` (new section, twenty-four counting, certificate table new row), `README.md`, `research/verification.md` (counting and new section),
  `formalization/README.md`, `formalization/FunctionalInequalities/Energy/README.md` (two lines),
  `formalization/blueprint/README.md`, `solutions/README.md` (counting and new section),
  `research/naming.md` (two lines, recording the three groups of names listed in the "Not Done" section)

### Two outdated statements corrected alongside registration

- `formalization/blueprint/README.md` Originally wrote "The remaining marked node is `thm:smooth-gradient-relaxation-two-cheeger`" —— the marking was removed at 2026-09-12, and now no node carries `\notready`; rewritten accordingly.
- `formalization/README.md` Originally wrote in the conditional fiber section: "does not provide ... an identification with Cheeger energy `2 · Ch`" —— now provides it within the absolutely continuous range; rewritten and note that the singular case remains open.

## Check

- `python3 research/check_ledger.py`: 24 node, 0 error. `python3 research/check_blueprint.py`: 88 label, 0 error.
- `python3 research/atlas.py check`: 75 math node, 24 certificate, acyclic.
- `python3 -m unittest discover -s research/tests -p 'test_*.py'`: all 103 items passed.
- `lake build` (default target) succeeded; `lake env lean -DwarningAsError=true` produced no output for either of the two newly registered modules or certificates.
- `blueprint/lean_decls` Because plastex is not installed locally, the old list remains, so the six newly added `\lean{}` names are now verified individually via `lake env lean`'s `#check` (see below). CI will regenerate the list and perform a true comparison.
- The receipt for `python3 research/verify.py` is generated after this record and all guide edits.

## Evidence Boundary

Local kernel replay trust third-party compiled import; no isolation reconstruction, remote CI, commit, or push.
This registration **does not advance** `thm:smooth-gradient-relaxation-two-cheeger`: comparison between two relaxations under singular measures and identification of smooth gradient relaxation still lack literature references and proofs, five obligations remain unchanged in the WIP module.
No advancement is made regarding Poincaré constants, Cheeger–Buser comparisons, or `def:isoperimetric-cheeger-scale`'s isoperimetric numbers.
