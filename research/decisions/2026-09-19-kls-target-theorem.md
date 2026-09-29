# KLS target exposed as a theorem with `sorry`; unproved assertions must not exist only as `def : Prop`

2026-09-19. Owner decision. The starting worktree contains the day's uncommitted semigroup modules (`S1`–`S5`).

## Decision

1. Add the leaf module `formalization/FunctionalInequalities/KLS/Target.lean`:
   `theorem FunctionalInequalities.KLS.kls : Conjecture := by sorry`.
   This is the repository's **sole intentionally retained direct hole**, making the final target visible in Lean as well as Blueprint.
2. **Keep** `def KLS.Conjecture : Prop` in `KLS/Statement.lean` as the name of the proposition,
   for proved theorems using it as a conclusion or hypothesis (`conjecture_of_affineBound`, certificate `ThmAffineIsotropicReduction`,
   `StatementChecks`, and the golden statement snapshot). All four references and certificates remain unchanged.
3. **Rule**, effective from this record:
   * `def X : Prop` may only name a proposition; it asserts nothing.
   * Any unproved **assertion** must appear in Lean as `theorem … := by sorry`, not merely “exist” as a def.
   * A target theorem containing `sorry` must live in a leaf module imported only by the aggregate root.

## Why the def is retained

`def : Prop` does not assume KLS is true; Mathlib uses the same pattern for `RiemannHypothesis` and `FermatLastTheorem`.
All four references have the form `… → Conjecture`, with KLS in the **conclusion**. These are unconditionally proved reductions,
which remain true even if KLS is false (in that case they say `AffineBound K` is false for every `K`).
There is no conditional result of the form `Conjecture → …` in the repository.
Deleting the def would require copying the full formula inline at four sites, losing a single source of truth and rebuilding
the golden snapshot, at greater cost and with more risk of drift.

## Validation constraints determining placement and labels

* `research/check_ledger.py` forbids `sorry` in any certificate's import closure, so `Target.lean` cannot be imported
  by any internal library module or certificate. Only aggregate root `FunctionalInequalities.lean` imports it.
* The `declaration-audit` gate of `research/verify.py` audits the axioms of each declaration in Blueprint `\lean{…}` tags
  and fails on `sorryAx`. Thus `conj:kls` still lists only `KLS.Conjecture` in `\lean`; `kls` is mentioned only in prose.
* `lake build` passes: the lakefile does not enable `warningAsError`, so `sorry` is a warning. The same applies to CI's `lake build`.
* The single-file check `lake env lean -DwarningAsError=true KLS/Target.lean` **will fail**, as expected;
  the zero-warning convention does not apply to this file.

## Reporting change

Earlier records reported “0 direct holes, 26 certificates”. From this record onward, report:
**1 intentional direct hole (`KLS.kls`), 0 unintended direct holes, 26 certificates**.
Subsequent audits must not treat this one hole as a regression.

## Rule refinement: why the other three `conjectural` nodes receive no theorem (same day, owner decision)

The precise formulation of rule 3 is: **every unproved assertion with an existing precise Lean proposition must appear as `theorem … := by sorry`.**
For nodes without such a proposition, do not invent statements or placeholder definitions merely to satisfy the rule;
that would fabricate content and defeat its purpose. The other three `conjectural` nodes in `tasks.json` all fall into this category.
This round **writes no Lean for them**, recording the reason and prerequisites in their respective `note` fields instead:

| Node | Kind | Why no Lean statement exists yet | Prerequisites for stating it |
| --- | --- | --- | --- |
| `q:smooth-gradient-raw-core-agreement` | Open-ended question (“determine when”) | Blueprint explicitly avoids assuming graph-norm/sequential-core equivalence by definition; the graph-norm finite-energy domain has not been constructed. A theorem would require us to invent a concrete proposition for the owner | The owner selects a precise formulation; define graph-norm density on the `Energy.Functional` domain |
| `ass:tight-prefix-carleson` | Assumption about manuscript objects | `S_t, r_t, D_t, τ_η` are two-color quantities from Eldan stochastic localization. Neither the repository nor pinned Mathlib has SDE/Itô theory (Mathlib has Brownian motion, filtrations, and stopping times, but no stochastic integration) | Stochastic-localization definitions: process, stopping times, two-color quantities |
| `q:mm-spectral-occupation` | Open-ended question | `g_t, H_t, A_t` are first-eigenfunction quantities along stochastic localization, again requiring SDE/Itô theory; a smooth strongly log-concave approximation scheme must also be fixed | The same prerequisites, plus formalization of the approximation scheme |

The difference from KLS is that `KLS.Conjecture` was already a precise `def : Prop`; adding its theorem changes presentation.
Adding theorems for these three nodes would create new mathematical content.

## Changes

* Add `formalization/FunctionalInequalities/KLS/Target.lean`.
* Add its import to `formalization/FunctionalInequalities.lean`.
* Append an explanatory paragraph after `conj:kls` in `formalization/blueprint/src/chapters/00-orientation-and-status.tex`.
* Append to the `note` of `conj:kls` in `research/tasks.json`.
* Add a table row in `formalization/FunctionalInequalities/KLS/README.md` and extend the status line in `formalization/README.md`.
