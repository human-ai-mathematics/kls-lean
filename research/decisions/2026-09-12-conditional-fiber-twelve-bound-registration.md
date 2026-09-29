# 2026-09-12 — `cor:conditional-fiber-twelve-bound`: Register as the 23rd certificate

## Decision

On the same day, after the proof landed (see [proof record](2026-09-11-conditional-fiber-twelve-bound-proofs.md)), the node was registered as a Lean certificate.
The six theorem types of `KLS/LogConcave/ConditionalFiber.lean` are consistent with the [statement record](2026-09-11-conditional-fiber-twelve-bound-statement.md), and no further modifications were made during registration. Not `git commit`, not `git push` (user instruction).

**Statement change (owner's decision)**: The original blueprint inference wrote `D_{μ,ρ}(f) ≤ 12∫|∇f|²`, `CPLit(μ) ≤ 12C`,
is now changed to `4` and `4C`—these are exactly the constants provided by `thm:one-dimensional-logconcave-poincare`, and also the strength actually proven in Lean.
The commonly cited `12` is retained as a direct weakening in one sentence of the main text and in Lean's `_of_four` version.
The `q:conditional-fiber-frame`-following section's `CPLit ≤ 12C` is simultaneously changed to `4C`.

## New and Modifications

- Certificate `solutions/CorConditionalFiberTwelveBound.lean`:
  `Solutions.CorConditionalFiberTwelveBound.certificate μ ρ hμ hρ m hac` Package the Blueprint proof in four steps:
  (1) `∀ᵐ b ∂baseLaw μ ρ, KLS.LogConcave ⟨kernel μ ρ b, _⟩`; (2) `FiberBound μ ρ 4`;
  (3) Each `Energy.LocalSlope.Admissible μ f` satisfies `energy μ ρ f ≤ 4 * Energy.LocalSlope.energy μ f ∧ ≠ ⊤`;
  (4) Each `C : NNReal`, the form gap bound on `domain μ ρ` implies `Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * C`.
  Six `example`: gradient form `4 ∫⁻ ofReal ‖∇f‖ ^ 2`, weak version of literature constant `12`, finite energy test landing on `domain μ ρ`,
  Corollary as an instance of the parametrized comparison lemma, `EuclideanSpace ℝ (Fin (n+1))` with `volume` as Haar reference,
  `Fin 0` The probability measure on the sphere does not exist. Three axioms guard (certificates and two library theorems), all of which are `propext / Classical.choice / Quot.sound`.
- `formalization/lakefile.toml`: `Solutions` adds `solutions.CorConditionalFiberTwelveBound`.
- `formalization/FunctionalInequalities.lean`: Added five imports (`KLS.ConditionalFiber.SliceKernel`,
  `KLS.LogConcave.Line.OfDensity`, `KLS.LogConcave.ConditionalFiber`, `Probability.Line.BrunnMinkowski`,
  (`Probability.HaarLine`), add a paragraph to the module documentation explaining the inference and its three analytical inputs.
- `research/a-series/ledger.yaml`: add node `cor:conditional-fiber-twelve-bound` (`kind: lemma`, `proved / lean`),
  `meta.scope` Append log-concave condition fiber with constant 4; total of twenty-three nodes.
- `research/check_blueprint.py`: `CERTIFICATES` new mapping.
- `formalization/blueprint/route-composition.yaml`: This node claims `open → proved`, Lean evidence
  (`kls-lean`, ledger node, certificate assertion).
- `research/tasks.json`: This node `missing → available`, `gaps` cleared, evidence changed to fifteen repository file entries (including four new modules and certifications)
  Hashes of sixteen used Mathlib files; `note` rewritten as a complete proof path.
  Also refresh three hashes expired due to this edit: `lem:conditional-fiber-energy-comparison`'s `EnergyComparison.lean`
  (Only removed one `private`, evaluation unchanged), `prop:weighted-spectator-obstruction`'s `50-kls-routes.tex`
  (This evaluation addresses the missing Eldan random localization objects, and is unrelated to the current edit's conditional fiber section.)
- Blueprint `50-kls-routes.tex`: the introductory section `leanok` states the addition of this lemma; the lemma block constant is changed to `4` (`12` as a weakened retention is retained as a sentence),
  add `\lean{ae_conditionalFiber_logConcave, conditionalFiber_fiberBound_four,
  conditionalFiber_energy_le_four_mul, conditionalFiber_literatureConstant_le_four_mul, certificate}`
  With `\leanok`, append Lean reading style for the tail; add `\leanok` to proof blocks and local Lean path segments (Borell density, slice kernels, Haar line splitting,
  One-dimensional Prékopa–Leindler, Dirac law at bad points); `q:conditional-fiber-frame` after `12C` amend `4C`;
  The "pinned provenance" section is rewritten as a statement already having Lean certificates, with a constant `4` assertion, and the upstream factor-four is merely historical provenance.
  `00-orientation-and-status.tex`: The conditional fiber path statement is modified to three nodes all certified, `12` is a weakening of `4`,
  The remaining gate is `q:conditional-fiber-frame`.
- Current guide: `HANDOFF.md` (new section, twenty-three counting, certificate table new row, rewrite at end of comparison lemma section), `README.md`,
  `research/verification.md` (counting and new section), `formalization/README.md` (two places),
  `formalization/FunctionalInequalities/KLS/README.md` (two lines),
  `formalization/FunctionalInequalities/KLS/LogConcave/README.md` (a line),
  `formalization/blueprint/README.md`, `solutions/README.md` (counting and new section), `research/naming.md` (five lines).
  statement golden, `STATEMENT_CHECKS`, `FoundationAxiomAudit` unchanged.

## Check

- `python3 research/check_ledger.py`: 23 node, 0 error. `python3 research/check_blueprint.py`: 87 label, 0 error.
- `python3 research/atlas.py check`: 74 mathematical node, 23 certification, acyclic.
- `python3 -m unittest discover -s research/tests -p 'test_*.py'`: 103 item passes entirely.
  (Differing from the previous round, this round no longer has failures caused by the lake/git environment: the local elan and all Lean toolchains have been switched from x86_64 to native arm64,)
  The cause was the missing x86_64 slice in CLT’s `libxcrun.dylib` when x86_64 Lake invoked `/usr/bin/git`; repository content and system Git configuration were unchanged.)
- `lake build` (default target) successful, 3390 jobs; `solutions.CorConditionalFiberTwelveBound` built.
- `python3 formalization/blueprint/build.py checkdecls` Run successful, but plastex is not installed on this machine,
  `blueprint/lean_decls` is still the old list from 2026-09-08, **not covering the five newly added `\lean{}` names**.
  As an alternative, the five qualified names were individually `lake env lean` `#check`, all parsed successfully, 0 error.
  CI will regenerate `lean_decls` and perform a true comparison.
- The receipt for `python3 research/verify.py` is generated after this record and all guideline edits, with its source code SHA recorded within the receipt itself, not written back to this file.

## Evidence Boundary

Local kernel replay trusts third-party compiled imports; no isolation reconstruction, remote CI, commit, or push.
This registration does not advance `q:conditional-fiber-frame`: the deduction provides fiber input `κ = 4`, not the framework bound,
thus still lacking `μ`'s Poincaré inequality and the KLS conclusion. `conj:kls` and the status of the four routes remain unchanged.

## Supplement (same day): Downstream residue cleanup for constant modifications

After the registration round, recheck the whole repository still writing `12`'s location, categorizing into three types: Bobkov's one-dimensional `12·Var` (retained), decision records that only append (not modified), and the constant output of this lemma (should be `4`). The third category discovered two errors, both in `HANDOFF.md`, already fixed:

- At the end of the section on one-dimensional sharp constants, the original text read "The fiber corollary `cor:conditional-fiber-twelve-bound` still records `12C` and can be sharpened to `4C`", which has now been strengthened to `4C` and certified.
- In the route status list, the original entry "the fiber corollary still records `12C` and can be sharpened to `4C`" has been updated to indicate that this corollary has also been formally verified in Lean (`Solutions.CorConditionalFiberTwelveBound.certificate`), stated as `4C`, with literature `12C` representing its weakened version.

After verification, it is confirmed that there are no other residuals: the adapters of `formalization/blueprint/route-composition.yaml` do not encode numerical constants; the `Var ≥ 1/(12c²)` of `45-shared-analytic-bridges.tex` is the Bobkov variance lower bound, independent of route constants; the `12` in `FunctionalInequalities.lean`, `Line/SharpPoincare.lean`, and `solutions/ThmOneDimensionalLogConcavePoincare.lean` all refer to Bobkov's one-dimensional independent proof.

**Labels and identifiers unchanged**: `cor:conditional-fiber-twelve-bound` (Blueprint label, ledger node ID, `tasks.json` key, route sidecar node) and `Solutions.CorConditionalFiberTwelveBound` still carry "twelve". According to `research/naming.md` "certificate entry, ledger node ID, and source label retain stable identity", constant changes do not trigger renaming; values are as stated in the statement and this record.
