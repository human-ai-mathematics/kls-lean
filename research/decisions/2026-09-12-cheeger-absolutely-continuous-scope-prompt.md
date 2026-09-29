# 2026-09-12 — Prompt for next session: Convert and register the absolutely continuous range identified by Cheeger to positive form

Preliminary remarks. The statement design for `thm:smooth-gradient-relaxation-two-cheeger` is documented in [Statement Record](2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md), proof filling is detailed in [Proof Record](2026-09-11-smooth-gradient-relaxation-two-cheeger-proofs.md), and the rationale for removal and classification of `\notready` remains consistent with `unknown` as described in [Metadata Record](2026-09-12-smooth-gradient-relaxation-two-cheeger-metadata.md).
This prompt **does not** require addressing the 5 open obligations: the goal is to extract and formalize the absolutely continuous/log-concave range from `Energy/WIP/Cheeger.lean` that is already free of `sorry`, and establish it as a new Blueprint node, registered as the twenty-fourth certificate. The complete template for the registration round is available in [Previous Registration Record](2026-09-12-conditional-fiber-twelve-bound-registration.md).

---

```
Repository: /Users/lyuyuwei/Documents/ChatGPT/KLS (Lean 4 / Mathlib v4.33.0, Mathlib submission
db584cd6d46c92f209a44c0f1c829460d327499d; Lake root directory formalization/).
Local elan and all Lean toolchain components are natively arm64, lake can git properly, **no** git wrapper scripts or GIT_EXEC_PATH are needed.

Task: Split the range of "absolute continuity / log-concave" from formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean, where the "sorry" has already been removed, and establish a new Blueprint node, then register it as the twenty-fourth Lean certificate according to repository standards.
**Do not attempt to prove the 5 open obligations** (comparison of AGS-type relaxations under singular measures); they remain in WIP.

The mathematical content being promoted to official status (all currently proven, no sorry):
  Energy.SmoothGradient.relaxation_le_localSlope_of_absolutelyContinuous
  Energy.SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous
      (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) :
      relaxation ν = LocalSlope.relaxation ν
  Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous
      (μ : ProbabilityMeasure E) (m : Measure (Probability.affineSupport μ).direction)
      [m.IsAddHaarMeasure] (hac : (Probability.intrinsicMeasure μ : Measure _) ≪ m)
      (f : Lp ℝ 2 (μ : Measure E)) : energy μ f = 2 * Cheeger.Intrinsic.energy μ f
  FunctionalInequalities.KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger
      (hμ : LogConcave μ) (f : Lp ℝ 2 (μ : Measure E)) :
      Energy.SmoothGradient.Intrinsic.energy μ f = 2 * Energy.Cheeger.Intrinsic.energy μ f
The last certified lemma: logconcave-intrinsic-absolute-continuity covers **all** log-concave laws, is the half truly needed in the KLS route.

Must remain in WIP of 5 sorry (position based on current file, line numbers will vary with splitting):
  LocalSlope.relaxation_eq_asymptoticLipschitz          -- genuine open obligation
  SmoothGradient.relaxation_eq_localSlope               -- genuine open obligation
  Cheeger.energy_eq_ofAsymptoticLipschitz               -- three-line inference of the former
  SmoothGradient.relaxation_eq_two_mul_cheeger          -- three-line inference of the latter
  SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger    -- three-line inference of the latter (Blueprint unconditional theorem entity)

Read first:
- research/decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md
  (Conventions: local slope Cheeger, Lip_a version to be explicitly stated separately; the "not done" section at the end already specifies what needs to be done upon promotion, follow it accordingly)
- research/decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-proofs.md (status of each obligation in 26)
- research/decisions/2026-09-12-smooth-gradient-relaxation-two-cheeger-metadata.md (reasons for removing \notready)
- research/decisions/2026-09-12-conditional-fiber-twelve-bound-registration.md (complete list of registered rounds, copy the procedure exactly)
- formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean (row 584, all content)
- research/verification.md (semantic meaning of field tasks.json, three status records in infrastructure)
- research/naming.md (short name rules; table rows to be added upon promotion are already listed in the "not done" section of the statement record)

Rules:
1. **Do not change the type of any already proven statement** (theorems, def, structure signatures remain unchanged), only move them and add docstrings.
2. **Do not touch the 5 sorry statements**, nor attempt to prove them.
3. After promotion, the module must be **completely without sorry**: after disassembly, verify that the "sorry-free" part is closed under dependencies — no declaration in the registered module may (indirectly) reference the 5 ones. Do not assert this based on this instruction; verify it yourself.
4. **Do not alter the statement of the unconditional node** thm:smooth-gradient-relaxation-two-cheeger, nor add \lean{}/\leanok; it remains unauthenticated. New nodes are **a different** label.
5. Decisions are only appended: create a new research/decisions/2026-09-1X-cheeger-absolutely-continuous-registration.md.
Do not revert any existing decision records.
6. Do not git commit, do not git push.

Suggested route:

## A. Module Splitting
The statement record has set the target layout: moving from `Energy/WIP/` to `Energy/Cheeger/` and `Energy/LocalSlope/`. Recommendation:
  Energy/LocalSlope/Relaxation.lean   —— AsymptoticLipschitz.{apply,energy,Admissible,preEnergy,relaxation},
                                          LocalSlope.{preEnergy,relaxation} and its sorry-free lemmas
  Energy/Cheeger/Basic.lean           —— Cheeger.{ofLocalSlope,ofAsymptoticLipschitz,energy,Intrinsic.energy}
                                          and energy_apply, two_mul_energy, energy_eq_zero_of_subsingleton
  Energy/Cheeger/SmoothGradient.lean  —— SmoothGradient.Test.*, localSlope_relaxation_le, two _of_absolutelyContinuous,
                                          Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous,
                                          as well as KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger
  Energy/WIP/Cheeger.lean             —— change to import the three above, **only** retain those 5 open obligations, and document in the module docstring that it remains WIP
The module splitting can be adjusted (for example, move KLS.LogConcave separately into KLS/LogConcave/), but the assignment of the four categories of content and the fact that "WIP remains only 5"
should not change.

## B. New Blueprint Node
In formalization/blueprint/src/chapters/30-open-canonical-bridges.tex, after the unconditional theorem block, add a corollary block.
Suggest labeling `cor:absolutely-continuous-relaxation-two-cheeger` (you may modify it, but once set, it must remain consistent: ledger node ID,
tasks.json key, route sidecar node, certificate filename, and namespace all follow it).
Content: Under the intrinsic law being absolutely continuous with respect to Haar measure, E^can_μ = 2 Ch_μ, and note that the log-concave law automatically satisfies the premise via lem:logconcave-intrinsic-absolute-continuity.
\uses at least def:selected-canonical-frontend and lem:logconcave-intrinsic-absolute-continuity.
Add \lean{...} and \leanok (for both statement and proof blocks). Additionally, in the explanatory paragraph following the unconditional theorem, add: the absolute continuity range has been separately certified; the remainder remains singular.

## C. Certification
solutions/Cor<Your selected label in camelCase>.lean, namespace Solutions.Cor<Same name>, follows
solutions/CorConditionalFiberTwelveBound.lean's structure: one `certificate` packaged (1) coordinate layer's
relaxation_eq_localSlope_of_absolutelyContinuous, (2) intrinsic layer's energy_eq_two_mul_cheeger_of_absolutelyContinuous,
(3) log-concave special case; plus several typed applications (at least: log-concave law does not require explicit hac, one affine support gives 0 = 2 * 0, EuclideanSpace with volume as Haar reference) and #print axioms guards (certification + two library theorems).

## D. Registration round
Proceed item by item according to the list in 2026-09-12-conditional-fiber-twelve-bound-registration.md:
  The root of formalization/lakefile.toml's Solutions; formalization/FunctionalInequalities.lean aggregation import (three new modules);
  research/a-series/ledger.yaml new node (the 24th) + meta.scope append; research/check_blueprint.py's CERTIFICATES;
  formalization/blueprint/route-composition.yaml new node claim (proved + Lean evidence);
  research/tasks.json (note: nodes recorded in the ledger **do not need** task entries, but atlas is fail-closed, take atlas.py check as reference;
  Additionally, this edit will cause the hash of evidence for several existing nodes to expire, refresh them individually and note in the record why the evaluation remains unchanged);
  Guidelines: HANDOFF.md (new section + count changed to twenty-four + new row in certificate table), README.md, research/verification.md, formalization/README.md,
  formalization/FunctionalInequalities/Energy/README.md, solutions/README.md, formalization/blueprint/README.md;
  research/naming.md list the three name groups mentioned in the "not done" section of the statement with a new table row.

Warnings and hints:
- `omit ... in` must appear **before the docstring**, otherwise `unexpected token 'omit'; expected 'lemma'` will be reported.
- unusedSectionVars linter reports issues iteratively: after fixing a batch, the next round reveals the next batch, requiring multiple compilation rounds to converge.
- Splitting changes the visibility of section variables; warnings previously eliminated by `omit` may shift in position or new ones may appear; refer to `-DwarningAsError=true` for details.
- No **plastex** is installed locally; `blueprint/lean_decls` is an old list, and `build.py checkdecls` compares outdated content.
  For newly added \lean{} names, create a temporary file using `lake env lean` and individually `#check` verify it (in scratch directory, do not commit to repository).
- research/verify.py must be run **after all** guide and decision records are completed; the receipt is then current.

Compilation and checking (run lake in formalization/, otherwise at repository root):
  lake build
  lake env lean -DwarningAsError=true <each new module and modified module>
  python3 research/check_ledger.py          # expects 24 node, 0 error
  python3 research/check_blueprint.py       # expects 88 label, 0 error
  python3 research/atlas.py check           # expects 24 certification, acyclic
  python3 -m unittest discover -s research/tests -p 'test_*.py'
  python3 research/verify.py                # run last
and verify the certification and two library theorems #print axioms, only allowing propext / Classical.choice / Quot.sound.

The final report should list: the list of modules after splitting and their respective public declarations; how the "sorry-free part respects dependency closure" is verified; the new label and certificate name; the Lean name and verification method for the Blueprint new block; the status of registration round completion; the actual output of all check commands; and, if you consider any statement problematic (missing premises, incorrect scope, etc.), provide specific reasons.
```
