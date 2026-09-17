# KLS Lean repository handoff

命名空间已表达的内容不再重复进声明短名；见[短名补充记录](research/decisions/2026-09-08-namespace-short-names.md)。
比较名称也只写一次共有操作，见[比较短名记录](research/decisions/2026-09-08-comparison-short-names.md)。

This is the current operational handoff for `kls-lean`. It records repository identity,
authority boundaries, certified results, exact non-claims, and reproducible checks.

## Consolidated submission review (2026-09-17)

See [the local review record](research/decisions/2026-09-17-consolidated-submission-review.md) for the combined proof scope,
comment corrections and validation boundaries. The dated rounds below retain their original
no-commit statements as historical records. The subsequent rounds below complete R4 and the C¹ vector-coarea route R0–R9.
Sharp finite-regularity Sard and the existing Cheeger/Energy holes remain open.

## Semantic alignment (2026-09-16)

**Current source status.** There are **24 registered certificates** and **8 direct holes**:
sharp finite-regularity Sard (1), Cheeger-infimum comparisons (2), and general Energy identities
(5). The current full-library axiom scan found 12 declarations depending on these holes, all
inside those three WIP modules; none escaped into the proved library or certificate layer.
The dimension-free KLS bound remains open.

The exact smooth recovery sequence is already proved by
`KLS.RelativePerimeter.exists_smooth_recovery_sequence`. Its infrastructure assessment is now
**available**, and its existing proof is now linked and marked complete in Blueprint. This
auxiliary registration does not add a ledger certificate. The
Cheeger-infimum node remains **missing** exactly the integrated superlevel bound and reverse
comparison. Coarea through L13, smooth Sard, Gauss–Green and recovery are available inputs;
they must not be listed as missing proofs. The Cheeger–Buser workstream remains assigned to
王浩丞; this alignment changes no theorem statement or proof body. The proved recovery
module is added to the aggregate imports so the registered declaration is audited there.

See [the semantic alignment record](research/decisions/2026-09-16-semantic-alignment.md) for the reviewed scopes and reproducible evidence.
The dated rounds below retain their historical counts and infrastructure assessments.

## `Analysis/` regrouped: the family word moved from the basename into the directory (2026-09-17)

**Newest round. It proves nothing and changes no declaration.** No hole was migrated: direct holes
stay **8 (1/2/5)** and certificates **24**. 32 of the 50 modules in
`formalization/FunctionalInequalities/Analysis/` moved into family sub-directories and dropped the
family word from their basenames, under the rule added to `research/naming.md` in the round below.

**Nothing mathematical moved, and the axiom report proves it.** The library-wide count is **672
reports with 12 `sorryAx`**, digit for digit what it was before the move. 43 of the 50 modules use
the flat `namespace FunctionalInequalities.Analysis`, and the three nested namespaces
(`Analysis.WhitneyCover`, `Analysis.WhitneyJet`, `Analysis.LipschitzJet`) were left alone, so
declaration names do not depend on the directory: ledger nodes, Blueprint declarations, the
statement-snapshot golden and every axiom report are untouched by construction.

**`WhitneyCover` was the trap.** It is both a module name and a namespace name. The module
`Analysis.WhitneyCover` became `Analysis.Whitney.Cover` while the namespace
`FunctionalInequalities.Analysis.WhitneyCover` stayed exactly as it was. The rewrite therefore
touched **only `import` lines** and `Analysis/<File>.lean` path strings in docstrings — never a
bare identifier. Of the 148 textual `FunctionalInequalities.Analysis.<moved module>` occurrences,
126 were on import lines; the other 22 were checked one by one and are all that namespace and its
declarations, left untouched.

**The layout.** `Whitney/` (Bump, Construction, Cover, Extension, Partition); `Sard/` (Basic,
Planar, Smooth, Equidimensional); `Vector/` (CriticalSlice, FiberIntegral, HausdorffSlicing,
LocalCoarea, RegularChart, RegularCoarea, SliceMeasurable) with `Vector/Graph/` nested one level
further (Basic, Area, Integral, Sandwich); `RankDeficient/` (Stratification, RightInverseBound,
TangentialLipschitz, RegularFibreFinite, TargetSplitFubini, StratumSlicing, Coarea,
ExponentObstruction); `Graph/` (Integral, Jacobian, Implicit, OpenIntegral). Eighteen modules stay
flat. `Sard/Equidimensional` is filed by **mathematical object rather than by route provenance** —
it is route obligation `R10`, but its subject is the equidimensional Sard lemma, and `naming.md`
groups files by their primary object; the trade-off is recorded rather than hidden.
`CoareaGraphJacobian` deliberately did **not** move: `Graph/CoareaJacobian` would create a second
module whose basename is `CoareaJacobian`, which reads worse than the repetition it removes. The
two-module families (`Divergence`, `HausdorffContent`/`HausdorffSlicing`,
`LipschitzC1Pieces`/`LipschitzJet`) are below the rule's three-module threshold.

**The historical citations are not rewritten; they are mapped.**
`research/api-migration/2026-09-17-analysis-module-map.json` carries 32 module mappings and 32 file
path mappings, so the ~434 textual `Analysis/<File>.lean` citations in the dated decision and
exploration records stay resolvable. This is the same device as the 2026-09-08 renames
(`2026-09-08-module-map.json`, `2026-09-08-library-naming-module-map.json`).

**What was rewritten**: 70 `import` lines and 44 docstring path strings across 61 `.lean` files, in
`formalization/`, `research/audits/` and the **seven** `build/audit/` clients that are re-run every
round. The 38 frozen `.before.lean` and route-review artifacts under `build/audit/` keep their old
imports on purpose. `research/tasks.json` had 29 evidence paths remapped and 59 hashes refreshed,
and the living `formalization/README.md` and `research/audits/README.md` were repointed.

**One correction to a standing claim.** `research/audits/RankDeficientRouteStatements.lean` was
recorded as **byte-unchanged** by every earlier round. This round changes **five lines** of it: one
`import` and four docstring path strings. That is unavoidable — a module move reaches every
importer. **All fifteen `#check` propositions are byte-identical**, verified block by block against
`HEAD`, and the stale status note at the top was not touched. The earlier rounds' statements remain
true of those rounds; this one supersedes them as to the current file.

**A build-scope fact worth recording.** The `Analysis` layer is outside the aggregate
`formalization/FunctionalInequalities.lean` — zero of its 50 modules are imported there — so a plain
`lake build` does not produce their `.olean`s and the audit clients fail with "object file does not
exist" until the modules are built explicitly. `research/verify.py` already does exactly that
through `build_replay_inputs`, which is why verification is unaffected; the round-local sweep now
does it too.

The two Cheeger comparisons and the five Energy holes are untouched.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the regrouping decision](research/decisions/2026-09-17-analysis-regrouping.md),
`research/explorations/2026-09-17-analysis-regrouping.json` and the path map
`research/api-migration/2026-09-17-analysis-module-map.json`. The final verification receipt is
identified in `build/audit/analysis-regrouping/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## File management: the `N2` repair moved into the module, and a module-naming rule added (2026-09-17)

**Newest round; no mathematics changed and no registration number moved.** Direct holes stay
**8 (1/2/5)** and certificates **24**. No statement was added, removed, weakened or strengthened:
every declaration proved in the two rounds below is still proved, with the same type.

**What moved.** The repaired `N2` — below the top dimension a set of positive Lebesgue measure has
infinite Hausdorff measure, *provided the dimension is positive* — was proved in the audit client a
round ago. It is mathematical content with a statement of its own, so it now lives in the module,
as `Analysis.hausdorffMeasure_finrank_sub_eq_top` in `Analysis/ExponentObstruction.lean`
(previously `ExponentObstructionAudit.hausdorffMeasure_finrank_sub_eq_top_of_finrank_pos`). The
module gained `import Analysis.LevelSet` for `hausdorffMeasure_finrank_eq_smul_volume`; its local
import closure is **4 modules, no WIP**. The audit keeps only the route bookkeeping,
`N2_repair_is_free_on_the_route`, and the refutation `route_N2_is_false` that makes the added
hypothesis necessary.

**Two name defects fixed, both in this session's own uncommitted code.**
`FunctionalInequalities.Analysis.ContinuousLinearMap.det_eq_zero_of_not_surjective` nested a
`ContinuousLinearMap` namespace inside `Analysis`, which buys nothing — dot notation resolves only
against the root `ContinuousLinearMap` — while repeating the namespace in the short name, against
the first rule of `research/naming.md`. It is now `Analysis.det_eq_zero_of_not_surjective`. And
`ExponentObstructionAudit` declared the zero-dimensional space **twice**, as `Pt₀` and as `Pt`, one
per counterexample; there is now a single `Pt`, and the client is regrouped so that all of `N1`
comes before all of `N2` rather than interleaving.

**A module-naming rule was added to `research/naming.md`** (§文件与声明作用域, new subsection
「家族词归目录，不进文件名」): once a mathematical family has three or more modules, the family
name belongs to the **directory** and the basename keeps only the distinguishing word.
`Poincare/SmoothTest/`, `Energy/LocalSlope/`, `Energy/CovarianceGradient/` and
`KLS/LogConcave/Line/` already do this.

**`Analysis/` does not, and is deliberately left alone for now.** Its 50 modules are flat and bake
the family word into every basename — `Vector` 11 times, `Graph` 9, `Whitney` 5, `Coarea` 5,
`Sard` 4. Regrouping is a **file-layer** change only: 43 of the 50 modules use the flat
`FunctionalInequalities.Analysis` namespace, so declaration names do not depend on the directory and
the ledger, Blueprint, statement snapshot and axiom audits would all be untouched. The cost is 238
`import` lines across 128 files and 84 `tasks.json` evidence paths, both mechanical — and **434
textual `Analysis/<File>.lean` citations in the dated decision and exploration records**, which this
project does not rewrite. The regrouping is therefore deferred to **its own round**, which will
publish a path map under `research/api-migration/`, exactly as the 2026-09-08 module renames did
(`2026-09-08-module-map.json`, `2026-09-08-library-naming-module-map.json`, which contain the same
kind of move — `KLS.LogConcave.AffineCovariance → KLS.LogConcave.Covariance`). Until that round the
existing modules stay where they are; the rule binds **new** `Analysis/` modules only.

**Also recorded, not acted on.** Twelve untracked macOS duplicate-name files (`* 2.*`) exist outside
`build/`; **six of them differ from the file they shadow**, some substantially —
`research/check_blueprint 2.py` is 460 lines against the real 1367,
`formalization/blueprint/route-composition 2.yaml` is 41 against 388, and
`formalization/FunctionalInequalities/Poincare/README 2.md` is 276 lines against a tracked README of
215, so it may hold edits that exist nowhere else. They are untracked, so deleting them is
unrecoverable; none was touched. Separately `build/` holds 21 GB, of which `build/verification/` is
8.4 GB across 175 receipts — **62 of those receipts are cited by name in the records**, so pruning
by age would break cited evidence and was not done.

**Verification.** The two affected modules and their two audit clients compile strictly; all **52**
audit clients were re-run with `-DwarningAsError=true`, 0 failures. Axiom reports are unchanged in
content and count except for the two renamed entries. Nothing in `KLS/WIP` or `Energy/WIP` was
touched, `research/audits/RankDeficientRouteStatements.lean` stays **byte-unchanged**, and no
committed `.lean` file was modified.

The two Cheeger comparisons and the five Energy holes are untouched.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the N1 decision](research/decisions/2026-09-17-exponent-obstruction-n1.md), whose addendum
records this move, and `build/audit/exponent-obstruction-n1/final-snapshot.json` for the receipt.
No commit or push; the real Git index is unchanged.

## `N1` proved: the obstruction of the small-Lipschitz method, stated as a theorem (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**`N1` is proved.** If `S` is measurable with `μH[n] S` finite, the target `W₂` has positive
dimension, and at every scale `ε` the composite `Q ∘ u` is `ε`-Lipschitz on the pieces of some
countable measurable partition of `S`, then for almost every `τ ∈ W₂` the slice
`S ∩ {Q ∘ u = τ}` is `μH[n − dim W₂]`-null. **No regularity whatever is assumed of `u`.** With
`R0`–`R10` that is twelve of the route's thirteen numbered items; the thirteenth, `N2`, was shown
**false as written** in the round below and its repair proved.

**Proving `N1` is not progress on the route, and the route record already said so.** `N1` is the
*statement of the obstruction*: the exponent it delivers is `n − dim W₂`, and in the route's
notation `W₂` is the orthogonal complement of the rank-`r` range inside the `m`-dimensional target,
so `dim W₂ = m − r` and the exponent is **`k + r`, not `k`** — recorded as
`N1_exponent_is_k_add_r` so it cannot be misread. For `r ≥ 1` that is weaker than `R0` in the
useless direction: at the exponent `k = n − r` every set of positive Lebesgue measure has
**infinite** Hausdorff measure, so no `μH[k]` statement follows from a `μH[k + r]` one
(`N1_null_at_higher_exponent_says_nothing_at_k`, a specialization of the repaired `N2`). `R0` does
not depend on `N1`; it was proved independently by slicing **inside a fibre**, where
`k + (m − r) = n − r` is the right exponent, and `Analysis/ExponentObstruction.lean` has **no
downstream consumer**.

**How it is proved.** At a single scale, the repository's codimension-`m` Eilenberg majorant
`exists_measurable_majorant_vector` is applied to each piece and the majorants are summed:
`exists_measurable_majorant_of_lipschitz_pieces` produces a **measurable** dominating function of
integral at most `C · ε ^ (dim W₂) · μH[n] S`. The slice function itself is not known to be
measurable — nothing is assumed about `u` — which is why the bound has to be carried by a majorant.
Measurability and disjointness of the pieces enter exactly once, in the countable additivity that
reassembles the pieces' right-hand sides into `μH` of `S`. Taking `ε_j = (j+1)⁻¹` and the pointwise
infimum of the resulting majorants gives a measurable function that still dominates and whose
integral beats every scale; positivity of `dim W₂` and finiteness of `μH[n] S` send the bound to
zero.

**The truncated exponent is harmless here, unlike in `N2`.** `finrank ℝ V - finrank ℝ W₂` is a
natural subtraction, and the proof never needs `dim W₂ ≤ n`: `hausdorffMeasure_truncated_add_le`
records that `(n − m) + m ≥ n` holds in `ℕ` either way, so the Eilenberg right-hand side stays
bounded by `μH[n] S`. This is the exact point on which `N2` fails, and `N1` survives it.

**Both side conditions are real.** `0 < finrank ℝ W₂` is necessary, not decoration:
`N1_needs_positive_codimension` refutes `N1` **with that hypothesis deleted** — with `V = W = ℝ`,
a zero-dimensional `W₂`, `Q = 0`, `u = id` and `S = [0,1]` the piece hypothesis holds trivially
because `Q ∘ u` is constant, the single fibre is all of `S`, and `μH[1] S = 1`. With `dim W₂ = 0`
the Eilenberg constant `ε ^ (dim W₂)` is `1` and nothing tends to zero. Measurability of `S` is
used exactly once, as described above.

**Still open.** `N2` remains **unproved and known false as written**; what is proved is the
repaired statement. Sharp finite-regularity `Analysis.sard` remains a direct hole and is untouched
— nothing in this round concerns critical values at all. No hole was migrated, no certificate was
added and no Blueprint `leanok` scope was widened: this is infrastructure, and the dimension-free
KLS bound remains open.

`research/audits/RankDeficientRouteStatements.lean` stays **byte-unchanged**; `route_N1` copies its
proposition verbatim and discharges it. No existing `.lean` file was modified: this round adds one
module and extends the audit client it had created a step earlier. The new module
`Analysis/ExponentObstruction.lean` has a local import closure of **2 modules, no WIP**, and the
audit client now carries **11** standard-only axiom reports.

The two Cheeger comparisons and the five Energy holes are untouched.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the N1 decision](research/decisions/2026-09-17-exponent-obstruction-n1.md) and
`research/explorations/2026-09-17-exponent-obstruction-n1.json`. The final verification receipt is
identified in `build/audit/exponent-obstruction-n1/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## `R10` proved: the equidimensional degenerate case; and the diagnostic `N2` shown **false as stated** (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**`R10` is proved.** When `n = m` the fibre dimension is `k = 0`, so `ℋ^0`-nullity of a slice means
the slice is **empty**: for almost every `t` the level `{u = t}` of a `C¹` map contains **no**
critical point at all. With `R0`–`R9` that is eleven of the route's thirteen numbered items.

**`R10` is not a Sard theorem, and it is not progress on the route.** Both points matter and are
easy to misread, because `R10` is the one item on the whole list that is about critical *values*.
Sard's theorem concerns the measure of the set of critical values of a map `ℝⁿ → ℝᵐ`; what is proved
is the case `n = m` alone, where a singular differential contracts volume and Mathlib already
supplies the self-map statement. For `n > m` the critical values of a merely `C¹` map can have
positive measure, and nothing here says otherwise. The direct hole
`FunctionalInequalities.Analysis.sard` is about a real-valued map on a domain of **any** dimension
at regularity `C^n`; **its status is unchanged and it was not touched.** The entire overlap is
`finrank ℝ V = 1` — `r10_reaches_only_dimension_one` records that, and
`sard_dimension_one_recovered` carries the recovery out — and that case was already proved
unconditionally by `Analysis.sard_of_finrank_le_one`, from the same Mathlib lemma. For `n ≥ 2`
nothing was said. As for the route: `R0` was proved independently by the stratification route, which
never specializes to `n = m`, so `R10` is an after-the-fact consistency check.
`Analysis/EquidimensionalSard.lean` imports **no part** of that route, which makes the check
genuinely independent; `equidimensional_R0_of_R10` and `equidimensional_R10_of_R0` derive each
statement from the other in the case `n = m`, where they are equivalent because `μH[0]` of a
nonempty set is at least `1`.

**How it is proved.** Mathlib's `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` is a self-map
statement; it is transported along the repository's `isometryEquivOfFinrankEq` by precomposing `u`
with the inverse isometry rather than postcomposing it, so the image already lives in `W` and the
null set itself never has to be moved. The linear-algebra step, that in equal dimensions a
non-surjective map is singular, goes through injectivity and is proved as
`ContinuousLinearMap.det_eq_zero_of_not_surjective`; Mathlib has only the converse direction.

**The diagnostic `N2` is false as written, and this round proves it false.** `N2` reads
`volume S ≠ 0 → 0 < r → μH[((finrank ℝ V - r : ℕ) : ℝ)] S = ⊤`, with `finrank ℝ V - r` a
**truncated** natural subtraction. At `finrank ℝ V = 0` the space is a single point, the only set of
nonzero volume is that point, the truncated exponent is `0` rather than negative, and `μH[0]` of a
singleton is `1`, not `⊤`. `N2_counterexample` exhibits the three facts and `route_N2_is_false`
derives the contradiction; it refutes the `Type` instance of the route proposition, which the
route's `Type*` version implies. **The repair is the missing positivity of the dimension and is
proved**: `hausdorffMeasure_finrank_sub_eq_top_of_finrank_pos` is `N2` with `0 < finrank ℝ V` added,
a hypothesis the counterexample shows is necessary and which is **free** wherever the route appeals
to `N2` — there `1 ≤ r < finrank ℝ W ≤ finrank ℝ V`, recorded as
`N2_repair_is_free_on_the_route` — so the diagnostic role of `N2` in the route record survives the
correction unchanged.

**Still open.** `N1`, the other diagnostic, is **not proved**; it needs the Eilenberg majorant
machinery and is not a step, `R0` not depending on it. `N2` remains **unproved and now known
false**; what is proved is the repaired statement, named so that the two cannot be confused. Sharp
finite-regularity `Analysis.sard` remains a direct hole. No hole was migrated, no certificate was
added and no Blueprint `leanok` scope was widened: this is infrastructure, and the dimension-free
KLS bound remains open.

**Boundary cases** are checked one by one: both spaces zero-dimensional (every linear map is
surjective, the critical set is empty); a constant map, together with
`constant_map_critical_everywhere` showing that case is not vacuous (the derivative vanishes
identically, so with a positive-dimensional target every point is critical, and the conclusion holds
because the whole image is one point); and `n = m` with an everywhere invertible differential, where
the critical set is empty and the conclusion holds for *every* level.

`research/audits/RankDeficientRouteStatements.lean` stays **byte-unchanged**, as in the previous
round and for the same reason: it is a committed historical route snapshot whose editing ownership
the collaborator has taken, and the repository's way of recording that an obligation is met is for an
audit client to copy its proposition **verbatim** and discharge it, which `route_R10` does. Its
header status note remains out of date and refreshing it is left to whoever maintains the file.

No existing `.lean` file was modified by this round, and the aggregate is untouched. The new module
`Analysis/EquidimensionalSard.lean` has a local import closure of **18 modules, no WIP**. The two
new clients have **13** and **4** standard-only axiom reports.

The two Cheeger comparisons and the five Energy holes are untouched.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the equidimensional Sard decision](research/decisions/2026-09-17-equidimensional-sard.md) and
`research/explorations/2026-09-17-equidimensional-sard.json`. The final verification receipt is
identified in `build/audit/equidimensional-sard/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## `R8`, `R0` and `R9` proved: the rank-deficient critical set, and the codimension-`m` coarea formula (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**The rank-deficient gap of the codimension-`m` coarea program is closed.** `R0` is proved: for a
`C¹` map into an `m`-dimensional target, **the whole critical set** `{x | fderiv ℝ u x` is not
surjective`}` — not merely the part where the derivative vanishes — meets almost every level in an
`ℋ^k`-null set. With it, `R9`: **the codimension-`m` coarea formula holds with no hypothesis on the
critical set**. With `R1`–`R7` that is ten of the route's thirteen numbered items.

**This is not a Sard theorem.** `R0` bounds the critical set **inside a level**; nothing whatever is
claimed about the measure of the set of critical *values*, which for a merely `C¹` map may well be
positive. Sharp finite-regularity Sard remains a direct hole and is untouched. The map is assumed
`C¹`, not Lipschitz, and the fibre measure is the normalized Hausdorff measure of the complementary
dimension, in the repository's standing convention.

**What the earlier rounds could not do, and now can.**
`Analysis/VectorRegularCoarea.lean` proved the formula where the differential is surjective;
`Analysis/VectorCriticalSlice.lean` extended it under the hypothesis that the derivative *vanishes*
wherever it fails to be surjective, which for `m ≥ 2` is a genuine restriction — its own audit
exhibited a rank-one projection of the plane where the hypothesis fails at **every** point. The new
audit's `rank_deficient_witness_now_covered` shows that same witness is covered by `R0`, and
`strictly_extends_conditional` derives the old conditional formula from the new one.

**The route in one paragraph.** `R1` stratifies the critical set by the exact rank of the
differential into finitely many measurable layers. On a layer, `R2` says the differential dies along
the fibres of the regular component `P ∘ u`, `R3` makes that quantitative with a locally uniform
right-inverse bound, and `R4` combines them into a tangential Lipschitz constant proportional to the
approximation parameter. `R7` runs the approximating partition on `u` itself and applies the
Eilenberg bound **inside a fibre**, where `k + (m − r) = n − r` is the right exponent, integrating
against the **proved** regular coarea formula. `R8`, proved here, patches those neighbourhoods
together by second countability; the finite union over `r < m` gives `R0`; and the critical part of
the coarea equality then vanishes on both sides, giving `R9`. **The exponent is repaired in the
fibre**: the same bound applied in the ambient space forces `k + r`, and forcing it back to `k` puts
`μH[n − r]` of a set of positive Lebesgue measure — that is, `∞` — on the right, which is exactly
the obstruction the route's diagnostic `N2` records.

**Still open.** `R10`, the equidimensional degenerate case, is a separate cheap sanity check and is
**not proved**; `N1` and `N2` are diagnostics of the obstruction rather than steps and are **not
proved**. No hole was migrated, no certificate was added and no Blueprint `leanok` scope was
widened: this is infrastructure, and the dimension-free KLS bound remains open.

**`m = 1` returns the proved scalar statements**, `KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero`
and `KLS.coarea_of_contDiff`, both with the extra `1 ≤ finrank V` that the codimension-`m`
bookkeeping forces, recorded rather than hidden.

`research/audits/RankDeficientRouteStatements.lean` stays **byte-unchanged**. Its header status note,
added by the collaborator in `e7c4403`, is now out of date — it says `R0` and `R4`–`R10` are open,
whereas `R4`–`R9` and `R0` are proved. This round deliberately did **not** edit it: it is a committed
historical route snapshot which the collaborator has already taken editing ownership of, and the
repository's way of recording that an obligation is met is for an audit client to copy its
proposition **verbatim** and discharge it — which `route_R8`, `route_R0` and `route_R9` of
`research/audits/RankDeficientCoareaAudit.lean` do. Refreshing that note is left to whoever maintains
the file. `AreaFormulaRouteStatements.lean` was re-run and shows **no new errors**.

No existing `.lean` file was modified by this round, and the aggregate is untouched. The new client
has **14 standard-only axiom reports**.

The two Cheeger comparisons and the five Energy holes are untouched.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the rank-deficient coarea decision](research/decisions/2026-09-17-rank-deficient-coarea.md) and
`research/explorations/2026-09-17-rank-deficient-coarea.json`. The final verification receipt is
identified in `build/audit/rank-deficient-coarea/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Route obligation `R7` proved: the per-stratum local slicing (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**`R7` is proved.** Around every point of the rank-`r` stratum there is a neighbourhood in which
almost every level meets the stratum in an `ℋ^k`-null set. With `R1`–`R6` that is **seven** of the
route's thirteen numbered items. **`R0` is still open**: it needs `R8`, the localization of `R7` to
the whole stratum, and the finite union over `r < m`, for which `R1`'s decomposition is already in
place.

**The argument, and where the wrong exponent gets repaired.** Run Mathlib's approximating partition
on `u` **itself**, so that one partition serves both components; on each piece the local package
makes `Q ∘ u` `c ε`-Lipschitz along every fibre of `P ∘ u`; the Eilenberg bound applies **inside a
fibre** at exponent `k` with a target of dimension `m − r`, where `k + (m − r) = n − r` is exactly
right; integrating over the fibre parameter against the **proved** regular coarea formula turns the
fibre measures into an ordinary integral of the coarea Jacobian, and the target-splitting identity
reads the result as an integral over the target. That is `lintegral_hausdorffMeasure_stratum_le`,
the per-scale bound, whose constant does **not** depend on `ε`. The limit `ε → 0` then gives `R7`:
the right-hand factor is finite because the neighbourhood's closure is compact, and the exponent
`m − r` is positive exactly because `r < m`.

Applying the same bound in the ambient space instead would force the exponent `k + r`, and forcing
it back to `k` would put `μH[n − r]` of a set of positive Lebesgue measure — that is, `∞` — on the
right. **The fibre is where the dimension count comes out right**, which is what `R5` and `R6` were
for: this round uses the same two engines, the proved regular coarea formula and measure-preserving
change of variables with Tonelli, in their integral rather than null-set form.

**Two existing `.lean` files were modified, recorded rather than hidden.** Both are this session's
own uncommitted files and both changes are additive. `Analysis/StratumSlicing.lean` gained the three
new theorems and had its module docstring **rewritten**, since it previously said `R7` was not
proved; the statements of `exists_stratum_local_data` and `lintegral_split_target` are **unchanged**.
`research/audits/StratumSlicingRouteStatements.lean` gained a status note at the top recording that
`R7b` and `R7c` are now proved, with **both propositions unchanged** — the same treatment the
collaborator gave `RankDeficientRouteStatements.lean`. That file and
`AreaFormulaRouteStatements.lean` were **not** modified by this round.

**What `R7` is not.** It is a statement about **one stratum in one neighbourhood**. It says nothing
about the whole critical set, which is the union of the strata of every rank `r < m`; it is not a
coarea formula in a new case, and it is not a Sard theorem — no claim whatever is made about the
measure of the set of critical *values*. `R0`, `R8`, `R9`, `R10`, `N1` and `N2` remain unproved.

**Next**: `R8`, the localization, estimated at about 90 lines and low to moderate risk; `R0` is then
`R1`'s finite union together with it, and `R9` the unconditional codimension-`m` coarea formula.

The new client `research/audits/StratumSlicingAudit.lean` has **16 standard-only axiom reports**,
among them `route_R7`, which copies `R7` **verbatim** from
`research/audits/RankDeficientRouteStatements.lean` and discharges it.

Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are untouched.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the R7 decision](research/decisions/2026-09-17-stratum-slicing-complete.md) and
`research/explorations/2026-09-17-stratum-slicing-complete.json`. The final verification receipt is
identified in `build/audit/stratum-slicing-complete/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Per-stratum slicing `R7`: the local package and the target split proved, **`R7` itself not** (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**`R7` was the target of this round and it is NOT proved.** `R0` remains open and so does the
general codimension-`m` coarea formula. What is proved is two parts of `R7`, and the remaining gap
is written down precisely as `R7b` and `R7c` in the new `#check`-only file
`research/audits/StratumSlicingRouteStatements.lean`, where **nothing is proved**.

**An existing `.lean` was modified, recorded rather than hidden.**
`Analysis/TangentialLipschitz.lean`, this session's `R4` module and still uncommitted, was refactored
so that the **explicit** constant comes first (`lipschitzOnWith_of_ker_bound`); the route's
existential statement `exists_lipschitzOnWith_of_ker_bound` is **kept verbatim** and re-derived from
it. This is a strict strengthening and weakens nothing. The reason is hard: the assembly needs
**one** constant valid on every piece of the approximating partition, and the existential form's
constant depends on each piece's linear model. This is where the previous round's insistence on the
**locally uniform** half of `R3` pays off.

**What is proved.** `Analysis/StratumSlicing.lean` (local import closure 25 modules, no
work-in-progress file, aggregate untouched):

* `exists_stratum_local_data`, the **local package**. At a point of the rank-`r` stratum, with `K`
  the range of the differential there and `P`, `Q` the orthogonal projections onto `K` and `Kᗮ`,
  there is an open neighbourhood with compact closure on which `P ∘ u` is a submersion, together
  with **one** constant `c` that works for **every** stratum point `y` in it, every `ε`, every set
  `ε`-approximated by `fderiv ℝ u y`, and every fibre: `Q ∘ u` is `c ε`-Lipschitz along each fibre
  of `P ∘ u`. **The uniformity of `c` over `y` is the whole difficulty**, since `R4`'s constant
  depends on the piece's linear model through `‖fderiv ℝ u y‖` and the right-inverse bound; it comes
  from `R2`, the locally uniform half of `R3`, and a bound on `‖fderiv ℝ u‖` near the point.
* `lintegral_split_target`, the **integral form of the target splitting**: an integral over the
  target is the iterated integral over an orthogonal splitting. This is what `R6` does for null sets,
  in the shape the per-scale estimate must be integrated against, and it assumes only almost
  everywhere measurability of the integrand.

**What is missing, stated precisely.** `R7b` is the per-scale bound: at a fixed `ε` the total fibre
measure of the stratum piece over the whole target is at most a constant — independent of `ε` —
times `ε ^ (m − r)` times the integral of the coarea Jacobian of the regular component. The route to
it is to run the approximating partition on `u` **itself** so one partition serves both components,
use the local package on each piece, apply the Eilenberg bound **inside a fibre** at exponent `k`
with a target of dimension `m − r` where `k + (m − r) = n − r` is exactly right, integrate over the
fibre parameter against the **proved** regular coarea formula, and read the result through
`lintegral_split_target`. `R7c` is the limit `ε → 0`, the pattern already used twice in the
repository. **Neither is proved.**

**Nothing here is a coarea formula, a slicing statement about the critical set, or a Sard theorem**,
and no claim whatever is made about the measure of the set of critical *values*. `R8`–`R10`, `N1`
and `N2` are also still unproved.

`research/audits/RankDeficientRouteStatements.lean` and `AreaFormulaRouteStatements.lean` were not
modified; the latter was re-run and shows **no new errors**. The new client
`research/audits/StratumSlicingAudit.lean` has **11 standard-only axiom reports**, and the new
route-statement file has **2 `#check`s and no declaration**.

Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are untouched.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the stratum slicing decision](research/decisions/2026-09-17-stratum-slicing.md) and
`research/explorations/2026-09-17-stratum-slicing.json`. The final verification receipt is
identified in `build/audit/stratum-slicing/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Fibre finiteness and target Fubini: route obligations `R5` and `R6` proved (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**What is proved: exactly `R5` and `R6`**, the two independent obligations that were next in the
recommended order, in `Analysis/RegularFibreFinite.lean` (local import closure 22 modules) and
`Analysis/TargetSplitFubini.lean` (Mathlib-only, closure **1 module**), both with no
work-in-progress file and the aggregate untouched. With `R1`–`R4`, **six** of the route's thirteen
numbered items are discharged.

**`R5`: the fibres of the regular part carry finite measure.** The route applies the Eilenberg
bound *inside* a fibre with `d = k` and a target of dimension `m − r`, so `d + (m − r) = n − r`;
for that to say anything the fibre must have **finite** `ℋ^{n−r}` measure, or the right-hand side
is `∞` and the estimate is vacuous — exactly the failure `N2` records for the one-step method.
`R5` is a **corollary of the proved regular coarea formula**, not new analysis: with weight `1` the
total fibre measure integrates to `∫⁻ coareaJacobian`, finite on a relatively compact piece because
the integrand is continuous there, and a finite integral has almost everywhere finite integrand.

**Relative compactness is necessary, and that is exhibited rather than asserted.** For the first
coordinate functional of the plane — a submersion everywhere — with `S = univ`, every other
hypothesis holds, but each fibre is a full line of infinite `ℋ^1` measure, so the conclusion fails
at **every** level, not merely on a null set of them.

**`R6`: Fubini across an orthogonal splitting of the target.** The two slicings produce "for almost
every `s`, for almost every `τ`" while the conclusion is about almost every `t`; `R6` joins the two
levels. It is assembly rather than new mathematics — `LinearIsometryEquiv.measurePreserving`,
`WithLp.volume_preserving_toLp` and `Measure.prod_apply` are all in Mathlib — but it was not in the
repository in any form. The splitting is stated abstractly as an isometry onto `WithLp 2 (W₁ × W₂)`;
the audit instantiates it along `Submodule.orthogonalDecomposition`, confirming that **the
instances resolve and the abstract statement is directly usable** for the splitting along the range
of the differential. The audit also records the **converse** direction, so `R6` is not mistaken for
the easy half.

**What `R5` does not say.** It assumes the differential is surjective on all of `O`; the critical
set of `v` is outside its reach, which is precisely why the route still needs the rest. It extends
the applicability of the proved codimension-`m` coarea formula by **nothing**.

**Still open: `R0`, `R7`–`R10`, `N1`, `N2`**, and the **general codimension-`m` coarea formula**.
Nothing here is a coarea formula in a new case, a slicing statement about the critical set, or a
Sard theorem; no claim whatever is made about the measure of the set of critical *values*. **Only
`R7` now stands between the proved pieces and `R0`**, followed by `R8` and `R9`. `R7` remains the
only high-risk item: it must run the approximating partition on `u` itself so that one partition
serves both components, may start only from points *of* the stratum, and needs its constant uniform
across the pieces.

`research/audits/RankDeficientRouteStatements.lean` was not modified by this round; the two new
clients `research/audits/RegularFibreFiniteAudit.lean` and
`research/audits/TargetSplitFubiniAudit.lean` copy its `R5` and `R6` propositions **verbatim** and
discharge them, with **8 and 6 standard-only axiom reports**. The area-formula route statements
were re-run and show **no new errors**.

Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are untouched,
and no existing `.lean` file was modified.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the fibre finiteness and Fubini decision](research/decisions/2026-09-17-fibre-finite-fubini.md)
and `research/explorations/2026-09-17-fibre-finite-fubini.json`. The final verification receipt is
identified in `build/audit/fibre-finite-fubini/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## The tangential small-Lipschitz estimate: route obligation `R4`, the point of no return, proved (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**What "point of no return" means, stated precisely before anything else.** The round below marked
`R4` so because, with `R2` and `R3` in place, it is self-contained and **the route is wrong if it
fails or if its constant is not uniform**. It does not fail: `R4` is proved and its constant is
genuinely independent of the approximation parameter. That means only that **the route has not been
refuted at its critical analytic step**. It does **not** mean `R0` holds, and it does not mean the
remaining steps will work: the exponent now matches and the estimate is available, but turning it
into null slices still needs the finite `ℋ^{n−r}` measure of the fibres (`R5`), Fubini across the
orthogonal splitting of the target (`R6`), and the genuinely hard per-stratum assembly (`R7`,
estimated 450–600 lines and the only high-risk item). **Not one inch of the rank-deficient part is
proved.**

**A concurrent session committed the workspace during this round, recorded rather than hidden.**
After this round's Lean was written and before it was wrapped up, the concurrent session committed
the whole workspace: `HEAD = origin/main` moved from `34b9269…` to
`e7c4403352011b6c3ed6dc02f0af3eef6cbb300e` (138 files). That commit **absorbed all four earlier
rounds of this session**, so their "not committed" status no longer holds — they were committed by
the collaborator, not by this session. The same commit made a submission-review pass that edited
two files this session had written: `research/audits/RankDeficientRouteStatements.lean` gained a
status note at the top (recording that `R1`, `R2` and both versions of `R3` are proved and that
**the propositions below are unchanged**; it still contains only `#check`s), and
`research/audits/RightInverseBoundAudit.lean` had one docstring reworded. **Neither edit was made
or reverted here.** This round therefore does not claim the route-statement file is byte-unchanged;
the accurate statement is that **this session did not modify it**, and it is clean against the
current `HEAD`. All verification below was redone on top of `e7c4403…`.

**What is proved: exactly `R4`**, in the new module `Analysis/TangentialLipschitz.lean` (local
import closure **3 modules**, no work-in-progress file, aggregate untouched), over the same round's
`Analysis/RankStratification.lean` and `Analysis/RightInverseBound.lean`. With `R1`, `R2` and `R3`,
**four** of the route's thirteen numbered items are discharged.

**The estimate.** For two points of one fibre the chord `b − a` satisfies
`‖P (A (b − a))‖ ≤ ‖P‖ ε ‖b − a‖` — it is *almost* in the kernel of `P ∘ A`, and this is the only
place the fibre hypothesis is used and the exact point where the situation differs from the
vanishing-derivative case. `R3` converts that into an honest kernel element, `R2` says the linear
model dies there, and so `‖A (b − a)‖ ≤ ‖A‖ C ‖P‖ ε ‖b − a‖`. Feeding it back into the
approximation and applying `Q` gives `‖Q‖ (1 + ‖A‖ C ‖P‖)`, which **does not depend on `ε`, on
`f`, on `S` or on the fibre**. That independence is the whole point — the `ε → 0` limit uses a
different approximating partition at every scale — and it is visible in the shape of the statement,
`∃ c, ∀ ε, …`.

**The `R2` hypothesis is necessary, and that is exhibited rather than asserted.** For the identity
of the plane with `P` the first and `Q` the second coordinate, the `R3` hypothesis holds, the `R2`
hypothesis fails, and the conclusion of `R4` fails outright: at `ε = 0` it would force the second
coordinate to be constant along the second axis. So `R4` is not a statement about the approximation
alone.

**The `R3` hypothesis is not claimed necessary.** It supplies the constant, not a restriction; in
finite dimensions its conclusion holds for every linear map, which this round neither proves nor
uses. At the other end, for the rank-zero model `A = 0` both hypotheses hold with `C = 0`, the
constant collapses to `‖Q‖`, and `R4` returns exactly the proved vanishing-derivative situation —
**adding nothing on the `r = 0` layer**.

`R4` itself uses no inner product, no measure, no completeness and no finite-dimensionality; `f`
and `S` are arbitrary. A corollary records what `R2`, `R3` and `R4` combine to on a rank stratum;
it is **a corollary of three proved obligations, not a new one, and in particular not `R7`** — no
measure, Hausdorff dimension, slice or approximating partition appears in it.

**Still open: `R0`, `R5`–`R10`, `N1`, `N2`**, and the **general codimension-`m` coarea formula**.
Nothing here is a coarea formula, a slicing statement or a Sard theorem, and no claim whatever is
made about the measure of the set of critical *values*. Next in the recommended order are `R5` and
`R6`, which are independent of each other, then `R7`.

Boundary cases are covered rather than excluded: the empty set, `ε = 0` with a genuine linear
model, a zero-dimensional projection target, and the rank-zero model.

`research/audits/RankDeficientRouteStatements.lean` stays **byte-unchanged**; the new client
`research/audits/TangentialLipschitzAudit.lean` copies its `R4` proposition **verbatim** and
discharges it, with **10 standard-only axiom reports**. The area-formula route statements were
re-run and show **no new errors**; that file too stays byte-unchanged.

Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are untouched,
and no existing `.lean` file was modified.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the tangential Lipschitz decision](research/decisions/2026-09-17-tangential-lipschitz.md) and
`research/explorations/2026-09-17-tangential-lipschitz.json`. The final verification receipt is
identified in `build/audit/tangential-lipschitz/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Approximate right inverses: route obligation `R3`, both versions, proved (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**What is proved: exactly `R3`**, pointwise and locally uniform, in the new Mathlib-only module
`Analysis/RightInverseBound.lean` (local import closure **1 module**, no work-in-progress file,
aggregate untouched). With `R1` and `R2` of the round below, **three** of the route's thirteen
numbered items are now discharged.

**What `R3` is for.** The route slices inside a fibre of the regular component `v = P ∘ u`, and a
chord of a fibre is *not* a tangent vector: two points of one fibre give only
`‖Dv (b − a)‖ ≤ ε ‖b − a‖`, not `Dv (b − a) = 0`. Converting that into smallness of `‖Du (b − a)‖`
needs the quantitative statement that a vector almost annihilated by a surjection is close to its
kernel, which is a norm bound on a right inverse.

**The uniform version is a hard requirement, not a convenience.** The `ε → 0` limit of the
Eilenberg argument runs through a *different* approximating partition at every scale, so a constant
depending on the piece is useless; the bound must hold with one constant on a whole neighbourhood.
`exists_nhds_uniform_rightInverse_bound` supplies it by perturbing a single right inverse at the
base point: `Units.isOpen` keeps `A ∘ R₀` invertible nearby, `NormedRing.inverse_continuousAt`
keeps the inverse bounded, and `R₀ ∘ (A ∘ R₀)⁻¹` is then a right inverse of `A` of norm at most
`2‖R₀‖`.

**Both statements are stronger than the route asked for**: they need **no inner product** and **no
finite-dimensional domain**. The domain is an arbitrary real normed space and only the target is
finite-dimensional; the route's `coareaJacobian (fderiv ℝ v x₀) ≠ 0` is converted to surjectivity
by the proved `coareaJacobian_ne_zero_iff`, so inner products enter only in that translation. The
core estimate needs no surjectivity at all — any right inverse gives the bound with its own norm.

**Where surjectivity is and is not needed, recorded so the obligation is not overstated.** It is
what makes the right inverse exist: the rank-one projection of the plane admits none. It is **not**
forced by the pointwise conclusion — the zero map satisfies that conclusion with `C = 0` while
failing to be surjective — so this round does **not** claim surjectivity is necessary for the
pointwise half, and does not prove the (true) statement that in finite dimensions every linear map
satisfies it. For the **locally uniform** half the hypothesis at the base point does real work:
along `t • id` the smallest admissible constant is `|t|⁻¹`, which blows up as the family approaches
the non-surjective `0`, so no neighbourhood of such a point carries a single constant.

**What is still open, which is most of it.** `R0` — the rank-deficient part of almost every level
being `ℋ^k`-null — and `R4`–`R10`, `N1`, `N2` are **not proved**, and the **general codimension-`m`
coarea formula remains open**. Nothing here is a coarea formula, a slicing statement or a Sard
theorem, and no claim whatever is made about the measure of the set of critical *values*. **The
next obligation, `R4`, is the point of no return**: with `R2` and `R3` in place it is
self-contained, and if it fails the route is wrong.

Boundary cases are covered rather than excluded: a zero-dimensional target, a linear isomorphism, a
constant map, and the core estimate without surjectivity.

`research/audits/RankDeficientRouteStatements.lean` stays **byte-unchanged**; the new client
`research/audits/RightInverseBoundAudit.lean` copies its two `R3` propositions **verbatim** and
discharges them, with **16 standard-only axiom reports**. The area-formula route statements were
re-run and show **no new errors**; that file too stays byte-unchanged.

Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are untouched,
and no existing `.lean` file was modified.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the right inverse decision](research/decisions/2026-09-17-right-inverse-bound.md) and
`research/explorations/2026-09-17-right-inverse-bound.json`. The final verification receipt is
identified in `build/audit/right-inverse-bound/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Rank stratification and the kernel lemma: route obligations `R1` and `R2` proved (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**A correction to the round below, recorded rather than hidden.** That round declined to prove
anything on the ground that a new library module would force an edit to the aggregate
`formalization/FunctionalInequalities.lean`. **That reason was wrong.** `research/verify.py`
computes its build and kernel-replay scope from the source tree, not from the aggregate's import
closure — `build_replay_inputs` is documented as building the exact replay scope *including modules
outside default import closures* — and the existing `Analysis/Vector*.lean` modules are covered
that way without appearing in the aggregate. Adding an `Analysis` module therefore needs no
aggregate edit. The round below, its decision record and its receipt are **not rewritten**; the
correction is appended there and repeated here.

**What is proved: exactly `R1` and `R2`**, the first two obligations in the recommended order, in
the new Mathlib-only module `Analysis/RankStratification.lean` (local import closure **1 module**,
no work-in-progress file, and `formalization/FunctionalInequalities.lean` untouched).

**`R2`, the kernel lemma**, is the structural heart of the route and pure linear algebra. If
`P ∘ L` is surjective onto a space whose dimension equals the rank of `L`, then `P` is injective on
the range of `L`, so `ker (P ∘ L) = ker L`. In the route `L` is the differential at a point of the
stratum and `P` the orthogonal projection onto its range, so the conclusion is that **the
differential vanishes along the fibre of the regular component** — the fact that will let the
Eilenberg bound be applied inside a fibre at the exponent that matches. It uses no inner product,
no measure and no completeness.

**The dimension hypothesis of `R2` is necessary, and that is exhibited, not asserted.** Dropping
only that hypothesis makes the statement false: for the identity of the plane composed with the
first coordinate functional the composite is surjective onto `ℝ`, but the second basis vector lies
in the kernel of the composite and not in the kernel of the identity. `R2` is therefore not a
statement about surjectivity of the composite alone; it says exactly that `P` collapses no part of
the range of `L`.

**`R1`, the stratification**, has two halves. `measurableSet_rank_fderiv_eq`: the rank strata of a
`C¹` differential are measurable, because Mathlib's `isOpen_setOfPred_nat_le_rank` makes
`{f | r ≤ rank f}` open and a stratum is the difference of two such sets pulled back along the
continuous derivative — needing **no** measurable structure on the operator space and **no**
finite-dimensionality of the target. `setOf_not_surjective_fderiv_eq_iUnion`: the critical set is
the finite union of the strata of rank below the target dimension, with **no** regularity of `u`,
being pointwise linear algebra.

**`m = 1` returns the proved scalar situation.** For a one-dimensional target the critical set is
exactly the vanishing-derivative set, so the stratification adds nothing in codimension one, and
the audit **derives** the `m = 1` case of the still-open `R0` from the already proved
`ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero`. That closes **no part of the rank-deficient
problem**, which is empty when `m = 1`; the open case is `m ≥ 2`.

**What is still open, which is nearly all of it.** `R0` — the rank-deficient part of almost every
level being `ℋ^k`-null — and `R3`–`R10`, `N1`, `N2` are **not proved**, and the **general
codimension-`m` coarea formula remains open**. Nothing here is a coarea formula, a slicing
statement or a Sard theorem: no claim whatever is made about the measure of the set of critical
*values*. The next step in the recommended order is `R3`, then the point of no return `R4`.

Boundary cases are covered rather than excluded: a zero-dimensional target (every map surjective,
both sides of the decomposition empty, which is why `R0` needs no positivity of the codimension), a
zero-dimensional domain, a stratum index above the target dimension, and a zero-dimensional
projection target in `R2`.

`research/audits/RankDeficientRouteStatements.lean` stays **byte-unchanged**: the new client
`research/audits/RankStratificationAudit.lean` copies its `R1` and `R2` propositions **verbatim**
and discharges them, which is this repository's existing convention for a route obligation being
met. It has **20 standard-only axiom reports**. This round also re-ran the area-formula route
statements and found **no new errors**; that file too stays byte-unchanged.

Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are untouched,
and no existing `.lean` file was modified.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the rank stratification decision](research/decisions/2026-09-17-rank-stratification.md) and
`research/explorations/2026-09-17-rank-stratification.json`. The final verification receipt is
identified in `build/audit/rank-stratification/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Rank-deficient critical slicing: route exploration only (2026-09-17)

**Newest round; it changes none of the registration numbers recorded above, and it proves
nothing.** Direct holes stay **8 (1/2/5)** and certificates **24**.

**No theorem was proved this round.** This was a route exploration for the one remaining
structural gap of the codimension-`m` coarea program: the part of the critical set where the
derivative is rank-deficient but nonzero. The deliverable is
`research/audits/RankDeficientRouteStatements.lean`, a file of **15 `#check`s and nothing else** —
no declaration, no proof, no placeholder axiom. **A proposition that type-checks is not a proof,
and none of the 15 is proved anywhere in this repository.**

**The obstruction, located.** Writing `Σ_r = {x | rank (fderiv ℝ u x) = r}`, the proved
vanishing-derivative argument is exactly the `r = 0` layer: the approximating partition's linear
models are values of the derivative, so on `Σ_0` the linear part drops out and `u` is genuinely
`ε`-Lipschitz on each piece. For `r ≥ 1` it is not, in any direction inside the range of `Du`.
Projecting onto the `m − r` surviving directions does restore a small Lipschitz constant, but at
the **wrong exponent**: the Eilenberg bound then reads
`∫⁻ τ, μH[d] (S ∩ {Q ∘ u = τ}) dτ ≤ C · ε ^ (m−r) · μH[d + (m−r)] S`, so a finite right-hand side
forces `d = k + r`, and `μH[k + r]`-nullity says nothing about `μH[k]`. Insisting on `d = k`
instead puts `μH[n − r] S` on the right, which is `∞` for every `r ≥ 1` as soon as `S` has positive
Lebesgue measure. Both halves of this are written down as the route statements `N1` and `N2`.

**The route.** The exponent is repaired by slicing first along the `r` good directions: with `W₁`
the range of the differential and `P`, `Q` the orthogonal projections onto `W₁` and `W₁ᗮ`, the map
`P ∘ u` is a submersion near a point of `Σ_r`, so the **proved** regular coarea formula applies and
its fibres carry finite `ℋ^{n−r}` measure. On the stratum the differential kills the kernel of
`P ∘ Du`, so `Q ∘ u` has vanishing derivative along those fibres, and the Eilenberg bound used
**inside a fibre** has `d + (m − r) = n − r`, which is exactly right. This is an iterated slicing,
and Fubini across the orthogonal splitting of the target puts the two levels back together.

**What Mathlib has and lacks.** Mathlib has **no coarea formula, no constant-rank theorem and no
degenerate part of Federer's coarea formula**. It does have `isOpen_setOfPred_nat_le_rank` (lower
semicontinuity of the rank), the `ApproximatesLinearOn` line — which supplies the approximating
partition and nothing about rank, and whose `antilipschitz` half needs the model to be an
equivalence, so it does not apply here — the **equidimensional** Sard lemma
`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, and the measure-preserving orthogonal
splitting tools `Submodule.orthogonalDecomposition`, `LinearIsometryEquiv.measurePreserving` and
`WithLp.volume_preserving_ofLp`.

**Ten numbered obligations, none proved**, with exact Lean statements in the route file: `R1` rank
strata measurable, `R2` the kernel lemma, `R3` an approximate right inverse pointwise and locally
uniformly, `R4` the tangential small-Lipschitz estimate, `R5` finiteness of the fibre measure, `R6`
Fubini across the target splitting, `R7` the local per-stratum assembly, `R8` localization, `R9`
the unconditional coarea formula that consumes it, and `R10` the equidimensional degenerate case.
Estimated at roughly 1500 lines in total, with `R7` (450–600 lines) the only high-risk item and
`R4` the single point of no return: it is self-contained once `R2` and `R3` are in, and if it fails
the route is wrong. Recommended order is `R2`, `R1`, `R3`, `R4`, then `R5`/`R6` in parallel, then
`R7`, `R8`, `R9`.

**`R10` is cheap and was deliberately not proved.** With `n = m` the fibre dimension is `0` and
`μH[0]`-nullity of a slice means the slice is empty, which Mathlib's equidimensional Sard lemma
gives directly. Proving it would require a new library module and therefore an edit to the
aggregate `formalization/FunctionalInequalities.lean`, which this round was instructed not to make.
It is recorded as cheap-but-unproved rather than smuggled in, and it must not be counted as
progress on the rank-deficient part: it says nothing about the intermediate ranks, which are the
whole difficulty.

**No Sard theorem is in scope here either.** The route targets null critical *slices*; nothing is
claimed about the measure of the set of critical *values*, which for a merely `C¹` map may well be
positive.

This round reviewed the area-formula route statements again and found **no new errors**;
`research/audits/AreaFormulaRouteStatements.lean` stays **byte-unchanged**. One new observation,
recorded rather than acted on: `A5` carries the same `μH`-against-Lebesgue pairing as the falsified
`A0`, but `A5` is an implication whose proof is countable additivity and is therefore
normalization-agnostic, so `A5` is **not** falsified — only its conclusion is the literally false
`A0`, so its hypothesis is unsatisfiable in that normalization.

No `.lean` library source was modified, no module was added to the library, and no hole was
migrated. The new client's local import closure is 28 modules with **no** work-in-progress file.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the rank-deficient route decision](research/decisions/2026-09-17-rank-deficient-route.md) and
`research/explorations/2026-09-17-rank-deficient-route.json`. The final verification receipt is
identified in `build/audit/rank-deficient-route/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Codimension-`m` critical slicing: the vanishing-derivative part (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**What is proved.** `Analysis/VectorCriticalSlice.lean` proves that for a `C¹` map into an
`m`-dimensional target with `m ≥ 1`, almost every level meets `{x | fderiv ℝ u x = 0}` in an
`ℋ^{n−m}`-null set. The argument is the scalar one verbatim — the approximating partition makes `u`
`ε`-Lipschitz on disjoint pieces precisely because the derivative vanishes — run with the
codimension-`m` Eilenberg bound, whose constant `ε ^ m` tends to `0` exactly because `m ≥ 1`. The
positivity of `m` is a genuine hypothesis: with a zero-dimensional target every derivative vanishes.
With it, `coarea_of_contDiff_of_critical_eq_zeroDeriv` extends the regular-case coarea formula to
the whole space **under the hypothesis that the derivative vanishes wherever it fails to be
surjective**; the measurability comes from the previous round's unconditional slice measurability,
and the critical contribution vanishes on both sides.

**`m = 1` gives back the proved scalar `L10` and `L11`.** For a real differential, non-surjective
and zero are the same condition, so the dichotomy is automatic, and the audit recovers
`KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero` and `KLS.coarea_of_contDiff` verbatim — both
with the extra `1 ≤ finrank V` that the codimension-`m` dimension bookkeeping forces, recorded
rather than hidden.

**The gap is exhibited, not asserted.** For `m ≥ 2` the coarea critical set is where the rank drops
below `m`, **strictly larger** than the vanishing-derivative set. The audit's
`rank_deficient_witness` is the rank-one orthogonal projection of the plane onto its first axis:
its derivative is **nowhere zero** and **nowhere surjective**, so the vanishing-derivative set is
empty while the critical set is everything, and the dichotomy hypothesis fails at every point. The
method does not extend, because it rests on `u` being `ε`-Lipschitz on the pieces, which needs the
derivative to vanish rather than merely to be non-surjective. **Nothing about the rank-deficient
part is proved**, and with it the **general codimension-`m` coarea formula remains open**.

**No Sard theorem is claimed**: nothing is asserted about the measure of the set of critical
*values*, which for a merely `C¹` map may well be positive. `KLS/Geometry/CriticalSlice.lean` and
`KLS/Geometry/SmoothCoarea.lean` were not modified; the codimension-`m` versions are parallel new
modules. Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are
untouched.

This round reviewed the area-formula route statements again and found **no further errors**;
`research/audits/AreaFormulaRouteStatements.lean` stays **byte-unchanged**.

The module's local import closure is 28 modules with **no** work-in-progress file.
`research/audits/VectorCriticalSliceAudit.lean` has 17 standard-only axiom reports.

**Next in the program**: the rank-deficient part is the only remaining structural gap. A plausible
route is a rank stratification with iterated slicing along the surviving directions — the hard part
of the degenerate case of Federer's coarea formula, for which neither this repository nor Mathlib
has tools; a route-exploration round is recommended before attempting it.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the critical slicing decision](research/decisions/2026-09-17-vector-critical-slice.md) and
`research/explorations/2026-09-17-vector-critical-slice.json`. The final verification receipt is
identified in `build/audit/vector-critical-slice/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Codimension-`m` compact slices and unconditional slice measurability (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**Only half of the scalar layer needed redoing.** `Analysis/HausdorffContent.lean` proves two
things: that the scalewise **open**-cover costs have `μH[d]` as their scale limit, and that at a
fixed scale the open-cover cost of the slices of a compact set is upper semicontinuous in the level.
The first is about the ambient space only and is reused **verbatim**; only the second mentions the
target. Its proof is unchanged except that the real-valued distance `|u x − t|` becomes
`dist (u x) t`.

**What is proved.** `Analysis/VectorSliceMeasurable.lean` gives
`measurable_hausdorffMeasure_inter_levelSet_vector` — for `S` compact and `u` continuous into a
metric space, the slice measure is Borel measurable in the level, with no Lipschitz hypothesis and
no finiteness — and then, with the Eilenberg inequality of the previous round, the whole chain:
`aemeasurable_setLIntegral_inter_levelSet_vector` for a map Lipschitz on a Borel set, and
`aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector` for a map that is `C¹` on an open
set only. Inner regularity exhausts the Borel set by compacts up to a Lebesgue-null remainder, the
compact pieces are handled by upper semicontinuity and the remainder by the Eilenberg null slicing;
increasing simple functions carry the result to an arbitrary measurable `ℝ≥0∞` weight.

**None of this needs the differential to be surjective.** Unlike the chart route of
`Analysis/VectorRegularCoarea.lean`, these statements cover the **critical** part of the domain; the
audit witnesses it with a constant map, whose differential is nowhere surjective once the target is
positive-dimensional.

**`m = 1` gives back the proved scalar statements, with one difference recorded rather than
hidden.** `Analysis.measurable_hausdorffMeasure_inter_levelSet` is recovered verbatim, and
`KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn` is recovered **with an extra
hypothesis `1 ≤ finrank V`**: the codimension-`m` statements carry
`k + finrank W = finrank V`, so a zero-dimensional ambient space — which the scalar statement covers
through natural subtraction and a subsingleton branch — is outside their reach.

**What this is not: a coarea formula.** What is removed is the regularity hypothesis from the
**measurability** half, not from the coarea **equality**, which still holds only where the
differential is surjective. The critical part of the equality needs a codimension-`m` Sard or
critical-slice argument, which is not proved. `HausdorffContent.lean`, `HausdorffSlicing.lean`,
`SurfaceSlicing.lean` and `OpenSliceMeasurable.lean` were not modified; the codimension-`m` versions
are parallel new modules. Sharp finite-regularity Sard, the two Cheeger comparisons and the five
Energy holes are untouched.

This round reviewed the area-formula route statements again and found **no further errors**;
`research/audits/AreaFormulaRouteStatements.lean` stays **byte-unchanged**.

The module's local import closure is 13 modules with **no** work-in-progress file.
`research/audits/VectorSliceMeasurableAudit.lean` has 18 standard-only axiom reports.

**Next in the program**: a codimension-`m` Sard or critical-slice argument, and then the general
codimension-`m` coarea formula.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the slice measurability decision](research/decisions/2026-09-17-vector-slice-measurable.md) and
`research/explorations/2026-09-17-vector-slice-measurable.json`. The final verification receipt is
identified in `build/audit/vector-slice-measurable/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## The Eilenberg slicing inequality in codimension `m` (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**What is proved.** `Analysis/VectorHausdorffSlicing.lean` is the codimension-`m` analogue of
`Analysis/HausdorffSlicing.lean`: for `u` Lipschitz on `S` with values in an `m`-dimensional inner
product space, the slice function `t ↦ μH[d] (S ∩ {u = t})` is dominated by a **measurable** `F`
with `∫⁻ F ≤ volume (closedBall 0 1) · K ^ m · μH[d + m] S`. The majorant's measurability is part of
the conclusion: the slice function itself is not known to be measurable at this point of the
development. Its null case — a `μH[d + m]`-null set has `μH[d]`-null slices at almost every level —
is proved with it, in the raw and in the normalized convention, the latter being what the coarea
layer consumes. The module's local import closure is **two** modules; everything else is Mathlib.

**Where the codimension enters, and only there.** The argument is a covering argument, not
Rademacher. In the real-valued case the `u`-image of a cover piece lies in an **interval** of length
`2 K · diam`; in codimension `m` it lies in a **ball** of radius `K · diam`, whose volume is
`volume (closedBall 0 1) · (K · diam) ^ m` — that is the whole of the difference, and it is where
the `m`-th power comes from.

**`m = 1` gives back the proved scalar bound, constant included.** On the real line
`volume (closedBall 0 1) = 2` and `K ^ 1 = K`, so the codimension-`m` constant **is** the scalar
`2 K`; the audit reproduces the statement of `Analysis.exists_measurable_majorant` verbatim and
discharges it from the codimension-`m` theorem.

Degenerate data are handled rather than excluded: `K = 0`, `d = 0`, an infinite cover cost, and
**a zero-dimensional target**, where every ball is the whole space and the inequality degenerates to
an equality. `S` need not be measurable, bounded or nonempty, and `u` need not be globally
Lipschitz, differentiable or measurable.

**What this is not: slice measurability.** The chain from the Eilenberg inequality to unconditional
weighted slice measurability is **not** completed: it also needs codimension-`m` **compact-slice
measurability**, the analogue of `Analysis.measurable_hausdorffMeasure_inter_levelSet`, which is
stated for a real-valued function and is not generalized here. So the coarea layer's
codimension-`m` slice measurability still carries the regularity hypothesis obtained from the chart,
the **critical set is still untreated**, and the **general codimension-`m` coarea formula remains
open**. `Analysis/HausdorffSlicing.lean` was not modified: the codimension-`m` version is a parallel
new module. Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are
untouched.

This round reviewed the area-formula route statements again and found **no further errors**;
`research/audits/AreaFormulaRouteStatements.lean` stays **byte-unchanged**.

`research/audits/VectorHausdorffSlicingAudit.lean` has 15 standard-only axiom reports.

**Next in the program**: codimension-`m` compact-slice measurability — generalizing the scalewise
open-cover costs and their upper semicontinuity in the level to a vector-valued map — then
unconditional weighted slice measurability, and only then the critical case.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the Eilenberg decision](research/decisions/2026-09-17-vector-hausdorff-slicing.md) and
`research/explorations/2026-09-17-vector-hausdorff-slicing.json`. The final verification receipt is
identified in `build/audit/vector-hausdorff-slicing/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Codimension-`m` slice measurability and the regular coarea formula (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**The route differs from the scalar one, and that is a real limitation.** In codimension one the
repository proves weighted slice measurability for an **arbitrary** Borel subset of an open `C¹`
domain, with **no** regular-point hypothesis, through the Eilenberg slicing inequality of
`KLS/Geometry/SurfaceSlicing.lean`. The **codimension-`m` Eilenberg inequality is not proved here**
and Mathlib does not provide it. So this round goes through the chart instead: on a level-graph
family the slice integral is the Tonelli section of one measurable function on the parameter–level
product, so its measurability is immediate and no slicing inequality is used. The cost is that the
statement holds **only where the differential is surjective**.

**What is proved.** `Analysis/VectorRegularCoarea.lean` gives chart-local weighted slice
measurability, the neighbourhood form carrying both the measurability and the equality, and their
assembly: **`coarea_of_contDiffOn_of_coareaJacobian_ne_zero`, the codimension-`m` regular coarea
formula** — the analogue of the scalar `L9`. On an open set where the differential is everywhere
surjective, for every Borel `S` inside it and every measurable `ℝ≥0∞` weight, the level function is
**measurable** and

`∫ coareaJacobian (Du) · g dx = ∫_t ∫_{S ∩ {u = t}} g dℋ^{n−m} dt`,

with the normalized Hausdorff measure of the codimension as fibre measure. The assembly is the same
shape as the scalar one: countable cover, `disjointed` pieces, the neighbourhood form on each, and
`lintegral_tsum`. The conclusion is `Measurable`, **stronger** than the scalar `L9`'s
`AEMeasurable`; that is a by-product of the chart route. No finiteness, boundedness, integrability,
regular-value or `SFinite` hypothesis, and no regularity outside the open set.

**`m = 1` gives back the proved scalar `L9` verbatim.** The audit reproduces the statement of
`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero` — gradient norm, `surfaceMeasure V`, `AEMeasurable` —
and discharges it from the codimension-`m` theorem, through `coareaJacobian_fderiv`, the dimension
identity, and the fact that a nonzero real differential is surjective.

**What this is not: the general codimension-`m` coarea formula.** That needs the **critical set**,
hence a codimension-`m` Sard or critical-slice argument, and it needs slice measurability without
the regularity hypothesis, hence the codimension-`m` Eilenberg slicing inequality — none of which is
proved. Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are
untouched.

This round reviewed the area-formula route statements again and found **no further errors**;
`research/audits/AreaFormulaRouteStatements.lean` stays **byte-unchanged**.

The module's local import closure is 21 modules with **no** work-in-progress file.
`research/audits/VectorRegularCoareaAudit.lean` has 11 standard-only axiom reports.

**Next in the program**: the codimension-`m` Eilenberg slicing inequality, which is what would make
slice measurability available without regularity and open the critical case.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the regular coarea decision](research/decisions/2026-09-17-vector-regular-coarea.md) and
`research/explorations/2026-09-17-vector-regular-coarea.json`. The final verification receipt is
identified in `build/audit/vector-regular-coarea/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Weighted codimension-`m` area formula and the local coarea equality (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.** No
hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

**The weighted area formula.** `Analysis/VectorGraphIntegral.lean` upgrades obligation `B2` from an
identity of *measures of sets* to an identity of *measures*:
`map_vectorGraphMap_withDensity` says the graph parametrization pushes the Jacobian-weighted
Lebesgue measure on the parameter space forward to the normalized surface measure restricted to the
graph — injectivity of the graph map is automatic by construction, and its image is measurable, both
already proved. From it, `setLIntegral_image_vectorGraphMap` is the **weighted codimension-`m` graph
area formula**: the surface integral of an arbitrary measurable `ℝ≥0∞` weight over a piece of a `C¹`
graph is the Lebesgue integral of that weight against the graph area density. `B2` is the `f = 1`
case, recovered verbatim in the audit. No integrability, finiteness or boundedness is assumed, and
the weight may be identically `∞`.

**The local coarea equality.** `Analysis/VectorLocalCoarea.lean` joins three results, one from each
of the last three rounds — the ambient-side identity, this round's weighted area formula, and the
slice description — by Tonelli in the level variable. The outcome is
`setLIntegral_coarea_levelGraphFamily`, the codimension-`m` analogue of the scalar
`setLIntegral_coarea_graph_family`, and hence `exists_vector_coarea_neighborhood`: **every point
where the differential is surjective has an open neighbourhood on every Borel subset of which the
codimension-`m` coarea equality holds**, for every measurable `ℝ≥0∞` weight, with the surface
measure in dimension `finrank V - finrank W`. The hypotheses are only that `u` is `C¹` on an open set
and that its differential is surjective at the point: no regularity outside that set, and no
finiteness, boundedness, integrability, regular-value or `SFinite` hypothesis.

**`m = 1` returns the proved scalar statements.** The audit recovers the repository's proved
`Analysis.setLIntegral_image_graphMap` from the codimension-`m` weighted formula, and checks that the
ambient density of the local coarea equality is `‖gradient u x‖ₑ` when the target is `ℝ`.

**What this is not: the codimension-`m` regular coarea formula.** Two things are missing. First,
codimension-`m` **weighted slice measurability** — the `AEMeasurable` statement for
`t ↦ ∫⁻ over S ∩ {u = t}` — without which a sum cannot be exchanged with the outer integral, since
`lintegral_tsum` needs measurability; the scalar analogue is
`KLS/Geometry/OpenSliceMeasurable.lean`. Second, the **countable cover with disjoint patching** that
assembles the neighbourhood form into an equality on a whole regular open set; the scalar analogue
is the assembly in `KLS/Geometry/RegularCoarea.lean`. Critical slicing, sharp finite-regularity
Sard, the two Cheeger comparisons and the five Energy holes are untouched.

This round reviewed the area-formula route statements again and found **no further errors**;
`research/audits/AreaFormulaRouteStatements.lean` stays **byte-unchanged**.

The two modules' local import closures are 11 and 20 modules, with **no** work-in-progress file.
`research/audits/VectorLocalCoareaAudit.lean` has 15 standard-only axiom reports.

**Next in the program**: codimension-`m` weighted slice measurability, then the countable cover and
disjoint patching.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the local coarea decision](research/decisions/2026-09-17-vector-local-coarea.md) and
`research/explorations/2026-09-17-vector-local-coarea.json`. The final verification receipt is
identified in `build/audit/vector-local-coarea/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Fibrewise `m`-dimensional change of variables (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.**
It is the **third** auditable sub-block of the codimension-`m` **regular** case and does not
complete it. **No coarea formula is proved.** No hole was migrated: direct holes stay **8 (1/2/5)**
and certificates **24**.

**A Mathlib gap had to be filled first.** Mathlib's change of variables
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` is a **self-map** statement, `f : E → E`, whose
volume factor `|det (f' x)|` is the determinant of an endomorphism. A fibre map `t ↦ ψ (y, t)` goes
from the level space `W` to the normal factor `K`, two **different** spaces of the same dimension,
so that determinant does not even typecheck.
`Analysis/VectorFiberIntegral.lean` proves the missing statement,
`lintegral_image_eq_lintegral_normDet_fderiv_mul`: the change of variables between two inner product
spaces of the same dimension, with `LinearMap.normDet` — which is defined between different spaces —
as the volume factor. The proof conjugates by a linear isometry equivalence, which is measure
preserving and has unit norm determinant, so nothing is added; the chosen isometry appears only
inside the proof and in no statement. The map needs only a within-derivative at each point and
injectivity there, and the weight is an arbitrary `ℝ≥0∞` function: **no integrability, finiteness or
continuity**.

**What is proved on top of it.** `setLIntegral_image_vectorVerticalMap` is the codimension-`m`
vertical substitution for `T (y, t) = (y, ψ (y, t))`, with the level space and the normal factor
kept distinct throughout; `setLIntegral_image_levelGraphMap` transports it to the ambient space
along the measure-preserving splitting proved two rounds ago; and
`setLIntegral_coareaJacobian_levelGraphFamily` is the **ambient side of the local coarea equality**:
on a Borel piece of a level-graph family, the integral of the ambient coarea density against an
arbitrary weight equals the integral over the parameter–level domain of the **graph area density**,
which is exactly what the proved area formula `B2` consumes. The change of density is the previous
round's fibre Jacobian identity, applied pointwise.

**The equal-dimension hypothesis is necessary**, and the audit exhibits the failure rather than
asserting it: for the line map from `ℝ` into the plane on the unit interval the left-hand side is
`0`, because the image lies in a proper subspace, and the right-hand side is `1`.

**`m = 1` returns the proved scalar substitution.** The audit derives the repository's already
proved `Analysis.setLIntegral_image_verticalMap` **verbatim** from the codimension-`m` statement.

**What this is not**: not the codimension-`m` coarea formula and not its regular case. Still missing
are the **weighted** codimension-`m` area formula on the fibre side — the analogue of
`setLIntegral_image_graphMap`, since last round's fibre measure carries weight one only — the
Tonelli assembly in the level variable, the patching, and codimension-`m` weighted slice
measurability. Critical slicing, sharp finite-regularity Sard, the two Cheeger comparisons and the
five Energy holes are untouched.

This round reviewed the area-formula route statements again and found **no further errors**;
`research/audits/AreaFormulaRouteStatements.lean` stays **byte-unchanged**.

The module's local import closure is 18 modules with **no** work-in-progress file.
`research/audits/VectorFiberIntegralAudit.lean` has 16 standard-only axiom reports.

**Next in the program**: the weighted codimension-`m` graph area formula, then Tonelli joining the
two sides into the local coarea equality, then the countable patching.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the fibre change-of-variables decision](research/decisions/2026-09-17-vector-fiber-integral.md) and
`research/explorations/2026-09-17-vector-fiber-integral.json`. The final verification receipt is
identified in `build/audit/vector-fiber-integral/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Codimension-`m` parametric implicit-function charting (2026-09-17)

**Newest implementation round; it changes none of the registration numbers recorded above.**
It is the **second** auditable sub-block of the codimension-`m` **regular** case and does not
complete it. **No coarea formula is proved.** No hole was migrated: direct holes stay **8 (1/2/5)**
and certificates **24**.

**What is proved.** `Analysis/VectorRegularChart.lean` builds the codimension-`m` analogue of
`RegularChart.lean`: near a point where the differential is surjective, the fibres of `u : V → W`
are **simultaneously** the graphs of **one globally `C¹` map** `ψ` over a fixed parameter space,
with the level as a parameter. `exists_levelGraphFamily` delivers an open joint domain `Ω ⊆ H × W`,
a globally `C¹` `ψ`, and an open neighbourhood `N ⊆ O` of the point that the graph map
`p ↦ ι p.1 + κ (ψ p)` carries **bijectively** onto `Ω`'s image, with `u (ι p.1 + κ (ψ p)) = p.2`.
Its regular-point form assumes only `coareaJacobian (fderiv ℝ u x₀) ≠ 0`: the parameter space is the
kernel of the differential, the normal factor its orthogonal complement, and the codimension match
is automatic. There is **no** regularity hypothesis outside `O` and no finiteness, boundedness,
integrability, regular-value or `SFinite` hypothesis anywhere.

**One step genuinely differs from codimension one.** The scalar chart
`x ↦ graphRetract ι x + u x • e` is still valued in `V`, because the normal direction is a line
inside `V` and `u x` is a scalar. In codimension `m` the value `u x` lies in `W`, which is **not**
inside `V`, so this round's chart maps into the **product**, `Φ x = (ιᵀ x, u x) : H × W`. No copy of
`W` inside `V` and no identification of the normal factor with `W` is needed, and the repository's
`exists_contDiffOn_localInverse` is already stated between two different spaces. The inverse of the
derivative is written down **explicitly**, `(y, w) ↦ ι y + κ (Q⁻¹ w)`, rather than obtained from a
dimension count.

**Two interfaces with results already proved.** `slice_eq_image_vectorGraphMap` identifies
`N ∩ {u = t}` with the graph of `y ↦ ψ (y, t)`, so
`hausdorffNormalized_slice_of_levelGraphFamily` measures that fibre through the proved area formula
`B2` — **with weight one**; the weighted version, the analogue of `setLIntegral_image_graphMap`, is
**not** proved. And `normDet_fderiv_mul_coareaJacobian_of_levelGraphFamily` shows the family
satisfies verbatim the hypotheses of the previous round's fibre Jacobian identity, so the two
densities match on the whole chart.

**`m = 1` returns the proved scalar shape.** The audit proves that a scalar `IsGraphSplitting` **is**
a vector splitting with one-dimensional normal factor, and that from the scalar hypotheses
`gradient u x₀ = c • e` with `c ≠ 0` the chart produces `u (ι y + ψ (y, t) • e) = t` — exactly the
`hlevel` shape consumed by the proved `Analysis.setLIntegral_coarea_graph_family`.

**What this is not**: not the codimension-`m` coarea formula and not its regular case. Still missing
are the fibrewise `m`-dimensional change of variables on the ambient side, the **weighted** area
formula on the fibre side, the local-to-global patching, and codimension-`m` weighted slice
measurability. Critical slicing, sharp finite-regularity Sard, the two Cheeger comparisons and the
five Energy holes are untouched.

This round reviewed the area-formula route statements again and found **no further errors**; the two
already recorded — `B1` and `A0`, the latter proved false last round — stand, and
`research/audits/AreaFormulaRouteStatements.lean` stays **byte-unchanged**.

The module's local import closure is 16 modules with **no** work-in-progress file.
`research/audits/VectorRegularChartAudit.lean` has 25 standard-only axiom reports.

**Next in the program**: the fibrewise `m`-dimensional change of variables on this round's
measure-preserving splitting, and the weighted codimension-`m` area formula; then the assembly into
the local coarea equality and the countable patching.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the charting decision](research/decisions/2026-09-17-vector-regular-chart.md) and
`research/explorations/2026-09-17-vector-regular-chart.json`. The final verification receipt is
identified in `build/audit/vector-regular-chart/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Codimension-`m` fibre Jacobian: the regular case's density matching (2026-09-16)

**Newest implementation round; it changes none of the registration numbers recorded above.**
It delivers **one complete, auditable sub-block** of the codimension-`m` **regular** case and
**does not** complete that case. **No coarea formula is proved.** No hole was migrated: direct
holes stay **8 (1/2/5)** and certificates **24**.

**Why not the whole regular case.** The scalar `L9` chain is four stages: local graph family,
measure-preserving splitting, fibrewise change of variables, pointwise density matching, then
patching. Stages one and two alone are `ImplicitGraph.lean` (859 lines), `RegularChart.lean` (164)
and `SubgraphDivergence.lean` (859), and the codimension-`m` analogue needs a **parametric**
implicit function theorem into an `m`-dimensional target and an `m`-dimensional fibrewise change of
variables. Rather than leave half a chain, this round finishes the one stage that is genuinely new
mathematics and independent of the charting machinery — the **density matching** — together with
the linear and measure backbone of stage two.

**What is proved.** `Analysis/CoareaGraphJacobian.lean` matches the two densities of the
codimension-`m` coarea formula. In linear form, under an orthogonal splitting `V = ι '' H ⊕ κ '' K`
with `finrank K = finrank W` and a slope whose graph lies in `ker L`,
`coareaJacobian L = normDet (L ∘ κ) · normDet (graphMapLinear ι κ A)`. In `C¹` form, along a level
family `u (ι y + κ (ψ (y, t))) = t`,
`normDet (Dₜψ) · coareaJacobian (fderiv ℝ u x) = normDet (graphMapLinear ι κ (D_yψ))` — the
codimension-`m` analogue of `abs_deriv_mul_norm_gradient`, whose right-hand side is exactly the
density the proved `B2` integrates. Only differentiability of `u` at the point is used: **no
finiteness, boundedness, integrability, regular-value or `SFinite` hypothesis**. The round also
proves that `(y, z) ↦ ι y + κ z` **preserves Lebesgue measure**, the Tonelli backbone the next
stage needs, and that a surjective differential supplies the splitting and the codimension match
automatically.

**One piece of linear algebra was missing from Mathlib.** The **Weinstein–Aronszajn identity in
linear-map form**, `det (1 + X ∘ Y) = det (1 + Y ∘ X)` with the two identity maps on *different*
spaces; Mathlib has the matrix statement only. It is precisely the passage from the Gram
determinant on the target — a coarea Jacobian — to the Gram determinant on the parameter space — an
area Jacobian.

**The codimension hypothesis `finrank K = finrank W` is necessary, and the audit exhibits the
failure rather than asserting it.** With `finrank W < finrank K` and `L` surjective the right-hand
side is `0` while the left-hand side is not; `necessity` instantiates this with the zero subspace
of `ℝ²` as parameter space, the whole plane as normal factor and `ℝ` as target, where orthogonality,
spanning and the slope equation all hold.

**A second route-statement error, reported and corrected rather than quietly fixed.** Reviewing
the route statements again for the defect recorded for `B1` last round, obligation **`A0`** — the
route's own target, the Federer area formula — carries **exactly the same** normalization defect: it
pairs the **raw** `μH[finrank H]` on the left with **Lebesgue** measure on the right. The audit's
`route_A0_false` **proves that statement false**, with the identity map of the plane on the closed
unit ball, the two sides differing by `2² / ω₂ = 4 / π`. Obligation **`A5`** writes the same
mis-pairing on **both** sides, so the constant cancels and `A5` is **not** falsified by it, though
its hypothesis is then not the true local area formula. `A1`–`A4` and `B2` are unaffected.
`research/audits/AreaFormulaRouteStatements.lean` is left **byte-unchanged** as its own round's
dated evidence.

**`m = 1` returns the proved scalar theory.** `normDet_graphMapLinear_eq_graphJacobian` identifies
the new volume factor with `graphJacobian`, `coareaJacobian_fderiv` already identified the ambient
density with `‖gradient u x‖`, and `abs_deriv_mul_norm_gradient_of_vectorGraphSplitting` is
literally the scalar identity.

**What this is not**: not the codimension-`m` coarea formula, not its regular case, and not the
codimension-`m` charting or the fibrewise `m`-dimensional change of variables — none of which
exists anywhere in the repository. Critical slicing, sharp finite-regularity Sard, the two Cheeger
comparisons and the five Energy holes are untouched.

The module's local import closure is 9 modules with **no** work-in-progress file.
`research/audits/CoareaGraphJacobianAudit.lean` has 30 standard-only axiom reports.

**Next in the program**: the codimension-`m` local graph family from a parametric implicit function
theorem, then the `m`-dimensional fibrewise change of variables on this round's measure-preserving
splitting, then the assembly with `B2` and the countable patching.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**

See [the fibre Jacobian decision](research/decisions/2026-09-16-coarea-graph-jacobian.md) and
`research/explorations/2026-09-16-coarea-graph-jacobian.json`. The final verification receipt is
identified in `build/audit/coarea-graph-jacobian/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Codimension-`m` area formula for `C¹` graphs: `B1` completed (2026-09-16)

**Newest implementation round; it changes none of the registration numbers recorded above.**
`Analysis/VectorGraphArea.lean` proves the **codimension-`m` area formula for `C¹` graphs**, in both
the raw and the normalized Hausdorff convention. Obligation `B1` of the area formula route is
complete. No hole was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

The `k`-dimensional measure of the graph of a `C¹` `K`-valued map over a measurable parameter set is
the integral of `√det (1 + Dγᵀ Dγ)` — against `μH[k]` in the raw form, against **Lebesgue** measure
in the normalized form, which is what the coarea program consumes. The parameter set need only be
measurable: **no finiteness, boundedness or injectivity hypothesis**, a graph map being injective by
construction.

**One step genuinely differs from codimension one.** That proof uses that the Jacobian
`√(1 + ‖a‖²)` is globally `1`-Lipschitz in the slope, so closeness of derivatives transfers to
closeness of Jacobians. In codimension `m` the Jacobian `√det (1 + AᵀA)` is **not** uniformly
Lipschitz — for `A = t • id` on a two-dimensional parameter space it grows like `1 + t²` — so the
previous round's partition was not enough. This round's partition controls the Jacobian
**directly**, which the continuity proved as obligation `A1` supplies. Everything after that
mirrors the codimension-one file, and its limit lemmas `tendsto_aux`, `tendsto_aux'` are
graph-independent and were reused unchanged.

**A correction to the route statements, recorded rather than quietly fixed.** Obligation `B1` as
written in `research/audits/AreaFormulaRouteStatements.lean` paired the **raw** `μH[k]` on the left
with **Lebesgue** measure on the right. Those differ by `2^k / ω_k`, which is `1` only for `k ≤ 1`,
so **that statement is false as written for `k ≥ 2`** and is not what was proved. Both correct
pairings are proved and audited: raw with raw, and normalized with Lebesgue — the latter being the
route's `B2`, which was stated correctly and is discharged verbatim. The route statements file is
left **byte-unchanged** as its own round's dated evidence.

**What this is not**: it is the area formula for a **graph**, not the Federer area formula `A0` for
an arbitrary injective `C¹` parametrization, which stays open together with `A2`–`A5`. The route
recommended the graph version precisely because a graph map is injective by construction and has an
explicit left inverse.

The module's local import closure is 10 modules with **no** work-in-progress file.
`research/audits/VectorGraphAreaAudit.lean` has 10 standard-only axiom reports.

**Next in the program**: the codimension-`m` **regular case** of the coarea formula, the analogue of
the scalar `L9` — on the open set where `coareaJacobian ≠ 0`, represent the fibres as a family of
graphs by the parametric implicit function theorem and apply this round's normalized area formula.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**
Sharp finite-regularity Sard, Energy's five holes and dimension-free KLS also remain open.

See [the `B1` completion decision](research/decisions/2026-09-16-vector-graph-area.md) and
`research/explorations/2026-09-16-vector-graph-area.json`. The final verification receipt is
identified in `build/audit/vector-graph-area/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Vector-valued sandwich estimates: `B1` fourth phase (2026-09-16)

**Superseded by the `B1` completion round above; retained as a dated snapshot. It it changes none of the registration numbers recorded above.**
`Analysis/VectorGraphSandwich.lean` proves the two-sided estimates of the codimension-`m` graph area
formula, together with the approximating partition that feeds the fifth phase. **The area formula
itself is still not proved**, no hole was migrated: direct holes stay **8 (1/2/5)** and certificates
**24**.

Everything rests on the **Pythagorean identity** `‖ι y + κ z‖² = ‖y‖² + ‖z‖²`, which holds because
the two embeddings have orthogonal ranges. Its consequence is that a graph map **never moves points
closer together** — and that is exactly the lower-bound input the general area formula route has to
extract from an inverse it does not have. With it, a graph map that is `ε`-close to its linear model
has `k`-dimensional image measure within a factor `(1 + ε)^k` of the linear one, on **both** sides.

Both directions reduce to the same generic comparison
`Analysis.hausdorffMeasure_image_le_of_norm_le`, which was already proved for the codimension-one
file and is **reused, not reproved**; the linear case comes from Mathlib. The round also supplies
`exists_approximating_partition_vectorGraph`, the countable measurable partition on which the graph
map is `ε`-approximated and the derivative stays `ε`-close to the corresponding slope.

The module's local import closure is 9 modules with **no** work-in-progress file.
`research/audits/VectorGraphSandwichAudit.lean` has 15 standard-only axiom reports. Its
`exact_at_zero` client is the sandwich **degenerating correctly at `ε = 0`**, not the area formula.

**Next, and last, for `B1`**: the fifth phase — `ε → 0` and the countable patching, about 280 lines
in the codimension-one file. The limit lemmas `tendsto_aux` and `tendsto_aux'` there are already
graph-independent, so they should be reusable and the remaining work should come in under that.
Route obligations `A2`–`A5` and `B2` remain untouched.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**
Sharp finite-regularity Sard, Energy's five holes and dimension-free KLS also remain open.

See [the fourth-phase decision](research/decisions/2026-09-16-vector-graph-sandwich.md) and
`research/explorations/2026-09-16-vector-graph-sandwich.json`. The final verification receipt is
identified in `build/audit/vector-graph-sandwich/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Vector-valued graphs: `B1` first part (2026-09-16)

**Superseded by the fourth-phase round above; retained as a dated snapshot. It it changes none of the registration numbers recorded above.**
`Analysis/VectorGraph.lean` mirrors phases two and three of the codimension-one area formula file
with a vector-valued slope. **The area formula itself is not proved**, no hole was migrated: direct
holes stay **8 (1/2/5)** and certificates **24**.

`Analysis/AreaFormula.lean` (codimension one, 957 lines) runs in five phases — linear model, `C¹`
graph map, linear approximation, two-sided estimates, area formula. This round does phases two and
three in codimension `m`, and gets phase one for free.

Proved: `vectorGraphMap ι κ γ = fun y ↦ ι y + κ (γ y)`; the retraction identity
`graphProj ι (vectorGraphMap ι κ γ y) = y`, which is the **explicit left inverse** the general route
`A3` has to construct by hand, valid for an arbitrary slope; injectivity with **no hypothesis on the
slope**, so no `InjOn` assumption and no multiplicity anywhere; the derivative identification
`HasFDerivAt (vectorGraphMap ι κ γ) (graphMapLinear ι κ (fderiv ℝ γ y)) y`, so the volume factor
computed last round is pointwise the right one; linear approximation on a ball where the derivative
varies by at most `ε` — **cleaner than codimension one**, since the second factor is an isometry and
its norm disappears rather than needing the `innerSL`/gradient detour; and image measurability.

**Phase one came for free.** The linear case of `B1` follows directly from Mathlib's linear area
formula together with last round's `normDet_graphMapLinear`, so the shear-and-dilation argument the
codimension-one file needed (about 160 lines) is not repeated. The round also consumes `A1` to show
the volume factor along a `C¹` slope is measurable, so the right-hand side of `B1` is a genuine
lower integral.

The module's local import closure is 8 modules with **no** work-in-progress file.
`research/audits/VectorGraphAudit.lean` has 20 standard-only axiom reports, including codimension
zero, a constant slope and a zero-dimensional parameter space.

**Next**: phases four and five — the two-sided Hausdorff estimates, where the explicit left inverse
pays for itself on the lower bound, then `ε → 0` and the countable patching. One to two rounds.
Route obligations `A2`–`A5` and `B2` remain untouched.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**
Sharp finite-regularity Sard, Energy's five holes and dimension-free KLS also remain open.

See [the `B1` first-part decision](research/decisions/2026-09-16-vector-graph.md) and
`research/explorations/2026-09-16-vector-graph.json`. The final verification receipt is identified
in `build/audit/vector-graph/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Route obligation `A1` proved: continuity of the volume factor (2026-09-16)

**Superseded by the `B1` first-part round above; retained as a dated snapshot. It it changes none of the registration numbers recorded above.**
`Analysis/NormDetContinuity.lean` proves that `normDet` is continuous in the operator and that the
area-formula integrand is measurable. **No area formula and no coarea formula are proved**, no hole
was migrated: direct holes stay **8 (1/2/5)** and certificates **24**.

Why it was a real obligation: Mathlib carries the algebra of `LinearMap.normDet` but **not** its
continuity, and without that the right-hand side of the area formula is not even known to integrate
a measurable function. The previous round's route exploration listed this as `A1`.

Proved: `normDet A = √det (Aᵀ ∘L A)` in continuous-linear-map form; `A ↦ Aᵀ ∘L A` is continuous
because the adjoint is a linear isometry and composition is a bounded bilinear map; hence
`continuous_normDet` by `ContinuousLinearMap.continuous_det` and `Real.continuous_sqrt`; hence
`measurable_normDet_fderiv`. The same chain gives `continuous_coareaJacobian` and
`measurable_coareaJacobian_fderiv` on the coarea side.

**Stronger than the route asked for**: the route stated measurability under `ContDiff ℝ 1 g`, but
`measurable_fderiv` holds for an arbitrary function — `fderiv` is zero where the function is not
differentiable — so the proved lemma carries **no** differentiability hypothesis and the route form
follows by discarding it. The audit records this against a function that is differentiable nowhere.

**Consistency with the proved scalar theory**: combining the new measurability with
`coareaJacobian_fderiv` gives measurability of `‖gradient u x‖`, the integrand of the already proved
`L11`/`L12`/`L13`. The new layer is the same object as the scalar one, not a parallel construction.

The module's local import closure is 2 modules with **no** work-in-progress file.
`research/audits/NormDetContinuityAudit.lean` has 13 standard-only axiom reports and reproduces the
two `A1` route statements verbatim before discharging them;
`research/audits/AreaFormulaRouteStatements.lean` is left **byte-unchanged** as the previous round's
dated evidence.

**Route progress.** `A1` is done. Still open: `A2` (image-side countable additivity), `A3` (the
two-sided comparison against an injective linear model — the high-risk gap of the general route),
`A4` (degenerate part null), `A5` (local to global), `B1` (the codimension-`m` graph area formula,
the recommended main target, 600–1000 lines over two to three rounds) and `B2` (its normalized
form). **Next is `B1`.**

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**
Sharp finite-regularity Sard, Energy's five holes and dimension-free KLS also remain open.

See [the `A1` decision](research/decisions/2026-09-16-normdet-continuity.md) and
`research/explorations/2026-09-16-normdet-continuity.json`. The final verification receipt is
identified in `build/audit/normdet-continuity/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Nonlinear area formula: route exploration (2026-09-16)

**Superseded by the `A1` round above; retained as a dated snapshot. It was a route exploration and changed none of the registration numbers above.**
**No theorem was proved and no `.lean` library source was modified.** The only new Lean file is
`research/audits/AreaFormulaRouteStatements.lean`, which contains **`#check`s only** — it declares
nothing, proves nothing and adds no placeholder axiom, exactly as
`WeightedCoareaRouteStatements.lean` did for the scalar route. Direct holes stay **8 (1/2/5)** and
certificates **24**.

**Findings.** Mathlib has **no** area formula for maps between spaces of differing dimensions, and
**no** continuity of `normDet`, so measurability of the integrand is a genuine obligation rather
than a lookup. The textbook route partitions the domain with
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, which does exist with the right shape
and even guarantees that each linear model is an actual differential.

**The obstruction is localized at the lower half of the sandwich.**
`ApproximatesLinearOn.antilipschitz` requires the linear model to be a continuous linear
**equivalence** — hence equal dimensions — so it does not apply when `finrank H < finrank V`. The
available replacement, `ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`, only
produces `∃ K, AntilipschitzWith K f` through `Classical.choose`, with none of the quantitative
control the sandwich needs. Supplying that step is obligation `A3`, estimated at 250–500 lines and
high risk.

**Recommendation: take the graph route instead.** A graph map `y ↦ ι y + κ (γ y)` is injective by
construction and its parameter projection `ιᵀ` is an **explicit** left inverse, which is precisely
what the general route lacks; its volume factor `√det (1 + Aᵀ A)` was proved last round, and it
already agrees with the repository's codimension-one `graphJacobian`. The repository proved the
codimension-**one** graph case in `Analysis/AreaFormula.lean` (957 lines, alongside
`Analysis/ImplicitGraph.lean` at 859), and that is the honest cost anchor for the codimension-`m`
analogue: obligation `B1`, 600–1000 lines, expected to take two to three rounds. The general
obligation `A3` can then be skipped, and `A4` — the degenerate part — does not arise at all,
because a graph map's differential is always injective.

**Suggested order**: `A1` (continuity and measurability of `normDet`, low risk) first, then `B1`,
then the patching obligations `A5` and `A2`, and only afterwards the codimension-`m` regular case
of the coarea formula itself.

The nine obligations `A0`–`A5`, `B1`, `B2` are stated exactly in the route statements file and
type-check under `-DwarningAsError=true`. **None of them is claimed to hold in Lean.**

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**
Sharp finite-regularity Sard, Energy's five holes and dimension-free KLS also remain open.

See [the area formula route decision](research/decisions/2026-09-16-area-formula-route.md) and
`research/explorations/2026-09-16-area-formula-route.json`. The final verification receipt is
identified in `build/audit/area-formula-route/final-snapshot.json`.
No commit or push; the real Git index is unchanged.

## Graph Jacobian in arbitrary codimension: codimension-`m` step 2, linear layer (2026-09-16)

**Superseded by the area formula route exploration above; retained as a dated snapshot. It it changes none of the registration numbers recorded above.**
`Analysis/GraphJacobian.lean` supplies the graph model the codimension-`m` coarea program needs.
**No area formula and no coarea formula are proved in this round**, and no hole was migrated:
direct holes stay **8 (1/2/5)** and certificates **24**.

What the round established first is a limitation of what was already there: the area formula proved
in `Analysis/AreaFormula.lean` is **codimension one only** — its graph is the graph of a
*real-valued* function, with linear model `graphLinear ι e a v = ι v + ⟪a, v⟫ • e` and factor
`graphJacobian a = √(1 + ‖a‖²)`. Fibres of a map into an `m`-dimensional target have codimension
`m`, so the plan of reducing a general `C¹` parametrization to the existing graph formula only
covers `m = 1`; a `K`-valued slope model had to be built first.

Proved: for a slope `A : H →L[ℝ] K` and isometric embeddings with orthogonal ranges, the Gram
operator of `y ↦ ι y + κ (A y)` is `1 + Aᵀ A` **on the parameter space**, the two isometries each
contributing the identity and the cross terms vanishing by orthogonality; hence the volume factor
in arbitrary codimension is `√det (1 + Aᵀ A)`, a determinant on the parameter space and therefore
independent of the ambient embedding. The squared form needs no square root and no positivity
argument.

The codimension-one case **agrees exactly**: `normDet (graphLinear ι e a) = graphJacobian a`. This
identifies the repository's own codimension-one Jacobian with Mathlib's general `normDet`, so the
already proved codimension-one area formula is the `m = 1` case of the general volume factor. The
proof avoids the rank-one determinant lemma: the repository's linear codimension-one area formula
and Mathlib's linear area formula describe the scaling of the same map, and the volume factor of a
linear map is unique because some set has positive finite measure.

The module's local import closure is 6 modules with **no** work-in-progress file.
`research/audits/GraphJacobianAudit.lean` has 11 standard-only axiom reports, including a flat
graph, a subsingleton target and a zero-dimensional parameter space.

**The next target is now pinned exactly.** The end of that audit file records, as a proposition
type-check and explicitly **not** a proof, the Federer area formula for an injective `C¹`
parametrization: `μH[k] (g '' s) = ∫⁻ y in s, ofReal (normDet (fderiv ℝ g y))`. That remains open.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**
Sharp finite-regularity Sard, Energy's five holes and dimension-free KLS also remain open.

See [the graph Jacobian decision](research/decisions/2026-09-16-graph-jacobian.md) and
`research/explorations/2026-09-16-graph-jacobian.json`. The final verification receipt and
exact-source comparison are identified in `build/audit/graph-jacobian/final-snapshot.json`.
All incoming Lean files, historical decisions and audit clients retain their bytes.
No commit or push; the real Git index is unchanged.

## Linear area formula and affine fibres: codimension-`m` step 1 (2026-09-16)

**Superseded by the graph Jacobian round above; retained as a dated snapshot. It it changes none of the registration numbers recorded above.**
`KLS/Geometry/LinearAreaFormula.lean` carries the **linear** area formula from Mathlib's raw `μH`
across to this repository's `KLS.hausdorffNormalized` normalization, and draws the fibre
consequence the codimension-`m` coarea formula needs. **No coarea formula and no `C¹` area formula
are proved in this round.** No hole was migrated and no certificate was added: direct holes stay
**8 (1/2/5)** and certificates **24**.

Why it is needed: Mathlib proves `μH[k] (L '' s) = normDet L * μH[k] s` for the raw Hausdorff
measure, while every measure here is the classical `ω_d (diam/2)^d` normalization. The two differ
by a dimensional constant, and the inner integral of the codimension-`m` formula has to come out
with **no residual constant**, or the whole formula acquires a spurious dimensional factor.

Proved: the normalized linear area formula, where the same constant appears on both sides and
cancels, so the norm determinant is the exact volume factor; the adjoint of a linear isometric
embedding is a left inverse, hence such an embedding has **unit** norm determinant and preserves
the normalized `k`-dimensional measure; and, combining these with the already proved translation
invariance and top-dimensional identity, that **a translated isometric slice carries exactly
Lebesgue measure on its parameter space**. Specialized to `ker L`, that is the fibre statement: the
fibres of a linear map are translates of its kernel, and measured in the kernel's dimension they
carry exactly its Lebesgue measure. For surjective `L` that dimension is `n - m`, which the audit
records separately.

The round **reuses rather than reproves**: `Analysis.hausdorffNormalized_image_add_left`,
`KLS.hausdorffNormalized_finrank_eq_volume` and Mathlib's `LinearMap.hausdorffMeasure_image` are
all taken as given. The module's local import closure is 8 modules and contains **no**
work-in-progress file. `research/audits/LinearAreaFormulaAudit.lean` has 14 standard-only axiom
reports, including a top-dimensional consistency check, a zero-dimensional parameter space, a
degenerate zero map and the codimension count.

**Next in the program**: the nonlinear local area formula — the `k`-dimensional measure of a `C¹`
parametrized image as the integral of `normDet (fderiv)`. The repository already has the `C¹`
**graph** case and the `RegularChart`/`ImplicitGraph`/`LocalInverse` charts, so the general case
should reduce to it locally. Then the codimension-`m` regular case, then the critical part and the
gluing.

**The log-concave Cheeger–Buser line belongs to 王浩丞 and is deliberately untouched here.**
Sharp finite-regularity Sard, Energy's five holes and dimension-free KLS also remain open.

See [the linear area formula decision](research/decisions/2026-09-16-linear-area-formula.md) and
`research/explorations/2026-09-16-linear-area-formula.json`. The final verification receipt and
exact-source comparison are identified in
`build/audit/linear-area-formula/final-snapshot.json`.
All incoming Lean files, historical decisions and audit clients retain their bytes.
No commit or push; the real Git index is unchanged.

## Coarea Jacobian: the codimension-`m` program opens (2026-09-16)

**Superseded by the linear area formula round above; retained as a dated snapshot. It it changes none of the registration numbers recorded above.**
`Analysis/CoareaJacobian.lean` defines `Analysis.coareaJacobian L = sqrt (det (L ∘ Lᵀ))` and proves
its basic theory. It is the **linear-algebra layer of the vector-valued (codimension-`m`) coarea
program**, and **no coarea formula is proved in this round**. No hole was migrated and no
certificate was added: direct holes stay **8 (1/2/5)** and certificates **24**.

Mathlib already carries the rectangular volume factor `LinearMap.normDet f = sqrt (det (fᵀ ∘ f))`,
together with its square, nonnegativity, singular-value product, vanishing criterion, and the fact
that it is the volume factor for Hausdorff measure. `normDet` is the **area**-formula Jacobian; the
coarea Jacobian is its adjoint counterpart, so this module defines `coareaJacobian L = normDet Lᵀ`
rather than re-deriving determinant theory. The linear-algebra layer of the program therefore did
not have to be built from scratch.

Proved here: nonnegativity; the defining identity `J² = det (L ∘ Lᵀ)`, a determinant on the
**target**, hence the `m × m` Gram determinant and not the `n × n` one; the adjoint of a real
functional sends `1` to its Riesz representative; the scalar value is the norm of that
representative; `ker Lᵀ = (range L)ᗮ`; and the regular-set characterization **`J ≠ 0` iff `L` is
surjective**, which is what the codimension-`m` formula will split on and which degenerates to a
nonzero gradient when `W = ℝ`.

The point of the round is **`coareaJacobian_fderiv`**: `coareaJacobian (fderiv ℝ u x)` is
*literally* `‖gradient u x‖`, the integrand of the proved `L11`/`L12`/`L13`. So the already
certified scalar theory is the `m = 1` case of this density, and no existing statement has to be
restated, weakened or rewritten to accommodate the vector-valued program. That compatibility is
proved, not asserted.

The module depends on **Mathlib only** — its local import closure is itself.
`research/audits/CoareaJacobianAudit.lean` has 17 standard-only axiom reports, including the
identity map, the zero map, a subsingleton target and a Euclidean projection.

**Next in the program**: the area formula for lowering dimension, then the codimension-`m` regular
case via a parametric implicit-function normal form, then the critical part and the gluing. The
scalar chain `L1`–`L13` took about ten rounds; no faster schedule is promised.

**The log-concave Cheeger–Buser line — the alignment of the isoperimetric-constant definitions
through the two-way Poincaré comparison, including the two remaining holes of
`KLS/WIP/CheegerInfimum.lean` — belongs to 王浩丞 and is deliberately untouched here.** Sharp
finite-regularity Sard, Energy's five holes and dimension-free KLS also remain open.

See [the coarea Jacobian decision](research/decisions/2026-09-16-coarea-jacobian.md) and
`research/explorations/2026-09-16-coarea-jacobian.json`. The final verification receipt and
exact-source comparison are identified in `build/audit/coarea-jacobian/final-snapshot.json`.
All incoming Lean files, historical decisions and audit clients retain their bytes.
No commit or push; the real Git index is unchanged.

## Locally Lipschitz coarea: L13 proved (2026-09-16)

**Historical L13 implementation snapshot; current registration status is recorded above.**
`KLS/Geometry/LocallyLipschitzCoarea.lean` proves `KLS.coarea_of_locallyLipschitz` (L13): the
weighted coarea equality and slice `AEMeasurable` for a **locally Lipschitz** real function, any
measurable set and any measurable `ENNReal` weight. No global Lipschitz constant, no `C¹`
regularity, and no boundedness, finite-volume, integrability, positive-dimension or `SFinite`
surface-measure hypothesis.

This is a **common generalization of L11 and L12**, which both keep their statements and proofs:
`LipschitzWith K u → LocallyLipschitz u` recovers L12, and `ContDiff ℝ 1 u → LocallyLipschitz u`
recovers L11. The generalization is **strict**, and the audit proves that rather than asserting it:
`x ↦ x² + ‖x‖` is shown to be locally Lipschitz, **not** globally Lipschitz for any constant, and
**not** differentiable at `0`, so neither earlier theorem reaches it, while L13 does.

The proof reduces to L12 on half-open annuli. A finite-dimensional space is proper, so `u` is
Lipschitz on each closed ball and McShane extension replaces it there by a globally Lipschitz
`v k`. Each piece `S ∩ (ball 0 (k+1) \ ball 0 k)` sits inside the **open** ball, where `u` and
`v k` agree on a neighbourhood of every point, so the gradients agree pointwise and the level sets
cut each piece identically — the equality is not inferred from agreement on a sparse set. Countable
additivity assembles both conclusions; the total slice measurability comes from the same countable
decomposition, since an unbounded `S` carries no global `LipschitzOnWith` bound and L5 does not
apply directly.

**No hole was migrated**, so direct holes stay **8 (1/2/5)**, certificates **24**, perimeter
infrastructure **missing**. The audit client imports no work-in-progress file and its 10 axiom
reports are standard-only.

**The log-concave Cheeger–Buser line — the alignment of the isoperimetric-constant definitions
through the two-way Poincaré comparison, including the two remaining holes of
`KLS/WIP/CheegerInfimum.lean` — was handed to 王浩丞 on 2026-09-16 and is deliberately untouched
here.** Sharp finite-regularity Sard, Energy's five holes and dimension-free KLS also remain open.

See [the L13 decision](research/decisions/2026-09-16-locally-lipschitz-coarea.md) and
`research/explorations/2026-09-16-locally-lipschitz-coarea.json`. The final verification receipt and
exact-source comparison are identified in
`build/audit/locally-lipschitz-coarea/final-snapshot.json`.
All incoming Lean files, historical decisions and audit clients retain their bytes.
No commit or push; the real Git index is unchanged.

## Original `T2` entry point migrated: the last coarea hole is closed (2026-09-16)

**Superseded by the L13 round above; retained as a dated snapshot.**
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` has left
`KLS/WIP/AnalyticPrerequisites.lean`, where it was a direct hole, for the end of the hole-free
`KLS/Geometry/LipschitzCoarea.lean`, beside the `L12` theorem `KLS.coarea_of_lipschitz` that
proves it at `S = Set.univ`. **No new theorem was proved this round**: this is a migration and a
rewiring, not a new proof, and the coarea theorem was not reproved.

The migration is signature-preserving, and that was checked by machine twice, not by eye and not
by a `defeq` claim. The `pp.all` type printed before the move from an environment importing the
work-in-progress file and after it from an environment importing the new module is byte-identical
(SHA256 `9e2121c254f66ed331b0f8fbb6b7ca7955f277f3f66705d7ed21a6ff490786a9`). Because `#check @`
renames universes, a second probe reads the stored `ConstantInfo` directly: the universe parameter
is `u` on both sides, the twelve binder names and binder kinds agree, and the type hashes are
equal; the only difference is the module tag inside the inaccessible anonymous instance binders,
which is by construction the enclosing module name. So the universe, the six instance arguments in
their original order — `CompleteSpace V` included, which is what the statement's `gradient`
actually elaborates against — the implicit binders `u`, `K`, `g`, the hypothesis names `hu`, `hg`,
the `LipschitzWith` hypothesis, the `KLS.surfaceMeasure` normalization and the unrestricted
`ℝ≥0∞` weight range are unchanged. No `C¹`, positive-dimension, finite-volume, integrability or
`SFinite` hypothesis was added, and no compatibility alias was introduced.

Direct source holes drop to **8 (1/2/5)**: `KLS/WIP/AnalyticPrerequisites.lean` keeps only the
sharp `C^(finrank)` `Analysis.sard`, whose statement and proof, and those of
`Analysis.ae_forall_fderiv_ne_zero`, are unchanged. Certificates stay **24**, perimeter
infrastructure stays **missing**. With `T1` and `T3` already migrated in earlier rounds, all three
original coarea targets are now formally wired to hole-free modules.

`research/audits/LipschitzCoareaMigrationAudit.lean` imports the new module and both
work-in-progress files, so its sixteen reports come from one environment: twelve are standard-only
(the migrated declaration, `KLS.coarea_of_lipschitz`, the two previously migrated neighbours, and
eight clients including a verbatim restatement discharged through named arguments, the original
`T2` proposition text, a function not differentiable at zero, an identically infinite weight and a
zero-dimensional space), while `Analysis.sard`, `Analysis.ae_forall_fderiv_ne_zero` and the two
Cheeger comparisons still report `sorryAx`. The two existing consumers,
`research/audits/LevelSetMeasurableAudit.lean` and `research/audits/IsoperimetryCoareaAudit.lean`,
gained the new import and lost `sorryAx` on exactly their two coarea reports each; their client
statements were not altered.

**Sharp finite-regularity Sard, both Cheeger comparisons, Energy's five holes and dimension-free
KLS remain open.** See [the T2 migration decision](research/decisions/2026-09-16-t2-coarea-migration.md)
and `research/explorations/2026-09-16-t2-coarea-migration.json`. The final full verification
receipt and exact-source comparison are identified in `build/audit/t2-migration/final-snapshot.json`.
All incoming Lean files, historical decisions and audit clients retain their bytes.
No commit or push; the real Git index is unchanged.

## Lipschitz coarea: L6a, L7 and L12 proved (2026-09-16)

**Superseded by the T2 migration round above; retained as a dated snapshot.**
`Analysis/LipschitzJet.lean` proves L6a: compact jets covering almost every point of a Lipschitz
function, retaining differentiability, continuity of the ambient derivative and a uniform
first-order remainder. The proof works for any additive Haar measure on a finite-dimensional
real normed space. `Analysis/LipschitzC1Pieces.lean` combines these jets with L6 and disjointifies
them to prove L7, preserving both values and ambient derivatives on each measurable piece.

`KLS/Geometry/LipschitzCoarea.lean` proves `KLS.coarea_of_lipschitz` (L12): weighted coarea and
slice AEMeasurable for a globally Lipschitz real function, any measurable set and any measurable
ENNReal weight. No C¹, positive-dimension, boundedness, finite-volume, integrability or SFinite
surface-measure hypothesis is added. L11 handles the C¹ pieces, L2 removes the remaining null
slices, and countable additivity joins them. The new strict client proves the original L6a/L7/L12
and T2 propositions with byte-identical statement text and 15 standard-only axiom reports.
It includes a function not differentiable at zero, an infinite weight and a zero-dimensional case.

**Next: migrate the original T2 entry point**, preserving its machine-printed `pp.all` signature.
The mathematical Lipschitz coarea theorem and the original T2 proposition are proved, but the old
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` declaration in
`KLS/WIP/AnalyticPrerequisites.lean` is unchanged and still contains `sorry`. Thus source holes
remain **9 (2/2/5)** until that separate integration; certificates **24**, perimeter infrastructure
**missing**. Sharp finite-regularity Sard, both Cheeger comparisons, Energy's five holes and
dimension-free KLS remain open.

See [the L12 decision](research/decisions/2026-09-16-lipschitz-coarea.md) and
`research/explorations/2026-09-16-lipschitz-coarea.json`. The final full verification receipt and
exact-source comparison are identified in `build/audit/lipschitz-coarea/final-snapshot.json`.
All incoming Lean files, historical decisions and audit clients retain their bytes.
No commit or push; the real Git index is unchanged.

## Whitney extension: L6 proved (2026-09-16)

**Superseded by the L6a/L7/L12 round above; retained as a dated snapshot.**
`Analysis/WhitneyConstruction.lean` proves `WhitneyJet.exists_contDiff_extension`: every compact
first-order real-valued jet in a finite-dimensional real inner-product space, with continuous
derivative data and the original uniform remainder condition, has a global C¹ extension with
exact values and ambient derivatives on the set. Empty sets, zero dimension and sparse sets are
included. This completes the original L6 compact-set statement; the arbitrary noncompact
closed-set version is not asserted.

The construction uses the new `WhitneyCover`, `WhitneyBump` and `WhitneyPartition` modules:
a capped-distance Vitali cover, local overlap at most `81^finrank`, smooth nonnegative weights
summing to one, and derivative bounds proportional to inverse radius. Nearest-point affine jets
then satisfy both uniform estimates required by the previously proved boundary gluing theorem.
`research/audits/WhitneyConstructionAudit.lean` proves the original L6 proposition with all its
instances and hypotheses retained. Its 13 axiom reports contain only the three standard axioms.
The source/client checks and preservation audit are in
`research/explorations/2026-09-16-whitney-extension.json`; the final exact-source verification
receipt is identified by `build/audit/whitney-extension/final-snapshot.json`.

**Next: L6a, compact jet extraction for Lipschitz functions**, retaining differentiability,
continuous derivative data and a uniform remainder on each compact piece. Then use L6 to prove
L7's exact C¹ pieces, before L12. See
[the extension decision](research/decisions/2026-09-16-whitney-extension.md).
L6a/L7/L12 and Lipschitz coarea remain open. Direct holes **9 (2/2/5)**, certificates **24**,
perimeter infrastructure **missing**; sharp finite-regularity Sard, both Cheeger comparisons,
and dimension-free KLS remain open. All incoming Lean files and historical decisions retain their
bytes. No commit or push; the real Git index is unchanged.

## Whitney boundary gluing: L6 started (2026-09-16)

**Superseded by the full L6 extension round above; retained as a dated snapshot.**
The new `Analysis/WhitneyExtension.lean` proves the **boundary gluing step**, not L6's existence
claim. `WhitneyJet.exists_contDiff_of_compl_approx` takes a C¹ candidate on the complement of a
compact set, with uniformly small value and derivative errors relative to nearest-point affine
jets, and constructs a globally C¹ extension with the exact prescribed values and derivatives.
The candidate need not be continuous or agree with the data on the compact set. The boundary
proof works in any real normed space; it does not require finite dimension or interior points.

**Next: construct the controlled candidate on `Sᶜ`.** The precise remaining proposition is
`#check`ed (not proved) in `research/audits/WhitneyExtensionAudit.lean`. Implement a Whitney
cover and smooth partition with support radii comparable to distance from `S`, bounded overlap,
and derivative bounds; combine the affine jets and prove both estimates consumed by the new
reduction. A qualitative partition of unity alone does not supply these quantitative bounds.
See [the boundary decision](research/decisions/2026-09-16-whitney-boundary.md) for the exact target
and the value/derivative cancellation argument. Do not replace this task with an interior bump
extension or assert equality of ambient derivatives from equality on a sparse set.

The new strict client covers empty sets, arbitrary nonzero derivatives on a singleton,
a zero-dimensional domain, and a candidate whose value on the set must be discarded. Thirteen
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The original FirstOrderJet
module/client, all prior Lean sources and all prior decisions retain their bytes.
A was closed first with receipt `20260915T170113.583163Z`: 10 gates, 190 replayed modules,
475 entries, snapshot `051483acb993b037ccccd2682cb0c735a9d373ce20cc399defc54a384b10fa09`.
The separate final B receipt and exact-source comparison are recorded in
`build/audit/whitney-boundary/final-snapshot.json`; source/check evidence is in
`research/explorations/2026-09-16-whitney-boundary.json`.

**L6/L6a/L7/L12 and Lipschitz coarea remain open.** Direct holes **9 (2/2/5)**, certificates
**24**, perimeter infrastructure **missing**. Sharp finite-regularity Sard, both Cheeger
comparisons, and dimension-free KLS remain open. No commit or push; the real Git index is unchanged.

## First-order jet necessity closeout (2026-09-16)

**Superseded by the Whitney boundary gluing round above; retained as a dated snapshot.**
`Analysis.uniform_jet_remainder_of_contDiff` in `Analysis/FirstOrderJet.lean` proves that a
globally C¹ realization on a compact set satisfies L6's uniform first-order remainder estimate.
This is the **necessity direction only**: L6's extension existence, L6a, L7 and Lipschitz
coarea remain open. The four strict axiom reports in `research/audits/FirstOrderJetAudit.lean`
use only the standard axioms. Direct WIP holes stay **9 (2/2/5)**, certificates **24**, and
perimeter infrastructure **missing**. The next proof target is the original compact-set jet
extension L6, with exact values and derivatives and no extra interior assumption.

The incoming migration receipt `20260915T164547.132773Z` covers 471 entries; the starting
workspace has 473 entries and SHA256 `2e0e01c666cbbec14f684c0ded0d5e6130719c95fbf106c895c0dc399cc908ad`.
Their only differences are the FirstOrderJet module and client. This expected mismatch is closed
by the new source-bound verification, not by rewriting the migration's historical evidence.
See `research/decisions/2026-09-16-first-order-jet.md` and
`research/explorations/2026-09-16-first-order-jet.json`; the exact closeout receipt is recorded in
`build/audit/first-order-jet/final-snapshot.json`. All existing work is retained; no commit or push.

## Isoperimetry coarea migration round (2026-09-16)

**Superseded by the First-order jet necessity closeout above; retained as a dated snapshot.**
This round **closes the second original coarea hole**. The direct hole
`KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` moved out of
`KLS/WIP/CheegerInfimum.lean` into the hole-free `KLS/Geometry/IsoperimetryCoarea.lean` with a
**byte-identical `pp.all` signature** and is now proved from last round's `L11`
(`KLS.coarea_of_contDiff` at `S = univ`). Direct holes drop **10 (2/3/5) → 9 (2/2/5)**;
`KLS/WIP/CheegerInfimum.lean` is down to its two Cheeger comparisons. Certificates stay **24**,
perimeter infrastructure **missing**.

Byte-identity is machine-checked: the `pp.all` type was printed before the move in an environment
importing the WIP file and after the move in one importing the new module, and the two logs `diff`
empty (`build/audit/iso-signature-before.log`, `iso-signature-after.log`). The same universe, the
same **seven** instance arguments in the same order — including the `CompleteSpace V` and
`SecondCountableTopology V` the proof does not use — the same binders and hypothesis names, and the
same conclusion. The unused section variables and the unused hypothesis name `hK` are kept and the
two linters silenced, rather than the signature being narrowed by `omit` or `hK` renamed to `_`.
The `LipschitzWith` hypothesis is never used: the declaration already assumes `ContDiff ℝ 1 u`.
The WIP file lost exactly that one declaration, plus the now-empty `section Coarea` scaffolding it
left behind; every other declaration there is unchanged in statement, proof and position, and the
original is kept at `build/audit/iso-migration-CheegerInfimum.before.lean`.

**This round proves no new theorem** and does **not** close the Lipschitz coarea formula.
`research/audits/IsoperimetryCoareaAudit.lean` imports the new module **and both** WIP files, so its
eight `#print axioms` reports come from one environment: the migrated result reports only `propext`,
`Classical.choice` and `Quot.sound`, while `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
(the **Lipschitz** formula, assuming no `C¹` regularity — the migrated result is its `C¹`
specialization and does not imply it), the sharp `Analysis.sard`, both Cheeger comparisons and the
Cheeger equality all still report `sorryAx`. A client theorem restating the Lipschitz formula
compiles **with** `sorryAx`.

Eighteen earlier strict clients re-pass unedited, the three WIP files actually recompile with
**2/2/5** direct holes, and default `lake build` and root `research/verify.py` pass; the final
source-bound receipt is `build/verification/latest.json`, with the final equality check in
`build/audit/iso-migration-final-snapshot.json`. No commit, no push. See
[the migration decision](research/decisions/2026-09-16-isoperimetry-coarea-migration.md) and
`research/explorations/2026-09-16-isoperimetry-coarea-migration.json`.

Still unproved: the **Lipschitz** coarea formula, which needs `L12`, hence `L7` and the closed-set
Whitney jet extension `L6`/`L6a`; sharp `C^(finrank)` `Analysis.sard` (no downstream consumer);
sharpness of the Eilenberg constant; both Cheeger comparisons; and equality of the two Cheeger
constants. No certificate or Blueprint leanok scope was expanded.

## Smooth coarea round (2026-09-16)

**Superseded by the Isoperimetry coarea migration round above; retained as a dated snapshot.**
This round **proves obligation `L11`**: the weighted coarea formula for **any** `C¹` real function
on a finite-dimensional inner-product space, over any measurable set and any measurable `ℝ≥0∞`
weight, together with almost everywhere measurability of the weighted slices
(`KLS.coarea_of_contDiff` in the new `KLS/Geometry/SmoothCoarea.lean`). Only the unused
`[CompleteSpace V]` is dropped; `u` is **not** assumed Lipschitz, bounded or proper, `S` need not
be bounded or of finite volume, `g` may be unbounded, non-integrable or identically `∞`, and **no
nondegeneracy of the derivative is assumed** — the critical set may be the whole space.

`L9` and `L10` meet exactly here and neither suffices alone. The critical set is closed, so its
complement is open and `L9` gives the identity on `S ∩ R`; on the left the critical part
contributes nothing because the gradient vanishes there; on the right `L10` makes the critical
slice null at almost every level, so the two slice integrals agree almost everywhere, and that
same equality transports `L9`'s `AEMeasurable` component to the full slice function.

**Target `T3` follows**, and it is verbatim the statement of the direct hole
`KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` in
`KLS/WIP/CheegerInfimum.lean`: that declaration already assumes `ContDiff ℝ 1 u`, so `L11` at
`S = univ` discharges it and its `LipschitzWith` hypothesis is never used.
**No WIP file was touched**, so the declaration still carries `sorry` and direct holes stay
**2/3/5**, total **10**; migrating it out would take `KLS/WIP/CheegerInfimum.lean` from 3 holes to
2 and the total to **9**, which by repository convention is a separate decision.

`research/audits/SmoothCoareaAudit.lean` (placed directly in the versioned audit path) compiles
strictly: the route's `L11` text `#check` and eleven theorems — `target`,
`target_of_not_completeSpace`, `target_T3`, `wip_isoperimetry_statement` (both discharged through
named arguments), an identically-`∞` weight, the empty set, an everywhere-critical constant
function, `constant_function` checking the `⊤ · 0` boundary **independently of `L11`**, and two
`preserved_*` signature checks — plus 12 `#print axioms` lines that all report only `propext`,
`Classical.choice` and `Quot.sound`. Sixteen earlier strict clients re-pass unedited, and the three
WIP files actually recompile with **2/3/5** direct holes. Default `lake build` and root
`research/verify.py` pass; the final source-bound receipt is `build/verification/latest.json`, with
the final equality check in `build/audit/smoothcoarea-final-snapshot.json`. Certificates stay
**24**, perimeter infrastructure **missing**. No commit, no push. See
[the smooth-coarea decision](research/decisions/2026-09-16-smooth-coarea.md) and
`research/explorations/2026-09-16-smooth-coarea.json`.

Still unproved: the **Lipschitz** coarea formula
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`, which assumes no `C¹` regularity and
needs `L12`, hence the exact `C¹` decomposition `L7` and the closed-set Whitney jet extension
`L6`/`L6a` — none of which is proved; sharp `C^(finrank)` `Analysis.sard` (no downstream
consumer); sharpness of the Eilenberg constant; `smoothConstant_le_minkowskiConstant`;
`smoothConstant_mul_lintegral_min_superlevel_le`; and equality of the two Cheeger constants. No
certificate or Blueprint leanok scope was expanded.

## Regular open-domain coarea round (2026-09-15)

**Superseded by the smooth coarea round above; retained as a dated snapshot.**
**L9 is proved in full**, including weighted-slice `AEMeasurable`, as
`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero` in `KLS/Geometry/RegularCoarea.lean`.
The hypotheses are exactly the requested open-domain C¹ regularity, Borel `S ⊆ O`, and measurable
ENNReal weight. No global regularity, boundedness, integrability, finite measure, nonzero-dimension,
or SFinite hypothesis is added; the client restates the complete target including `CompleteSpace`.

The joint C¹ inverse keeps the level parameter. Orthogonal volume splitting (already proved via
`WithLp 2`) and Mathlib's one-dimensional specialization of the same-dimensional Jacobian theorem
provide a fiberwise substitution, followed by Tonelli. The proved identity
`|∂t ψ| * ‖∇u‖ = sqrt(1 + ‖∇y ψ‖²)` matches the weighted graph-area formula by multiplication
only, so infinite weights and measures remain in scope. Interior C¹ representatives on smaller
balls and countably many disjoint Borel pieces remove all outside-domain regularity. Slice
measurability is proved independently by localizing L5 in `OpenSliceMeasurable.lean`.
`Analysis/LocalInverse.lean` and `Analysis/FiberIntegral.lean` depend only on Mathlib;
`Analysis/RegularChart.lean` supplies the joint chart and differential identity.

Five new modules and `RegularCoareaAudit` compile with `-DwarningAsError=true`. All 29 new/client
axiom reports use only the standard three axioms. Clients cover infinite weight, the empty set,
zero dimension, actual infinite-volume integrals, infinite surface slices at every level, and a
function discontinuous outside its C¹ domain. All 15 previous clients re-pass unedited; the three
WIP files actually compile with **2/3/5** direct holes, total **10**. Existing Lean files and
historical decisions are unchanged. The final acceptance receipt is `build/verification/latest.json`,
with source/evidence equality attested in `build/audit/l9-final-snapshot.json`.

**Still unproved:** L11, L12, L6/L6a/L7 (Whitney extension and exact pieces), both original weighted
coarea equality holes, sharp `C^(finrank)` `Analysis.sard` (no downstream consumer), Eilenberg
constant sharpness, `smoothConstant_le_minkowskiConstant`,
`smoothConstant_mul_lintegral_min_superlevel_le`, and equality of the two Cheeger constants.
L10 was not used. Certificates stay **24**, perimeter infrastructure **missing**, and no Blueprint
leanok scope was expanded. No commit/push; HEAD remains `2965b32`.
See [the L9 decision](research/decisions/2026-09-15-regular-coarea.md) and `research/explorations/2026-09-15-regular-coarea.json`.

## Open-domain graph area round (2026-09-15)

**Superseded by the regular open-domain coarea round above; retained as a dated snapshot.**
This round **proves obligation `L8`**: the weighted graph-area change of variables, previously
available only for a graph function that is `C¹` on the whole parameter space, now holds for one
that is `C¹` on an **open set** `O`, over any measurable `S ⊆ O`
(`Analysis.setLIntegral_image_graphMap_of_contDiffOn` in the new
`Analysis/OpenGraphIntegral.lean`). The route's statement is matched exactly; the weight may be
unbounded, non-integrable or identically `∞`, `S` need not be bounded or of finite measure, `v` has
no regularity outside `O`, and `O = ∅`, `S = ∅` are covered.

A `ContDiffOn` function on an open set generally does **not** extend to a globally `C¹` function —
`x ↦ x⁻¹` on `(0, ∞)` is the standard counterexample, and the client applies `L8` to exactly that
instance, which the pre-existing global theorem cannot reach. So the localization is genuinely
countable: `exists_contDiff_one_eqOn_ball` gives, around each point of `O`, a ball on which some
globally `C¹` function agrees with `v` (multiply by a `ContDiffBump` supported in `O`; smoothness
is local). Second countability extracts a countable subfamily of such balls covering `O`,
`disjointed` makes countably many pairwise disjoint measurable pieces of `S`, `graphMap` is
injective so the images are disjoint and measurable, both sides are countably additive over the
pieces, and the gradients agree because the functions agree on an **open** ball. This is the
**interior** localization the route prescribes; it is **not** the Whitney extension from a closed
set, which is the separate unproved obligation `L6`. `Analysis/SmoothSard.lean`'s `C^∞` analogue
`exists_contDiff_eventuallyEq` is deliberately left untouched, since generalizing it would change a
published signature.

`build/audit/OpenGraphAudit.lean` compiles strictly: the route's `L8` text `#check` and six
theorems — `target`, `global_case` (recovering the pre-existing global theorem at `O = univ`, so
`L8` is a genuine generalization), an identically-`∞` weight, the empty parameter set, the `x⁻¹`
instance, and a `preserved_*` named-argument signature check — plus 9 `#print axioms` lines that
all report only `propext`, `Classical.choice` and `Quot.sound`. Fourteen earlier strict clients
re-pass unedited, and the three WIP files actually recompile with **2/3/5** direct holes, total
**10** — unchanged, since `L8` fills no hole. Default `lake build` and root `research/verify.py`
pass; the final source-bound receipt is `build/verification/latest.json`, with the final equality
check in `build/audit/opengraph-final-snapshot.json`. Certificates stay **24**, perimeter
infrastructure **missing**. The incoming passed receipt `20260915T040555.802878Z` matched all 427
snapshot entries. HEAD stays `2965b32`; no commit/push. See
[the open-graph decision](research/decisions/2026-09-15-open-graph-area.md) and
`research/explorations/2026-09-15-open-graph-area.json`.

`L8` gives the area of a **graph**, not a coarea formula. Still unproved: `L9` (regular-part `C¹`
coarea, which additionally needs the `t`-**parametrized** `C¹` implicit function family, the
same-dimensional Jacobian change of variables and the cancellation
`|det DΦ| = |Du(e)|`, `√(1 + ‖D_yψ‖²) = ‖∇u‖ / |Du(e)|`), `L11`, `L12`, the weighted coarea
**equality** and its `C¹` specialization, `L6`/`L6a`/`L7`, sharp `C^(finrank)` `Analysis.sard` (no
downstream consumer), sharpness of the Eilenberg constant,
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and
equality of the two Cheeger constants. No certificate or Blueprint leanok scope was expanded.

## Critical-slice round (2026-09-15)

**Superseded by the open-domain graph area round above; retained as a dated snapshot.**
This round **proves obligation `L10`**: for a `C¹` real function on a finite-dimensional
inner-product space, almost every level meets the critical set `{x | fderiv ℝ u x = 0}` in a set of
zero `surfaceMeasure` (`KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero` in the new
`KLS/Geometry/CriticalSlice.lean`). Only the unused `[CompleteSpace V]` is dropped; `u` is **not**
assumed Lipschitz, bounded or proper, the critical set needs no measurability hypothesis (it is
closed), and `V` may be zero-dimensional.

**This is not Sard's theorem and does not imply it.** Sard concerns the Lebesgue measure of the set
of critical *values*, needs `C^(finrank)` regularity in general, and is still the unproved direct
hole `Analysis.sard`. `L10` concerns the codimension-one measure of the critical *part of each
slice*, for merely `C¹` functions. The client makes the difference concrete: for a constant function
the critical set is everything, so the slice at the attained value is the whole line and has
**nonzero** surface measure — "almost every level" cannot be strengthened to "every level".

`L10` is the first genuine consumer of the Eilenberg bound `L1`. On the critical set the derivative
vanishes, and the approximating linear maps of Mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` are *values of the derivative*, so
they are all zero and its approximation becomes a genuine `ε`-Lipschitz estimate on countably many
**pairwise disjoint measurable** pieces. Applying `L1` on each piece inside a ball of radius `R`
and summing gives a measurable majorant of integral at most
`eilenbergConstant V * ε * volume (closedBall 0 R)`; the pointwise infimum over `ε = (k + 1)⁻¹` has
integral zero, and a countable union over the radii removes the ball. Localizing to a ball is
essential — the bound is only useful where the ambient volume is finite.

`build/audit/CriticalSliceAudit.lean` compiles strictly: the route's `L10` text `#check` and seven
theorems — `target`, `target_of_not_completeSpace`, `ae_slice_eq_regular` (the form `L11` will
consume: almost every slice may be computed after discarding the critical set), the singleton
computation, `constant_exceptional_level`, a `C¹` non-Lipschitz application, and a `preserved_*`
named-argument signature check — plus 11 `#print axioms` lines that all report only `propext`,
`Classical.choice` and `Quot.sound`. Thirteen earlier strict clients re-pass unedited, and the
three WIP files actually recompile with **2/3/5** direct holes, total **10** — unchanged, since
`L10` fills no hole. Default `lake build` and root `research/verify.py` pass; the final
source-bound receipt is `build/verification/latest.json`, with the final equality check in
`build/audit/critical-final-snapshot.json`. Certificates stay **24**, perimeter infrastructure
**missing**. The incoming passed receipt `20260915T035117.865459Z` matched all 424 snapshot
entries. HEAD stays `2965b32`; no commit/push. See
[the critical-slice decision](research/decisions/2026-09-15-critical-slice.md) and
`research/explorations/2026-09-15-critical-slice.json`.

Still unproved: `L8` (weighted graph area on an open domain), `L9` (regular-part `C¹` coarea),
`L11`, `L12`, the weighted coarea **equality** and its `C¹` specialization, sharp `C^(finrank)`
`Analysis.sard` (no downstream consumer), sharpness of the Eilenberg constant,
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and
equality of the two Cheeger constants. No certificate or Blueprint leanok scope was expanded.

## Level-set measurability migration round (2026-09-15)

**Superseded by the critical-slice round above; retained as a dated snapshot.**
This round **closes the first original coarea hole**. The direct hole
`Analysis.aemeasurable_lintegral_levelSet` moved out of `KLS/WIP/AnalyticPrerequisites.lean` into
the hole-free `KLS/Geometry/LevelSetMeasurable.lean` with a **byte-identical `pp.all` signature**
and is now proved from last round's `L5` (`KLS.aemeasurable_setLIntegral_inter_levelSet` at
`S = univ`). Direct holes drop **11 (3/3/5) → 10 (2/3/5)** — the first hole-count reduction of
this sequence. Certificates stay **24**, perimeter infrastructure **missing**.

Byte-identity is machine-checked, not asserted: the `pp.all` type was printed before the move in an
environment importing the WIP file and after the move in one importing the new module, and the two
logs `diff` empty (`build/audit/migration-signature-before.log`,
`migration-signature-after.log`). The same universe, the same six instance arguments in the same
order — including the `CompleteSpace V` the proof does not use — the same binders and hypothesis
names, and the same conclusion. The unused section variables are kept and the linter silenced with
`set_option linter.unusedSectionVars false in`, the way the 2026-09-15 superlevel rewire did it,
rather than narrowing the signature with `omit`. The WIP file lost exactly that one declaration;
every other declaration there is unchanged in statement, proof and position.

**This round proves no new theorem** — it is a migration and rewiring only, and it does **not**
close the weighted coarea formula. `build/audit/LevelSetMeasurableAudit.lean` imports **both** the
new module and the WIP file, so its six `#print axioms` reports come from one environment in which
the migrated name resolves to a single declaration: the migrated result reports only `propext`,
`Classical.choice` and `Quot.sound`, while `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
(the **equality**), the sharp `C^(finrank)` `Analysis.sard` and `Analysis.ae_forall_fderiv_ne_zero`
all still report `sorryAx`. A client theorem restating the equality compiles **with** `sorryAx`,
which is the point: restating is not proving.

Twelve earlier strict clients re-pass unedited, the three WIP files actually recompile with
**2/3/5** direct holes, and default `lake build` and root `research/verify.py` pass; the final
source-bound receipt is `build/verification/latest.json`, with the final equality check in
`build/audit/migration-final-snapshot.json`. The incoming passed receipt
`20260915T033803.710026Z` matched all 421 snapshot entries. HEAD stays `2965b32`; no commit/push.
See [the migration decision](research/decisions/2026-09-15-levelset-measurable-migration.md) and
`research/explorations/2026-09-15-levelset-measurable-migration.json`.

Still unproved: the weighted coarea **equality** (`L6`–`L12`, targets `T2`/`T3`, including the
Whitney `C¹` extension), the remaining two original coarea holes, sharpness of the Eilenberg
constant, sharp `C^(finrank)` `Analysis.sard` (no downstream consumer),
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and
equality of the two Cheeger constants. No certificate or Blueprint leanok scope was expanded.

## Borel-slice and measurable-weight round (2026-09-15)

**Superseded by the level-set measurability migration round above; retained as a dated snapshot.**
This round **proves obligations `L4` and `L5`** of the weighted coarea route, and with them the
full statement of the first original target **`T1`** — which is verbatim the statement of the
direct hole `Analysis.aemeasurable_lintegral_levelSet`. **No WIP file was touched**: migrating that
declaration out of `KLS/WIP/AnalyticPrerequisites.lean` is a separate decision, so the direct-hole
count is unchanged at **11** (3/3/5) and that hole is still a hole. What is established is that its
statement is now provable from hole-free modules.

`KLS.aemeasurable_surfaceMeasure_inter_levelSet` (`L4`) and
`KLS.aemeasurable_setLIntegral_inter_levelSet` (`L5`) are added to
`KLS/Geometry/SurfaceSlicing.lean`; no new module, and no other Lean file changed. `L4` combines
all three earlier results and needs each: inner regularity
(`exists_isCompact_seq_volume_sdiff_eq_zero`, new here) splits a measurable `S` into an increasing
sequence of compact pieces plus a Lebesgue-null remainder, `L3` makes each compact slice
measurable, continuity from below turns the supremum into the slice measure of the union, and `L2`
kills the remainder for almost every level. `L5` follows by simple-function approximation: each
simple weight turns the slice integral into a **finite sum** of slice measures of the measurable
sets `S ∩ s ⁻¹' {c}`. No parametric-integral theorem is used, so the inner measure is never
assumed `SFinite` — which it is not in positive dimension.

Both drop the recorded `[CompleteSpace V]` and weaken global `LipschitzWith K u` to `Continuous u`
plus Lipschitz **on `S` only**; `S` need not be bounded, nonempty or of finite volume, and `g` may
be unbounded, non-integrable or identically `∞`. `L4` and `L5` give measurability only: **no
equality**, so the weighted coarea identity itself (targets `T2`/`T3`, obligations `L6`–`L12`) is
untouched.

`build/audit/BorelSliceAudit.lean` compiles strictly: three statement `#check`s (the route's `L4`,
`L5` and `T1` texts) and twelve theorems — `target_L4`, `target_L5`, `target_T1`, two
weakened-hypothesis versions, `eilenberg_borel` packaging `L1` with `L4`, `weighted_one`,
an infinite-volume unbounded set, an identically-`∞` weight, and three `preserved_*`
named-argument signature checks — plus 15 `#print axioms` lines that all report only `propext`,
`Classical.choice` and `Quot.sound`. Eleven earlier strict clients re-pass unedited, their own
`preserved_*` theorems re-confirming the previous rounds' statements, and the three WIP files
actually recompile with **3/3/5** direct holes, total **11**. Default `lake build` and root
`research/verify.py` pass; the final source-bound receipt is `build/verification/latest.json`,
with the final equality check in `build/audit/borelslice-final-snapshot.json`. Certificates stay
**24**, perimeter infrastructure **missing**. The incoming passed receipt
`20260915T024959.891644Z` matched all 419 snapshot entries. HEAD stays `2965b32`; no commit/push.
See [the Borel-slice decision](research/decisions/2026-09-15-borel-slice-measurable.md) and
`research/explorations/2026-09-15-borel-slice-measurable.json`.

Still unproved: the weighted coarea **equality** itself (`L6`–`L12`, targets `T2`/`T3`, including
the Whitney `C¹` extension), both remaining original coarea holes, sharpness of the Eilenberg
constant, sharp `C^(finrank)` `Analysis.sard` (no downstream consumer),
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and
equality of the two Cheeger constants. No certificate or Blueprint leanok scope was expanded.

## Compact-slice measurability round (2026-09-15)

**Superseded by the Borel-slice and measurable-weight round above; retained as a dated snapshot.**
This round **proves obligation `L3`** of the weighted coarea route: for `S` **compact** and `u`
merely continuous, `t ↦ surfaceMeasure V (S ∩ {u = t})` is Borel measurable
(`KLS.measurable_surfaceMeasure_inter_levelSet` in `KLS/Geometry/SurfaceSlicing.lean`, over the
Mathlib-only `Analysis.measurable_hausdorffMeasure_inter_levelSet` in the new
`Analysis/HausdorffContent.lean`). `L3` is **not** a consequence of `L1`: the majorant bound says
nothing about the slice function's own measurability. Both `[CompleteSpace V]` and
`[FiniteDimensional ℝ V]` of the recorded `L3` are dropped as unused — `surfaceMeasure` only reads
`Module.finrank` — and no Lipschitz, boundedness or finiteness hypothesis is added.

The new module names Mathlib's scalewise cover cost (`coverCost`) and adds the variant restricted
to **open** covers (`openCoverCost`). Two facts carry the proof. At a fixed scale the open-cover
cost of the slices is upper semicontinuous in the level, because an open cover of one slice still
covers all nearby slices: the compact remainder `S \ U` keeps `u` at a positive distance from the
level (`isOpen_setOf_slice_subset`). And the open-cover costs have the same scale limit,
`⨆ n, openCoverCost d (n+1)⁻¹ A = μH[d] A`, proved by thickening a near-optimal cover with
summably small radii (`Metric.ediam_thickening_le`, `ENNReal.exists_pos_sum_of_countable`). At a
**fixed** scale `openCoverCost` is generally strictly larger than `coverCost`, so the equality
genuinely needs the scale limit; **no upper semicontinuity of `μH[d]` itself is claimed**, which
would be false.

`build/audit/CompactSliceAudit.lean` compiles strictly: the route's `L3` text `#check` and eleven
theorems — `target` restating it verbatim, `target_of_not_finiteDimensional`, `eilenberg_compact`
packaging `L1` with `L3` into the measurable-integrand Eilenberg bound that `L4`/`L5` will consume,
a measurability consumer, a continuous **non-Lipschitz** application, three computations on the
unit interval of the line showing `∫⁻ t, surfaceMeasure ℝ (Icc 0 1 ∩ {id = t}) = 1` against the
Eilenberg bound `2`, and two `preserved_*` named-argument signature checks — plus 29
`#print axioms` lines that all report only `propext`, `Classical.choice` and `Quot.sound`. Ten
earlier strict clients re-pass unedited (the Eilenberg client's four `preserved_*` theorems
re-confirm the two previous rounds' statements through named arguments), and the three WIP files
actually recompile with **3/3/5** direct holes, total **11** — unchanged, because `L3` fills none
of the original coarea holes. Default `lake build` and root `research/verify.py` pass; the final
source-bound receipt is `build/verification/latest.json`, with the final equality check in
`build/audit/compactslice-final-snapshot.json`. Certificates stay **24**, perimeter infrastructure
**missing**. The incoming passed receipt `20260914T213846.405397Z` matched all 416 snapshot
entries. HEAD stays `2965b32`; no commit/push. See
[the compact-slice decision](research/decisions/2026-09-15-compact-slice-measurable.md) and
`research/explorations/2026-09-15-compact-slice-measurable.json`.

Still unproved: **L4** (Borel-set slices, a.e. measurable) and **L5** (measurable weights) — `L3`
asserts nothing for a general Borel set, and the first original coarea hole is stated for `univ`,
so the compact version cannot fill it. Also all three original coarea holes, sharp `C^(finrank)`
`Analysis.sard` (no downstream consumer), `smoothConstant_le_minkowskiConstant`,
`smoothConstant_mul_lintegral_min_superlevel_le`, and equality of the two Cheeger constants. No
certificate or Blueprint leanok scope was expanded.

## Eilenberg measurable-majorant round (2026-09-15)

**Superseded by the compact-slice measurability round above; retained as a dated snapshot.**
This round **proves obligation `L1`** of the weighted coarea route, with an explicit positive
constant: for `u` Lipschitz **on `S` only**, the slice function
`t ↦ surfaceMeasure V (S ∩ {u = t})` is dominated by a **measurable** `F` with
`∫⁻ F ≤ eilenbergConstant V * K * volume S`, where
`eilenbergConstant V = 4 ω_{n-1} / ω_n > 0` (`KLS.exists_measurable_majorant` and
`KLS.eilenbergConstant_pos` in `KLS/Geometry/SurfaceSlicing.lean`, over the Mathlib-only
`Analysis.exists_measurable_majorant` in `Analysis/HausdorffSlicing.lean`, which carries Mathlib's
diameter-gauge constant `2` on an arbitrary `EMetricSpace` with no dimension and no ambient
volume). Last round's `L2` is now the null special case, with **statements unchanged**. No
sharpness is claimed for the constant; the audit client computes it as `2` on the line and `4` in
dimension zero.

`S` is not assumed measurable, bounded, nonempty or of finite volume, `u` is not assumed globally
Lipschitz, differentiable or measurable, `K = 0` and `volume S = ∞` are explicit branches, and `V`
may be zero-dimensional — `[CompleteSpace V]` and `[Nontrivial V]` of the recorded `L1` are both
dropped as unused. Measurability is still asserted only of the **constructed** majorant: the slice
function itself is not known to be measurable, and `L1` supplies no such statement.

`build/audit/EilenbergMajorantAudit.lean` compiles strictly: the route's `L1` text `#check`, a
`target` theorem restating it verbatim with `[CompleteSpace V]` and `[Nontrivial V]`, a
`target_of_trivial` without `[Nontrivial V]`, six independent consumers (`L2` re-derived from the
majorant alone; **finiteness** of almost every slice measure when `volume S < ∞`, which `L2`
cannot give; `K = 0` forcing a vanishing integral; `S = univ` with no finiteness hypothesis; and
the constant computed as `2` on the line and `4` in dimension zero), four `preserved_*` theorems that re-check last round's statements
through **named** arguments so a renamed binder fails to elaborate, and 23 `#print axioms` lines
that all report only `propext`, `Classical.choice` and `Quot.sound`. Nine earlier strict clients
re-pass unedited, and the three WIP files actually recompile with **3/3/5** direct holes, total
**11** — unchanged, because `L1` fills none of the original coarea holes. Default `lake build` and
root `research/verify.py` pass; the final source-bound receipt is
`build/verification/latest.json`, with the final equality check in
`build/audit/eilenberg-final-snapshot.json`. Certificates stay **24**, perimeter infrastructure
**missing**. The incoming passed receipt `20260914T211119.924157Z` matched all 414 snapshot
entries. HEAD stays `2965b32`; no commit/push. See
[the Eilenberg-majorant decision](research/decisions/2026-09-15-eilenberg-majorant.md) and
`research/explorations/2026-09-15-eilenberg-majorant.json`.

Still unproved: the **L3–L5 fibre-measurability bridge**, all three original coarea holes, sharp
`C^(finrank)` `Analysis.sard` (no downstream consumer),
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and
equality of the two Cheeger constants. No certificate or Blueprint leanok scope was expanded.

## Null slicing round (2026-09-15)

**Superseded by the Eilenberg measurable-majorant round above; retained as a dated snapshot.**
This round **proves obligation `L2`** of the weighted coarea route: a Lebesgue-null set has
`surfaceMeasure`-null slices along almost every level of a function that is Lipschitz **on that
set only**. The metric-space core is `Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero` in the
new `Analysis/HausdorffSlicing.lean` (local import closure empty, Mathlib only, arbitrary
`EMetricSpace`), and the normalized wrapper is
`KLS.ae_surfaceMeasure_inter_levelSet_eq_zero` in the new `KLS/Geometry/SurfaceSlicing.lean`.
`N` is not assumed measurable, bounded or nonempty, `u` is not assumed globally Lipschitz,
differentiable or measurable, `K = 0` is allowed and `V` may be zero-dimensional. Rademacher's
theorem does **not** give this; the proof is a covering argument with a **measurable majorant**,
so nothing is inferred from `∫⁻ f = 0` for a function not known to be measurable.

`build/audit/NullSlicingAudit.lean` compiles strictly: the route's `L2` text `#check`, a `target`
theorem restating it verbatim with `[CompleteSpace V]`, nine independent consumers (subset of a
null set with no measurability, `K = 0`, arbitrary `ℝ≥0∞` weight over slices, dimension zero and
its unit mass `ℋ^{0-1} univ = 1`, dimension one with its genuine exceptional level
`ℋ⁰ ({0} ∩ {id = 0}) = 1`, an `N`-only-Lipschitz discontinuous `u`, and a nondegenerate planar
segment of nonzero `ℋ¹`), plus 14 `#print axioms` lines that all report only `propext`,
`Classical.choice` and `Quot.sound`. Eight earlier strict clients re-pass unedited, and the three
WIP files actually recompile with **3/3/5** direct holes, total **11** — unchanged, because `L2`
fills none of the original coarea holes. Default `lake build` and root `research/verify.py` pass;
the final source-bound receipt is `build/verification/latest.json`, with the final equality check
in `build/audit/nullslicing-final-snapshot.json`. Certificates stay **24**, perimeter
infrastructure **missing**. The incoming passed receipt `20260914T194849.197366Z` matched all 410
snapshot entries. HEAD stays `2965b32`; no commit/push. See
[the null-slicing decision](research/decisions/2026-09-15-null-slicing.md) and
`research/explorations/2026-09-15-null-slicing.json`.

Still unproved: the **L3–L5 fibre-measurability bridge** (`L2` gives no measurability), all three
original coarea holes, the constant-carrying general `L1`, sharp `C^(finrank)` `Analysis.sard`
(no downstream consumer), `smoothConstant_le_minkowskiConstant`,
`smoothConstant_mul_lintegral_min_superlevel_le`, and equality of the two Cheeger constants. No
certificate or Blueprint leanok scope was expanded.

## Weighted coarea route exploration (2026-09-15)

**Superseded by the null-slicing round above; retained as a dated snapshot.**
This round proves no new theorem and changes no Lean library source. The proposed general theorem
combines weighted coarea and fiber AEMeasurable on any Borel restriction, for Lipschitz `u` in every
finite dimension and arbitrary ENNReal measurable weights. The three original targets remain
unchanged. The precise missing foundations are the Eilenberg measurable-majorant/null-slicing
lemma and the C¹ Whitney jet extension plus exact C¹ decomposition of Lipschitz functions.
The existing C¹ graph area formula and same-dimensional Jacobian theorem are ingredients, not
Lipschitz coarea. Fiber measurability can be proved independently of the equality, but needs compact
fiber measurability and null slicing; ambient surfaceMeasure is not SFinite in positive dimension.

`build/audit/WeightedCoareaRouteStatements.lean` has 17 strictly checked statements and no
new declaration, proof or axiom; a second strict client checks 20 existing infrastructure APIs.
Six previous clients re-pass strictly, and the three WIP files actually recompile with **3/3/5**
direct holes, total **11**. Default `lake build` and root `research/verify.py` pass; the final
source-bound receipt is `build/verification/latest.json`, with the final equality check in
`build/audit/coarea-final-snapshot.json`. Certificates stay **24**, perimeter infrastructure
**missing**. The incoming passed receipt `20260914T181901.237724Z` matched all 408 snapshot entries.
HEAD stays `2965b32`; no commit/push. See [the route decision](research/decisions/2026-09-15-weighted-coarea-route.md) and
`research/explorations/2026-09-15-weighted-coarea-route.json` for exact statements and hashes.

Still unproved: sharp C^(finrank) `Analysis.sard` (no downstream consumer), all three coarea
holes, `smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`,
and equality of the two Cheeger constants. Smooth Sard and `ae_exists_superlevel` remain proved
without `sorryAx`; the full chain is not closed. Next suggested step: L2 null slicing, then L3–L5
fiber measurability. No certificate or Blueprint leanok scope was expanded.

## Superlevel rewiring round (2026-09-15)

**Superseded by the weighted coarea route round above; retained as a dated snapshot.**
`SmoothDomain.ae_exists_superlevel` and `SmoothDomain.frontier_superlevel_subset` have moved out of
`KLS/WIP/CheegerInfimum.lean` into the new hole-free `KLS/Geometry/RegularSuperlevel.lean`, with
**byte-identical `pp.all` signatures** (diff-checked). The former is now proved from
`Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top`, a consequence of the proved
`Analysis.sard_smooth`, so **it no longer inherits `sorryAx`** — the first KLS conclusion freed
from the Sard dependency.

The packaging was deliberately not put back into `Geometry/SmoothDomain.lean`, whose docstring
keeps it independent of Sard; it sits one layer up. `WIP/CheegerInfimum.lean` swapped its import of
`WIP/AnalyticPrerequisites` for the new module and still compiles, which shows that Sard
consequence was its only real dependency there: **no module now imports
`KLS/WIP/AnalyticPrerequisites.lean` at all**, so the sharp Sard and coarea holes sit in a file
nothing depends on.

Holes are unchanged at **11** (3/3/5): what moved was a filled body, not a direct hole — this round
reduced `sorryAx` propagation, not the hole count. Certificates stay **24**, perimeter
infrastructure **missing**. `build/audit/SuperlevelSardScope.lean` now reports the boundary side by
side: `ae_exists_superlevel`, `frontier_superlevel_subset` and `Analysis.sard_smooth` carry only
standard axioms, while `Analysis.sard` and `Analysis.ae_forall_fderiv_ne_zero` still carry
`sorryAx`. Ten earlier audits re-pass strictly with no edits; default `lake build` passes
(3393 jobs). The incoming passed receipt `20260914T171940.461693Z` was matched byte-for-byte.
HEAD stays `2965b32`; no commit/push. See the
[new decision](research/decisions/2026-09-15-superlevel-rewire.md).

Next blocker: weighted coarea `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` and its
level-set measurability, then the reverse Cheeger comparison. The sharp `C^n` `Analysis.sard` now
has no downstream consumer.

## Smooth Sard round (2026-09-15)

**Superseded by the superlevel rewiring round above; retained as a dated snapshot.**
**Sard's theorem for `C^∞` real-valued functions is proved**, in `Analysis/SmoothSard.lean`, with
standard three axioms only: `Analysis.sard_smooth_pi` on `Fin n → ℝ` in every dimension,
`Analysis.sard_smooth` on an arbitrary finite-dimensional real normed space, and
`Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top`. The critical set is not assumed measurable.

Second route correction: the recorded L3 (open-domain form of the flat layer) was **not needed**.
A cheaper replacement, `Analysis.exists_contDiff_eventuallyEq` (a bump-multiplied local smooth
extension), lets the induction stay global, so the already proved
`volume_image_flat_pow_univ_eq_zero` handles the top layer unchanged. The induction on dimension
splits the critical set by `critical_subset_layers`, turns each intermediate layer into a lower
dimension through `exists_flat_direction` and `exists_local_graph`, replaces the local graph by a
globally smooth map agreeing with it near the base parameter, applies the inductive hypothesis to
`u ∘ γ'`, and glues with Lindelöf.

`build/audit/SmoothSardAudit.lean` shows what this closes: `superlevel_without_sard` reproves the
statement of `SmoothDomain.ae_exists_superlevel` from the new theorem and reports **no `sorryAx`**,
while the WIP declaration itself, in the same log, still carries it. **No WIP file was changed this
round**, so `SmoothDomain.ae_exists_superlevel` still inherits `sorryAx`, holes stay **11**
(3/3/5), certificates **24**, perimeter infrastructure **missing**, and the sharp `C^n`
`Analysis.sard` keeps its statement and direct-hole status with the `n = 4, j = 2` obstruction
untouched. Rewiring WIP to the new theorem is a separate decision for the next round.

The module and its client pass `-DwarningAsError=true`; eight earlier audits re-pass strictly with
no edits; the three WIP files re-elaborate with **3/3/5** direct holes; default `lake build` passes
(3393 jobs). The incoming passed receipt `20260914T165021.064313Z` was matched byte-for-byte.
HEAD stays `2965b32`; no commit/push. See the
[new decision](research/decisions/2026-09-15-smooth-sard.md).

Still open: the WIP rewiring, the sharp `C^n` Sard, and — the main blocker for the reverse Cheeger
comparison — weighted coarea and its level-set measurability, both untouched.

## Smooth Sard ingredients round (2026-09-15)

**Superseded by the smooth Sard round above; retained as a dated snapshot.**
`Analysis/SmoothSard.lean` proves three of the seven lemmas listed by the route exploration, with
standard three axioms only: `critical_subset_layers` (L2, the layer decomposition of the critical
set), `exists_flat_direction` (L4, a nonvanishing derivative of order `j + 1` yields a scalar
`C^∞` function vanishing on the `j`-th layer with nonvanishing differential) and
`exists_local_graph` (L5, the regular zero set of such a function is locally the image of a map
`C^∞` on an open parameter set, with a fixed continuous parameter map).

One route correction: `ContDiffAt ℝ ∞` does **not** upgrade to `ContDiffOn ℝ ∞` on a
neighbourhood — `ContDiffAt.contDiffOn` carries the side condition `m = ∞ → n = ω`, and this is
real, not an interface defect. So the inverse function theorem's pointwise output is not enough
and L5 was strengthened to an open parameter set: shrink to the open region where the chosen
partial derivative of `w` is nonzero, rebuild the invertible differential at each of its points,
and apply `OpenPartialHomeomorph.contDiffAt_symm` pointwise. The chart is the map replacing one
coordinate by `w`; no manifold or implicit-function framework was built, and
`Analysis/ImplicitGraph.lean` still does not apply.

The module and its client pass `-DwarningAsError=true` with 10 standard-axiom reports, covering
dimension zero, the planar `j = 1` case and a concrete regular zero set. Seven earlier audits
re-pass strictly with no edits; the three WIP files re-elaborate with **3/3/5** direct holes.
**No `sorryAx` was removed and no statement changed**: general `Analysis.sard` and both its
consumers still inherit `sorryAx`, holes stay **11**, certificates **24**, perimeter
infrastructure **missing**. Default `lake build` passes (3393 jobs). The final root receipt is
`build/verification/latest.json`; the incoming passed receipt `20260914T162757.518089Z` was
matched byte-for-byte. HEAD stays `2965b32`; no commit/push.

Still missing before `C^∞` Sard exists: **L3** (open-domain form of the already proved flat
layer, which also needs the order-`n` remainder relaxed to an open domain), **L1** (the dimension
induction assembling L2/L4/L5 with Lindelöf), and **L6/L7** (transfer to a general
finite-dimensional space and the `C^∞` a.e. variant). See the
[new decision](research/decisions/2026-09-15-smooth-sard-ingredients.md).

## Sard route exploration round (2026-09-15)

**Superseded by the ingredients round above; retained as a dated snapshot.**
**No theorem was proved this round and no Lean source under `formalization/` changed.** The round
determined the route for the remaining Sard layers and produced type-checked statements only.

Main finding: the sharp `C^n` `Analysis.sard` is **not needed by any consumer**. Its only user is
`Analysis.ae_forall_fderiv_ne_zero`, whose only user is `SmoothDomain.ae_exists_superlevel`, and
that statement already assumes `ContDiff ℝ ∞ u` and downgrades ∞ to `finrank` at the call site.
Proving a `C^∞` Sard plus a `C^∞` variant of `ae_forall_fderiv_ne_zero` would free
`ae_exists_superlevel` from `sorryAx` without touching the sharp statement, which keeps its text
and its direct-hole status.

The sharp version's first genuine obstruction is located exactly: layer `A_j \ A_{j+1}` in
dimension `d` closes elementarily only when `j ≥ d-1`, and by hypersurface descent only when
`j ≤ 1`, so `n = 4, j = 2` is the first uncovered case — the restricted function is only `C²` on a
3-dimensional slice while 3-dimensional Sard needs `C³`. Sharp Sard in dimension 3 is reachable
with what exists today; dimension 4 and up is the Whitney–Morse–Sard difficulty and is not
attempted. Under `C^∞` the descent never exhausts regularity, which is the whole reason to switch.

The recommended inductive statement is over **open** domains, `ContDiffOn ℝ ∞ u O` with `IsOpen O`,
since that is exactly what the descent step supplies; `O = univ` recovers the global form. Seven
supporting lemmas are listed with effort estimates in the decision record. Mathlib turns out to
have all the ingredients for the hardest one (the local `C^∞` graph of a regular zero set) in
`Mathlib/Analysis/Calculus/ImplicitContDiff.lean`, including the graph characterization, not just
an inclusion; the repository's own `Analysis/ImplicitGraph.lean` still does not apply. There is no
ready-made smooth-extension-from-a-neighborhood lemma, which is why the open-domain formulation is
preferred over bump extensions.

`build/audit/SmoothSardRouteStatements.lean` passes `-DwarningAsError=true` with nine `#check`s and
contains no declaration, proof or placeholder axiom. Holes stay **11** (3/3/5), certificates **24**,
perimeter infrastructure **missing**; `Analysis.sard` and both consumers still inherit `sorryAx`.
Default `lake build` and `python3 research/verify.py` re-pass. HEAD stays `2965b32`; no commit/push.
See the [route decision](research/decisions/2026-09-15-smooth-sard-route.md).

## Higher-order flat layer round (2026-09-15)

**Superseded by the route exploration round above; retained as a dated snapshot.**
Both obligations recorded last round are proved verbatim, with standard three axioms only.
`Analysis.exists_uniform_pow_remainder` in `Analysis/TaylorRemainder.lean` gives the order-`n`
uniform remainder at points of a compact set where every derivative of order `1` to `n` vanishes,
on an arbitrary real normed domain — no finite-dimensionality, completeness, inner product or
measure. `Analysis.volume_image_eq_zero_of_oscillation_pow` in `Analysis/QuadraticCover.lean`
gives the `n`-dimensional covering lemma: a bounded `A ⊆ Fin n → ℝ` with a uniform `o(‖y-x‖ⁿ)`
modulus has null image, with no measurability anywhere. Combining them,
`Analysis.volume_image_flat_pow_eq_zero` and `Analysis.volume_image_flat_pow_univ_eq_zero` make
the fully flat layer null on a compact subset and on all of `Fin n → ℝ`.

The remainder is proved by induction on the order: the inductive step applies the statement to
`fderiv f` (vector-valued, hence an auxiliary same-universe lemma) and raises the power by one
convex mean-value inequality, without degrading the constant. The covering lemma replaces the
`ℤ × ℤ` grid by `Fintype.piFinset` over `Fin n → ℤ`, where `(2M+1)ⁿ` cells of image length
`O(ε rⁿ)` cancel exactly. `n = 0` and `n = 1` need no branch.

No duplicated proof was added: `exists_uniform_quadratic_remainder` and
`volume_image_eq_zero_of_quadratic_oscillation` are now corollaries, with their statements
**byte-identical** (diff-checked) and every existing client unchanged and still passing.

The two modules and the new client pass `-DwarningAsError=true`; 17 axiom reports use only
standard axioms, covering the two recorded obligations verbatim, the remainder on a
dimensionless normed space, dimensions zero, one and three, the unchanged planar interface, and
a constant function that is fully flat on **all of `ℝⁿ`** yet has null image. Six earlier audits
re-pass strictly with no edits; the three WIP files re-elaborate with **3/3/5** direct-hole
warnings only. General Sard and its two consumers still inherit `sorryAx`: holes stay **11**,
certificates **24**, perimeter infrastructure **missing**. Default `lake build` passes
(3393 jobs). The final root verification receipt is `build/verification/latest.json`; the incoming
passed receipt `20260914T154144.742286Z` was matched byte-for-byte. HEAD stays `2965b32`;
no commit/push.

This round completes the **top layer in dimension `n` only**. The intermediate layers
(`1 ≤ j < n`, derivatives of order `1..j` vanishing but order `j+1` not), the stacked
dimension-`n` Sard, and the general `Analysis.sard` over an arbitrary finite-dimensional space
are all still unproved; the first two are type-checked in
`build/audit/IntermediateLayerNextStatement.lean`. See the
[new decision](research/decisions/2026-09-15-higher-order-flat-layer.md).

## Planar Sard round (2026-09-14)

**Superseded by the higher-order flat layer round above; retained as a dated snapshot.**
`Analysis.sard_plane` is proved in
`formalization/FunctionalInequalities/Analysis/PlanarSard.lean`, with standard three axioms only:
the critical values of a `C²` function on `Fin 2 → ℝ` are Lebesgue null. The critical set is not
assumed measurable, bounded or compact. Its nonflat layer
`Analysis.volume_image_nonflat_eq_zero` and a one-dimensional covering lemma
`Analysis.volume_image_eq_zero_of_quadratic_bound` are proved alongside it.

The nonflat layer avoids the implicit function theorem. Near a point with `D²u ≠ 0` a
mean-value inequality with linear principal part shows the critical set is a Lipschitz graph over
one coordinate; that bound also forces injectivity of the coordinate, so the layer collapses onto
the one-dimensional covering lemma, whose cell count `O(r⁻¹)` already beats the image length
`O(r²)` without any `ε`-refinement. Lindelöf glues the local balls countably, so no compactness
hypothesis survives. The repository's `Analysis/ImplicitGraph.lean` was **not** reused: it needs
`C^∞` and an inner product, while `Du` is only `C¹` here. No new implicit-function framework was
built, no declaration moved, no signature changed, no WIP dependency, no certificate expansion.

`Analysis.sard_plane` is **not** `Analysis.sard`: the latter is the arbitrary-finite-dimension
statement and remains a direct hole, with both consumers still inheriting `sorryAx`. Holes stay
**11**, certificates **24**, perimeter infrastructure **missing**.

The two modules and the independent client pass `-DwarningAsError=true`; 16 axiom reports use only
standard axioms, covering the previously recorded compact-`K` obligation verbatim, an arbitrary
non-measurable subset, a constant function whose critical set is the **whole plane** yet has null
image, and `x ↦ (x 0)²` whose critical set is proved to be exactly the line `{x 0 = 0}`.
QuadraticCoverAudit, QuadraticRemainderAudit, SardLowDimAudit, AreaFormulaAudit and
SuperlevelSardScope re-pass strictly; the three WIP files re-elaborate with **3/3/5** direct-hole
warnings only. Default `lake build` passes (3393 jobs). The final root verification receipt is
`build/verification/latest.json`; the incoming passed receipt `20260914T150543.429034Z` was matched
byte-for-byte to the working tree. HEAD stays `2965b32`; no commit/push.

Next: the `n`-dimensional covering lemma and the order-`n` uniform remainder at fully flat points,
both type-checked but unproved in `build/audit/HigherSardNextStatement.lean`. They give only the
top layer in dimension `n`; the intermediate layers still need finite-order implicit charts and
per-order dimension descent with regularity loss. See the
[new decision](research/decisions/2026-09-14-planar-sard.md).

## Planar quadratic covering round (2026-09-14)

**Superseded by the planar Sard round above; retained as a dated snapshot.**
`Analysis.volume_image_eq_zero_of_quadratic_oscillation` and `Analysis.volume_image_flat_eq_zero`
are proved in `formalization/FunctionalInequalities/Analysis/QuadraticCover.lean`, with standard
three axioms only. The covering lemma is exactly the statement proposed last round: for a bounded
`A : Set (Fin 2 → ℝ)` and an arbitrary `f`, a uniform `|f y - f x| ≤ ε‖y-x‖²` on pairs of points of
`A` forces `volume (f '' A) = 0`. Neither `A` nor `f '' A` is assumed measurable and `f` has no
regularity anywhere; the empty set is covered. The proof grids `A` into `O(r⁻²)` cells of width
`r = min δ 1` indexed by `⌊·/r⌋ : ℤ × ℤ`, picks one `A`-representative per occupied cell, covers
its image by an interval of length `2εr²`, and sums with `measure_biUnion_finset_le`; the total
`2ε(2R+3)²` is independent of `r`, and `ENNReal.le_of_forall_pos_le_add` sends `ε → 0`. Dimension
two is used where the cell count `O(r⁻²)` meets the interval length `O(εr²)`.

Connecting it to `Analysis.exists_uniform_quadratic_remainder` gives the second-order flat layer:
for `C²` `u` and compact `K ⊆ Fin 2 → ℝ`, the image of `{x ∈ K | Du x = 0 ∧ D²u x = 0}` is null.
Flatness is pointwise on that **subset**; all of `K` is not assumed flat, and the subset is not
assumed measurable. `Analysis.volume_image_flat_univ_eq_zero` exhausts the plane by
`⋃ n : ℕ, closedBall 0 n` and drops compactness, boundedness and measurability entirely. Mathlib-only imports plus the local `Analysis/TaylorRemainder`; no existing
declaration moved or changed, no WIP dependency or certificate expansion.

The new module and independent client pass `-DwarningAsError=true`; 19 axiom reports use only
standard axioms, covering the empty set, a singleton with a completely arbitrary `f`, an arbitrary
bounded set with no measurability instance in the client at all, the hypothesis-free whole-plane
flat layer, and the flat layer of the nonconstant `x ↦ (x 0)³` on a closed ball, together with an
explicit nonflat point `![1,0]` and an explicit flat point `0` inside that ball. QuadraticRemainderAudit, SardLowDimAudit, AreaFormulaAudit
and SuperlevelSardScope re-pass strictly. The three WIP files actually re-elaborate with **3/3/5**
direct-hole warnings only. General Sard and its two consumers still inherit `sorryAx`: holes stay
**11**, certificates **24**, perimeter infrastructure **missing**. No coarea, reverse Cheeger
comparison or equality is proved. Default `lake build` passes (3393 jobs). The final root
verification receipt is `build/verification/latest.json`; the incoming passed receipt
`20260913T190354.174769Z` was matched byte-for-byte to all 390 files. HEAD stays `2965b32`;
no commit/push.

This round completes the **planar second-order flat layer only**. The planar nonflat layer
`{x ∈ K | Du x = 0 ∧ D²u x ≠ 0}` (type-checked, unproved, in
`build/audit/PlanarNonflatNextStatement.lean`), general Sard, weighted coarea and the reverse
Cheeger comparison are all still unproved, and nothing here closes the chain. See the
[new decision](research/decisions/2026-09-14-planar-quadratic-cover.md).

## Uniform quadratic remainder round (2026-09-14)

**Superseded by the planar covering round above; retained as a dated snapshot.**
`Analysis.exists_uniform_quadratic_remainder` is proved in
`formalization/FunctionalInequalities/Analysis/TaylorRemainder.lean`, with standard three axioms
only. For a C² real-valued function and compact K, every ε>0 has a single δ>0 such that
`|u y-u x| ≤ ε * ‖y-x‖²` whenever x∈K has Du(x)=D²u(x)=0 and ‖y-x‖<δ.
Not all of K must be flat; y may lie outside K. Empty K, zero dimension and y=x are included.
The proof works on arbitrary real normed spaces, without finite dimension, completeness,
inner product or domain measure. It uses Heine–Cantor's external-neighbourhood control and two
convex mean-value inequalities, rather than adding a Taylor framework. Mathlib-only imports;
no existing declaration moved or changed, no WIP dependency or certificate expansion.

The new module and independent client pass `-DwarningAsError=true`; 10 axiom reports use only
standard axioms, including cubic-function tests with nonflat points in K and an actual point
outside K. SardLowDimAudit, AreaFormulaAudit and SuperlevelSardScope re-pass strictly.
The three WIP files actually re-elaborate with **3/3/5** direct-hole warnings only.
General Sard and its two consumers still inherit `sorryAx`: holes stay **11**, certificates **24**,
perimeter infrastructure **missing**. No coarea, reverse Cheeger comparison or equality is proved.
Default `lake build` passes (3393 jobs). The final root verification receipt is
`build/verification/latest.json`; the incoming passed
receipt `20260913T184752.039532Z` was matched to all 387 files. HEAD stays `2965b32`; no commit/push.

Next: the bounded planar-set covering lemma turning uniform o(r²) oscillation into nullity of
the image, with no measurability assumption. Its precise statement and the remaining higher-order
and dimension-descent gaps are in the
[new decision](research/decisions/2026-09-14-uniform-quadratic-remainder.md).
The new estimate itself is not an image-nullity or general Sard theorem.

## Low-dimensional Sard round (2026-09-14)

**Superseded by the quadratic remainder round above; retained as a dated snapshot.**
`Analysis.sard_of_finrank_le_one` is proved in
`formalization/FunctionalInequalities/Analysis/Sard.lean`, with only
`propext`, `Classical.choice`, `Quot.sound`. It covers arbitrary finite-dimensional real normed
spaces of dimension at most one, with exactly `ContDiff ℝ (Module.finrank ℝ V) u`:
zero dimension uses a subsingleton domain and a singleton image; dimension one uses
`e : ℝ ≃L[ℝ] V`, the chain rule with zero derivative on the pulled-back critical set, and
Mathlib's equidimensional null-image theorem. Only the target's Lebesgue measure is used.
There is no domain measure, inner product, critical-set measurability, compact-support or
boundedness assumption. The new module imports Mathlib only, with no local dependency or migration.

The original general `Analysis.sard` and its consumers retain their statements and proofs.
`sard`, `ae_forall_fderiv_ne_zero` and `SmoothDomain.ae_exists_superlevel` each still carry
`sorryAx`. Direct holes remain **11 = 3 / 3 / 5**; certificates remain **24** and perimeter
infrastructure remains **missing**. General Sard, weighted coarea, its level-set measurability,
`h_S ≤ h_M`, equality of Cheeger constants and the full chain are still unproved.

`build/audit/AreaFormulaAudit.lean` now explicitly imports `Analysis.Divergence` and passes strict
compilation with six standard-axiom reports. The `ae_exists_superlevel` docstring now says `t-u`.
The low-dimensional independent client passes `-DwarningAsError=true`, with eight standard-axiom
reports covering general one-dimensional normed spaces, arbitrary functions on the zero-dimensional
space, real C¹ functions, constants, and the square function with a proved critical point and
nonconstancy. All 16 selected existing clients pass strictly; the Sard scope client's inherited
`sorryAx` is expected and separately recorded. The four selected hole-free modules pass strictly;
all three WIP modules actually re-elaborate with exactly 3/3/5 hole warnings and no other diagnostic.
Default `lake build` passes (3393 jobs). Root verification binds the final snapshot; its
authoritative final receipt is `build/verification/latest.json`, not the incoming receipt.

**Next bounded obligation:** the uniform quadratic remainder at points with vanishing first and
second derivatives on a compact set, stated precisely in the
[new decision](research/decisions/2026-09-14-low-dimensional-sard.md).
Mathlib already provides multivariate integral Taylor, inverse/implicit function, chain-rule and
countable-cover tools. Higher-order critical strata, regularity-preserving dimension descent and
the quantitative covering/null-image argument are still missing; naive descent loses regularity
on higher strata. A base case is not a completed induction.
Incoming receipt `20260913T182956.860385Z` was independently matched to all 384 files.
HEAD remains `2965b32`; no commit or push. All earlier uncommitted work is preserved.

## Superlevel round: the regular-value smooth-domain construction is proved and the Sard packaging is filled (2026-09-14)

**Superseded by the low-dimensional Sard round above; retained as a dated snapshot.**
Two results, deliberately kept apart.

**(1) Hole-free, no `sorryAx`.** `SmoothDomain.ofSuperlevel` and its `ofSuperlevel_carrier` are new
in `formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain.lean`: a strict superlevel set
`{x | t < u x}` of a `C^∞` function is a smooth domain as soon as `fderiv ℝ u` is nonzero on
**`frontier {x | t < u x}`** — not on the whole level set `{x | u x = t}` and not on the whole
space. The defining data is `W = {y | fderiv ℝ u y ≠ 0}`, open because `hu.continuous_fderiv` makes
`y ↦ fderiv ℝ u y` continuous, and `φ = t - u`, matching the structure's **negative**-sublevel
convention: `fderiv_const_sub` and `neg_ne_zero` give nonvanishing, and
`carrier ∩ W = {y ∈ W | φ y < 0}` is the pure rewrite `t - u y < 0 ↔ t < u y`. Empty frontier, empty
carrier, full carrier and dimension zero are covered by the construction itself, with no extra
hypothesis and no branch: in each of them the frontier is empty and the field's premise is vacuous.
The construction lives in the module that owns the structure and its other constructors
(`empty`, `univ`, `homothety`), needs only `NormedAddCommGroup` + `NormedSpace ℝ`, imports no WIP
module and builds no manifold framework.

**(2) Filled body that still inherits `sorryAx`.** `SmoothDomain.ae_exists_superlevel` in
`KLS/WIP/CheegerInfimum.lean` is no longer a direct hole: its statement text is unchanged and its
proof is `filter_upwards [Analysis.ae_forall_fderiv_ne_zero (hu.of_le ENat.LEInfty.out)]` followed
by `ofSuperlevel` applied through `frontier_superlevel_subset`. It **still depends on `sorryAx`**
through `Analysis.sard`, which is untouched, and must not be listed as a `sorryAx`-free result;
it closes the Sard-to-smooth-domain *packaging* gap only and frees nothing downstream. The order
reduction's side condition is `(Module.finrank ℝ V : WithTop ℕ∞) ≤ ∞`, discharged by
`ENat.LEInfty.out`: `le_top` does not apply (that type's top is `ω`, not `∞`) and `simp` makes no
progress.

No module migration. `frontier_superlevel_subset` stays in `KLS/WIP/CheegerInfimum.lean` — its only
consumer is the wrapper in the same file, and the frontier-form hypothesis means the hole-free
construction does not need it; it was only moved **above** the wrapper inside that file, carrying
its `omit ... in` prefix. `KLS/WIP/CheegerInfimum.lean` gains one import line,
`FunctionalInequalities.KLS.WIP.AnalyticPrerequisites`, which no module imported before. The filled
body makes `unusedSectionVars` fire (a `sorry` body is exempt from that linter), so the linter is
silenced for that one declaration with a comment; `omit` was **not** used, since it would narrow the
published signature.

Current holes: **11 = 3 / 3 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**. Sard, the weighted coarea and
its level-set measurability are untouched direct holes, so this is **not** Sard, **not** the reverse
comparison, **not** an equality of Cheeger constants and **not** a completed chain.

`Geometry/SmoothDomain.lean` and the new `build/audit/SuperlevelDomainAudit.lean` pass
`-DwarningAsError=true`, the client's 8 axiom reports using only the standard three axioms and
covering the frontier-only hypothesis, the sign direction of the defining function, an
**everywhere-critical** level set with empty frontier (empty carrier), the full carrier, dimension
zero and an unbounded half-space with explicitly unbounded carrier and frontier. The separate
`build/audit/SuperlevelSardScope.lean` records that `ae_exists_superlevel` carries `sorryAx`.
The `pp.all` `#check` output for `ae_exists_superlevel` and `frontier_superlevel_subset` is
byte-identical before and after. `KLS/WIP/CheegerInfimum.lean` re-elaborates with exactly 3 hole
warnings and no other diagnostics. The `BoundaryChartAudit`, `CheegerInfimumAudit`,
`CutoffRouteReview`, `DilationAudit`, `DistanceCutoffAudit`, `GaussGreenAudit`,
`MinkowskiCoareaAudit`, `MinkowskiConstantAudit`, `MollifiedBoundaryScope`,
`PerimeterInterfaceAudit`, `RecoveryAudit` and `SubgraphDivergenceAudit` clients re-pass;
`build/audit/AreaFormulaAudit.lean` remains broken from an **earlier** round (it names
`Analysis.divergence` without importing `Analysis/Divergence.lean`) and was left as it is.
Read the [new decision](research/decisions/2026-09-14-regular-superlevel-smooth-domain.md).

**Route correction and completed base case:** `Analysis.sard_of_finrank_le_one` is now proved
as recorded above. Use `ContinuousLinearEquiv.ofFinrankEq` from ℝ to V, then the zero-derivative
chain rule and the equidimensional null-image theorem on ℝ. No isometry or measure-preserving
transport is needed. The original derivative `V →L[ℝ] ℝ` is not an endomorphism and must not be
assigned a determinant. The zero-dimensional branch uses only subsingletonness, not C¹.
The [new decision](research/decisions/2026-09-14-low-dimensional-sard.md) corrects the earlier
historical decision without rewriting it. The general Sard hole remains open.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Distance-cutoff round: the gradient integral estimate is proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written, the dated rounds below
retain their earlier snapshots, and the
[route correction](research/decisions/2026-09-13-cutoff-route-audit-correction.md) supersedes the
status and next-step text of the round below it.**
`Isoperimetry.lintegral_enorm_gradient_distanceCutoff_le` is proved, with its original statement
text, in the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/DistanceCutoff.lean`, whose **local import
closure is empty** (Mathlib only): for every probability law `ν`, every `r > 0` and an **arbitrary**
`B` — not assumed nonempty, measurable, closed or bounded, and with no null boundary —
`∫ ‖∇w_r‖ dν ≤ (ν(B^r) - ν(closure B)) / r`,
with `closure B` on the right rather than the weaker `ν(B)`, and with the thickening still open.
The Haar measure `m`, its instance and `hac` are kept verbatim in the signature although the proof
does not use them; nothing in the interface changed.

The route is pointwise, not almost-everywhere. Empty `B` is a separate branch: Mathlib's
`Metric.infDist x ∅ = 0` makes `distanceCutoff ∅ r` the constant **`1`**, not `0`, so
`gradient_fun_const` gives zero on the left, while `thickening r ∅ = ∅` and `closure ∅ = ∅` make the
right-hand side zero — no `B.Nonempty` was added to dodge this. For nonempty `B`, `w_r` attains its
global maximum `1` on `closure B` and its global minimum `0` outside the open thickening, so
`IsLocalMax.fderiv_eq_zero` and `IsLocalMin.fderiv_eq_zero` make the gradient vanish **at every
point** of those two sets, the endpoint level sets `{d = 0}` and `{d = r}` included; neither lemma
needs a `DifferentiableAt` hypothesis, because Mathlib defines `fderiv` and `gradient` to be zero at
points of non-differentiability. On the open annulus `B^r ∖ closure B` — measurable because the
thickening is open and the closure closed, **not** because `B` is measurable —
`norm_fderiv_le_of_lipschitz` with the proved `lipschitzWith_distanceCutoff` bounds the gradient by
`1/r`. Then `lintegral_mono`, `lintegral_indicator_const`, `measure_sdiff` via
`Metric.closure_subset_thickening`, and `ENNReal.ofReal_inv_of_pos` with `ENNReal.div_eq_inv_mul` to
match the original division. No Rademacher, no Lebesgue density theorem, no general "the gradient
vanishes almost everywhere on a level set" lemma and no absolute continuity. The two unused-argument
linters are silenced for this one declaration with a comment, never file-wide, and no hypothesis was
deleted or given a fake use; the non-differentiability convention is local to this estimate and is
**not** a comparison result for singular laws.

Layer changes: `Geometry/DistanceCutoff.lean` is new, hole-free and Mathlib-only. The complete cutoff
basis moved there verbatim — `distanceCutoff`, `distanceCutoff_mem_Icc`,
`lipschitzWith_distanceCutoff`, `distanceCutoff_eq_one_of_mem_closure`,
`distanceCutoff_eq_zero_of_notMem_thickening` and the `L¹(ν)` convergence
`tendsto_distanceCutoff_indicator` — with all seven `pp.all` signatures byte-identical before and
after the move. `exists_smooth_approximation_lipschitz` was deliberately **not** moved: it is
already proved, but it belongs to the smooth-replacement interface rather than the cutoff basis and
would drag the `Energy.Euclidean.LipschitzApproximation` import into a geometry module. Sard, the
coarea obligations, the reverse comparison, the equality and the affine-support transport stay in
`KLS/WIP/CheegerInfimum.lean`, which gains one import line.
`Geometry/{MinkowskiConstant,CheegerInfimum,PerimeterRecovery}.lean` are untouched.

Current holes: **12 = 3 / 4 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**. This is a gradient estimate on
the reverse-direction chain — **not** the reverse comparison, **not** an equality of Cheeger
constants, **not** a completed chain. `smoothConstant_le_minkowskiConstant` is still a direct hole,
and `minkowskiConstant_eq_smoothConstant`, which has a `le_antisymm` body, inherits `sorryAx`
through it.

The new module and `Geometry/{CheegerInfimum,MinkowskiConstant,MinkowskiContent}` pass
`-DwarningAsError=true`; the new `build/audit/DistanceCutoffAudit.lean` has 7 clients and 14 axiom
reports, all standard three axioms, covering an explicitly **non-measurable and unbounded** `B`, the
**empty set whose cutoff is constantly `1`**, the whole space, dimension zero, vanishing of the
gradient at **every** point of `closure B` (inner endpoint level set included), the same at the
**outer endpoint level set `{d = r}`**, and the migrated `L¹` convergence. The `CheegerInfimumAudit`,
`MinkowskiConstantAudit`, `MinkowskiCoareaAudit`, `RecoveryAudit`, `DilationAudit`,
`GaussGreenAudit` and `CutoffRouteReview` files re-pass. The three WIP files were re-elaborated with
exactly 3/4/5 hole warnings and no other diagnostics. The final root verification receipt is
`build/verification/latest.json`; the incoming passed receipt matched all 381 files. Read the
[new decision](research/decisions/2026-09-13-distance-cutoff-gradient-integral.md).

**What the reverse direction still needs, kept apart:** (1) weighted coarea
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` — **direct hole**; (2) level-set
integral measurability `Analysis.aemeasurable_lintegral_levelSet` — a **separate direct hole**;
(3) Sard `Analysis.sard` — **direct hole**, with `Analysis.ae_forall_fderiv_ne_zero` a filled body
inheriting `sorryAx` through it; (4) the Sard-to-smooth-superlevel packaging
`SmoothDomain.ae_exists_superlevel` — **still a direct hole, not a filled body**; (5) the assembly
`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (`C¹` specialization),
`smoothConstant_mul_lintegral_min_superlevel_le` and `smoothConstant_le_minkowskiConstant`.

**Next target: `SmoothDomain.ae_exists_superlevel`** — the packaging in (4), the clearest-bounded
remaining step. Proving it makes it a filled body that **still inherits `sorryAx` through
`Analysis.sard`**, so it closes the packaging gap only and frees nothing downstream; direct holes go
12 → 11 (3/3/5). Route: `carrier = {x | t < u x}` with `isOpen_lt`; the proved
`frontier_superlevel_subset` gives `u x = t` at a frontier point; `ae_forall_fderiv_ne_zero`, after
`hu.of_le` from `ContDiff ℝ ∞` down to `ContDiff ℝ (Module.finrank ℝ V)` — side condition
`(finrank : WithTop ℕ∞) ≤ ∞`, **not** `le_top`, since `∞` is not that type's top — gives
`fderiv ℝ u x ≠ 0`; take `W = {y | fderiv ℝ u y ≠ 0}`, open because `hu.continuous_fderiv` makes
`y ↦ fderiv ℝ u y` continuous; take `φ = fun y ↦ t - u y`, smooth by `contDiff_const.sub hu`, with
`fderiv_const_sub` and `neg_ne_zero` for nonvanishing and `carrier ∩ W = {y ∈ W | φ y < 0}` a pure
set rewrite; combine with `filter_upwards`. The two large analytic blocks, weighted coarea and Sard,
are untouched this round.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## One-sided Cheeger round: `h_M ≤ h_S` is proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written, and its status and
next-step text are corrected by the
[route correction](research/decisions/2026-09-13-cutoff-route-audit-correction.md).**
`Isoperimetry.minkowskiConstant_le_smoothConstant` is proved, with its original statement text, in
the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean`: for every finite-dimensional
real inner-product space — **zero dimension included** — and every Borell density `ρ` of `ν`
relative to Lebesgue `volume`,
`minkowskiConstant ν ≤ smoothConstant ρ (interior ν.support) ν`.
No bounded support, no bounded domain, no finite total boundary measure, no finiteness or
positivity of either constant, no existence of an admissible smooth domain and no finiteness of
relative perimeters were added; the `iInf` definition of `smoothConstant`, the `relativePerimeter`
normalization, `Ω = interior ν.support` and all admissible sets are unchanged. The reverse
comparison, weighted coarea, Sard and every `sorryAx`-carrying WIP theorem are unused.

**Only one direction is proved.** `smoothConstant_le_minkowskiConstant` still has a direct `sorry`;
`minkowskiConstant_eq_smoothConstant` has a `le_antisymm` body but inherits `sorryAx` from
that reverse direction. The **equality of the two Cheeger constants is not established**,
and neither is the relative-perimeter comparison chain.

The route is: `simp only [smoothConstant]` and three `le_iInf` layers, then
`ENNReal.le_div_iff_mul_le` with `m ≠ 0` (from `lt_min` and `tsub_pos_of_lt`) and `m ≠ ⊤` (from
`prob_le_one`), reducing the goal to `h_M · m ≤ P_ρ(U)` → a case split on `P_ρ(U) = ⊤`, where
`le_top` finishes and `exists_smooth_recovery_sequence` is never invoked, so its finiteness
argument stays a branch-local fact rather than a hypothesis of the theorem → unpacking the
recovery sequence, with `ContDiff.of_le` down to `C¹` whose side condition `(1 : WithTop ℕ∞) ≤ ∞`
is discharged by `simp` and **not** by `le_top` (`∞` is not that type's top), and per-term
application of `minkowskiConstant_mul_lintegral_min_superlevel_le` → the already proved
`tendsto_lintegral_min_superlevel`, fed by `U.isOpen.measurableSet`, giving `I_j → m` →
`ENNReal.Tendsto.const_mul` with `Or.inl (m ≠ 0)`, which is exactly what keeps `h_M = ⊤`
legitimate, then `Tendsto.limsup_eq` and `limsup_le_limsup` against the recovery-sequence `limsup`
bound. `h_M` is never divided out and no limit is exchanged with an integral without proof. When no
admissible smooth domain exists, `le_iInf` has an empty premise and the bound is covered by the
`iInf` structure itself; no nonemptiness or positive-dimension assumption was added.

Layer changes: `Geometry/CheegerInfimum.lean` is new and hole-free, and its 32-module local import
closure contains **no WIP module**. `smoothConstant`, `smoothConstant_eq_top_of_subsingleton`,
`lintegral_measure_symmDiff_superlevel`, `min_measure_le_add_measure_symmDiff` and
`tendsto_lintegral_min_superlevel` moved there verbatim from `KLS/WIP/CheegerInfimum.lean`; the
`pp.all` signatures of all six declarations — the newly proved theorem included — are byte-identical
before and after the move, and `unusedSectionVars` reports nothing on the filled body, so no
hypothesis or type changed. `Geometry/MinkowskiConstant.lean` was left untouched: no recovery,
relative-perimeter or WIP dependency was pushed into that base layer. Sard, weighted coarea, the
distance cutoffs, the reverse comparison, the equality and the affine-support transport stay in
`KLS/WIP/CheegerInfimum.lean`, which now imports only the new module.

Current holes: **13 = 3 / 5 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**.

The new module and `Geometry/{MinkowskiContent,MinkowskiConstant,PerimeterRecovery}` pass
`-DwarningAsError=true`; the new `build/audit/CheegerInfimumAudit.lean` has 6 clients and 14 axiom
reports, all standard three axioms, covering the general case with an explicitly unbounded support,
dimension zero with both infima `⊤`, **no admissible smooth domain** (so `h_S = ⊤` from the `iInf`
structure alone), a single admissible domain of **infinite relative perimeter** whose quotient is
`⊤` and constrains nothing, an admissible domain of **zero relative perimeter** forcing
`h_M = 0`, and `h_M = ⊤` forcing every admissible domain to have infinite relative perimeter with
no division. The `MinkowskiConstantAudit`, `MinkowskiCoareaAudit`, `RecoveryAudit`, `DilationAudit`
and `GaussGreenAudit` clients re-pass. The three WIP files were re-elaborated with exactly 3/5/5
hole warnings and no other diagnostics. The final root verification receipt is
`build/verification/latest.json`; the incoming passed receipt matched all 378 files. Read the
[new decision](research/decisions/2026-09-13-cheeger-infimum-one-sided.md).

**Next target: `lintegral_enorm_gradient_distanceCutoff_le`** — the only one of the three
reverse-direction gaps independent of Sard and coarea, so it can be finished on its own and takes
`WIP/CheegerInfimum` from 5 holes to 4. Route, with Mathlib names checked: empty `B` is a separate
branch where `Metric.infDist_empty` makes the cutoff constant and both sides vanish, so no
nonemptiness hypothesis is added; for nonempty `B`, `mem_closure_iff_infDist_zero` and
`mem_thickening_iff_infDist_lt` identify `closure B = {d = 0}` and `thickening r B = {d < r}`, and
`{0 < w_r < 1}` is the **open** annulus. The key step needs **no Lebesgue density theorem**: `w_r`
attains its global maximum `1` on `closure B` and its global minimum `0` on `{d ≥ r}`, so
`IsLocalMax.fderiv_eq_zero` and `IsLocalMin.fderiv_eq_zero` kill the gradient at **every point**
there, without a differentiability hypothesis. Mathlib defines `fderiv` and `gradient` as zero
at nondifferentiable points, and `norm_fderiv_le_of_lipschitz` likewise needs no differentiability
hypothesis. Thus a pointwise annulus bound followed by `lintegral_mono`,
`lintegral_indicator_const` and `measure_sdiff` suffices; no Rademacher theorem or use of `hac`
is needed for this route. Keep the original theorem signature, including `m` and `hac`.
For empty `B` the cutoff is specifically the constant **one**, with zero gradient and zero RHS.
`SmoothDomain.ae_exists_superlevel` remains a **direct hole**; only
`Analysis.ae_forall_fderiv_ne_zero` has a filled body inheriting `sorryAx` from Sard.
See the [audit correction](research/decisions/2026-09-13-cutoff-route-audit-correction.md),
which supersedes the corresponding route and status claims in the historical decision.
By contrast `exists_smooth_approximation_lipschitz` is already
**proved** from the certified `LipschitzApproximation.exists_smooth_bounded_L1` and needs no
further work; weighted coarea and Sard remain the two large blocks, untouched this round.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Minkowski-constant round: the integrated coarea bound is proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written.**
`Isoperimetry.minkowskiConstant_mul_lintegral_min_superlevel_le` is proved, with its original
statement text, in the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/MinkowskiConstant.lean`: for every probability
law `ν` on a finite-dimensional real inner-product space and every `C¹`, globally Lipschitz,
`[0,1]`-valued `u`,
`h_M · ∫₀¹ min {ν{u > t}, 1 - ν{u > t}} dt ≤ ∫ ‖∇u‖ dν`.
The law may be singular or atomic; no density, no absolute continuity, no nonatomicity, no positive
dimension, no finiteness or positivity of `h_M` and no null superlevel boundary were added, and the
admissible sets of `minkowskiConstant` and the definition of `minkowskiContent` are unchanged.
Neither the smooth recovery sequence, weighted coarea nor Sard is used.

The route is: `ae_measure_superlevel_lt_eq_le` — for **any** `SFinite` measure and **any**
measurable `u`, the strict and the closed superlevel sets have equal mass for Lebesgue-almost every
level, because the level sets `{u = t}` are pairwise disjoint
(`Measure.countable_meas_level_set_pos`, `Set.Countable.measure_zero`) → `minkowskiConstant_mul_min_le`,
the defining infimum in multiplied form `h_M · m(ν B) ≤ ν⁺(B)`, whose only case split is zero
balance, where `mul_zero` absorbs `⊤`, against intermediate mass, where `iInf_le` and
`ENNReal.le_div_iff_mul_le` apply, so degenerate levels are never substituted into the infimum and
`h_M` is never divided out → `measurable_min_measure_superlevel`, the measurability of the balance
for an arbitrary `u`, extracted from the inlined `hFmeas` of `tendsto_lintegral_min_superlevel`,
whose proof was migrated rather than duplicated → `lintegral_const_mul` to move `h_M` inside (the
only place `⊤ · I` could appear, after which `⊤` meets `m = 0` only pointwise), `lintegral_mono_ae`,
`setLIntegral_le_lintegral` to enlarge `Ioo 0 1` to the whole axis, and the proved
`lintegral_minkowskiContent_superlevel_le`. `t ↦ ν⁺({u ≥ t})` is still never assumed measurable.

Layer changes: `Geometry/MinkowskiConstant.lean` is new, hole-free, and its local import closure is
the single hole-free `Geometry/MinkowskiContent.lean`. `minkowskiConstant` and
`minkowskiConstant_eq_top_of_subsingleton` moved there verbatim from `KLS/WIP/CheegerInfimum.lean`;
the `pp.all` signatures of all three migrated declarations are byte-identical before and after the
move, so there is no compatibility alias, forwarding declaration, empty shim or duplicated proof.
`smoothConstant`, the layer-cake identities, `tendsto_lintegral_min_superlevel`, the distance
cutoffs and the two unfinished comparisons stay in `KLS/WIP/CheegerInfimum.lean`, which now imports
the new module. `hu01` is unused by the proof and is kept in the signature with the
`unusedVariables` linter silenced, so the statement is not narrowed.

Current holes: **14 = 3 / 6 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**. This round is **not** a
weighted coarea formula, not Sard, not an equality of Cheeger constants and not a completed
comparison chain.

The new module and `Geometry/MinkowskiContent.lean` pass `-DwarningAsError=true`; the new
`build/audit/MinkowskiConstantAudit.lean` has 9 clients and 17 axiom reports, all standard three
axioms, covering a law that is singular against every Haar measure **and** has an atom, zero balance
at the empty and full sets with `h_M = ⊤`, dimension zero forcing the balance integral to vanish,
constant functions, a Dirac law, an explicit `h_M = ⊤` hypothesis forcing the balance integral to
vanish with no division, almost-everywhere superlevel agreement for a Dirac law, measurability of
the balance for an arbitrary `u`, and the one-dimensional instance. The `MinkowskiCoareaAudit`,
`RecoveryAudit`, `DilationAudit` and `GaussGreenAudit` clients re-pass. The three WIP files were
re-elaborated with exactly 3/6/5 hole warnings and no other diagnostics. The final root
verification receipt is `build/verification/latest.json`; the incoming passed receipt matched all
376 files. Read the
[new decision](research/decisions/2026-09-13-minkowski-constant-coarea-product.md).

**Next target: `minkowskiConstant_le_smoothConstant`.** Every API it needs is now checked and no new
analysis is required, but it is not "already done": five side conditions have to be written — three
`le_iInf` layers plus `ENNReal.le_div_iff_mul_le` with `m ≠ 0`, `m ≠ ⊤`; a case split on
`relativePerimeter = ⊤` (`le_top`, recovery sequence not invoked), since
`exists_smooth_recovery_sequence` demands finiteness; unpacking the recovery sequence, where
`ContDiff.of_le` down to `C¹` needs `(1 : WithTop ℕ∞) ≤ ∞` and **`le_top` does not apply** because
`∞` is not that type's top (`by simp` does); `tendsto_lintegral_min_superlevel` with
`U.isOpen.measurableSet`; and `ENNReal.Tendsto.const_mul` with `Or.inl (m ≠ 0)`, which is exactly
what keeps `h_M = ⊤` legitimate, followed by `Tendsto.limsup_eq` and `limsup_le_limsup`. A layering
decision comes with it: the assembled theorem will be `sorryAx`-free while `smoothConstant` and
`tendsto_lintegral_min_superlevel` are still in WIP, so that group should then move down with its
consumers. The opposite direction still needs Sard, weighted coarea,
`lintegral_enorm_gradient_distanceCutoff_le` and
`smoothConstant_mul_lintegral_min_superlevel_le`; none of them moved this round.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Minkowski coarea round: the coarea inequality is proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written.**
`Isoperimetry.lintegral_minkowskiContent_superlevel_le` is proved, with its original statement
text, in the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean`: for every probability
law `ν` on a finite-dimensional real inner-product space and every `C¹` globally Lipschitz `u`,
`∫ ν⁺({u ≥ t}) dt ≤ ∫ ‖∇u‖ dν`, with closed superlevel sets, the integral over the whole real
axis and the unchanged `minkowskiContent` (open thickenings, `ENNReal` truncated subtraction,
`𝓝[>] 0` liminf). The law may be singular or atomic; no density, no absolute continuity, no
bounded range or compact support for `u`, no positive dimension, no extra integrability and no
null superlevel boundary were added. Neither weighted coarea nor Sard is used.

The route is: the local supremum `ballSup u r x = sup_{closedBall x r} u`, Lipschitz with the same
constant, so `0 ≤ (ballSup u r - u)/r ≤ K` and both functions are measurable → the near-neighbour
witness `thickening r {u ≥ t} ⊆ {u < t ≤ ballSup u r} ∪ {u ≥ t}`, giving the strip bound through
`tsub_le_iff_right` and `measure_union_le` rather than a set difference → product measurability of
the strip, `measurable_measure_prodMk_left` and Tonelli, so that Fatou is applied only to the
measurable strip quotient and `t ↦ ν⁺({u ≥ t})` is never assumed measurable → radii `1/(n+1)` with
`Tendsto.liminf_le_liminf_comp` in the direction that only enlarges the original neighbourhood
liminf → the one-sided growth bound `limsup ofReal((ballSup u r_n x - u x)/r_n) ≤ ‖∇u x‖ₑ` from
Fréchet differentiability, with `limsup_lintegral_le` dominated by the constant `K`.

Layer changes: `Geometry/MinkowskiContent.lean` is new, hole-free and has a **zero-module** local
import closure (Mathlib only). `minkowskiContent` and
`measure_closure_eq_of_minkowskiContent_ne_top` moved there with their full names unchanged;
`KLS/WIP/CheegerInfimum.lean` imports the new module and keeps the unfinished Cheeger-infimum
comparisons. No compatibility alias, forwarding declaration, empty shim or duplicated proof.

Current holes: **15 = 3 / 7 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**. This round is **not** a
weighted coarea formula, not Sard, not an equality of Cheeger constants and not a completed
comparison chain.

The new module passes `-DwarningAsError=true`; the new `build/audit/MinkowskiCoareaAudit.lean` has
8 clients and 18 axiom reports, all standard three axioms, covering an arbitrary probability law
that is singular against every Haar measure and an `u` with unbounded range, constant functions,
dimension zero, an atomic (Dirac) law, `ballSup u 0 = u`, the near-neighbour witness, the growth
quotient bound, and `u = id` on the line. The three earlier clients re-pass unchanged. The three
WIP files were re-elaborated with exactly 3/7/5 hole warnings and no other diagnostics. The final
root verification receipt is `build/verification/latest.json`; the incoming passed receipt matched
all 374 files. Read the
[new decision](research/decisions/2026-09-13-minkowski-coarea-inequality.md).

**Next target: `minkowskiConstant_mul_lintegral_min_superlevel_le`.** Its only missing input is the
almost-everywhere agreement of open and closed superlevel masses (the level sets `{u = t}` are
disjoint and `ν` is finite, so only countably many carry mass); the zero- and full-mass levels need
no case split because `⊤ * 0 = 0` in `ENNReal`, and the outer `⊤ * 0` is avoided by moving the
constant inside the integral with `lintegral_const_mul` instead of dividing. After that,
`minkowskiConstant_le_smoothConstant` is pure assembly of the proved recovery sequence with the
proved `tendsto_lintegral_min_superlevel`. The opposite direction still needs Sard, weighted coarea
and `lintegral_enorm_gradient_distanceCutoff_le`; none of them moved this round.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Recovery-sequence round: smooth recovery sequence proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written.**
`RelativePerimeter.exists_smooth_recovery_sequence` is proved in the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean`, with the original
statement text: any finite-dimensional real inner-product space, any Borell density relative to
Lebesgue `volume`, any smooth domain, only the original finite-relative-perimeter hypothesis.
The sequence is globally `C^∞`, globally Lipschitz per term, `[0,1]`-valued, converges to `𝟙_U`
in `L¹(ν)` and has `limsup ∫ ‖∇u_j‖ dν ≤ P_ρ(U)`. No boundedness of the domain, its boundary or
the carrier, no finite total boundary measure, no positive dimension and no extra density
regularity were added; the Lipschitz constants are not claimed uniform in `j`. The finiteness
hypothesis is kept in the statement but is not used by the proof, so it is bound as `_hU`.

The route is: interior density ball and global upper bound from `DensityBounds` (its existing
private ball lemma was exposed, not reproved) → `ν ≪ volume` plus the Haar-null frontier →
exact mollification off the boundary at a fixed dilation, by local constancy on the bump's outer
ball → diagonal choice of `s_j = 1 - 1/(j+2)` with bump radii meeting both
`s_j φ_j.rOut / (1 - s_j) < r` and a vanishing `L¹` tolerance → the previously proved dilation
bound with its prefactor tending to one.

Layer changes: `Geometry/PerimeterRecovery.lean` is new and hole-free, with a 30-module local
closure and no WIP import; `LogConcave/DensityBounds.lean` gained `absolutelyContinuous` and
public `exists_ball_le`; `KLS/WIP/RelativePerimeter.lean` had no content left and was **deleted**;
`KLS/WIP/CheegerInfimum.lean` now imports the new module directly. No compatibility alias,
forwarding declaration or empty shim was used.

Current holes: **16 = 3 / 8 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**. Coarea, Sard, Cheeger
infima and singular-law comparisons are untouched, and this round is **not** a coarea bridge, a
Cheeger bridge or a completion of the relative-perimeter chain.

Eight hole-free modules and three independent clients pass `-DwarningAsError=true`; the new
`build/audit/RecoveryAudit.lean` has 9 clients and 14 axiom reports, all standard three axioms,
checking simultaneously unbounded domain/boundary/carrier, per-term Lipschitz and `[0,1]` range,
arbitrary `L¹` tolerance, zero perimeter giving `limsup = 0`, dimension zero, the whole space as
an unbounded zero-perimeter domain, mollification of the full and of the empty domain (kernel
direction and normalization), and arbitrarily small bump radii. The three remaining WIP files
were actually re-elaborated with exactly 3/8/5 hole warnings. The final root verification receipt
is `build/verification/latest.json`; the incoming passed receipt matched all 372 files. Read the
[new decision](research/decisions/2026-09-13-smooth-recovery-sequence.md).

**Next target: `lintegral_minkowskiContent_superlevel_le`** (Minkowski coarea inequality,
Ambrosio–Di Marino–Gigli 2017, Lemma 3.2), the one genuinely independent analytic lemma left on
the `h_M ≤ h_S` branch. With it, `minkowskiConstant_mul_lintegral_min_superlevel_le` follows from
the almost-everywhere agreement of open and closed superlevel masses, and
`minkowskiConstant_le_smoothConstant` becomes pure assembly of this round's recovery sequence with
the already proved `tendsto_lintegral_min_superlevel`. The opposite direction still needs Sard,
weighted coarea and `lintegral_enorm_gradient_distanceCutoff_le`; none of them moved this round.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Dilated gradient round: quantitative integral bound proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written.**
`RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le` is proved in
`formalization/FunctionalInequalities/KLS/Geometry/RelativePerimeter.lean`, with the original
statement text, normalized surface measure, Lebesgue density, all dimensions, unbounded domains
and carriers, and even infinite relative perimeter. No additional hypotheses were added.

The completed route is: pointwise gradient bound → measurable Tonelli on the locally finite
restricted boundary measure → weighted normalized boundary change of variables → log-concave
kernel-average bound, including exact zero contribution outside Ω. Zero dimension is handled
by empty frontier before converting natural subtraction to the real scaling exponent.

New layers: `Geometry/SurfaceHomothety.lean` provides weighted surface change of variables;
`LogConcave/DensityBounds.lean` owns the migrated density bounds and new positivity/support
interior inclusion; `Geometry/RelativePerimeter.lean` owns the perimeter, indicator-dilation
convergence and proved quantitative bound. Its 29-module local closure contains no WIP import.
`WIP/RelativePerimeter.lean` retains only `exists_smooth_recovery_sequence`.

Current holes: **17 = 1 / 3 / 8 / 5** (RelativePerimeter / AnalyticPrerequisites /
CheegerInfimum / Energy-WIP-Cheeger). Certificates stay **24**; perimeter infrastructure stays
**missing**. Coarea, Sard, Cheeger infima and singular-law comparisons are untouched.

Ten relevant modules and two independent clients pass `-DwarningAsError=true`; 39 axiom reports
(17 dilation + 22 GaussGreen) contain only the standard three axioms. The new clients check
outside-support zero contribution, zero and finite perimeter, dimension-three factor four,
line reflection, dimension zero, and the complete one-dimensional s=1/2 density coefficient.
All four WIP files were actually re-elaborated with exactly the expected 1/3/8/5 hole warnings.
The final root verification receipt is `build/verification/latest.json`; the incoming passed
receipt matched all 368 files. Read the [new decision](research/decisions/2026-09-13-dilated-gradient-integral.md).

**Next target: `exists_smooth_recovery_sequence`.** Select an interior density ball; establish
fixed-dilation L¹ mollification convergence using local constancy away from the null frontier;
combine the existing homothety convergence with diagonal bump radii, then use the now-proved
quantitative bound and convergence of its prefactor to one for the finite-perimeter limsup.
No coarea or Sard is needed for this route. Existing private positivity-interior nonemptiness
can be exposed when needed, without reproducing its proof.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Mollified gradient round: pointwise bound proved, recovery still open (2026-09-13)

**Current state supersedes the dated snapshots below.**
`SmoothDomain.enorm_gradient_mollified_le` is proved, with its original mathematical scope and
normalized `surfaceMeasure`, in `formalization/FunctionalInequalities/KLS/Geometry/MollifiedBoundary.lean`.
The proof uses the proved negative boundary-vector formula, actual boundary integrability,
the integral triangle inequality, unit outward normal and nonnegative bump kernel. No boundedness,
finite total surface measure or positive-dimension hypothesis was added.

The actual import cycle is removed: `Geometry/SmoothDomain.lean` holds the domain foundations;
`Geometry/Mollification.lean` holds the mollified indicator and its regularity; the scalar
Gauss--Green formula moved into `Geometry/GaussGreen.lean`; the mollified gradient formula and
new bound live in `Geometry/MollifiedBoundary.lean`. The two duplicated private indicator/convolution
helpers were consolidated into the original, now public, interfaces. Consumers were migrated;
no compatibility alias or forwarding proof remains. The new consequence module has 15 local
modules in its import closure, **zero WIP imports** and no coarea/Sard dependency.

Current direct holes are **18**: RelativePerimeter **2**, AnalyticPrerequisites **3**,
CheegerInfimum **8**, Energy/WIP/Cheeger **5**. AnalyticPrerequisites now has four public theorems:
three holes, and one filled Sard consequence that still inherits `sorryAx`. Certificates remain
**24**; `lem:relative-perimeter-smoothing` infrastructure remains **missing**.

Validation: seven geometry modules and the independent GaussGreen client pass
`-DwarningAsError=true`; 22 axiom reports use only the standard three axioms. The client includes
the unbounded half-space bound and zero gradient when the bump vanishes on the boundary, plus the
previous orientation, interval, empty-boundary and zero-dimensional checks. Four WIP files were
actually re-elaborated, with exactly 2/3/8/5 expected hole diagnostics and no others.
Default `lake build` passed (3393 jobs). The unified final-source receipt is
`build/verification/latest.json`, produced from the root by `python3 research/verify.py`.
The incoming receipt was passed and all 364 files matched before edits.

**Next target:** `RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le`.
It needs a weighted normalized boundary change of variables (the existing total-mass homothety
identity is insufficient), measurable Tonelli on the locally finite restricted surface measure,
and the convex support argument that makes the kernel-averaged density zero outside Ω.
After that, recovery still needs fixed-dilation mollification convergence in L¹, selection of an
interior density ball, diagonal radii, and the finite-perimeter limsup argument. Neither step
needs coarea or Sard. See the [new decision and exact route](research/decisions/2026-09-13-mollified-gradient-bound.md).
HEAD remains `2965b32`; prior dirty and untracked work is preserved. No commit or push this round.

## Gauss--Green round: the global vector-field theorem is proved (2026-09-13)

The ledger still has 24 certified nodes; this round added none and changed no certificate. The
**global** vector-field Gauss--Green obligation is **no longer a `sorry`**, and the two downstream
formulas it feeds are free of transitive `sorryAx` as well. The four WIP files now total **19**
direct holes (`RelativePerimeter` 3, `AnalyticPrerequisites` 3, `CheegerInfimum` 8,
`Energy/WIP/Cheeger` 5). What changed:

* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/KLS/Geometry/GaussGreen.lean`:**
  `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` —
  `∫_U div F = ∫_{∂U} ⟪F, ν⟫ dℋ^{n-1}` for **any** compactly supported `C¹` vector field on a
  smooth domain. The statement is the one that carried the `sorry`, verbatim: same name, same
  namespace, the same `ContDiff ℝ 1` and `HasCompactSupport` hypotheses, the same `surfaceMeasure`
  normalization and outward orientation. Nothing was added — not boundedness of the domain, not
  finite total surface measure, not higher smoothness of `F`, not `Nontrivial V`.
* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/Analysis/PartitionOfUnity.lean`:**
  `Analysis.exists_finset_sum_eq_of_isOpen_cover`, the finite smooth decomposition. Given an open
  cover of `tsupport F`, it produces a `Finset` and a family `G` with `ContDiff`, compact support,
  **`tsupport (G i) ⊆ W i`** (closed support, so the derivative vanishes outside `W i` too) and
  `∑ i ∈ s, G i x = F x` at **every** point of the space — an identity of functions, which is what
  may be differentiated. Because of that, no partition-derivative term ever appears: the divergence
  splits by `Analysis.divergence_finset_sum` and the flux integrand by `sum_inner`. The route is
  Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate` on `V` modelled on itself, plus
  `LocallyFinite.finite_nonempty_inter_compact` on the compact `tsupport F`.
* **All three kinds of local block are handled, and it takes all three.** The cover is: one
  boundary-chart cylinder per frontier point (`BoundaryChart.self_mem_cylinder`, then the
  chart-local identity of `LocalGaussGreen.lean`), the domain `U` itself
  (`…_of_tsupport_subset_carrier`: no flux, because `∂U` misses the open `U`, and zero volume
  integral by `Analysis.integral_divergence_eq_zero`), and `(closure U)ᶜ`
  (`…_of_tsupport_subset_compl_closure`: both sides vanish). A support lying entirely inside or
  entirely outside the domain is therefore covered, as are an empty support, an empty frontier and
  dimension zero — with no nonemptiness or nontriviality hypothesis anywhere.
* **Integrability is proved, not assumed.** `Analysis/Divergence.lean` gains `traceLM`,
  `continuous_traceLM`, `continuous_divergence`, `hasCompactSupport_divergence` and
  `divergence_finset_sum`; `GaussGreen.lean` proves `norm_outwardNormal_le_one` and
  `integrableOn_inner_outwardNormal`, the latter from `‖ν‖ ≤ 1`, `measurable_outwardNormal` and
  `isLocallyFiniteMeasure_surfaceMeasure_frontier` only — no bound on `surfaceMeasure (∂U)` is used,
  so an unbounded frontier of infinite total measure stays in scope.
* **Migration, not restatement:** `isLocallyFiniteMeasure_surfaceMeasure_frontier` and
  `integrableOn_smul_outwardNormal` moved from `AnalyticPrerequisites` into `GaussGreen.lean`
  unchanged, and `Analysis.fderiv_eq_zero_of_notMem_tsupport` moved down from
  `SubgraphDivergence.lean` to `Divergence.lean`. No compatibility alias, no duplicated proof, no
  forwarding declaration; the single consumer was migrated.

**Count correction.** `AnalyticPrerequisites` now carries **six public theorems and no definitions:
three filled bodies, three direct holes (weighted coarea, its measurability, Sard), and two of the
filled bodies free of transitive `sorryAx`** —
`setIntegral_gradient_eq_integral_smul_outwardNormal` and `gradient_mollifiedIndicator_eq` are
complete theorems now; only `ae_forall_fderiv_ne_zero` still inherits `sorryAx`, from `sard`.
Before this round it carried nine public theorems, five filled bodies, four holes and two filled
bodies free of `sorryAx`. Earlier records keep their original text.

**Still open, explicitly.** Closing Gauss--Green does **not** close the relative-perimeter chain.
Weighted coarea and Sard are untouched, and so are the mollified gradient-integral estimate and the
recovery sequence; `lem:relative-perimeter-smoothing` keeps infrastructure status `missing`, with
refreshed evidence hashes and rewritten gaps, and no ledger certificate or Blueprint anchor
changed. Read the [global Gauss--Green record](research/decisions/2026-09-13-global-gauss-green.md).

## Subgraph divergence round: the chart-local Gauss--Green is proved, the global one is not (2026-09-13)

The ledger still has 24 certified nodes; this round added none and changed no certificate. The
**global** vector-field Gauss--Green obligation of `KLS/WIP/AnalyticPrerequisites.lean` is **still
an explicit `sorry`**, and the scalar form and `gradient_mollifiedIndicator_eq` still inherit it.
The four WIP files still total **20** direct holes (`RelativePerimeter` 3,
`AnalyticPrerequisites` 4, `CheegerInfimum` 8, `Energy/WIP/Cheeger` 5). What changed:

* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/Analysis/SubgraphDivergence.lean`:** the divergence formula
  on a smooth subgraph. For an orthogonal splitting `V = ι H ⊕ ℝ e`, a `C¹` height function
  `g : H → ℝ`, the graph `Ψ y = x₀ + ι y + g y • e` and the region `S` strictly below it, every
  compactly supported `C¹` vector field satisfies
  `∫_S div F = ∫_H ⟪F (Ψ y), ι (-∇g y) + e⟫ dy` (`Analysis.integral_divergence_subgraph`). The
  right-hand side is the **unnormalized** flux: the graph Jacobian `√(1 + ‖∇g‖²)` has already
  cancelled against the denominator of the unit normal, and the tangential `-∇g` term is present.
  No boundedness, no global Lipschitz bound on `g`, no nontriviality of `H`. The route is a
  measure-preserving shear chart (`WithLp 2 (H × ℝ) ≃ₗᵢ V` plus Fubini and fibrewise translation
  invariance — no Jacobian determinant is ever computed), a basis-free trace splitting of the
  divergence (`LinearMap.trace_comp_comm'` plus the rank-one identity of `Analysis/Divergence.lean`),
  and the fundamental theorem of calculus along each fibre. The same module proves
  `Analysis.integral_divergence_eq_zero` — a compactly supported `C¹` field on `H` has divergence
  integrating to zero — by induction on `finrank`, since Mathlib's divergence theorem covers only
  boxes in `Fin (n+1) → ℝ`.
* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/Analysis/GraphIntegral.lean`:** the weighted boundary
  change of variables. The area formula is an identity of *measures of sets*;
  `Analysis.map_graphChartMap_withDensity` upgrades it to
  `map Ψ ((volume.withDensity √(1+‖∇g‖²)).restrict s) = ℋ^k ⌊ (Ψ '' s)` using injectivity and
  measurability of the graph parametrization, and `setLIntegral_image_graphChartMap` /
  `setIntegral_image_graphChartMap` state the resulting change of variables. Only measurability is
  assumed, never integrability. This is the minimal interface the flux needs, not a general area
  or manifold integration library.
* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/KLS/Geometry/LocalGaussGreen.lean`:**
  `KLS.SmoothDomain.BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal` — for a
  compactly supported `C¹` field with `tsupport F ⊆ C.cylinder`,
  `∫_U div F = ∫_{∂U} ⟪F, ν⟫ dℋ^{n-1}`. The support hypothesis is what makes *both* `F` and
  `div F` vanish outside the cylinder, which is what localizes the volume integral and the flux.
  The globally extended graph is **not** identified with `∂U`: the two sets agree only inside the
  cylinder, and the support condition cancels the extra sheet. Boundary integrability is never
  assumed — the restriction steps are pointwise identities of indicator functions — so an
  unbounded frontier of infinite total surface measure stays in scope.
* **Refactor, not restatement:** `KLS.SmoothDomain.isGraphSplitting_tangent` keeps its name and
  statement and is now one line, calling the new general
  `Analysis.isGraphSplitting_orthogonal`; `Analysis.graphChartMap_injective` likewise calls the
  new `graphChartMap_injective_of_perp`. No duplicated proof, no compatibility alias.

**Still open, explicitly.** The global
`integral_divergence_eq_integral_inner_outwardNormal` now needs exactly **one** further piece: a
finite smooth partition of unity subordinate to a cover of the compact support by chart cylinders,
with the partition-derivative terms cancelling. Coarea, Sard and the recovery sequence remain
untouched. Read the
[subgraph record](research/decisions/2026-09-13-subgraph-divergence-and-local-gauss-green.md).
Nothing here registers `lem:relative-perimeter-smoothing`; its infrastructure status stays
`missing`, with refreshed evidence hashes and shortened gaps.

## Boundary chart round: the local smooth graph is proved, Gauss--Green is not (2026-09-13)

The ledger still has 24 certified nodes; this round added none and changed no certificate. The
vector-field Gauss--Green obligation of `KLS/WIP/AnalyticPrerequisites.lean` is **still an explicit
`sorry`**, and the scalar form and `gradient_mollifiedIndicator_eq` still inherit it. The four WIP
files still total **20** direct holes (`RelativePerimeter` 3, `AnalyticPrerequisites` 4,
`CheegerInfimum` 8, `Energy/WIP/Cheeger` 5). What changed:

* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/Analysis/ImplicitGraph.lean`:** the local `C^∞` graph
  representation of a regular level set. For `φ` of class `C^∞` with `φ x₀ = 0` and
  `∇φ x₀ = c • e`, `c > 0`, inside an explicit cylinder `{φ = 0}` is *exactly* the graph
  `Ψ y = x₀ + ι y + g y • e` and `{φ < 0}` is *exactly* the part below it
  (`Analysis.exists_graphRepr`). The height function is **globally** `C^∞`. The route is the
  `C^k` inverse function theorem applied to the flattening chart, plus the openness of the
  invertible operators, which upgrades `ContDiffAt.to_localInverse`'s single-point conclusion to a
  neighbourhood; Mathlib's implicit function theorem gives only strict differentiability at one
  point. The same module proves the gradient identity
  `∇φ(Ψ y) = ⟨∇φ(Ψ y), e⟩ • (ι(-∇g y) + e)` and its normalization.
* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/KLS/Geometry/BoundaryChart.lean`:**
  `KLS.SmoothDomain.exists_boundaryChart` — every frontier point of a smooth domain has such a
  chart, with `∂U ∩ Cyl = Ψ '' param`, `U ∩ Cyl` exactly the region below the graph, and
  `ν = (ι(-∇g) + ν₀)/√(1 + ‖∇g‖²)` along the graph, the sign fixed rather than up to `±`.
  `BoundaryChart.surfaceMeasure_image` is the area identity
  `surfaceMeasure (Ψ '' s) = ∫_s √(1 + ‖∇g‖²)` against the Lebesgue measure of the tangent
  hyperplane, for one chart's parameter set — not for the whole boundary. The local-to-global
  regularity gap is closed by a `ContDiffBump` cutoff **inside** `exists_graphRepr`, so no consumer
  turns a `ContDiffOn` into a `ContDiff` and no global extension is assumed.
* **Migration, not restatement:** `SmoothDomain.outwardNormal` and its four proved lemmas
  (`outwardNormal_eq`, `norm_outwardNormal`, `continuousOn_outwardNormal`,
  `measurable_outwardNormal`) moved out of `AnalyticPrerequisites` into the new `BoundaryChart`
  module, below it, with names and statements unchanged; the single consumer was migrated. No
  compatibility alias, no duplicated proof, no forwarding declaration. The `SmoothDomain` structure
  itself did not move.

**Count correction.** `AnalyticPrerequisites` now carries **nine public theorems and no
definitions: five filled bodies, four direct holes, and only two of the filled bodies free of
transitive `sorryAx`.** Before the migration it carried **thirteen public theorems and one
definition** (`outwardNormal`), nine filled theorem bodies, four holes, six filled theorems free of
`sorryAx`. The "12 obligations, 8 filled" of the 2026-09-12 records subtracted the migrated
`divergence` *definition* from the *theorem* count; those records keep their original text and the
correction is recorded in the new decision record.

**Still open, explicitly.** `integral_divergence_eq_integral_inner_outwardNormal` now needs two
further pieces, one fewer than before: the local Gauss--Green identity on a subgraph (Fubini along
`V ≅ H × ℝ`, the fundamental theorem of calculus in the normal direction, differentiation under a
variable-limit integral in the tangential directions), and a finite smooth partition of unity to
glue the local identities. Coarea, Sard and the recovery sequence remain untouched. Read the
[boundary-chart record](research/decisions/2026-09-13-boundary-chart-and-area-interface.md).
Nothing here registers `lem:relative-perimeter-smoothing`; its infrastructure status stays
`missing`, with refreshed evidence hashes and shortened gaps.

## Gauss--Green round: the area formula is proved, the theorem is not (2026-09-12)

The ledger still has 24 certified nodes; this round added none and changed no certificate. The
two Gauss--Green targets of `KLS/WIP/AnalyticPrerequisites.lean` are **not** complete. What
changed:

* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/Analysis/AreaFormula.lean`:** the codimension-one area
  formula for `C¹` graphs. For a linear isometry `ι : H →ₗᵢ V`, a unit `e` orthogonal to its range
  and `g : H → ℝ` of class `C¹`, the graph map `Ψ y = ι y + g y • e` satisfies
  `ℋ^k (Ψ '' s) = ∫_s √(1 + ‖∇g y‖²) dy` for every measurable `s`, in the normalized convention
  (`Analysis.hausdorffNormalized_image_graphMap`) and in Mathlib's convention
  (`Analysis.hausdorffMeasure_image_graphMap`). No boundedness anywhere; dimension zero included.
  This is the geometric input that the repository's own earlier assessment named as the residual
  sub-obligation of Gauss--Green ("the area formula for Lipschitz graphs"), and Mathlib has only
  the equal-dimension change of variables.
* **Proved, new module `Analysis/Divergence.lean`:** `divergence` (moved down out of WIP) with the
  rank-one trace identity `divergence (η • v) = ⟪∇η, v⟫` for a constant vector `v`.
* **Reduction, not a proof:** `setIntegral_gradient_eq_integral_smul_outwardNormal` (the scalar
  test form, `∫_U ∇η = ∫_{∂U} η ν`) is now *derived* from
  `integral_divergence_eq_integral_inner_outwardNormal` (the vector-field form) by taking
  `F = η • v` and commuting both integrals with the inner product. It therefore still depends on
  `sorryAx`, and so does `gradient_mollifiedIndicator_eq`. Only the vector-field form remains as
  an *independent* Gauss--Green obligation: `AnalyticPrerequisites` goes from 5 direct holes to 4,
  and the four WIP files from 21 to 20.

**Still open, explicitly.** `integral_divergence_eq_integral_inner_outwardNormal` needs three
further pieces, none of which is in Mathlib or in this repository:

1. a `C^∞` implicit-function representation of a `SmoothDomain` frontier as a graph over a tangent
   hyperplane, with the side condition and the identification `ν = (ι(-∇g) + e)/√(1 + ‖∇g‖²)`.
   Mathlib's implicit function theorem gives strict differentiability at one point, not `C¹`
   regularity on a neighbourhood; the `C^k` route goes through `ContDiffAt.to_localInverse`;
2. the local Gauss--Green identity on a subgraph, by Fubini along `V ≅ H × ℝ` plus the fundamental
   theorem of calculus in the normal direction and differentiation under a variable-limit integral
   in the tangential directions;
3. a finite smooth partition of unity subordinate to a cover of the compact support, to glue the
   local identities and cancel the partition derivatives.

Read the [Gauss--Green record](research/decisions/2026-09-12-gauss-green-area-formula.md). Closing
the area formula does **not** register `lem:relative-perimeter-smoothing`, and no Blueprint anchor
or task infrastructure status changed.

## Perimeter-chain interface integration (2026-09-12)

The current ledger still has 24 certified nodes; this round added none. The three interfaces whose
mathematical input was already present in the repository are now proved and wired in, so the WIP
hole count drops from 24 to 21: `RelativePerimeter` 5 → 3, `CheegerInfimum` 9 → 8,
`AnalyticPrerequisites` 5 (unchanged) and `Energy/WIP/Cheeger` 5 (unchanged). Formal certificates
still do not import any of these modules, and no WIP result was registered in the ledger or
anchored in the Blueprint. A completed proof body inside WIP is still not necessarily
`sorryAx`-free; the Sard and mollified-gradient consequences remain concrete examples.

Closed this round, each with only `propext / Classical.choice / Quot.sound`:

* `KLS.hausdorffNormalized_finrank_eq_volume`, from
  `Analysis.hausdorffMeasure_finrank_eq_smul_volume` (ω_n > 0 in every dimension; the
  zero-dimensional case is covered by the general input).
* `KLS.SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`, from
  `Analysis.exists_hausdorffMeasure_levelSet_lt_top` applied in one defining neighbourhood at a
  time. Unbounded domains stay in scope; no hypothesis of finite total boundary measure was added.
* `KLS.Isoperimetry.exists_smooth_approximation_lipschitz`, from the certified
  `Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1`; the `[0,1]` range,
  smoothness, global Lipschitz property and the original measure hypotheses are unchanged.

The import direction that had blocked this is fixed by a module split, not by restating anything:
the base definitions `unitBallVolume / hausdorffNormalized / surfaceMeasure` moved down to
`formalization/FunctionalInequalities/KLS/Geometry/SurfaceMeasure.lean`, and the proved, KLS-independent
Hausdorff and level-set geometry moved out of `AnalyticPrerequisites` into
`formalization/FunctionalInequalities/Analysis/LevelSet.lean`. `RelativePerimeter` imports both;
`AnalyticPrerequisites` keeps only the open Gauss--Green, coarea and Sard obligations and still
imports `RelativePerimeter` for `mollifiedIndicator`. After the migration the prerequisite module
has 13 obligations: 8 filled bodies, 6 without transitive `sorryAx`.

Gauss--Green (C1/C2), coarea, Sard, the smooth recovery sequence, and the singular-law Cheeger
comparison remain open. Closing three interfaces does **not** register the perimeter chain as
proved. Read the [integration record](research/decisions/2026-09-12-perimeter-interface-integration.md),
the earlier [proof record](research/decisions/2026-09-12-outward-normal-interfaces-proofs.md) and
[closeout](research/decisions/2026-09-12-outward-normal-interfaces-closeout.md); both sorry prompts
and the earlier retention record are historical handoffs and keep their original counts.

Read [the audit record](research/decisions/2026-09-12-status-audit-and-wip-retention.md) before using older counts or infrastructure
assessments below. The unconditional singular-law Cheeger comparison remains unregistered; its
absolutely continuous scope is already certified as `cor:absolutely-continuous-relaxation-two-cheeger`.
The dimension-free KLS bound and the uniform conditional-fiber frame inequality remain open.

## Upstream research sync (2026-09-12)

The current research source is `kls-conjecture-search@34b5fcd57fef17089e781616005fe6d3641bd11e`.
Read [the synchronization record](research/decisions/2026-09-12-upstream-research-sync.md) for
wave-four/five results, the two July 2026 preprints, and the next formalization candidates.
The route source key `kls-exploration` is retained as an identifier; its URL and ledger path
now point to the renamed repository. Upstream `proved` with `assumes` remains conditional
here, and `proofs.mode: agent` is not Lean certification. The 24 local certificates are unchanged.

## Mathematical API organization (2026-09-08)

The public frontends are `SmoothTest`, `SmoothGradient`, `WeightedGradient`,
`CovarianceGradient`, and `LocalSlope`; `Ambient` and `Intrinsic` identify the carrier construction.
Probability pushforwards and L² pullbacks occupy their own layers. See [the naming guide](research/naming.md) and [the migration record](research/decisions/2026-09-08-mathematical-api-organization.md).

## Repository identity

- Canonical repository: `https://github.com/numina-functional-inequalities/kls-lean.git`.
- Publication branch: `main`, following
  [`research/explorations/2026-09-03-main-only-workflow.md`](research/explorations/2026-09-03-main-only-workflow.md).
- Phase-one alignment baseline: `5b1b44219050be0290c24e5765166f0298ff1ca4`.
- The Lake package is rooted at `formalization/`, not at the Git root.
- `legacy-fork` and `legacy-upstream` must be treated as read-only historical sources by project
  policy. In particular, `lyw-ops/numina-functional-inequalities-formalization` is not the
  repository named by this handoff and must not be used as the write target.

Verify the live checkout before changing anything:

```bash
git status --short --branch
git branch --show-current
git remote -v
git log -5 --oneline
```

## Read this first

| Purpose | Authority or entry point |
| --- | --- |
| Repository overview | [`README.md`](README.md) |
| Lean layout and build | [`formalization/README.md`](formalization/README.md) |
| Energy foundation boundary | [`formalization/FunctionalInequalities/Poincare/README.md`](formalization/FunctionalInequalities/Poincare/README.md) |
| Mathematical design contract | [`LEAN_DESIGN.md`](LEAN_DESIGN.md) |
| Executable dependency map | [`formalization/blueprint/README.md`](formalization/blueprint/README.md) |
| Certification lifecycle | [`research/a-series/ledger.yaml`](research/a-series/ledger.yaml) and [`research/ledger-schema.md`](research/ledger-schema.md) |
| Node certificates | [`solutions/README.md`](solutions/README.md) |
| Decisions and audits | [`research/decisions/`](research/decisions/) and [`research/explorations/`](research/explorations/) |

Older candidate, freeze, proof, and acceptance records are time-stamped, append-only evidence.
An earlier `drafted` or incomplete state never overrides a later accepted ledger state.
Historical freezes record the statement reviewed at that time; they do not impose permanent
signature stability under the current interface-evolution policy.

The 2026-09-06 follow-ups should be read in this order:

1. [Comparison proof acceptance](research/decisions/2026-09-06-poincare-comparison-proofs.md):
   the twelve Lean comparisons; the 77-label, 27-page snapshot.
2. [Analytic bridge resolution](research/decisions/2026-09-06-analytic-bridge-resolution.md):
   the subsequent analytic appendix and five generic Lean lemmas; the 86-label, 33-page snapshot.
3. [Review clarifications](research/decisions/2026-09-06-blueprint-review-clarifications.md):
   the later fiber-density dependency, BV/Minkowski convention, numerical wording, and Lean
   documentation corrections. Earlier counts describe their own validation runs.
4. [Rayleigh test-class alignment](research/decisions/2026-09-06-rayleigh-test-class-alignment.md):
   the explicit density-lemma reference and the mean correction preserving bounded support
   in the Cheeger--Buser proof.
5. [Workflow and documentation status](research/decisions/2026-09-06-workflow-and-documentation-status.md):
   the owner's CL policy and corrections aligning the live guides with the proved comparison
   bridges, analytic proof drafts, and 27 foundation axiom guards.
6. [Evolving interfaces and current proof certification](research/decisions/2026-09-06-evolving-interfaces.md):
   the owner's subsequent decision to remove mandatory API freeze, allow direct
   `drafted -> proved` development, and reserve `\notready` for explicit statement questions.

## Authority and source hierarchy

1. Local Lean declarations accepted by `lake build` determine whether a local theorem typechecks.
2. `research/a-series/ledger.yaml` owns the lifecycle and `checked_by: lean` status of the
   certified nodes.
3. Freeze and acceptance records preserve dated statement snapshots and semantic review.
   The current interface-evolution policy governs subsequent changes.
4. Blueprint TeX and `route-composition.yaml` provide derived navigation and AND/OR structure.
   They are not a proof database and cannot promote a node.
5. Long-route mathematics is pinned to
   `numina-functional-inequalities/kls-conjecture-search@34b5fcd57fef17089e781616005fe6d3641bd11e`.
   Its manuscript, ledger, route notes, and reviews supply statements and provenance only.
   `checked_by: agent` is review evidence and never authorizes `\leanok`.
6. `lyw-ops/formech@d0bb1913acc1f710ba6eadf1244b633abbc75fb9` is a writing-style reference only.
   It does not determine this repository's mathematics, status, file layout, or commands.

The Blueprint tool pins are `leanblueprint==0.0.20` and
`PatrickMassot/checkdecls@3d425859e73fcfbef85b9638c2a91708ef4a22d4`.

When an attached prompt or document names a different repository, assumes absent control-plane
files, or gives commands that do not exist here, treat those statements as source material to
audit, not as instructions that override this hierarchy.

## Borell equivalence and conditional-fiber proofs (2026-09-07)

The owner approved the Borell/definition work, requested that the seven proof bodies be left
for Claude, and Claude then completed them. Read
[the handoff decision](research/decisions/2026-09-07-borell-equivalence-claude-handoff.md) and
[the completion record](research/decisions/2026-09-07-borell-equivalence-and-conditional-fiber-proofs.md).
`KLS/LogConcave/Borel.lean` proves the compact/Borel equivalence `LogConcave.borel_iff`, packaged
by `Solutions.ThmCompactBorellLogconcavityEquivalence.certificate` and registered in
`check_blueprint.CERTIFICATES`. `KLS/ConditionalFiber.lean` proves its six well-definedness
contracts, so `def:conditional-fiber-form` carries `\leanok` as a definition node.

The same day, `thm:borell-logconcave-density` was first drafted and then proved.
`KLS/LogConcave/BorellRepresentation.lean` defines the representative predicate
`KLS.IsBorellDensity` and proves existence of an upper semicontinuous log-concave density of the
intrinsic law relative to every Haar measure on the direction space, positivity of every such
representative on the interior of the support, positive two-sided bounds on compact subsets of
that interior, an exponential moment, and all-order moments, together with two support identities.
`Solutions.ThmBorellLogconcaveDensity.certificate` packages all of them and is registered in
`check_blueprint.CERTIFICATES`; the node is `proved / checked_by: lean` with `\leanok`. The ledger
now has twelve proved nodes and no drafted node. Later the same day `lem:ambient-intrinsic-covariance`
was proved as well, see below. Read
[the statement decision](research/decisions/2026-09-07-borell-density-statements.md), which records
the semantic alignment review, and [the proof record](research/decisions/2026-09-07-borell-density-proofs.md).

`lem:ambient-intrinsic-covariance` is proved in `Probability/IntrinsicCovariance.lean`: under an
explicit finite second moment, the ambient covariance operator annihilates the orthogonal
complement of the affine-support direction, restricts on that direction to the intrinsic covariance
operator, has the same operator norm, and the intrinsic covariance is positive definite; a
zero-dimensional direction gives zero operators. `Solutions.LemAmbientIntrinsicCovariance.certificate`
packages these, so the ledger then had thirteen proved nodes. This unblocks the definition node
`def:affine-poincare-constant`. Read
[the record](research/decisions/2026-09-07-ambient-intrinsic-covariance.md).

`def:affine-poincare-constant` is now implemented. `Energy/CovarianceGradient/Basic.lean`
defines the globally Lipschitz covariance-weighted gradient pre-energy `Energy.CovarianceGradient.preEnergy ν` with
`Σ = Covariance.operator ν`, its sequential `L²(ν)` relaxation, and the affine specialization
`Energy.CovarianceGradient.Intrinsic.energy μ` on the intrinsic law; `Poincare/CovarianceGradient/Intrinsic.lean` defines
`Poincare.CovarianceGradient.Intrinsic.constant μ` through `Poincare.L2Energy.constant` and proves that a zero-dimensional
direction gives constant zero. `KLS/LogConcave/Covariance.lean` proves the three log-concave
well-definedness contracts: intrinsic finite second moment, almost-everywhere differentiability of
every test by Rademacher, and representative independence of the energy. The Blueprint definition
carries `\leanok` as a definition node and does not enter the ledger. Closability, closed-form
identification and translation invariance are certified by the subsequent nodes below; the
definition alone asserts no Poincaré bound. Read
[the record](research/decisions/2026-09-07-affine-poincare-constant-definition.md).

`lem:covariance-core-closure` was proved on 2026-09-08. `Energy/Relaxation/LinearPMap.lean` proves,
for any closable partially defined operator `T` from a normed space into a Hilbert space, that the
sequential relaxation of `‖T f‖²` is `‖T̄ f‖²` on the domain of the closure and `⊤` outside it (via
a weak-topology-free Hilbert selection lemma), and that graph-norm dense cores have the same
closure. `Energy/Euclidean/WeakDerivative.lean` proves integration by parts for globally Lipschitz
functions against `C_c^∞` tests. `Energy/Euclidean/CovarianceGradient/{Operator,Closable,Core}.lean`
define the weighted gradient operator `g ↦ B ∘ ∇g` on `L²(ν)`, prove it closable under absolute
continuity, null support frontier and local domination of Haar measure, and prove dense domain and
the smooth-core closure identity. `KLS/LogConcave/WeightedGradient.lean` discharges these
hypotheses for every full-dimensional log-concave law and for the intrinsic law of any log-concave
law, and identifies `Energy.CovarianceGradient.Intrinsic.energy` with the operator relaxation for every `B` with
`⟪Σ v, v⟫ = ‖B v‖²`. `Solutions.LemCovarianceCoreClosure.certificate` packages dense domain,
closability, core independence and the relaxation identity; the ledger then had fourteen proved
nodes. Read [the record](research/decisions/2026-09-08-covariance-core-closure.md).

`thm:affine-covariance-relaxation-closed` was proved the same day. `Probability/CovarianceFactorization.lean`
gives a norm factorization `B` of any covariance quadratic form (`⟪Σ v, v⟫ = ‖B v‖²`, spectral theorem);
`Energy/CovarianceGradient/Translation.lean` proves that translating a law gives an `L²`
isometry preserving variance, covariance operator, covariance relaxation and optimal constant;
`KLS/LogConcave/ClosedForm.lean` shows for every log-concave law that the affine pre-energy has
dense realization, that `Energy.CovarianceGradient.Intrinsic.energy μ` is a closed quadratic form with the globally
Lipschitz tests as sequential core, and that it equals the squared-norm energy of the closure of
`B ∇` on the core `ℝ + C_c^∞` (the CMH closed form), with `Poincare.CovarianceGradient.Intrinsic.constant μ` its optimal
constant. `Solutions.ThmAffineCovarianceRelaxationClosed.certificate` packages these; the ledger
then had fifteen proved nodes. Read
[the record](research/decisions/2026-09-08-affine-covariance-relaxation-closed.md).

`lem:affine-poincare-translation-invariance` was proved later the same day.
`Energy/CovarianceGradient/Isometry.lean` transports a law, its covariance operator, the
gradient, the covariance relaxation and its optimal constant along a linear isometric equivalence;
`Poincare/CovarianceGradient/Translation.lean` shows that the ambient translate
`Probability.translateLaw μ b` has the translated affine support with the same direction, that
its intrinsic law is a translate of the isometric image of the intrinsic law of `μ`, and hence that
`Poincare.CovarianceGradient.Intrinsic.constant` is unchanged (for every Borel law), together with a variance-preserving
`L²` isometry intertwining the two affine relaxations and the barycenter identity for translates;
`KLS/LogConcave/Translation.lean` proves that translation keeps compact-set log-concavity,
that log-concave laws have a finite ambient second moment, and that translating by the negative
barycenter centers the law. `Solutions.LemAffinePoincareTranslationInvariance.certificate` packages
these; the ledger then had sixteen proved nodes. Read
[the record](research/decisions/2026-09-08-affine-poincare-translation-invariance.md).

`thm:affine-isotropic-reduction` was proved next. `Energy/CovarianceGradient/LinearEquiv.lean`
transports a law, its covariance operator (conjugated by the map and its adjoint), the gradient,
the covariance relaxation and its optimal constant along any continuous linear equivalence;
`Probability/CovarianceWhitening.lean` gives a self-adjoint whitening of a positive definite
covariance, with `W Σ W = I` but no positivity or uniqueness conclusion for `W`;
`Poincare/LipschitzGradient/Comparison.lean` identifies the optimal constant of
the identity-weighted Lipschitz gradient relaxation with the smooth-test and literature
constants and bounds the covariance relaxation by `‖Σ‖` times it (with the new scaled relaxation
comparison `PreEnergy.sequentialRelaxation_comp_le_mul`); `KLS/LogConcave/Isotropic.lean`
defines the three statements `KLS.IsotropicBound K`, `KLS.CovarianceBound K`, `KLS.AffineBound K`
over every finite-dimensional Euclidean space of a fixed universe and proves their equivalence by
centering and whitening the intrinsic law, together with `KLS.conjecture_of_affineBound`.
`Solutions.ThmAffineIsotropicReduction.certificate` packages these; the ledger then had seventeen
proved nodes. The same inspection recorded `thm:cmh-recovery-affine-poincare-bound` as `missing`
infrastructure (no Lean `W₂`, CMH constant or upstream proofs). Read
[the record](research/decisions/2026-09-08-affine-isotropic-reduction.md).

Isotropy, the isoperimetric scale and the affine covariance Poincaré constant are implemented
definitions. The Dirac raw-energy obstruction is a named, proved library result outside the ledger.
Twenty-five named StatementChecks, the six conditional-fiber guards, the five affine covariance
guards and the Dirac and normal-direction obstruction guards cover the implemented contracts with
the standard three axioms only. The Borell density/moment representation is Lean-certified; the downstream KLS routes
remain unproved. Local certification does not by itself imply publication or a remote CI pass.

## Dirichlet property of the smooth-gradient relaxation (2026-09-10)

`thm:smooth-gradient-relaxation-dirichlet` is proved in `Energy/SmoothGradient/Dirichlet.lean`.
The normal contraction is mollified on the real line (`Energy.NormalContraction.smoothed`: smooth,
`1`-Lipschitz, uniformly within `2/(j+1)` of the contraction); composing a smooth test with it gives
a smooth test with pointwise smaller gradient norm whose `L²` class converges to the contracted
class, which is the relaxed contraction bound on realized tests; the certified contraction-transfer
theorem then gives `Energy.Markovian` and `Energy.Dirichlet` for `Energy.SmoothGradient.relaxation μ`
for every Borel probability law, singular laws and dimension zero included, and the intrinsic-affine
relaxation `SmoothGradient.Intrinsic.energy μ` inherits the property.
`Solutions.ThmSmoothGradientRelaxationDirichlet.certificate` packages Markovianity and both Dirichlet
statements. Read
[the record](research/decisions/2026-09-10-smooth-gradient-relaxation-dirichlet.md).

## One-dimensional log-concave Poincaré bound, sharp constant 4 (2026-09-11)

`thm:one-dimensional-logconcave-poincare` now carries the sharp constant: every compact-set
log-concave law `ν` on `ℝ` has `Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal
(4 * variance id ν)` (`KLS/LogConcave/Line/SharpPoincare.lean`), zero variance included, and the
certificate `Solutions.ThmOneDimensionalLogConcavePoincare.certificate` packages the real and
extended-variance forms with `4`; Bobkov's `12` is a typed corollary and keeps its independent
proof. The proof follows the collaborator audit
`research/explorations/2026-09-11-poincare-constant-4-audit.md`: `Probability/Line/AffineProfile.lean`
(affine quantile model on the unit uniform law, variance closed form, `1/(√A+√B)⁴ ≤ Var`),
`KLS/LogConcave/Line/Profile.lean` (supporting line `ρ ≤ A(1−F)+BF`, profile bound `F(1−F) ≤ σρ`),
`Line/SharpHardy.lean` (tests clipped outside `[a,b] ⊆ Ω` straddling a median, integration by
parts, ground-state identity with boundary control on larger intervals, `Var(clip) ≤ 4·Var·∫f'²`),
and `Line/SharpPoincare.lean` (half-line Hardy bounds anchored at arbitrary interior points, now
generalized in `Line/Hardy.lean`, make the clipping tails vanish; a `(1+δ)`-split finishes). The
Blueprint statement changed from `12` to `4`; the published constant `4` (Alonso-Gutiérrez–Bastero
p. 11, credited to KLS 1995, no proof there) is now locally proved rather than imported. The fiber
corollary `cor:conditional-fiber-twelve-bound` was sharpened to `4C` on 2026-09-12, when it was
proved and certified.
Read [the record](research/decisions/2026-09-11-one-dimensional-logconcave-poincare-four.md).

## One-dimensional log-concave Poincaré bound, constant 12 (2026-09-10)

`thm:one-dimensional-logconcave-poincare` was first proved with Bobkov's constant in
`KLS/LogConcave/Line/Poincare.lean`: every compact-set log-concave law `ν` on `ℝ` has
`Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal (12 * variance id ν)`, zero variance
(one-point affine support) included; this proof is kept as an independent corollary. The
supporting modules are `Probability/Line/Cdf.lean` (distribution function, continuity and
derivative under a density, median, uniform pushforward `map_cdf_eq_uniform`, centered moments
`1/12` and `0`), `Probability/Line/ExpIntegral.lean`, and `KLS/LogConcave/Line/{Density, Hazard,
Hardy, Variance}.lean`: the Borell line density `KLS.LineDensity`, the four-point inequality and the
median hazard bounds `2ρ(m)(1 − F) ≤ ρ`, `2ρ(m)F ≤ ρ`, the integration-by-parts Hardy inequality
giving `SmoothTest.Holds ν (1/ρ(m))²`, and the supporting-line variance bound
`1/(12ρ(m)²) ≤ Var`. The route differs from Bobkov's Cheeger argument and gives exactly the
Blueprint constant `12`; the node moves from an `imported` published input to a `proved` Lean
claim, and `KLS.logConcave_dirac` supplies the Dirac example.
The certificate then packaged the real and extended-variance forms with `12`; it now packages `4`.
Read [the record](research/decisions/2026-09-10-one-dimensional-logconcave-poincare.md).

## Normal-direction raw-energy obstruction (2026-09-10)

`obs:normal-direction-raw-energy` is a proved library obstruction in
`Energy/SmoothGradient/NormalDirection.lean`, outside the ledger like the Dirac obstruction: when
the direction space of the affine support of `μ` is proper, the coordinate `x ↦ ⟪n, x − a⟫` along a
unit normal `n` is zero in `L²(μ)` but is a smooth-gradient test of energy `1`, so
`Energy.SmoothGradient.preEnergy μ` fails `RespectsAmbientFibers`
(`SmoothGradient.not_respectsAmbientFibers`). Two default-build axiom guards were added to
`solutions/FoundationAxiomAudit.lean`. Read
[the record](research/decisions/2026-09-10-normal-direction-raw-energy.md).

## Raw/sequential-core agreement under density hypotheses (2026-09-10)

`thm:smooth-gradient-raw-core-agreement-density` is proved in `Energy/SmoothGradient/Core.lean`.
The Blueprint's density hypotheses are the structure `Energy.SmoothGradient.LocalDensity ν m` (open
carrier `Ω`, `ν(Ωᶜ) = 0`, density `ρ` on `Ω` for a Haar measure `m`, `ρ > 0` a.e. on `Ω`, `ρ⁻¹`
locally essentially bounded; the Blueprint's local bound on `ρ` is not used). They give absolute
continuity, a null support frontier and local domination of `m` by `ν` on compact subsets of `Ω`;
the closability theorem of `Energy/WeightedGradient/Closable.lean` was generalized from the
interior of the support to an arbitrary open carrier (`Probability.LocallyDominatesOn`,
`WeightedGradient.operator_isClosable_of_isOpen`; `LocallyDominates` is now the special case).
Smooth cutoffs put every smooth test in the closure domain of the unit-weight Lipschitz gradient
operator with closure value its gradient, recovery sequences give the Lipschitz relaxation at most
the smooth relaxation, and the closable-operator relaxation formula yields `AgreesOnTests` and
`IsSequentialCoreFor` for `SmoothGradient.preEnergy ν` and `SmoothGradient.relaxation ν`; the
intrinsic law is the named instance. `Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate`
packages both; the ledger has twenty proved nodes. Read
[the record](research/decisions/2026-09-10-smooth-gradient-raw-core-agreement-density.md).

## Conditional-fiber energy comparison (2026-09-11)

`lem:conditional-fiber-energy-comparison` is proved in `KLS/ConditionalFiber/EnergyComparison.lean`.
The fiber hypothesis is `KLS.ConditionalFiber.FiberBound μ ρ κ`: for base-law almost every
nondegenerate fiber, `Poincare.LocalSlope.Intrinsic.constant` of the fiber law is at most
`κ · eVar[T]`. For `μ ≪ m` (any Haar measure) and an admissible frame `ρ`,
`energy_le_of_fiberBound` bounds the conditional-fiber energy of every literature test
(`Energy.LocalSlope.Admissible`) by `κ` times its finite local-slope energy, which is
`κ ∫‖∇f‖² dμ` by `energy_eq_lintegral_gradient`; `literatureConstant_le_of_fiberBound` turns a
form-gap bound `Var_μ ≤ C · D_{μ,ρ}` on `domain μ ρ` into `C_P^lit(μ) ≤ κ C`. The proof transports
`Poincare.LocalSlope.Holds` across a measure-preserving isometric equivalence, so that the intrinsic
constant of a law with full affine support (Haar-absolutely continuous laws; real laws with nonzero
variance) is the infimum of its coordinate constants and a finite bound on it is a per-test
inequality; identifies the local slope of the line slice `t ↦ f(z + tθ)` with `|⟪θ, ∇f⟫|` at
Rademacher points; pushes the Rademacher null set and square integrability through the joint law
and the disintegration; and finishes with Tonelli and the frame identity.
`Solutions.LemConditionalFiberEnergyComparison.certificate` packages both conclusions; the ledger
has twenty-four proved nodes. The statement was written first as a `sorry` skeleton with
sentence-by-sentence alignment, then proved; read
[the statement record](research/decisions/2026-09-11-conditional-fiber-energy-comparison-statement.md)
and [the proof record](research/decisions/2026-09-11-conditional-fiber-energy-comparison-proofs.md).
Several private helpers (the `Holds` isometry transport, the two full-affine-support criteria, the
`evariance` transport, the fiber-wise almost-everywhere lemmas) belong in shared modules and are
listed in the proof record for a later move. `affineSupport_eq_top_of_absolutelyContinuous` was the
first of them to be made public, without a type change, for the corollary below. The downstream
corollary `cor:conditional-fiber-twelve-bound` is now proved and certified; see the next section.

## Cheeger identification, absolutely continuous scope (2026-09-12)

`cor:absolutely-continuous-relaxation-two-cheeger` is proved in `Energy/Cheeger.lean` and certified
by `Solutions.CorAbsolutelyContinuousRelaxationTwoCheeger.certificate`, the twenty-fourth ledger
node. For a law whose intrinsic law is absolutely continuous with respect to a Haar measure on the
direction space, the smooth-gradient relaxation of the intrinsic law is the relaxed squared local
slope, hence `𝓔^can_μ = 2 Ch_μ` on ambient `L²(μ)`; every compact-set log-concave law satisfies the
hypothesis through the certified `lem:logconcave-intrinsic-absolute-continuity`, so the
identification is available throughout the KLS routes.

`Ch_μ` is the Blueprint's own local-slope convention, fixed by
`Energy.Cheeger.energy := Cheeger.ofLocalSlope` and nowhere else; the asymptotic-Lipschitz
relaxation is a separate definition and only the unconditional comparison
`LocalSlope.relaxation ≤ AsymptoticLipschitz.relaxation` is proved. The material that used to sit
in the single WIP module was split: `Energy/LocalSlope/Relaxation.lean` (both pre-energies and
their `L²` relaxations) and `Energy/Cheeger.lean` (the Cheeger energy, its affine-support
transport, the absolutely continuous identification and the log-concave corollary) are registered
and `sorry`-free, while `Energy/WIP/Cheeger.lean` now contains **only** the five open obligations
of the singular case, of which two are genuine (`LocalSlope.relaxation_eq_asymptoticLipschitz`,
`SmoothGradient.relaxation_eq_localSlope`) and three are their immediate consequences. The
unconditional `thm:smooth-gradient-relaxation-two-cheeger` stays open and uncertified. Read
[the statement record](research/decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md),
[the proof record](research/decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-proofs.md)
and [the registration record](research/decisions/2026-09-12-cheeger-absolutely-continuous-registration.md).

## Log-concave conditional fibers (2026-09-12)

`cor:conditional-fiber-twelve-bound` is proved in `KLS/LogConcave/ConditionalFiber.lean` and
certified by `Solutions.CorConditionalFiberTwelveBound.certificate`, the twenty-third ledger node.
For a compact-set log-concave `μ ≪ m` (any Haar measure) with an admissible frame `ρ`, the
certificate packages the four steps of the Blueprint proof: base-law almost every conditional
kernel `kernel μ ρ b` is a compact-set log-concave law on `ℝ`; hence `FiberBound μ ρ 4`; hence
`D_{μ,ρ}(f) ≤ 4 ∫‖∇f‖² dμ < ∞` on the literature test domain; hence `C_P^lit(μ) ≤ 4 C` from a
finite form-gap bound `C`. The Blueprint corollary, which previously recorded the literature
constant `12`, is restated with the sharp `4` supplied by
`thm:one-dimensional-logconcave-poincare`; the `12` versions remain as
`conditionalFiber_energy_le_twelve_mul_of_four` and
`conditionalFiber_literatureConstant_le_twelve_mul_of_four`.

The three gaps recorded with the statement skeleton are closed by new modules.
`Probability/Line/BrunnMinkowski.lean` proves compact one-dimensional Brunn--Minkowski, its
inner-regular convex-combination form, and the one-dimensional Prékopa--Leindler inequality with no
boundedness hypothesis; `KLS/LogConcave/Line/OfDensity.lean` turns it into `LineDensity.logConcave`,
the converse of `LogConcave.exists_lineDensity`. `Probability/HaarLine.lean` builds the linear
equivalence `θ^⊥ × ℝ ≅ E` and the Fubini splitting `c · ∫G dm = ∬G(z + sθ)`, the proportionality
constant depending on `θ` and never being evaluated. `KLS/ConditionalFiber/SliceKernel.lean` builds
the explicit slice kernel with density `t ↦ p(z + tθ)/Z(θ, z)`, proves
`baseLaw ⊗ₘ sliceKernel = jointLaw`, and concludes `ae_sliceKernel_eq` from Mathlib's uniqueness of
conditional kernels. Base points with vanishing or infinite slice mass carry a Dirac law, which is
log-concave by `KLS.logConcave_dirac`, so the assembly discards no exceptional set. Read
[the statement record](research/decisions/2026-09-11-conditional-fiber-twelve-bound-statement.md)
and [the proof record](research/decisions/2026-09-11-conditional-fiber-twelve-bound-proofs.md).
The route's remaining gate is `q:conditional-fiber-frame`, still open: no frame bound, no Poincaré
inequality for `μ` and no KLS statement follows from this corollary.

## Closed conditional-fiber form (2026-09-11)

`lem:conditional-fiber-form` is proved in `KLS/ConditionalFiber/Closed.lean`. The form of
`def:conditional-fiber-form` is packaged as the extended functional
`KLS.ConditionalFiber.functional μ ρ` on `L²(μ)`, and `KLS.ConditionalFiber.dirichlet` proves
`Energy.Dirichlet`: dense finite domain, lower semicontinuity, the extended quadratic identities and
the normal-contraction (Markov) property. The proof is the jump representation
`energyAt_eq_jump_div`: on a nondegenerate fiber the normalized variance is the squared jump
integral against the symmetric two-point measure `μ_{θ,z} ⊗ μ_{θ,z}` divided by `2 Var(T)`, using
the new two-point variance identity `Probability.two_mul_evariance_eq_lintegral_prod` (valid in
`[0, ∞]` without square integrability). Symmetry and reversibility are read as this representation
together with the swap invariance `twoPointMeasure_swap`. Closedness disintegrates an
almost-everywhere convergent subsequence through the joint law and applies Fatou on the two-point
space and on the base law; a globally `L`-Lipschitz test has energy at most `d L²`
(`energy_le_of_lipschitzWith`), so the smooth compactly supported core lies in the finite domain.
The Lean theorem needs no log-concavity, density, second moment or frame identity; the Blueprint
scope is a typed application. `Solutions.LemConditionalFiberForm.certificate` packages the Dirichlet
property, the jump representation, the swap invariance and the Lipschitz bound; the ledger has
twenty-one proved nodes. Read
[the record](research/decisions/2026-09-11-conditional-fiber-form.md). The same session recorded
`prop:weighted-spectator-obstruction` (no Lean statement of the stochastic-localization objects of
`ass:weighted-package`; no SDE theory in the pinned Mathlib) and `lem:relative-perimeter-smoothing`
(no smooth-domain surface measure, Gauss--Green or several-variable BV in the pinned Mathlib) as
`missing` infrastructure with concrete gaps; read
[the assessment](research/decisions/2026-09-11-spectator-and-relative-perimeter-infrastructure.md).
On 2026-09-12 those gaps first became seventeen KLS-independent typed obligations in `formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean`:
isodiametric inequality via Prékopa--Leindler and Brunn--Minkowski (pins only the normalization of
`surfaceMeasure`; unlocks no node), Lipschitz-graph form of regular level sets with locally finite
`μH[n-1]`, Gauss--Green with an outward normal for `SmoothDomain`, weighted coarea for Lipschitz
functions, and Sard with the sharp `C^n` exponent. Two findings: the "restricted `μH[n-1]` is a
locally finite measure" form of the level-set statement is false for level sets inside an open set
(graph of `sin(1/x)`) and was replaced by a pointwise statement; and the only load-bearing gaps are
Gauss--Green (whose residual sub-obligation is the area formula for Lipschitz graphs), coarea and
Sard. Read [the statement record](research/decisions/2026-09-12-relative-perimeter-prerequisites-statement.md)
and [the proof prompt](research/decisions/2026-09-12-relative-perimeter-prerequisites-sorry-prompt.md).
The subsequent [proof round](research/decisions/2026-09-12-relative-perimeter-prerequisites-proofs.md)
filled 12 of those 17 bodies, leaving 5 explicit holes. Of the 12 filled bodies, 10 are free of
`sorryAx`; the Sard restatement and mollified-gradient formula still depend on unproved inputs.
The file remained unregistered, and at that point the companion perimeter/Cheeger files still had
5/9 holes. Those counts are the historical state of that round; the current numbers, and the
migration of the isodiametric/Hausdorff and level-set results out of that file into
`formalization/FunctionalInequalities/Analysis/LevelSet.lean`, are recorded in the section
"Perimeter-chain interface integration (2026-09-12)" at the top of this file.

## Current certified state

The local proof-atlas extension is described in
[`research/verification.md`](research/verification.md) and
[`research/decisions/2026-09-06-local-proof-atlas.md`](research/decisions/2026-09-06-local-proof-atlas.md).
`python3 research/verify.py` checks the current source snapshot, every Blueprint Lean anchor,
all twenty-four certificates and local module kernel replay. It also compares the elaborated local
statement-definition closure with the explicit golden and audits twenty-five named definition checks.
Afterwards export and query the task atlas. Task schema version 2 separates verification from
infrastructure assessment (`available`, `missing`, `unchecked`); these do not change mathematical
classification. Finish decisions before the final run so the resulting receipt stays current.
The new `FunctionalInequalities.KLS.Conjecture` is only a proposition declaration, with explicit
literature-facing definitions and typed checks. It is not itself a proved ledger node.
The weighted smooth-approximation/literature-comparison chain is the prioritized formalization
pilot. Its first node, `lem:covariance-test-core-density`, is now proved: all four contracts are
packaged by `Solutions.LemCovarianceTestCoreDensity.certificate`, with default-build transitive
axiom guards. The ledger records `proved / checked_by: lean`; the local approximation adapter
is assessed as `available`. See the
[acceptance record](research/decisions/2026-09-06-weighted-approximation-acceptance.md).
`thm:smooth-lipschitz-constant-equivalence` now has eight proved interfaces in
`Energy/LocalSlope/Gradient.lean` and `Poincare/LocalSlope/SmoothTestComparison.lean`.
The sole certificate in `solutions/ThmSmoothLipschitzConstantEquivalence.lean` packages all eight;
it and every component have default-build axiom guards. The ledger records
`proved / checked_by: lean`. Read the
[proof record](research/decisions/2026-09-06-smooth-literature-proofs.md).
The general log-concave extension is now proved as well. `KLS/LogConcave/AbsoluteContinuity.lean` derives
intrinsic absolute continuity directly from compact-set log-concavity, and
`KLS/LogConcave/Poincare.lean` identifies the selected and literature constants
without an added density premise. Two separate certificates record these exact results; the
full Borell density representative and moment theorem is separately certified by
`Solutions.ThmBorellLogconcaveDensity.certificate`. Read the
[general log-concave proof record](research/decisions/2026-09-06-general-logconcave-comparison.md).

Lean and Mathlib are pinned to `v4.33.0`. The production ledger contains twenty-four proved nodes,
each with `status: proved` and `checked_by: lean`.

| Ledger node | Public certificate |
| --- | --- |
| `lem:linear-test-lower` | `Solutions.LemLinearTestLower.certificate` |
| `lem:poincare-tensorization` | `Solutions.LemPoincareTensorization.certificate` |
| `lem:poincare-finite-tensorization` | `Solutions.LemPoincareFiniteTensorization.certificate` |
| `lem:poincare-gaussian-one-dimensional` | `Solutions.LemPoincareGaussianOneDimensional.certificate` |
| `lem:ambient-intrinsic-poincare-comparison` | `Solutions.LemAmbientIntrinsicPoincareComparison.certificate` |
| `lem:legacy-relaxed-poincare-comparison` | `Solutions.LemLegacyRelaxedPoincareComparison.certificate` |
| `lem:covariance-test-core-density` | `Solutions.LemCovarianceTestCoreDensity.certificate` |
| `thm:smooth-lipschitz-constant-equivalence` | `Solutions.ThmSmoothLipschitzConstantEquivalence.certificate` |
| `lem:logconcave-intrinsic-absolute-continuity` | `Solutions.LemLogConcaveIntrinsicAbsoluteContinuity.certificate` |
| `thm:selected-literature-constant-equivalence` | `Solutions.ThmSelectedLiteratureConstantEquivalence.certificate` |
| `thm:compact-borell-logconcavity-equivalence` | `Solutions.ThmCompactBorellLogconcavityEquivalence.certificate` |
| `thm:borell-logconcave-density` | `Solutions.ThmBorellLogconcaveDensity.certificate` |
| `lem:ambient-intrinsic-covariance` | `Solutions.LemAmbientIntrinsicCovariance.certificate` |
| `lem:covariance-core-closure` | `Solutions.LemCovarianceCoreClosure.certificate` |
| `thm:affine-covariance-relaxation-closed` | `Solutions.ThmAffineCovarianceRelaxationClosed.certificate` |
| `lem:affine-poincare-translation-invariance` | `Solutions.LemAffinePoincareTranslationInvariance.certificate` |
| `thm:affine-isotropic-reduction` | `Solutions.ThmAffineIsotropicReduction.certificate` |
| `thm:smooth-gradient-relaxation-dirichlet` | `Solutions.ThmSmoothGradientRelaxationDirichlet.certificate` |
| `thm:one-dimensional-logconcave-poincare` | `Solutions.ThmOneDimensionalLogConcavePoincare.certificate` |
| `thm:smooth-gradient-raw-core-agreement-density` | `Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate` |
| `lem:conditional-fiber-form` | `Solutions.LemConditionalFiberForm.certificate` |
| `lem:conditional-fiber-energy-comparison` | `Solutions.LemConditionalFiberEnergyComparison.certificate` |
| `cor:conditional-fiber-twelve-bound` (the label keeps the literature `12`; the node states `4C`) | `Solutions.CorConditionalFiberTwelveBound.certificate` |
| `cor:absolutely-continuous-relaxation-two-cheeger` | `Solutions.CorAbsolutelyContinuousRelaxationTwoCheeger.certificate` |

The reusable library also proves intrinsic real `L²` mean, centering and variance; extended
energies; sequential relaxation and recovery; quadratic relaxation as a closed quadratic form;
the ambient smooth-gradient closed form; affine support and intrinsic `L²` equivalence; the
intrinsic-affine closed form; and the generic optimal-constant order law. These are foundational
theorems, not a proof of KLS.

`Energy/Relaxation/Approximation.lean` contains the shared concrete-test selection steps used by
lower semicontinuity and recovery. The default build also compiles the usage and boundary examples
in `examples/PoincareFoundation.lean` and the 27 foundation and comparison guards in
`solutions/FoundationAxiomAudit.lean`. The four previous certificates retain their public contracts; two new certificates package the
comparison results with unchanged theorem signatures.

The comparison batch in `solutions/LemAmbientIntrinsicPoincareComparison.lean` and
`solutions/LemLegacyRelaxedPoincareComparison.lean` now has five and seven proved comparisons.
They are exported by `Poincare.Foundation` and the root aggregate. All 12 theorem dependencies
and both certificates have axiom guards. Read the
[comparison guide](formalization/FunctionalInequalities/Poincare/Euclidean/README.md) and
[proof acceptance](research/decisions/2026-09-06-poincare-comparison-proofs.md).

## Current mathematical boundary

The Blueprint selects the intrinsic-affine smooth-gradient relaxation as the repository-facing
canonical frontend. Its optimal constant now equals the literature constant for every
finite-dimensional log-concave law; equality of energies is a separate question.
The generic `Poincare.L2Energy.constant μ E` remains an optimizer parameterized by an
arbitrary energy; it is not, by itself, the selected Poincare constant.

The following statements are not currently Lean-certified:

- unconditional identification with `2 Ch_μ` for arbitrary singular intrinsic laws, and equality
  with the asymptotic-Lipschitz convention. The local-slope identification is certified under
  intrinsic absolute continuity, hence for every log-concave law; the Dirichlet property is
  certified for every Borel probability law;
- Cheeger--Poincare comparison, self-adjoint generator, and spectral-gap interfaces needed by the
  long routes; the closed covariance form, the ambient translation invariance of the affine
  constant and the affine/isotropic reduction (equivalence of the three KLS formulations for
  each fixed `K`) are now certified.

The 2026-09-06 analytic-comparison follow-up supplies complete written arguments for the
locally Lipschitz approximation, relative-perimeter Cheeger infimum, and CMH covariance-core
identification in Blueprint Appendix A. The approximation lemma and the covariance-core closure
are now Lean-certified. The exact smooth-domain recovery theorem is proved as
`RelativePerimeter.exists_smooth_recovery_sequence`; its separate Blueprint registration has
not been completed. Gauss–Green, weighted coarea through locally Lipschitz functions and smooth
Sard are proved. The sharp finite-regularity Sard theorem is the remaining analytic WIP hole
and is not needed by the smooth superlevel construction. The remaining Cheeger-infimum work
is the integrated superlevel bound and reverse comparison; the forward comparison is proved.
Five generic comparison theorems
are proved in Lean, with the foundation audit extended to 27 guards. See
`research/decisions/2026-09-06-analytic-bridge-resolution.md` for their exact scope and evidence.

The proved smooth-test-to-relaxed bridge does **not** require raw test/core agreement. One
direction uses the defining relaxation upper bound on each smooth test. The other uses recovery
sequences and continuity of `L²` variance. Raw/core agreement is a separate, stronger question.
It cannot hold without extra hypotheses: for `μ = δ₀`, the functions `0` and `x` represent the
same `L²(μ)` class but have raw gradient energies `0` and `1`.

Likewise, `ClosedQuadratic` contains no Markov property. The generic contraction-transfer theorem
is conditional; the concrete smooth-gradient Dirichlet property is now established separately by
mollifying the contraction (`Energy.SmoothGradient.dirichlet`).

## KLS route status

The target `conj:kls` is open. TeX `\uses{...}` records logical AND. The route sidecar records
that any one active branch may discharge the target. Its shared requirements are the
selected/literature frontend comparison and the affine/isotropic normalization adapter (both now
Lean-certified); they are repository-facing adapters and are not asserted to be premises of every
upstream argument.

- Eldan localization: the tight-prefix Carleson gate is open; its consumption theorem is proved
  only in the pinned upstream, with agent review.
- Moment-map spectral: the fixed-eigenfunction full-damping occupation estimate is open; the
  sufficiency implication is conditional and agent-reviewed upstream.
- Moment-map CMH: the recovery-envelope assumption is open; its sufficiency implication is
  conditional and agent-reviewed upstream. It is a sufficient condition, not a reformulation of
  KLS.
- Conditional-fiber frame: the test-independent frame question is open. The structural form
  statement `lem:conditional-fiber-form` has pinned upstream agent review and is now also
  Lean-certified (`Solutions.LemConditionalFiberForm.certificate`, for every Borel law and every
  direction law); the local energy comparison with an explicit finite input `κ`,
  `lem:conditional-fiber-energy-comparison`, is Lean-certified as well
  (`Solutions.LemConditionalFiberEnergyComparison.certificate`, for Haar-absolutely continuous
  laws and admissible frames). The one-dimensional input `thm:one-dimensional-logconcave-poincare` is now the sharp local Lean
  theorem `4 Var` (Bobkov's `12 Var` a corollary), and the log-concave specialization
  `cor:conditional-fiber-twelve-bound` that consumes it is Lean-certified too
  (`Solutions.CorConditionalFiberTwelveBound.certificate`), restated with the sharp `4C`; the
  literature `12C` is its immediate weakening. Failure of the natural simplex
  root frame does not refute the all-frame question. The frame construction uses positive
  dimensions; zero-dimensional KLS has zero variance and needs no frame. The sidecar explicitly
  includes affine/isotropic reduction for the passage to all affine supports.

The literal global-operator-norm weighted Eldan-B package is refuted in the pinned manuscript.
It is retained only as historical provenance and must not appear among the active alternatives.
Any replacement branch needs an explicit mathematical statement, traceable provenance, and an
accurate route status. A separate API freeze is not required.

The route chapter is a KLS-facing interface summary, not the transitive closure of the upstream
ledger. Missing Riccati, stochastic, moment-map and recovery inputs must be
formalized explicitly before an active route can become a Lean proof; the one-dimensional
`4 Var` input is now Lean-certified; the older `12 Var` bound follows as a corollary.

## Reproducible checks

From the repository root:

```bash
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 research/atlas.py check
python3 -m unittest discover -s research/tests -p 'test_*.py'
(cd formalization && lake build)
python3 research/verify.py
python3 research/atlas.py export
python3 research/atlas.py ready
```

`verify.py` already runs the structural checks, tests and build above, then the statement golden,
declaration/axiom audit and replay. The individual commands are useful for diagnosing a failed gate.
`python3 research/statement_snapshot.py check` builds and compares just the public statement
definition closure. Baseline changes require a new decision and the explicit update command in
[`research/verification.md`](research/verification.md); no automatic regeneration or API freeze.

For rendered Blueprint artifacts, create a temporary environment once and run:

```bash
python3 -m venv /tmp/kls-blueprint-venv
/tmp/kls-blueprint-venv/bin/pip install -r formalization/blueprint/requirements.txt
/tmp/kls-blueprint-venv/bin/python formalization/blueprint/build.py all
```

The generated PDF, web tree, and `lean_decls` file are ignored outputs. Do not edit them by hand.
A local pass, a pushed commit, and remote CI are three different facts; record only the one that
was actually checked for the named SHA.

For `575c82c` the `Lean certification` workflow passed and the `Lean Blueprint` workflow failed at
`checkdecls`, because the pinned checker imports every `lean_lib` root and the never-built `Dev`
scratchpad library had been declared. The library declaration is removed locally (the file stays,
loaded with `lake env lean Dev/Search.lean`); see
[the CI record](research/explorations/2026-09-07-blueprint-ci-checkdecls-dev-library.md). The fix
takes effect with the next push.

The 2026-09-08 semantic review and the owner's subsequent publication authorization are recorded
in [the affine-foundations publication CL](research/decisions/2026-09-08-affine-foundations-publication.md).
It corrects the whitening contract's wording and obsolete Borell status summaries, and records
the restoration of the reviewed foundation tree while retaining the earlier remote revert in
history. The candidate's verification receipt and exact-SHA GitHub workflows determine the
publication and CI evidence; earlier local-only records retain their dated meaning.

## Change discipline and next stages

- Owner workflow instruction (2026-09-06): “后面我们除了大的推送其他的都不用CL”.
  Use CL only for large pushes. Routine analysis, edits, documentation maintenance, and small
  pushes proceed without a CL workflow. Run local checks appropriate to the change.
- Owner interface policy (2026-09-06): public Lean interfaces may evolve, including proved
  interfaces. Do not require a freeze before proof work; new nodes may move directly from
  `drafted` to `proved`. There is no default backward-compatibility promise.
- `proved`, `checked_by: lean`, and `\leanok` certify the current statement and proof. After
  interface changes, migrate consumers and rerun the relevant build, semantic, and axiom checks.
  Record changes to mathematical assumptions, conclusions, domains, or normalization explicitly;
  synchronize the ledger and Blueprint and check whether the original goal is still covered.
  An unproved revision returns to `drafted` / `checked_by: null` without `\leanok`.
- Reserve Blueprint `\notready` for an explicit unresolved statement choice, such as its test
  domain or normalization. Possible future API changes alone do not justify the marker.
  Historical `frozen` records remain review snapshots; see `research/ledger-schema.md`.
- Public API naming follows [research/naming.md](research/naming.md): use namespaces for object
  roles and retain theorem conditions needed to distinguish mathematical claims.
- Keep decisions and explorations append-only. Record a correction in a new file instead of
  rewriting the historical state.
- Ordinary Mathlib `C∞` is `ContDiff ℝ ∞`; `ContDiff ℝ ⊤` is analytic.
- Do not modify production ledger statements, route status, or Lean claims merely to make a
  diagram pass.

The next proof workstreams are deliberately separate; their numbering is not a fixed scheduling
decision:

1. Build the Cheeger, generator, and spectral interfaces on top of the now-proved Borell
   density/moment representation, the closed affine covariance form, its translation invariance
   and the affine/isotropic reduction.
2. Formalize one long KLS branch after an explicit branch-selection decision. The present route
   ordering is a navigation order, not a fixed scheduling priority. On the conditional-fiber
   branch, `cor:conditional-fiber-twelve-bound` now has its one-dimensional input
   `thm:one-dimensional-logconcave-poincare`, the structural form lemma
   `lem:conditional-fiber-form` and the comparison lemma
   `lem:conditional-fiber-energy-comparison` (fiber disintegration of the gradient energy)
   certified; what remains for the corollary is the log-concavity and nondegeneracy of almost every
   conditional fiber of a log-concave law, which instantiates `FiberBound` with `κ = 4`.

The ambient/intrinsic, smooth-test/relaxed, and general log-concave literature constant equalities
are Lean-certified, and so is the Borell density/moment representation of the intrinsic law. KLS,
`2 Ch_μ`, and the long routes still require their own local proofs; the Dirichlet property of the
smooth relaxation, the one-dimensional `12 Var` bound, raw/core agreement under local density
hypotheses, the Dirichlet structure of the conditional-fiber form and its comparison with the gradient energy under a fiber Poincaré input are certified. Unrestricted raw/core agreement is refuted by the recorded Dirac example
and, for the ambient pre-energy, by the normal-direction obstruction on proper affine supports.

## 全库命名补充整理（2026-09-08）

全库声明作用域和文件归属已进一步整理：33 个公共短名、12 个模块路径，
881 个公共签名及 1085 项展开后的类型/定义闭包核对一致。完整记录见
[research/decisions/2026-09-08-library-naming.md](research/decisions/2026-09-08-library-naming.md)。
最终验收读取 `build/verification/latest.json` 并核对当前源码快照；工作区改动尚未提交。
