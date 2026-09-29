# Energy's five holes closed: `𝓔^can = 2Ch` proved for singular laws, final WIP module removed, certificate 26

2026-09-19, **implementation and registration round**, following the same day's [Energy route investigation](2026-09-19-energy-slope-route.md). Two proof sessions worked in parallel
(A: sandwich argument; B/C: mollified recovery and density), with integration, migration, and registration in this session. Results:

* **All five holes proved**: `SmoothGradient.relaxation_eq_localSlope`, `LocalSlope.relaxation_eq_asymptoticLipschitz`,
  `Cheeger.energy_eq_ofAsymptoticLipschitz`, `SmoothGradient.relaxation_eq_two_mul_cheeger`, and
  `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger`, moved into the new `Energy/Cheeger/Identification.lean` with
  **byte-identical `pp.all` signatures** (empty `diff` on 978 printed lines). `Energy/WIP/Cheeger.lean` was deleted, removing `Energy/WIP/` as well.
  **The repository has no remaining WIP modules; direct holes 5 (0/0/5) → 0.**
* **Certificate 26**: `solutions/ThmSmoothGradientRelaxationTwoCheeger.lean` registers `thm:smooth-gradient-relaxation-two-cheeger`
  (`certificate μ`: for **any** Borel law, the two relaxations of its intrinsic law agree and `𝓔^can_μ f = 2·Ch_μ f`; `conventions_agree ν`), with 4 axiom guards.
  Certificates **25 → 26**.

No commit or push. Starting point: `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; starting passed receipt
`build/verification/20260918T141537.829419Z/report.json`: 10 gates, 237 module replays, 650 entries, snapshot `f91b06cac5cf4d62e270ae9ec48c1d6c2459fa53583be0b4f06a51d7baa3aa4c`.

## Boundaries

Dimension-free KLS remains open; the Buser direction of Cheeger–Buser is unproved. No compatibility aliases, restatements of existing theorems, or weakened proved conclusions are added.
`cor:absolutely-continuous-relaxation-two-cheeger` remains unchanged as a special case.

## Three new modules

| Module (lines) | Content |
| --- | --- |
| `Energy/Euclidean/SlopeComparison.lean` (218) | `A1`: the asymptotic Lipschitz constant of a smooth test equals its gradient norm pointwise (`SmoothGradient.Test.asymptoticLipschitz_apply`, general form `AsymptoticLipschitz.apply_eq_norm_gradient`); `A2` `asymptoticLipschitz_relaxation_le`; `A3`: collapsing the sandwich, `LocalSlope.relaxation_eq_asymptoticLipschitz_of_smoothGradient` |
| `Energy/Euclidean/SlopeRecovery.lean` (659) | `B1` `SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith` (fixed-radius mollification, inheritance of local Lipschitz bounds, reverse Fatou); `B2` `locallyLipschitz_mul`; `B3` `exists_lipschitzWith_of_eq_zero_outside_ball`; `B4`, `B5`: one-moving-point Leibniz bounds for the two slopes |
| `Energy/Euclidean/SlopeDensity.lean` (1202) | `C1` `LocalSlope.measurable_apply`; `C2` `LocalSlope.exists_patch` (`exists_partition` + `exists_thickening_pairwise_disjoint` + `exists_patch_of_isCompact`); `C4` `SmoothGradient.relaxation_le_localSlope_of_lipschitzWith`; `C5` `…_of_admissible`; `C6` `SmoothGradient.relaxation_le_localSlope` |

Three implementation corrections; all route statements themselves were proved literally:

* The library form of `C2` proves an extra conclusion: `|F x − f x| ≤ 2L + 2α` for **every** `x`. The patches do not converge pointwise; `C4`'s `L²` convergence uses zero error on the compact core, bounded error outside, and `ν Kᶜ → 0`.
  The audit's `route_C2` projects the route's exact conjunction. The block constant is `min ((k+1)α) (L+α)`, tighter by `α` than the route's `(k+2)α`.
* `B4` (the two-moving-point constant) needs an `O(r)` correction omitted in the route text: at the second moving point, `|g z| ≤ |g x| + Lip_a g(x)·r`, with radius `min r₁ (η/((a+η)N+1))`. `B5` does not need this correction.
* Empty compact cores produced by inner regularity must be **discarded**: `Metric.infDist x ∅ = 0` makes their cutoff constantly 1, breaking the construction (the same pitfall as `K7` in the Cheeger line).

## Registration and integration

Certificate file, ledger node (`kind: lemma`, with `meta.scope` appended), `check_blueprint.py` mapping, and lakefile root; the theorem in Blueprint chapter 30 gains
`\lean{…}`, `\leanok`, and a proof block naming the route and Eriksson-Bique / AGS sources, with the following explanation rewritten. Aggregate imports add four modules and revise the Energy prose.
In `research/tasks.json`, `thm:smooth-gradient-relaxation-two-cheeger` changes from `mathematics unknown` to `local_argument`, with an infrastructure block added.
All pinned evidence hashes were refreshed; progress views were regenerated through a temporary index. The certificate import closure (47 modules) was scanned beforehand and contained no escape hatches.

## Explicitly unproved

Dimension-free KLS; the Buser direction; the literature-Poincaré clause of `thm:klartag-density-frontend-identification`. `D1` (the diagnosis that a uniform radius is insufficient) was not formalized.
No equality of raw slope energy and relaxed energy on an individual test is claimed.

## Verification

The default `lake build` passed (3512 jobs, including the `Solutions` library with the new certificate). All **66** audit clients (59 in `research/audits` + 7 active clients in `build/audit`) were rerun with `-DwarningAsError=true`, with **0 failures**; **867 axiom reports, 0 occurrences of `sorryAx`**. No WIP modules remain; direct holes **0**. `check_ledger.py`: **26** certificates, 0 errors; `check_blueprint.py`: 88 labels, 0 errors; `atlas.py check`: 75 nodes, 26 certificates, acyclic; all 104 unit tests passed.
The before/after `pp.all` diff for all five declarations is empty. Root `python3 research/verify.py` was rerun at the end of the round, with the final receipt recorded in
`build/audit/energy-slope-proofs/final-snapshot.json`. The snapshot and workspace were recalculated entry by entry, with empty drift.
See `research/explorations/2026-09-19-energy-slope-proofs.json`.
