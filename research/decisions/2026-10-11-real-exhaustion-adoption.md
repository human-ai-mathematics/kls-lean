# Letwin Lemma A.4 real-parameter exhaustion: canonical adoption (2026-10-11)

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17), `χ_R ↑ 1` for real `R`. Codex accepted the exact isolated
candidate `build/reviews/2026-10-11-bkl-a4-goal-setup/claude-q4r-canonical-candidate-v1/` (patch sha256 `a33947d2fd4044e464b181a94083d48cd86d392ab179e33f04ef60f10ca873e7`; acceptance
`build/reviews/2026-10-11-bkl-a4-goal-setup/ROOT-Q4R-CANONICAL-ACCEPTANCE.json`, independent rebuild `root-q4r-canonical-independent-v1`), released the
source-pin hold (`build/reviews/2026-10-11-bkl-a4-goal-setup/root-current-controller-20261011/Q4R-ADOPTION-RELEASE.json`) and authorized copying exactly two
paths (CLAUDE-REQUEST-I, Task I.1).

## Placement and provenance

- `monotoneOn_and_tendsto_smoothTransition_two_sub_div` (Q4R) is appended verbatim after the affine rescaling in the
  generic leaf `Analysis/CutoffProfile.lean` (same three Mathlib imports): for every real `a`, `R ↦ η(a/R)` is monotone on
  `(0, ∞)` and tends to `1`, with `η t = smoothTransition (2 − t)`. Proof: the Astra response of
  `letwin-a4-real-exhaustion-astra-high-goal-v2` with obsolete guessed API names replaced by the exact existing lemmas
  (`q4r-current-api-repair-v1/candidate.lean`, b3b01128…), independently verified. The original Q4R packet keeps its
  terminal HTTP500 classification.
- New audit `research/audits/BKL/LetwinRealExhaustionAudit.lean` (6 reports). No import, name or existing declaration
  change; the module docstring is extended. Copied bytes (sha256): {"formalization/FunctionalInequalities/Analysis/CutoffProfile.lean": "ed6fd537397495707a20596d0caf354a686890c9a0bb6dfdfd7019714fcf92ba", "research/audits/BKL/LetwinRealExhaustionAudit.lean": "a63c1fd9f95ab41d07ecee5237dc37d9ced60be166c27c668d65e3a25daa0997"}
- Verification of the copied bytes before any metadata (`build/reviews/2026-10-11-bkl-a4-goal-setup/q4r-canonical-adoption-20261011/PRODUCTION-EVIDENCE.json`):
  strict builds 9 (objects identical to the candidate's: MongeAmpere 34, InverseHessian 6, CutoffProfile 21, FunctionalInequalities 0, Search 0, LetwinCutoffPrimitiveAudit 10, LetwinCutoffProfileAudit 3, LetwinRealExhaustionAudit 5, LetwinRescalingPositivityAudit 13), standard axioms (92 constants), fresh kernel replay of 9 modules, and the reports of all four cutoff audits (8 + 6 + 6 + 13) equal to the candidate's.

## Value map (new values; earlier CutoffProfile values unchanged, see the candidate MAPS.json)

| Accepted module | Name (identical) | Owner | Value / type class |
| --- | --- | --- | --- |
| `Stage2RealExhaustion` | `FunctionalInequalities.Analysis.monotoneOn_and_tendsto_smoothTransition_two_sub_div` | `FunctionalInequalities.Analysis.CutoffProfile` | module-map-in-hygiene-labels / type-raw |
| `Stage2RealExhaustion` | `FunctionalInequalities.Analysis.monotoneOn_and_tendsto_smoothTransition_two_sub_div._simp_1_1` | `FunctionalInequalities.Analysis.CutoffProfile` | raw-exact / type-raw |

Exception, strictly limited: the public value differs from its scratch object only in compiler hygiene binder labels
`x._@.<Module>.<h>._hygCtx._hyg.<n>` whose module component is `Stage2RealExhaustion` instead of
`FunctionalInequalities.Analysis.CutoffProfile` (hash and counters identical); the type is raw-exact and the generated
`_simp_1_1` is raw-exact. Codex's checker maps only the component immediately after `_@` in actual hygiene labels, with 15
controls.

## Status and scope

Blueprint `lem:letwin-cutoff-profile` extended; Letwin LA4 stays `partial` (◐) with seven declarations. Not completed:
the real-parameter Lemma A.4 producer (energy estimate, compact support, explicit `C/R` defect), Lemma A.5 with an actual
nonconstant source-law client, Theorems 2.5 and 1.2, BKL Lemma 4.2, `KLS.kls`. No certificate or paper-coverage change;
the final full receipt follows producer/client integration. Task pins updated: [{"at": "/nodes/thm:logconcave-cheeger-poincare-comparison/infrastructure/evidence[6]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "28f4ba4b20b504c536698dc50dd6c0b214ee0f27f79640dfa65aea9c3bdae82a", "new": "b818f0b75ee3d6d45b45fb7be86fb28a5cc5dba1f5b82e4bdd793cd2831cbc8f"}, {"at": "/nodes/thm:logconcave-cheeger-poincare-comparison/infrastructure/evidence[165]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "28f4ba4b20b504c536698dc50dd6c0b214ee0f27f79640dfa65aea9c3bdae82a", "new": "b818f0b75ee3d6d45b45fb7be86fb28a5cc5dba1f5b82e4bdd793cd2831cbc8f"}, {"at": "/nodes/thm:klartag-density-frontend-identification/infrastructure/evidence[3]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "28f4ba4b20b504c536698dc50dd6c0b214ee0f27f79640dfa65aea9c3bdae82a", "new": "b818f0b75ee3d6d45b45fb7be86fb28a5cc5dba1f5b82e4bdd793cd2831cbc8f"}, {"at": "/nodes/lem:relative-perimeter-smoothing/infrastructure/evidence[1]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "28f4ba4b20b504c536698dc50dd6c0b214ee0f27f79640dfa65aea9c3bdae82a", "new": "b818f0b75ee3d6d45b45fb7be86fb28a5cc5dba1f5b82e4bdd793cd2831cbc8f"}, {"at": "/nodes/lem:relative-perimeter-smoothing/infrastructure/evidence[145]", "path": "research/naming.md", "old": "1ef35202166e30f13b3320cc9a13a20fb5d40f575d62fcd48a334edda69d641b", "new": "ddb0ef32f63d0f571be97de8eb9d1321f6e43fff6494bcf69b57437da1367b5d"}]

## Superseded passages

Preserved verbatim; their claims are unchanged here.

`formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex`:

```text
$|\eta''|\le w$.  For every real $a$, $n\mapsto\eta(a/(n+1))$ is monotone and tends to $1$.  Tail primitive: for every
```

`formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex`:

```text
  $a/(n+1)\to0$ with $\eta=1$ on $t\le1$ gives the limit $1$.  Primitive:
```

`README.md`:

```text
(cutoff profile, majorant,
  monotone exhaustion, tail primitive, affine rescaling)
```

`HANDOFF.md`:

```text
  positivity (appended to `CutoffProfile.lean` and `Analysis/BakryEmery/MongeAmpere.lean`, with the audit
  `BKL/LetwinRescalingPositivityAudit.lean` and metadata). These Lean changes are NOT covered by this receipt:
```

`HANDOFF.md`:

```text
The scalar profile/majorant/exhaustion, the Q3 tail primitive and the Q5 rescaling are adopted in
```

`research/progress/literature.json LA4/note`:

```text
Proof: chi_R = eta((phi - min phi + 1)/R) with L phi = n - <grad V(grad phi), grad phi> bounded, plus (2.2). Partial: only the real-variable part is formalized (eta(t) = smoothTransition(2 - t) with derivative support and a common bound, a smooth majorant w >= |eta''| vanishing for t <= 0 and t >= 3, the monotone exhaustion eta(a/(n+1)) increasing to 1, and the tail primitive q_R(t) = R^{-1} int_{t/R}^3 w for R > 0 with q_R' = -R^{-2} w(t/R), 0 <= q_R <= R^{-1} int_0^3 w and q_R = 0 for t >= 3R, the affine rescaling of first and second derivatives of f((t - c)/R), and the nonnegative inverse-Hessian quadratic form sum_ij A_ij a_i a_j >= 0 under C^2/PD); the minimum of phi, the cutoffs chi_R, their compact support and the O(1/R) bound on ||L chi_R||_{L^1(nu)} are not formalized.
```

`research/progress/literature.json local_results/cutoff-profile`:

```text
Lemma A.4, real-variable part only: profile η(t) = smoothTransition(2 − t) with derivative support and bound, smooth majorant w ≥ |η″| vanishing for t ≤ 0 and t ≥ 3, monotone exhaustion η(a/(n+1)) ↑ 1, tail primitive q_R(t) = R⁻¹∫_{t/R}^3 w (R > 0), affine rescaling of derivatives; not the cutoffs η((φ − min φ + 1)/R), their compact support or the O(1/R) generator-defect bound
```

`research/progress/literature.json remaining`:

```text
The covariance step of the proof of Theorem 1.2 (p. 14, Cov(|M|^{1/2} X) = |M| for every symmetric M) is formalized; the Stein-kernel identity (2.21), Theorem 2.5 and the quadratic inequality, its moment-map/Stein proof and the κₙ-to-KLS conversion are not locally formalized. Quadratic tests do not suffice for full KLS. Two supporting identities (Lemma A.3 and the finite form of (2.12)) are formalized; the moment map, its regularity (A.1), the Hessian-metric generator and Theorem 2.5 are not. The real-variable part of Lemma A.4 (cutoff profile, a majorant of its second derivative, monotone exhaustion, tail primitive, affine rescaling) and the nonnegative inverse-Hessian quadratic form is formalized; Lemma A.4 itself (the cutoffs and their O(1/R) generator defect), Lemma A.5 and the moment map are not.
```

`research/progress/nodes.json lem:letwin-cutoff-profile`:

```text
Letwin Lemma A.4 (p. 17), real-variable part: the cutoff profile η(t) = smoothTransition(2 − t) (smooth, antitone, [0,1]-valued, 1 for t ≤ 1, 0 for t ≥ 2; η′ and η″ vanish off [1,2], are compactly supported and share a bound B), a smooth compactly supported nonnegative majorant w ≥ |η″| vanishing for t ≤ 0 and t ≥ 3, and the monotone exhaustion η(a/(n+1)) ↑ 1 for every real a; the tail primitive q_R(t) = R⁻¹∫_{t/R}^3 w of a smooth nonnegative w vanishing off (0,3), for R > 0 (smooth, q_R′ = −R⁻² w(t/R), 0 ≤ q_R ≤ R⁻¹∫_0^3 w, q_R = 0 for t ≥ 3R); the affine rescaling (f((·−c)/R))′ = R⁻¹ f′((·−c)/R), ″ = R⁻² f″((·−c)/R) for arbitrary f, c, R (total-derivative conventions). Immediate consumer: the Lemma A.4 cutoffs η((φ − min φ + 1)/R) with O(1/R) generator defect → Lemma A.5 → Theorem 2.5 → Theorem 1.2 → BKL Lemma 4.2; none of these is provided.
```
