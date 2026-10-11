# Letwin Lemma A.4 affine rescaling and inverse-Hessian quadratic positivity: canonical adoption (2026-10-11)

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17). Codex accepted the exact isolated candidate
`build/reviews/2026-10-11-bkl-a4-goal-setup/claude-q5-b1-canonical-candidate-v1/` (patch sha256 `94aa6ba8514902498287d7b7390682be44e4dd0783bab26361bb5b057a9c28fb`;
acceptance `build/reviews/2026-10-11-bkl-a4-goal-setup/ROOT-Q5-B1-CANONICAL-ACCEPTANCE.json`, independent rebuild
`root-q5-b1-independent-v1`) and authorized copying exactly three paths (CLAUDE-REQUEST-04, Task F).

## Placement and provenance

- `deriv_comp_sub_div_and_deriv_deriv` (Q5) is appended verbatim after the tail primitive in the generic leaf
  `Analysis/CutoffProfile.lean`; arbitrary `f`, `c`, `R`, `t` with Lean total-derivative conventions (`R = 0` included).
  Proof: the Q5 Astra response with the intended shift lemma explicitly instantiated and two compiler-reported tactic
  cleanups (`q5-explicit-specialization-v3/candidate.lean`, 4f36afcd…).
- `sum_inverseHessianEntry_mul_mul_nonneg` (B1) is appended verbatim to `Analysis/BakryEmery/MongeAmpere.lean` in a fresh
  namespace block (`section QuadraticForm`, own binders; exact C²/PD/any-orthonormal-basis/any-rank scope), beside the
  inverse-Hessian positivity facts. Proof: the B1 Astra response with the intended `inv_hessianMatrixIn` lemma explicitly
  instantiated (`b1-explicit-specialization-v1/candidate.lean`, 99d92f10…).
- No import, name or existing declaration changes; module docstrings extended. Original API packets keep their terminal
  rejections. Copied bytes (sha256): {"formalization/FunctionalInequalities/Analysis/CutoffProfile.lean": "a54e73b55d676a82e7c0777a285f7f12ce27074475480beb59b55f599b92d9c1", "formalization/FunctionalInequalities/Analysis/BakryEmery/MongeAmpere.lean": "6e74da300adcdab50a74352fcf662a63a195613058b2bc31a87c4c929992e1ba", "research/audits/BKL/LetwinRescalingPositivityAudit.lean": "67deb9ec419865584c219e94afb401ecf35efcd73d632f6f0f95c8cdcc6ca4d1"}

## Value map (new values; earlier CutoffProfile values unchanged, see the candidate MAPS.json)

| Accepted module | Name (identical) | Owner | Value / type class |
| --- | --- | --- | --- |
| `Stage2ScalarRescaling` | `FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv` | `FunctionalInequalities.Analysis.CutoffProfile` | raw-exact / type-raw |
| `Stage2Quadratic` | `FunctionalInequalities.Analysis.BakryEmery.sum_inverseHessianEntry_mul_mul_nonneg` | `FunctionalInequalities.Analysis.BakryEmery.MongeAmpere` | module-map-in-hygiene-labels / type-module-map-in-hygiene-labels |

Exception, strictly limited: B1's value and type differ from its scratch object only in compiler hygiene binder labels
`inst._@.<Module>.<h>._hygCtx._hyg.<n>` whose module component is `Stage2Quadratic` instead of
`FunctionalInequalities.Analysis.BakryEmery.MongeAmpere` (hash 1446449524 and counters identical); Codex's checker maps only
the component immediately after `_@` in actual hygiene labels, with 15 controls. Q5 is raw-exact.

## Status and scope

Blueprint `lem:letwin-cutoff-profile` (extended) and the new supporting node `lem:letwin-inverse-hessian-quadratic`;
Letwin LA4 stays `partial` (◐) with six declarations. The Gaussian positivity examples of the new audit are local
coordinate-property tests, not the bounded-gradient source-law client required for Lemmas A.4/A.5. Not completed: the
real-parameter Lemma A.4 producer, Lemma A.5 and its source-law client, Theorems 2.5 and 1.2, BKL Lemma 4.2, `KLS.kls`. No
certificate or paper-coverage change; the final full receipt follows producer/client integration. Task pins updated:
[{"at": "/nodes/thm:logconcave-cheeger-poincare-comparison/infrastructure/evidence[6]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "6a6b3aed1ca61ac82aa066b4da7631fca6dc5457f0242ce27837d6577d9ef1d3", "new": "28f4ba4b20b504c536698dc50dd6c0b214ee0f27f79640dfa65aea9c3bdae82a"}, {"at": "/nodes/thm:logconcave-cheeger-poincare-comparison/infrastructure/evidence[165]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "6a6b3aed1ca61ac82aa066b4da7631fca6dc5457f0242ce27837d6577d9ef1d3", "new": "28f4ba4b20b504c536698dc50dd6c0b214ee0f27f79640dfa65aea9c3bdae82a"}, {"at": "/nodes/thm:klartag-density-frontend-identification/infrastructure/evidence[3]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "6a6b3aed1ca61ac82aa066b4da7631fca6dc5457f0242ce27837d6577d9ef1d3", "new": "28f4ba4b20b504c536698dc50dd6c0b214ee0f27f79640dfa65aea9c3bdae82a"}, {"at": "/nodes/lem:relative-perimeter-smoothing/infrastructure/evidence[1]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "6a6b3aed1ca61ac82aa066b4da7631fca6dc5457f0242ce27837d6577d9ef1d3", "new": "28f4ba4b20b504c536698dc50dd6c0b214ee0f27f79640dfa65aea9c3bdae82a"}, {"at": "/nodes/lem:relative-perimeter-smoothing/infrastructure/evidence[145]", "path": "research/naming.md", "old": "27b0d72d804b78ca2679304b2f578195c2c125e7292dc10d0ec8944e4fe12732", "new": "1ef35202166e30f13b3320cc9a13a20fb5d40f575d62fcd48a334edda69d641b"}]

## Superseded passages

Preserved verbatim; their claims are unchanged here.

`formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex`:

```text
        FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff}
```

`formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex`:

```text
  $C^\infty$ with $q_R'(t)=-R^{-2}w(t/R)$, $0\le q_R\le R^{-1}\int_0^3w$ and $q_R(t)=0$ for $t\ge3R$.  Immediate consumer: the
```

`formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex`:

```text
  $w=0$ off $(0,3)$.
\end{proof}
```

`README.md`:

```text
The real-variable part of Letwin's Lemma A.4 (cutoff profile, majorant,
  monotone exhaustion, tail primitive) is formalized;
```

`research/naming.md`:

```text
`monotone_and_tendsto_smoothTransition_two_sub_div_succ`, `inv_mul_intervalIntegral_div_three_cutoff` |
```

`HANDOFF.md`:

```text
  `BKL/LetwinCutoffPrimitiveAudit.lean` and metadata). These Lean changes are NOT covered by this receipt:
```

`HANDOFF.md`:

```text
The scalar profile/majorant/exhaustion and the Q3 tail primitive are adopted in `Analysis/CutoffProfile.lean`; source A.4
```

`HANDOFF.md`:

```text
The original Q5 and B1 API packets are terminal rejected, but their separate explicit-specialization candidates are
independently accepted as isolated supports, not adopted
```

`HANDOFF.md`:

```text
Q5 and B1 are accepted isolated
supports (original packets terminal rejected), and the new E1 run is terminal without a proof response.
```

`research/progress/literature.json LA4/note`:

```text
and q_R = 0 for t >= 3R); the minimum of phi
```

`research/progress/literature.json local_results/cutoff-profile`:

```text
tail primitive q_R(t) = R⁻¹∫_{t/R}^3 w (R > 0); not the cutoffs
```

`research/progress/literature.json remaining`:

```text
(cutoff profile, a majorant of its second derivative, monotone exhaustion, tail primitive)
```

`research/progress/nodes.json lem:letwin-cutoff-profile`:

```text
Letwin Lemma A.4 (p. 17), real-variable part: the cutoff profile η(t) = smoothTransition(2 − t) (smooth, antitone, [0,1]-valued, 1 for t ≤ 1, 0 for t ≥ 2; η′ and η″ vanish off [1,2], are compactly supported and share a bound B), a smooth compactly supported nonnegative majorant w ≥ |η″| vanishing for t ≤ 0 and t ≥ 3, and the monotone exhaustion η(a/(n+1)) ↑ 1 for every real a; the tail primitive q_R(t) = R⁻¹∫_{t/R}^3 w of a smooth nonnegative w vanishing off (0,3), for R > 0 (smooth, q_R′ = −R⁻² w(t/R), 0 ≤ q_R ≤ R⁻¹∫_0^3 w, q_R = 0 for t ≥ 3R). Immediate consumer: the Lemma A.4 cutoffs η((φ − min φ + 1)/R) with O(1/R) generator defect → Lemma A.5 → Theorem 2.5 → Theorem 1.2 → BKL Lemma 4.2; none of these is provided.
```
