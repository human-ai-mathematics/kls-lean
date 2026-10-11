# Letwin Lemma A.4 tail primitive: canonical adoption (2026-10-11)

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17), `q_R(t) = R⁻¹ ∫_{t/R}^∞ w`, real-variable part only. Codex
accepted the exact isolated candidate `build/reviews/2026-10-11-bkl-a4-goal-setup/claude-cutoff-profile-q3-candidate-v1/`
(patch sha256 `1c8bae61a8466e41eaef3181e3fcd3bdec54f1a5ab7847c23b7a09e3a0735f94`; acceptance `build/reviews/2026-10-11-bkl-a4-goal-setup/ROOT-Q3-CANONICAL-ACCEPTANCE.json`,
independent rebuild `root-q3-canonical-independent-v1`) and authorized copying exactly two source paths (CLAUDE-REQUEST-02).

## Placement and provenance

- Owner: the existing generic leaf `formalization/FunctionalInequalities/Analysis/CutoffProfile.lean` (same three Mathlib
  imports); the declaration `inv_mul_intervalIntegral_div_three_cutoff` is appended verbatim after the existing Q4
  declaration, so no existing declaration moves; only the module docstring and a declaration docstring are new. The
  aggregate already imports the module. New audit `research/audits/BKL/LetwinCutoffPrimitiveAudit.lean`.
- Proof body: the API proof of `letwin-a4-scalar-primitive-astra-high-takeover-v6` (original `5f48742c…`, whose packet
  keeps its terminal candidate failure) with exactly three compiler-reported unused tactics removed (`21912ed5…`,
  `q3-lint-cleanup-v1/mechanical-cleanup.patch`); no new inference, statement, import or option. No aliases or renames.
- Copied bytes (sha256): {"formalization/FunctionalInequalities/Analysis/CutoffProfile.lean": "94128e317e54bca6ab8bbbbd16e4957eea56c20d40901466130418b158ef2bd4", "research/audits/BKL/LetwinCutoffPrimitiveAudit.lean": "1d44052008b40019e133fd3f83da10d025fe71da6a4c3e38c1add6f2040e12cd"}

## Value map

All 18 constants of the module are found under exact stable names with equal kind, universes and raw type; old
interface unchanged (10 → 18, nothing missing or changed). Exception, strictly limited and identical to the 2026-10-11
cutoff-profile adoption: public proof values may differ only in compiler hygiene binder labels
`x._@.<Module>.<h>._hygCtx._hyg.<n>` whose `<Module>` component is the accepted scratch module (here
`Stage2ScalarPrimitive`) instead of `FunctionalInequalities.Analysis.CutoffProfile`, hash and counter identical; Codex's
independent checker restricts the map to actual hygiene labels with 12 controls.

| Accepted module | Accepted name | Canonical name | Value class |
| --- | --- | --- | --- |
| `Stage2ScalarPrimitive` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_5` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_5` | raw-exact |
| `Stage2ScalarPrimitive` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_3` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_3` | raw-exact |
| `Stage2ScalarPrimitive` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_1` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_1` | raw-exact |
| `Stage2ScalarPrimitive` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff` | module-map-in-hygiene-labels |
| `Stage2ScalarPrimitive` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_7` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_7` | raw-exact |
| `Stage2ScalarPrimitive` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_4` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_4` | raw-exact |
| `Stage2ScalarPrimitive` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_6` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_6` | raw-exact |
| `Stage2ScalarPrimitive` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_2` | `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff._simp_1_2` | raw-exact |
| `Stage2ScalarProfile` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff` | module-map-in-hygiene-labels |
| `Stage2ScalarProfile` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_2` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_2` | raw-exact |
| `Stage2ScalarProfile` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_1` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_1` | raw-exact |
| `Stage2ScalarProfile` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_3` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_3` | raw-exact |
| `Stage2ScalarMajorant` | `FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub._simp_1_2` | `FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub._simp_1_2` | raw-exact |
| `Stage2ScalarMajorant` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff` | module-map-in-hygiene-labels |
| `Stage2ScalarMajorant` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_2` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_2` | raw-exact |
| `Stage2ScalarMajorant` | `FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub._simp_1_1` | `FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub._simp_1_1` | raw-exact |
| `Stage2ScalarMajorant` | `FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub._simp_1_3` | `FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub._simp_1_3` | raw-exact |
| `Stage2ScalarMajorant` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_1` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_1` | raw-exact |
| `Stage2ScalarMajorant` | `FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub` | `FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub` | module-map-in-hygiene-labels |
| `Stage2ScalarMajorant` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_3` | `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff._simp_1_3` | raw-exact |
| `Stage2ScalarMonotone` | `FunctionalInequalities.Analysis.monotone_and_tendsto_smoothTransition_two_sub_div_succ` | `FunctionalInequalities.Analysis.monotone_and_tendsto_smoothTransition_two_sub_div_succ` | raw-exact |
| `Stage2ScalarMonotone` | `FunctionalInequalities.Analysis.monotone_and_tendsto_smoothTransition_two_sub_div_succ._simp_1_1` | `FunctionalInequalities.Analysis.monotone_and_tendsto_smoothTransition_two_sub_div_succ._simp_1_1` | raw-exact |

## Status and scope

Supporting node `lem:letwin-cutoff-profile` and Letwin LA4 (relation `partial`, ◐) now include the primitive. Not
completed: the real-parameter Lemma A.4 producer (the Stage 2A target), its natural-index form, Lemma A.5 and its
nonconstant source-law client, Theorems 2.5 and 1.2, BKL Lemma 4.2, `KLS.kls`. No certificate or paper-coverage change.
The latest full local receipt predates both scalar adoptions; the goal's final full receipt follows full producer/client
integration. Task pins updated: [{"at": "/nodes/thm:logconcave-cheeger-poincare-comparison/infrastructure/evidence[6]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "a97514810261ba634cac6313fb8f5faeda66eca13414f370ce67eca0e9f53d5d", "new": "6a6b3aed1ca61ac82aa066b4da7631fca6dc5457f0242ce27837d6577d9ef1d3"}, {"at": "/nodes/thm:logconcave-cheeger-poincare-comparison/infrastructure/evidence[165]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "a97514810261ba634cac6313fb8f5faeda66eca13414f370ce67eca0e9f53d5d", "new": "6a6b3aed1ca61ac82aa066b4da7631fca6dc5457f0242ce27837d6577d9ef1d3"}, {"at": "/nodes/thm:klartag-density-frontend-identification/infrastructure/evidence[3]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "a97514810261ba634cac6313fb8f5faeda66eca13414f370ce67eca0e9f53d5d", "new": "6a6b3aed1ca61ac82aa066b4da7631fca6dc5457f0242ce27837d6577d9ef1d3"}, {"at": "/nodes/lem:relative-perimeter-smoothing/infrastructure/evidence[1]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "a97514810261ba634cac6313fb8f5faeda66eca13414f370ce67eca0e9f53d5d", "new": "6a6b3aed1ca61ac82aa066b4da7631fca6dc5457f0242ce27837d6577d9ef1d3"}, {"at": "/nodes/lem:relative-perimeter-smoothing/infrastructure/evidence[145]", "path": "research/naming.md", "old": "c6b9409fc464344a5e9aa46016fe6e7d3d0fa2c2f3adaf451a517123c62d6472", "new": "27b0d72d804b78ca2679304b2f578195c2c125e7292dc10d0ec8944e4fe12732"}]

## Superseded passages

Preserved verbatim; their claims are unchanged here.

`formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex`:

```text
        FunctionalInequalities.Analysis.monotone_and_tendsto_smoothTransition_two_sub_div_succ}
  \leanok
  Letwin \cite{Letwin2026QuadraticKLS}, Lemma~A.4 (p.~17), the real-variable part of the cutoff construction.
```

`formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex`:

```text
  $|\eta''|\le w$.  For every real $a$, $n\mapsto\eta(a/(n+1))$ is monotone and tends to $1$.  Immediate consumer: the
```

`formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex`:

```text
  $a/(n+1)\to0$ with $\eta=1$ on $t\le1$ gives the limit $1$.
\end{proof}
```

`README.md`:

```text
The real-variable part of Letwin's Lemma A.4 (cutoff profile, majorant,
  monotone exhaustion) is formalized;
```

`research/naming.md`:

```text
`exists_majorant_abs_deriv_deriv_smoothTransition_two_sub`, `monotone_and_tendsto_smoothTransition_two_sub_div_succ` |
```

`HANDOFF.md`:

```text
Lemma A.4 scalar profile (new `Analysis/CutoffProfile.lean`, one aggregate import, the audit
  `BKL/LetwinCutoffProfileAudit.lean` and metadata).
```

`HANDOFF.md`:

```text
The scalar profile/majorant/exhaustion remains adopted in `Analysis/CutoffProfile.lean`; source A.4
```

`HANDOFF.md`:

```text
reviewed but not adopted. Q3 v6 now reports terminal candidate failure; E1 recorded a terminal provider
HTTP500 with no proof response.
```

`HANDOFF.md`:

```text
kernel-replayed. It is not canonically adopted. Evidence and current handles are in
```

`HANDOFF.md`:

```text
preparing its scalar canonical candidate and the full real-parameter A.4 interface; B1 is an actual
single-response API request, with Q5/E1 prepared separately.
```

`research/progress/literature.json LA4/note`:

```text
and the monotone exhaustion eta(a/(n+1)) increasing to 1); the minimum of phi
```

`research/progress/literature.json local_results`:

```text
monotone exhaustion η(a/(n+1)) ↑ 1; not the cutoffs
```

`research/progress/literature.json remaining`:

```text
(cutoff profile, a majorant of its second derivative, monotone exhaustion)
```

`research/progress/literature.json priorities/1`:

```text
Immediate milestone: complete source Lemma A.4, i.e. the actual minimum-based energy estimate, the compact support of the cutoffs and the explicit C/(n+1) generator-defect bound, from the adopted real-variable profile (η, majorant w, monotone exhaustion), then consume the cutoffs in A.5.
```

`research/progress/nodes.json lem:letwin-cutoff-profile`:

```text
Letwin Lemma A.4 (p. 17), real-variable part: the cutoff profile η(t) = smoothTransition(2 − t) (smooth, antitone, [0,1]-valued, 1 for t ≤ 1, 0 for t ≥ 2; η′ and η″ vanish off [1,2], are compactly supported and share a bound B), a smooth compactly supported nonnegative majorant w ≥ |η″| vanishing for t ≤ 0 and t ≥ 3, and the monotone exhaustion η(a/(n+1)) ↑ 1 for every real a. Immediate consumer: the Lemma A.4 cutoffs η((φ − min φ + 1)/R) with O(1/R) generator defect → Lemma A.5 → Theorem 2.5 → Theorem 1.2 → BKL Lemma 4.2; none of these is provided.
```
