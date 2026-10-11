# Letwin Lemma A.4 scalar cutoff profile: canonical adoption (2026-10-11)

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17), real-variable part only. Codex accepted the exact isolated
candidate `build/reviews/2026-10-10-bkl-stage2-orchestration/claude-cutoff-profile-candidate-takeover-v1/` (patch sha256
`c5dc2f3158376ae8136454b5eaa11f175792eb5a5f2816870154c77c7796f988`; acceptance `build/reviews/2026-10-10-bkl-controller-takeover/ROOT-SCALAR-CANONICAL-ACCEPTANCE-20261011.json`)
and authorized copying exactly its three source paths (CONTROLLER-REQUEST-03).

## Placement

- Owner: generic real-variable analysis; a new narrow leaf `formalization/FunctionalInequalities/Analysis/CutoffProfile.lean`
  (namespace `FunctionalInequalities.Analysis`) importing exactly `Mathlib.Analysis.SpecialFunctions.SmoothTransition`,
  `Mathlib.Analysis.Calculus.ContDiff.Deriv` and `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`, the
  imports of the accepted sources. The existing `Analysis/Whitney/Bump.lean` (Whitney-cover family, Whitney radii) was
  reviewed and rejected as owner. One aggregate import in `FunctionalInequalities.lean`; a new audit
  `research/audits/BKL/LetwinCutoffProfileAudit.lean`.
- No module or namespace migration of existing production declarations, no aliases, no wrappers. The accepted
  declaration blocks are verbatim (Q1 `letwin-a4-scalar-profile-astra-high-v2` 156e2d03…, Q2
  `letwin-a4-scalar-majorant-astra-high-takeover-v2` 2489dec3…, Q4 `letwin-a4-scalar-monotone-astra-high-v1` 4bb28339…);
  the Q1 prefix of the Q2 source is not duplicated. Only declaration and module docstrings are new.
- Copied bytes (sha256): {
  "formalization/FunctionalInequalities/Analysis/CutoffProfile.lean": "327b4c0ed964502d98b3a2a939bfccc1fa07f14e6fcba83e7fb4b27c750c4654",
  "formalization/FunctionalInequalities.lean": "4b2967fb33a2eacd4bc13deaeed4cb67ce22cf8100d774d8950956b2f05e386b",
  "research/audits/BKL/LetwinCutoffProfileAudit.lean": "ce598b67861a66d479921f43770d9f94662c26baa4675210ad21dc35b44354f2"
}

## Accepted-to-canonical value map

Every owned value of the three accepted objects is found under its exact stable name in the canonical module (10
constants), with equal kind, universe parameters and raw type; the declaration map is the identity.

| Accepted module | Accepted name | Canonical name | Value class |
| --- | --- | --- | --- |
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

Exception, strictly limited: the three non-raw values differ only in compiler hygiene binder labels
`x._@.<Module>.<h>._hygCtx._hyg.<n>`, where `<Module>` changes from the accepted module (`Stage2ScalarProfile`,
`Stage2ScalarMajorant`) to `FunctionalInequalities.Analysis.CutoffProfile` with identical hash `<h>` and counter `<n>`.
The accepted class is equality after this literal module map applied to binder names only; label erasure is not
accepted. Eleven synthetic controls (candidate `CHECKS.json`) show that counter, hash, hygienic or plain user binder,
binder info, binder type, constant, universe argument and term-constructor changes are all rejected. Codex's
`ComparePrefixHygiene.lean` agrees on all ten values.

## Status and scope

Blueprint `lem:letwin-cutoff-profile` (`\leanok`, supporting node); `literature.json` Letwin LA4 relation `partial`
(◐) with the three declarations; local result scope recorded. Immediate consumer: the actual Lemma A.4 cutoffs and
their C/(n+1) generator defect → Lemma A.5 → Theorem 2.5 → Theorem 1.2 → BKL Lemma 4.2. NOT completed: Lemma A.4
itself, Lemma A.5, the moment-potential producer and regularity, Theorems 2.5 and 1.2, BKL Lemma 4.2, `KLS.kls`. No
certificate or paper-coverage change.

## Verification gap

The pre-adoption full local receipt `build/verification/20261010T093056.948739Z/report.json` no longer matches the
current Lean snapshot: this adoption adds a Lean module, an aggregate import and an audit. The new proof delta awaits a
new full local receipt; the candidate evidence (4 strict builds, 3 full types, 13 standard values, kernel replay,
clients) and Codex's independent rebuild are the evidence until then. Task pins updated: [{"at": "/nodes/thm:logconcave-cheeger-poincare-comparison/infrastructure/evidence[6]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "29560aac656c6e990bf7efc52ea403c8b098d847a9ceca7792de47c87855ffce", "new": "b5829c95ea37fb0b2efb29f31015b7bf6f0d08b054358f4782d4107a25035706"}, {"at": "/nodes/thm:logconcave-cheeger-poincare-comparison/infrastructure/evidence[165]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "29560aac656c6e990bf7efc52ea403c8b098d847a9ceca7792de47c87855ffce", "new": "b5829c95ea37fb0b2efb29f31015b7bf6f0d08b054358f4782d4107a25035706"}, {"at": "/nodes/thm:klartag-density-frontend-identification/infrastructure/evidence[3]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "29560aac656c6e990bf7efc52ea403c8b098d847a9ceca7792de47c87855ffce", "new": "b5829c95ea37fb0b2efb29f31015b7bf6f0d08b054358f4782d4107a25035706"}, {"at": "/nodes/lem:relative-perimeter-smoothing/infrastructure/evidence[1]", "path": "formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex", "old": "29560aac656c6e990bf7efc52ea403c8b098d847a9ceca7792de47c87855ffce", "new": "b5829c95ea37fb0b2efb29f31015b7bf6f0d08b054358f4782d4107a25035706"}, {"at": "/nodes/lem:relative-perimeter-smoothing/infrastructure/evidence[145]", "path": "research/naming.md", "old": "d7577dc0dd2c9abd6ce81a4e6cde381c5dae9ffdab7fe8379cc62e5223444a99", "new": "c6b9409fc464344a5e9aa46016fe6e7d3d0fa2c2f3adaf451a517123c62d6472"}]

## Superseded current-state passages

Preserved verbatim; their claims are unchanged here.

`HANDOFF.md`:

```text
  (below). Post-receipt changes are documentation/metadata only: this handoff, the staged-goal plan, the rank-1
  literature next step, the regenerated progress views and the Stage 1 receipt history. Every Lean source still
  equals the receipt snapshot, but the whole-tree hash differs (verified Lean snapshot ≠ final whole tree); the
  receipt does not verify these later edits.
```

`HANDOFF.md`:

```text
Lemma 4.2; the theorem remains open. On 2026-10-11, the actual scalar Q2 majorant was independently accepted in
isolated scratch (full original type, eight standard actual values and fresh kernel; exact Q1 prefix values retained
up to documented compiler-generated binder labels). It is not canonically adopted. The combined A4/A5 support candidate
```

`HANDOFF.md`:

```text
are under `build/reviews/2026-10-10-bkl-controller-takeover/`; Q3 exact typed-feedback v5 is dependency-ready.
```

`HANDOFF.md`:

```text
  (BKL2026 P71 `same`, E7274 `⇑`, T11/T41/L42/L43/E67 partial; Letwin2026 CZ14 `⇑`,
  L23/LA3/T25/D26/L27/L29/LA7/E23/T12 partial)
```
