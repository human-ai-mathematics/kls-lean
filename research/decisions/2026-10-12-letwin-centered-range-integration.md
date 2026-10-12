# Letwin Lemma A.6 support: centered range density of diffusion images; current controller

Date: 2026-10-12. Controller: Codex thread `01a12de4-2412-7082-ae33-15b1c3502420` (continuing the owner-authorized Goal; predecessor root thread
`01a12b29-a858-7c43-9bb3-b28e3d038b05`). Integrator: the sole reviewed Claude conversation, sequenced writer window AA.

## Integration

`KLS/LogConcave/HeatSemigroup/Range.lean` (new, namespace `FunctionalInequalities.KLS.LogConcave.HeatSemigroup`) holds
the definition `compactSmoothDiffusionImage` and the theorems `centered_mem_closure_compactSmoothDiffusionImage` and
`center_mem_closure_compactSmoothDiffusionImage`: for a log-concave probability law `ν = m.tilted (−U)` on a
finite-dimensional real inner-product space, `U` of class `C¹`, `m` an additive Haar measure, every mean-zero class of
`L²(ν)` (and the centering of every class) lies in the closure of the images `−L f`, `f` smooth with compact support.
`research/audits/BKL/LetwinCenteredRangeAudit.lean` holds the real nonzero Gaussian client. Source: strong-API candidate
`api-centered-range-gaussian-compiler-v6/candidate.lean` (gpt-6-astra, high; SHA-256 `527e35ef…`), independently
kernel- and semantics-accepted; the definition, both theorems and the client are copied verbatim; the client-only imports
(BKL Gaussian Taylor, regular isotropic laws) stay in the audit. The module additionally owns the two generated congruence
lemmas `adjointComp.congr_simp` and `closedWeightedOperator.congr_simp`, raw-identical to the copies already owned by
`KLS/LogConcave/Regular.lean` and `HeatSemigroup/Decay.lean`. Comparison evidence (all 6 candidate constants equal in kind,
ordered universes, type and value under the module-name map of hygiene labels; `_proof_1`, `_proof_2` and the client
raw-equal): `build/reviews/2026-10-12-bkl-letwin-t25-continuation/claude-aa-centered-range-integration-v1/`.

This is finite-energy Brascamp–Lieb infrastructure for Letwin, arXiv:2607.24164v1, Lemma A.6. Brascamp–Lieb itself, Lemma
A.6 with an infinite right side, the moment map, Letwin Theorems 2.5 and 1.2, BKL and KLS remain open; Letwin LA6 is partial.

## Superseded current-state wording (verbatim)

The passages are quoted in code blocks, so their repository-root links are inert here; their claims are unchanged.

`HANDOFF.md`, Controller and next steps (before this batch):

```text
The current mathematical controller is the root Goal thread `01a12b29-a858-7c43-9bb3-b28e3d038b05`, which continues the owner-authorized Goal; its active record is [the 2026-10-12 Letwin Theorem 2.5 goal](research/handoffs/2026-10-12-bkl-letwin-t25-goal.md). The bounded Stage 2A goal ([2026-10-11 BKL A.4 goal](research/handoffs/2026-10-11-bkl-a4-goal.md)) and its earlier controllers are historical; the superseded controller paragraph is preserved verbatim in [the 2026-10-12 controller record](research/decisions/2026-10-12-controller-letwin-t25-goal.md). Current packet handles are in `build/reviews/2026-10-12-bkl-letwin-t25-continuation/`.
```

`research/handoffs/2026-10-12-bkl-letwin-t25-goal.md`, header (before this batch):

```text
Created 2026-10-12. Controller: root Goal thread `01a12b29-a858-7c43-9bb3-b28e3d038b05`, continuing the owner-authorized Goal after the bounded
```
