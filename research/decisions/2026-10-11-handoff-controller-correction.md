# Handoff controller-status correction (2026-10-11)

Metadata-only correction after Codex's semantic review of the 2026-10-11 cutoff-profile adoption: no Lean source, proof body, worker packet or status changes. The current-state passages below were replaced in the named files (stale controller status, job states and the Goal-service sentence in `HANDOFF.md`; the Blueprint proof sketch of `lem:letwin-cutoff-profile` now spells out the `a < 0` and `a ≥ 0` cases of the exhaustion). They are preserved verbatim; their claims are unchanged here. Exact Theorem 1.2 and source Lemma A.4 remain open; the latest full local receipt `build/verification/20261010T093056.948739Z` predates the cutoff-profile adoption and does not match the current Lean snapshot until Codex runs the new full verification.

`HANDOFF.md`:

```text
earlier versions are preserved in the
[2026-10-10 Stage 1 record](research/decisions/2026-10-10-bkl-stage1-integration.md), the
```

`HANDOFF.md`:

```text
## Uncommitted (2026-10-07–10, continuous BKL goal)
```

`HANDOFF.md`:

```text
Controller takeover (2026-10-10): the owner renewed the Codex/strong-API/Claude construction pattern in chat `01a12661-eb02-7580-9fbd-e91e778454cf`; its Stage 2 Goal is active. The previous controller `01a123b5-2c39-72a2-951e-e4d148382678` is observed in `systemError`, and its unfinished goal is not completed. The accepted A4/A5 scratch supports and candidates are being independently reviewed before combined adoption. Scalar rescaling v2 and primitive v3 are terminal failures (connection reset and provider HTTP429 `invalid_api_key`); their packets are retained and the stale running labels reconciled. Existing configured models endpoint authentication passed a read-only check; generation availability remains to be established. Claude Message62 is confirmed running on the isolated combined candidate. The takeover baseline preserves 1098 real-index entries and the broad dirty tree. This is a control update, not new production proof progress.
```

`HANDOFF.md`:

```text
Q3 v5 was rejected for a missing integrand
annotation and v6 is in preparation; the E1 energy identity is dispatched.
```

`HANDOFF.md`:

```text
 The Goal service's old parallel-paper text cannot be edited by the available tools; the newer owner scope controls execution.
```

`formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex`:

```text
compact support, are bounded; $w$ is $B$ times a product of two smooth transitions, equal to $B$ on $[1,2]$; and
  $a/(n+1)\to0$, with $\eta$ antitone and equal to $1$ on $t\le1$.
```
