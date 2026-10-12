# Controller handoff to Claude (2026-10-12)

On 2026-10-12 the owner made the Claude session of 2026-10-12 the sole controller and canonical
integrator for BKL Theorem 1.1 and adopted the
[Claude controller goal](../handoffs/2026-10-12-bkl-claude-controller-goal.md). The Codex thread
`01a12de4-2412-7082-ae33-15b1c3502420` had stopped (its last request
`api-trace-cutoff-consumption-compiler-v5` completed at 22:22 and was not integrated). Commit
`313a43c` records the vendored libraries and the provenance lock (full receipt
`20261012T151046.694236Z`). This record changes no proof, certificate or coverage status.

## Superseded HANDOFF.md text (as of commit 313a43c), preserved verbatim

- Local `main` is `ad630b00` (2026-10-12, owner-authorized commit of the snapshot `bf72ed91` covered by the full receipt `20261011T173331.204329Z`); `origin/main` is `ca59365726bca899f26cdd889dcc62850089eb09`. No push, tag or remote CI has been made. The vendored stochastic calculus below is in the working tree only, uncommitted. Remote Lean certification passed for `36e7c78` only; later work has local evidence only.

## Controller and next steps

The current mathematical controller is Codex thread `01a12de4-2412-7082-ae33-15b1c3502420`, which continues the owner-authorized Goal (predecessor root thread `01a12b29-a858-7c43-9bb3-b28e3d038b05`, historical); its active record is [the 2026-10-12 Letwin Theorem 2.5 goal](research/handoffs/2026-10-12-bkl-letwin-t25-goal.md). The bounded Stage 2A goal ([2026-10-11 BKL A.4 goal](research/handoffs/2026-10-11-bkl-a4-goal.md)) and its earlier controllers are historical; the superseded controller wording is preserved verbatim in [the 2026-10-12 centered-range record](research/decisions/2026-10-12-letwin-centered-range-integration.md) and [the 2026-10-12 controller record](research/decisions/2026-10-12-controller-letwin-t25-goal.md). Current packet handles are in `build/reviews/2026-10-12-bkl-letwin-t25-continuation/`.

The immediate mathematical next stage is Letwin Theorem 1.2, including the moment-map and regularity work, Proposition 2.8, Theorem 2.5, and the Stein-kernel identity (2.21), without assuming the desired estimate. Later stages are the Eldan localization/SDE/Itô/non-explosion argument, universal Theorem 4.1, unconditional Theorem 1.1, and `KLS.kls`. Existing Theorem 3.1, conditional Proposition 7.1, and the Section 2 reduction remain in scope as already recorded.

Codex coordinates and accepts; strong API models construct candidates; the reviewed Claude conversation remains the production integrator. No new proof, certificate, or coverage status is asserted by this handoff or by the file-management batch.

## Vendored stochastic calculus (uncommitted, 2026-10-12)

- Provenance lock (2026-10-12, uncommitted): `formalization/vendor/vendor-lock.json` pins, for all
  243 vendored files (239 modules, 4 licenses), the upstream path, SHA-256 and Git blob at the
  pinned commit, the vendored SHA-256 and the `port.patch` SHA-256 and file set. Placement: new
  tooling module `research/vendor_lock.py` (owner: verification tooling; no Lean or API change),
  tests in `research/tests/test_vendor_lock.py`, and an offline `vendor-provenance-lock` gate in
  the full `research/verify.py` (the Lean-only CI mode is unchanged). `--fetch` re-checks every
  locked blob, the LevyStochCalc manifest pins and the toolchains against GitHub. Candidate code
  by GPT (`gpt-6-astra`), reviewed and corrected in integration; evidence in
  `build/reviews/2026-10-12-levystochcalc-vendor/provenance-lock/`. Verified for its own snapshot
  by the full local receipt `20261012T145253.174906Z`, which also covers the rest of the working
  tree, including the Legendre first variation.
