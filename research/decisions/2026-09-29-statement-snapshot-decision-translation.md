# Statement-snapshot baseline: re-pin after translation of the decision record

Date: 2026-09-29 (Asia/Shanghai). Scope: metadata only. This record repairs the
statement-snapshot baseline (`research/a-series/statement-snapshot/golden.json`) whose
pinned decision record was rewritten by a documentation-translation commit. It changes no
Lean declaration, no golden semantic field and no checker logic, and it is separate from the
phase-23 proof work (integrated upper content of thickenings) that exposed it.

## Observed defect

- The golden baseline pinned the decision record
  `research/decisions/2026-09-20-formalization-directory-organization.md` with SHA-256
  `c9ecd836c12886c1424549753bb7143a6d3f18e53d33ac78d50940dcaab4d570` (the content at
  `f8e4ca8`, `2f9f7e2` and `2e7b712`).
- Commit `443f352` ("docs: translate repository documentation into English", 2026-09-29
  18:34 +0800) translated that historical record into English; its SHA-256 at `HEAD` is
  `5b60e0876ca67e984573eaea43b6c152c158f941b50e56ca003e23aa7708930b`.
- Consequently `statement_snapshot.check_snapshot` reports "snapshot decision record changed;
  append a new record instead of rewriting it" on every snapshot at `443f352`, and
  `research/verify.py` stops at the `statement-golden` gate before `declaration-audit` and
  `leanchecker`. The full-verifier run `build/verification/20260929T115711.018636Z/report.json`
  (frozen phase-23 snapshot `3992f3f7…0439b5`) failed with exactly this single error; the runs
  `20260928T193145.404166Z` and `20260929T061540.560399Z`, both on snapshots carrying the
  pre-translation record, passed all 165 gates.

## Semantic comparison

The statement snapshot itself is unchanged. Compiling the current snapshot
(`lake build FunctionalInequalities.KLS.Statement`, `#statement_snapshot` over the seven
roots with `pp.all`) and calling `statement_snapshot.compare_snapshot(current, golden)` returns
`[]`: the toolchain, `lake-manifest` hash, printing options, roots, external dependencies and all
26 local declarations are identical to the golden. The gate log of the failed run states
"Compared 26 local declarations with the explicit baseline" and no dependency difference. This
was confirmed independently by the Codex reviewer on the same frozen snapshot.

## Decision

Following the checker's own rule, a new decision record is appended rather than rewriting
the old one: this file. The baseline is re-pinned with the existing workflow

```sh
python3 research/statement_snapshot.py update \
  --decision research/decisions/2026-09-29-statement-snapshot-decision-translation.md
```

which recomputes the snapshot from the current sources and stores it together with this
record's path and hash. Because the semantic comparison is empty, the only field of
`golden.json` that changes is `decision`. The translated historical record is preserved as it
now stands in `HEAD`; the checker is not weakened; the seven roots and the 26 declarations are
not touched. Provenance of the translation is the commit `443f352` itself, not this repair.

## Not claimed

No proof status changes. No remote CI, commit or push is part of this record. The phase-23
result and its receipt are documented separately in
`research/handoffs/claude-bv-overnight.md` and `build/audit/minkowski-upper-integrated/`.
