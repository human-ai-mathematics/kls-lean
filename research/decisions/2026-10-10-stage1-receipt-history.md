# Stage 1 receipt history (2026-10-10)

The full local receipt `build/verification/20261010T093056.948739Z/report.json` (scope full, status passed, report sha256
`7b258cf3708a0b85b55554db003166fd1ded33bed12cdb30ce952e011b75abe2`, snapshot sha256
`7e50d2bc4a44d07196d047691ef3d10b544d3c3aa55fc13ea5fd96892317f308`) covers the integrated Stage 1 sources
(BKL (74) grouped with (72); the covariance step of the proof of Letwin Theorem 1.2, p. 14, preceding (2.21)),
adopted from the root-accepted combined candidate. The current-state passages below were replaced afterwards
by a documentation/metadata-only edit (no Lean change; the receipt does not verify that edit). They are
preserved verbatim; their claims are unchanged here.

`HANDOFF.md`:

```text
- Latest full local verification: `build/verification/20261009T191839.009889Z/report.json` (report sha256
  `70553bf76f029cfc23760fd841eab6df0a36c865f7342ac9cc5ff03ad9d52423`, snapshot sha256
  `d39c40d44d5c53005898734c861d6762527472e0fc27e287571e689102408d57`, 1252 snapshot files, 249 gates, 238 strict research
  audits, 830 standard declaration axiom reports, local kernel replay of the 495 owned modules; upstream compiled
  dependencies are trusted, not replayed). It covers the adopted CEK Proposition 12 batch (below) but not the Stage 1
  integration (below), whose matching full local receipt is pending and is recorded here after it passes (verified Lean
  snapshot ≠ final whole tree). Still open: the SDE/Itô dynamics,
  CEK essential continuity, Euler–Lagrange identification and Theorem 2, the regularity bridge (H2), Letwin's
  quadratic-form bound with constant 8, BKL Theorem 1.1 and `KLS.kls`. Earlier receipts apply to their own snapshots
  only; the previous paragraph is preserved in
  [the 2026-10-09 receipt history](research/decisions/2026-10-09-receipt-history.md).
```

`HANDOFF.md`:

```text
BKL/Letwin Stage 1 (adopted 2026-10-10; matching full local receipt pending):**
```

`HANDOFF.md`:

```text
is proved, independently accepted and integrated; it completes with its matching full local
receipt. Pending stages: 2 — Letwin Theorem 1.2 (constant-2 gradient-energy and isotropic constant-8 forms)
for BKL Lemma 4.2; 3 —
```

`HANDOFF.md`:

```text
1. **Stage 1 matching full local receipt (active):** run the full local verifier on the integrated snapshot
   after the intended-index progress regeneration and record the receipt under "State"; Stage 1 then completes.
2. **Stage 2 (pending): Letwin Theorem 1.2,** `Var ≤ 8‖M‖²_HS` for isotropic log-concave laws, the input of BKL
   Lemma 4.2 (moment-map producer, Lemmas 2.1/2.2, Proposition 2.8, Theorem 2.5, the Stein-kernel identity (2.21)).
3. **Current focus: BKL Theorem 1.1.**
```

`HANDOFF.md`:

```text
4. New BKL modules go
```

`HANDOFF.md`:

```text
5. **Owner decision (outside the staged goals):**
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
| 1 — active |
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
| 2 — pending |
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
; Stage 1 completes with its
  matching full local receipt.
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
; the matching full local receipt is pending, and there is no paper coverage.
```

`research/progress/literature.json priorities[rank 1].next_step`:

(JSON string value, verbatim)

```json
"Immediate: the matching full local receipt of the integrated Stage 1 (BKL (74) grouped with (72); the covariance step of the proof of Letwin Theorem 1.2), then Stage 2: Letwin Theorem 1.2 (Var ≤ 8‖M‖²_HS) for Lemma 4.2. "
```
