# Stage 2A protocol and scheduling correction (2026-10-11)

Metadata-only correction of current-state controller and scheduling labels (Task H.4 proposal, approved in scope with
root's required refinements in CLAUDE-REQUEST-I, Task I.1), based on `build/reviews/2026-10-11-bkl-a4-goal-setup/STATE.json` (sha256 `fb6ee22b…` at writing) and
`build/reviews/2026-10-11-bkl-a4-goal-setup/root-current-controller-20261011/PROTOCOL-DIAGNOSIS.json`.

- Current controller: Codex chat `01a128eb-e254-7d63-bd15-05abfcb7aaec`; `01a12708-9c39-7f33-aa23-3b135e6d1de2` is historical. Updated in `HANDOFF.md` and the dated plans that
  still named it as current (`research/handoffs/2026-10-11-bkl-a4-goal.md`, `2026-10-10-bkl-staged-goals.md`,
  `2026-10-09-api-first-goal.md`); no goal completion claim changes.
- The same original authorized connection, key and provider continue; individual proof units deliberately pin
  authorized strong models. The current transport diagnostic (same Astra model) reproduced a chat/completions
  metadata/store incompatibility while stateless Responses requests succeed. Earlier packets keep their own recorded
  classifications or unknown outcomes; user-key invalidity or balance exhaustion is not established, and no owner
  credential restoration is required. The separately selected Sol attempt returned an upstream `rate_limit_error`.
- E1 pointwise, the full original E1 identity and E3 are independently accepted, not in source; B2 has no accepted proof
  (root owns the v6 feedback preflight). Q4R is adopted only after the copy verification of its own record.

No proof, status or certificate change: Lemma A.4, Lemma A.5, Letwin Theorems 2.5/1.2, BKL Lemma 4.2 and `KLS.kls`
remain open. The replaced passages are preserved verbatim below; their claims are unchanged here.

`HANDOFF.md`:

```text
Current controller: Codex chat `01a12708-9c39-7f33-aa23-3b135e6d1de2`. On 2026-10-11 the owner requested a
```

`HANDOFF.md`:

```text
reviewed but not adopted. Q3 is adopted in source
```

`HANDOFF.md`:

```text
The new E1
single-response run (session 90364) is terminal: a client transport failure (`ConnectionResetError`, exit 1) after one
consumed request, with no proof response and an unknown remote outcome
(`build/reviews/2026-10-11-bkl-a4-goal-setup/E1-TERMINAL-OBSERVATION.json`); the consumed request is not replayed. Reconcile
```

`HANDOFF.md`:

```text
(original packets terminal rejected); the new E1 run is terminal without a proof response, the new Q4R request
returned HTTP500 with no response (history preserved), and E1 typed-v3 is prepared but not dispatched. Authoritative handles override old
scheduling labels; no source A.4/A.5 or paper-status upgrade is made.
```

`research/handoffs/2026-10-11-bkl-a4-goal.md`:

```text
Current controller: Codex chat `01a12708-9c39-7f33-aa23-3b135e6d1de2`. The Goal service returned
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
The current controller is Codex chat `01a12708-9c39-7f33-aa23-3b135e6d1de2`. The owner requested a new
```

`research/handoffs/2026-10-09-api-first-goal.md`:

```text
The current controller is `01a12708-9c39-7f33-aa23-3b135e6d1de2`, under the owner
```
