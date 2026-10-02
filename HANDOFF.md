# Current KLS handoff

Updated 2026-10-02. This file holds the current state only; earlier sections are preserved in the
[handoff history](research/decisions/2026-10-02-handoff-history.md) and are not current task
authorization. Exact results, scopes and certificates are in the
[paper register](research/progress/LITERATURE.md) and the [node register](research/progress/STATUS.md).

## State

- Remote Lean certification last passed for `6ca1824` ([run 36846629874](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/36846629874)).
  Later local commits have no remote receipt yet.
- The full local verifier passed 184 gates for the working tree containing the new certificate
  (`build/verification/20261002T095750.910817Z/report.json`), before documentation-only edits.
- 27 ledger certificates. `FunctionalInequalities.KLS.kls` in `KLS/Target.lean` is the one
  intentional hole, outside every certificate closure. Dimension-free KLS is open.
- Covered papers: Ambrosio–Di Marino–Gigli Theorem 3.6, certificate
  `thm:relaxed-minkowski-content-perimeter`, accepted by the owner on 2026-10-02
  ([review record](research/decisions/2026-10-02-admg-theorem-3-6-certificate.md)).
- Paper lemma maps cover KLS 1995, Bobkov 1999, E. Milman 2009, ADMG 2017 and De Ponti–Mondino
  2021 ([progress page](research/progress/README.md#paper-lemma-map)). Source PDFs are kept
  outside the repository.

## Next

1. Push the local commits and tag a `milestone/**` release to obtain the remote receipt for the
   first covered paper (owner decision on timing).
2. Formalize De Ponti–Mondino Lemmas 3.2 and 3.3 (elementary monotonicity of explicit functions)
   and extend the lemma maps (AGS 2013, Eldan 2013, Chen 2021).
3. Blocked: the priority-1 Bakry–Émery `C_P ≤ 1/ρ` target waits for the Bakry–Gentil–Ledoux text.

## Open owner decisions

- Stochastic calculus for priorities 4–5: build it here or build on external Lean efforts.
- Upstreaming generic infrastructure to Mathlib after an API cleanup.
- CI cost: project build cache or a self-hosted runner while the repository is private
  (no scheduled runs; the opt-in [milestone gate](research/workflow.md#local-milestone-gate) exists).

## Delivery

Follow [research/workflow.md](research/workflow.md): select work by paper and target theorem,
run change-appropriate checks, stage canonical metadata and regenerate progress with
`python3 research/progress/update.py`. Remote CI is Lean-only, on manual dispatch or a
`milestone/**` tag.
