# Current KLS handoff

Updated 2026-10-02. This file holds the current state only; earlier sections are preserved in the
[handoff history](research/decisions/2026-10-02-handoff-history.md) and are not current task
authorization. Exact results, scopes and certificates are in the
[paper register](research/progress/LITERATURE.md) and the [node register](research/progress/STATUS.md).

## State

- Remote Lean certification passed for `b9c8a39` on tag `milestone/admg-theorem-3-6`
  ([run 37017009088](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/37017009088),
  2026-10-02). The full local verifier also passed 184 gates for that commit
  (`build/verification/20261002T134816.216230Z/report.json`).
- 27 ledger certificates. `FunctionalInequalities.KLS.kls` in `KLS/Target.lean` is the one
  intentional hole, outside every certificate closure. Dimension-free KLS is open.
- Covered papers: Ambrosio–Di Marino–Gigli Theorem 3.6, certificate
  `thm:relaxed-minkowski-content-perimeter`, accepted by the owner on 2026-10-02
  ([review record](research/decisions/2026-10-02-admg-theorem-3-6-certificate.md)).
- Paper lemma maps cover all 22 downloaded research sources (all but Borell 1974, Bakry–Gentil–Ledoux,
  Alonso-Gutiérrez–Bastero and the two surveys): KLS 1995, Bobkov 1999, E. Milman 2009, Guédon–Milman
  2011, AGS 2013, Eldan 2013, Klartag 2014, Cordero-Erausquin–Klartag 2015, ADMG 2017, Fathi 2019, De Ponti–Mondino 2021, Chen 2021, Klartag–Lehec 2022, Jambulapati–Lee–Vempala
  2022, Klartag 2023, Guan 2024, Lee–Vempala 2024, Bizeul 2025, Klartag–Lehec 2025 (slicing and thin shell),
  Chen–Klartag 2026 and Letwin 2026
  ([progress page](research/progress/README.md#paper-lemma-map)). Source PDFs are kept
  outside the repository.

## Next

1. Formalize De Ponti–Mondino Lemmas 3.2 and 3.3 (elementary monotonicity of explicit functions)
   The remaining unmapped sources are books, surveys or not downloaded.
2. Blocked: the priority-1 Bakry–Émery `C_P ≤ 1/ρ` target waits for the Bakry–Gentil–Ledoux text.

## Open owner decisions

- Stochastic calculus for priorities 4–5: build it here or build on external Lean efforts; evidence
  and a recommendation are in [the options record](research/decisions/2026-10-03-stochastic-calculus-options.md).
- Upstreaming generic infrastructure to Mathlib after an API cleanup.
- CI cost: project build cache or a self-hosted runner while the repository is private
  (no scheduled runs; the opt-in [milestone gate](research/workflow.md#local-milestone-gate) exists).

## Delivery

Follow [research/workflow.md](research/workflow.md): select work by paper and target theorem,
run change-appropriate checks, stage canonical metadata and regenerate progress with
`python3 research/progress/update.py`. Remote CI is Lean-only, on manual dispatch or a
`milestone/**` tag.
