# Handoff of 2026-10-04 (superseded)

Historical snapshot of `HANDOFF.md` as committed in `36e7c78` (it still described the BGL work as
uncommitted), archived on 2026-10-07 when the current handoff was rewritten. Its claims and
instructions are unchanged and are historical, not current task authorization. Only relative
Markdown links were rebased for this location. See the [current handoff](../../HANDOFF.md) and the
[earlier history](2026-10-02-handoff-history.md).

---

# Current KLS handoff

Updated 2026-10-04. This file holds the current state only; earlier sections are preserved in the
[handoff history](2026-10-02-handoff-history.md) and are not current task
authorization. Exact results, scopes and certificates are in the
[paper register](../progress/LITERATURE.md) and the [node register](../progress/STATUS.md).

## State

- Remote Lean certification passed for `b9c8a39` on tag `milestone/admg-theorem-3-6`
  ([run 37017009088](https://github.com/human-ai-mathematics/kls-lean/actions/runs/37017009088),
  2026-10-02). The full local verifier also passed 184 gates for that commit
  (`build/verification/20261002T134816.216230Z/report.json`).
- `main` = `origin/main` = `89a85e1` (BGL Chapter 4 map and the Bakry–Émery curvature work, pushed
  2026-10-03). The working tree adds the uncommitted BGL ergodicity work (four new modules, an
  extended `HeatSemigroup/Curvature.lean`, one audit client and documentation; receipts in the
  renewed handoff) and the BGL Corollary 4.8.2 certificate registered on 2026-10-04.
- 28 ledger certificates. `FunctionalInequalities.KLS.kls` in `KLS/Target.lean` is the one
  intentional hole, outside every certificate closure. Dimension-free KLS is open.
- Covered papers: Ambrosio–Di Marino–Gigli Theorem 3.6, certificate
  `thm:relaxed-minkowski-content-perimeter`, accepted by the owner on 2026-10-02
  ([review record](2026-10-02-admg-theorem-3-6-certificate.md)).
- Bakry–Gentil–Ledoux 2014 Corollary 4.8.2, certificate `thm:bakry-emery-poincare`
  (`solutions/ThmBakryEmeryPoincare.lean`, relation `⇑`, with a constructed Gaussian nonvacuity
  witness), accepted by the owner on 2026-10-04
  ([review record](2026-10-04-bgl-corollary-4-8-2-candidate.md)). Coverage is
  for that corollary only; the general Markov-triple framework is not formalized.
- Paper lemma maps cover 23 sources (all but Borell 1974, Alonso-Gutiérrez–Bastero and the two
  surveys; Bakry–Gentil–Ledoux 2014 is mapped for Chapter 4 only): KLS 1995, Bobkov 1999, E. Milman 2009, Guédon–Milman
  2011, AGS 2013, Eldan 2013, Klartag 2014, Cordero-Erausquin–Klartag 2015, ADMG 2017, Fathi 2019, De Ponti–Mondino 2021, Chen 2021, Klartag–Lehec 2022, Jambulapati–Lee–Vempala
  2022, Klartag 2023, Guan 2024, Lee–Vempala 2024, Bizeul 2025, Klartag–Lehec 2025 (slicing and thin shell),
  Chen–Klartag 2026, Letwin 2026 and Bakry–Gentil–Ledoux 2014 (Chapter 4)
  ([progress page](../progress/README.md#paper-lemma-map)). Source PDFs are kept
  outside the repository.

## Next

1. Owner decision on stochastic calculus (see below); it gates every priority-4 paper.
2. Priority 1, Bakry–Émery `C_P ≤ 1/ρ` (BGL 2014 Corollary 4.8.2): certificate registered
   2026-10-04, uncommitted. Placement: owner `solutions/` (paper-target entry point), imports
   `HeatSemigroup/Curvature` and Mathlib's Gaussian integrability, new certificate file only, no
   library API change; the Blueprint node extends `45-shared-analytic-bridges.tex`. Next: the
   full local verifier on the frozen tree, then owner authorization to commit and push, and
   optionally a `milestone/**` tag for remote Lean certification. Previous block:
   [renewed handoff](../handoffs/2026-10-03-renewed-eight-hour-bgl-ergodicity.md).
3. Supporting lemmas formalized on 2026-10-03, none of them a paper main theorem: De Ponti–Mondino
   Lemmas 3.2–3.3, Bobkov Lemma 3.1 (Borell) and part of Proposition 4.1, E. Milman Lemma 4.1,
   Lee–Vempala Lemma 42, Guédon–Milman Lemmas 2.2 (Grünbaum) and A.2, Klartag–Lehec 2025
   Lemma 4.7. Module list, relations and an independent statement review are in the
   [overnight log](2026-10-03-overnight-plan.md) and the
   [review record](2026-10-03-overnight-statement-review.md).

## Open owner decisions

- Stochastic calculus for priorities 4–5: build it here or build on external Lean efforts; evidence
  and a recommendation are in [the options record](2026-10-03-stochastic-calculus-options.md).
- Commit and push of the uncommitted BGL ergodicity work and the BGL Corollary 4.8.2 certificate.
- E. Milman Lemma 4.1 is recorded as `same`, although the real-infimum quantile differs from the
  paper's `−∞` in the degenerate case `f = 0`, `1 − ε < 0`, where the paper's statement is literally
  false. The reviewer called it `partial`; accept the convention or relabel the entry.
- Upstreaming generic infrastructure to Mathlib after an API cleanup.
- CI cost: project build cache or a self-hosted runner while the repository is private
  (no scheduled runs; the opt-in [milestone gate](../workflow.md#local-milestone-gate) exists).

## Delivery

Follow [research/workflow.md](../workflow.md): select work by paper and target theorem,
run change-appropriate checks, stage canonical metadata and regenerate progress with
`python3 research/progress/update.py`. Remote CI is Lean-only, on manual dispatch or a
`milestone/**` tag.

---

# Superseded "Next" items of the 2026-10-07 handoff (after the eight-hour block)

Archived on 2026-10-07 during the four-hour BKL continuation, when items 2 and 3 of the current
handoff's "Next" list were replaced. Text unchanged; historical, not current task authorization.

2. BKL priority 1 (Theorem 3.1 route): Lemma 2.1 on the class `𝒜` (smooth representatives,
   pointwise equation, the tensor lift) and the first-eigenfunction facts of Section 2 (compact
   resolvent, an eigenfunction attaining `λ₁`); they construct the iterates `h_i` used by
   Lemmas 3.2–3.4 and 3.8.
3. Lemma 4.2 conditionally on the Letwin bound: a frozen candidate
   (`build/reviews/2026-10-07-bkl-eight-hour/workers/N-ThirdCumulant.frozen.lean`) has two open steps
   (the second derivative of the tilt average at `0`, and the Cauchy–Schwarz conclusion); it is not in
   the library. Theorem 4.1 needs Eldan localization; the Letwin theorem stays an explicit dependency.
