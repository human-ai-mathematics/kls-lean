# Literature register as the primary progress view

Date: 2026-10-02. Source: [issue #8](https://github.com/numina-functional-inequalities/kls-lean/issues/8),
section 1: make the literature register the primary progress view and define paper coverage.
Moving the four exploratory routes out of the progress page is deliberately not done: the
combined route diagram and approach table restored in `6c3437f` stay on
`research/progress/README.md`, and `route-composition.yaml` and `portfolio.json` keep their paths.

## Decisions

- The project goal is to formalize published KLS literature. Proof and infrastructure work is
  selected by a named paper, pinned version and target theorem.
- [`LITERATURE.md`](../progress/LITERATURE.md) is the primary progress register. Each paper row shows
  the target theorem locator, a link to its local Lean statement inventory, local coverage, and
  certificates. Existing ledger certificates whose Blueprint label is mapped from the paper are
  listed as *supporting only*; they never mark the paper covered.
- **Paper covered** means: the main theorem is stated faithfully in Lean (same hypotheses,
  constants, normalization and dimensional scope), proved without nonstandard axioms, and
  registered with a certificate and verification evidence for that exact statement. No paper
  currently meets this criterion.
- The progress hub shows source-review priorities generated from `literature.json`
  (`priorities`). These rank future work; they do not claim the targets are proved.
- The four routes remain on the progress page as exploratory research records sharing the
  analytic infrastructure. They are not formalization targets in their own right.

No Lean source, Blueprint statement, ledger record or certificate changed. No new paper
coverage or certificate is claimed.

## Open owner decisions from issue #8

- Stochastic calculus: build Itô/SDE infrastructure here or build on external Lean efforts
  (Mathlib `Probability/BrownianMotion`, RemyDegenne/brownian-motion). Priority 4 and 5 papers
  stay blocked until this is decided.
- Upstreaming generic infrastructure (coarea, sharp Sard, heat semigroup, Cheeger–Buser) to
  Mathlib, after an API cleanup.
- The local pre-push gate and the remaining CI cost proposals.

## ADMG target review

The [pinned source](https://arxiv.org/html/1603.08412v1#S3) uses Borel measures finite on bounded
Borel sets. Definition 3.3 uses globally Lipschitz approximants and global indicator `L¹`
convergence. Theorem 3.6 equates relaxed lower Minkowski content with perimeter at finite-mass
Borel targets; Lemma 2.1 identifies the relaxed lower and upper contents.

The register names `lipschitzRelaxation_eq_perimeter_of_measure_lt_top`
(`Perimeter/TestClassRelaxation.lean`) for the Definition 3.3 class bridge, and both
`_eq_perimeter_of_finite_on_bounded` endpoints in `Perimeter/RelaxedMinkowski.lean`. Their
statements retain measurable finite-mass targets and the bounded-set finiteness premise, with no
properness or finite-total-mass premise. They identify infima; they do not assert pointwise
equality of content and perimeter. All three were proved in the `6ca1824` snapshot, whose
remote Lean certification passed. No ADMG paper-target certificate is registered, so the paper
is not marked covered. Other results in Section 4 and nonproper locally Lipschitz variants
remain separate.
