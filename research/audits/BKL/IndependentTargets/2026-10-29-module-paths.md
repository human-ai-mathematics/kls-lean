# Module path review for the statement baseline (2026-10-29 layout migration)

This review accepts only the owning-module substitution below in the existing elaborated
statement/definition closure. It is a path-only module move recorded in
`research/progress/2026-10-29-layout-map.json`. The prior `REVIEW.md` and
`2026-10-19-module-ownership.md` remain unchanged and retain their discussion.

- Every declaration owned by `FunctionalInequalities.Probability.AffineSupport`:
  `FunctionalInequalities.Probability.AffineSupport` → `FunctionalInequalities.Probability.Support.Affine`.

The root names and order, types, definition values, universe parameters, dependency names,
external leaves, hypotheses, constants, normalization, dimensional scope and certificate
contracts must equal the previous payload after inverse substitution of this module field.
No root or local definition is added or removed. Namespaces and declaration names are
unchanged; no alias, compatibility module or replacement definition is introduced.

The new baseline must be compared with fresh compiler output. A passing build, declaration
axiom audit and kernel replay retain their independently reported scopes; this review alone
supplies no new proof or source-fidelity claim.
