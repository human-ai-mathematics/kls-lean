# Remaining-family maintenance

This is a live maintenance register for layout and documentation. It changes no proof,
hypothesis, normalization, dimensional or certificate status.

## Unresolved debt

| Item | State | Acceptance requirement |
| --- | --- | --- |
| C2 | Cross-top-level relocation of `KLS/Geometry/Perimeter/MetricBV` remains a candidate; the family stays with its actual KLS perimeter consumers | An actual independent reuse consumer and a dependency benefit; until then the existing owner is retained |

## Accepted structural constraints

- Existing qualified public names are unchanged; module moves and namespace or name changes are
  separate migration classes with their own maps and validation.
- The metric BV tests require bounded function support on arbitrary metric spaces; infinite
  perimeter may reflect an empty approximation class, and recovery is asserted only under the
  original finite-perimeter condition.
- The shared private weak-derivative calculus helpers stay together, as do the CEK trace and
  Stein chains; no further split is justified solely by file length.
- Generic cutoffs, weak-derivative foundations, Hessian owners, trace algebra, the proximal object
  boundary, the Stein identity boundary and the CEK producer layers are placed as described in the
  current family READMEs; BKL's per-paper reorganization is likewise settled.

## Source ownership and checks

Owners and imports are listed in the generated [module directory](../../formalization/MODULES.md)
and described in the [source map](../../formalization/README.md) and the family READMEs. A
proposed or implemented layout is accepted only with exact source and interface comparison, real
clients and the change-appropriate checks of the [workflow](../workflow.md); a targeted build
alone does not establish acceptance, and each acceptance applies to its recorded snapshot.

The [section-variable review](variable-scopes.md) records the shared-context pattern,
the maintained mathematical boundaries and the required interface comparisons.
