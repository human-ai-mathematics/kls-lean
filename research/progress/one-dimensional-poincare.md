# One-dimensional Poincare scope and attribution

The registered one-dimensional theorem gives the literature Poincare bound
`C_P <= 4 Var` for every log-concave probability law on the real line, including Dirac laws.
The bound uses the variance/gradient convention with no factor one half. The
[sharp Hardy and exhaustion proof](../../formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean)
uses a Borell density, a supporting affine quantile profile and the profile bound
`F(1-F) <= sigma rho`. The [constant-12 proof](../../formalization/FunctionalInequalities/KLS/LogConcave/Line/Poincare.lean)
via median hazard estimates is retained independently. The
[paper register](LITERATURE.md) identifies the exact certificate and source scope.

The coefficient 4 is stated on p. 11 of Alonso-Gutierrez--Bastero (2015), credited there to
KLS (1995), and recalled by Cattiaux--Guillin (2018), equation (2.25). This attribution is
distinct from the local one-dimensional proof. The local proof follows an independent
elementary reconstruction supplied to the project by a collaborator; it does not claim that
the reconstruction appears verbatim in the cited papers or that the monograph was reread
in full. The former literature-search and reconstruction report is preserved locally.

This scope note does not certify an all-dimensional coefficient-4 trace-covariance theorem.
The Lean declarations, certificate ledger and source-bound verification receipts determine
formalization and verification status separately from bibliographic attribution.
