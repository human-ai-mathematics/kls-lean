# Analysis/Matrix family (2026-10-10)

Rule 1 of [naming.md](../naming.md) requires three or more modules for one mathematical object to form a family
directory. The flat `Analysis/MatrixTrace.lean`, `MatrixPositivity.lean` and `MatrixDeterminantDerivative.lean`
(real matrices: functional-calculus traces, positivity and Gram floors, the determinant derivative) move to
`Analysis/Matrix/{Trace,Positivity,DeterminantDerivative}.lean`, byte-identical, with namespace
`FunctionalInequalities.Analysis` and every declaration unchanged. The root-accepted spectral prerequisites of the covariance step of
Letwin Theorem 1.2 (p. 14, preceding (2.21)) are placed in `Analysis/Matrix/Sign.lean` with exactly their accepted imports, so their proof values equal the
accepted objects (extending `MatrixPositivity` changed one value through its additional imports). This is a
module-path migration plus one new module; there is no declaration rename and no compatibility module. Complete map:
[`2026-10-10-analysis-matrix-family-map.json`](../api-migration/2026-10-10-analysis-matrix-family-map.json).
