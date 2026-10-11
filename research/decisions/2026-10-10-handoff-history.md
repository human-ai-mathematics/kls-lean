# Handoff history (superseded 2026-10-10)

The following `HANDOFF.md` bullet was current after the 2026-10-09 CEK adoption and was superseded when the CEK
Proposition 12 batch (with the source-condition adapter and Proposition 12 attainment) was adopted on 2026-10-10. It is
preserved byte-for-byte below the rule; it is not current state or task authorization.

---

- **CEK convex duality and Lemma 17 (adopted 2026-10-09):** the root-accepted 13-file patch
  (`build/reviews/2026-10-09-moment-map-letwin-parallel/integration-candidate/`, acceptance c645fee4…) adds
  `Analysis/Convex/{Legendre,AffineMaximum,PointwiseCompactness,RadialExtension}.lean`,
  `Probability/MomentMeasure/{Basic,ConjugateMass,Compactness}.lean`, extends `Probability/ConvexSupport.lean`
  (CEK Lemma 16 for finite measures; the nine existing constants are unchanged) and adds `research/audits/CEK/`.
  Lemma 17 holds with one subsequence and one limit for both inequalities, with `0 ∈ interior (convexHull ℝ μ.support)`
  explicit; the adapter from the Theorem 2 conditions is not promoted. Map:
  `research/api-migration/2026-10-09-cek-scratch-promotion-map.json` (scratch promotion, no production rename);
  Blueprint `lem:cek-point-control`, `lem:legendre-convexification`, `lem:cek-compactness`; `literature.json` CEK L16
  `alternative` (⇑), L17 partial. Proposition 12 attainment, Lemmas 14–15, essential continuity and Theorem 2 remain
  open; the four unused statement definitions (`HasMomentMeasure`, …) stay deferred in lane A scratch.
