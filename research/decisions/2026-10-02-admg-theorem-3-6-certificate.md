# ADMG Theorem 3.6 paper-target certificate

Date: 2026-10-02. Status: accepted by the owner on 2026-10-02 after semantic review; committed
locally, remote milestone run pending.

## Placement plan

- Owner: metric BV perimeter family (`KLS/Geometry/Perimeter`, namespace `KLS.MetricBV`).
- Scope: Theorem 3.6 of Ambrosio–Di Marino–Gigli, arXiv:1603.08412v1, with the perimeter of its
  Definition 3.3, at the paper's standing measure assumption.
- Destination: a new certificate entry point `solutions/ThmRelaxedMinkowskiContentPerimeter.lean`.
  No library module is added or changed: the certificate composes two existing library theorems,
  as the ledger convention allows ("one named certificate directly referencing the reusable
  library").
- Imports: `Perimeter.RelaxedMinkowski`, `Perimeter.TestClassRelaxation` and Mathlib's
  `Measure.Haar.InnerProductSpace` (for the Lebesgue typed application).
- API impact: none. New ledger node, Blueprint node, `CERTIFICATES` entry, Lake root and
  `nodes.json` description; `literature.json` marks it as the ADMG2017 `target_certificate`.

## Statement correspondence

| Paper (v1) | Lean |
| --- | --- |
| `(X, d)` metric space, `m` Borel, finite on bounded Borel sets | `[MetricSpace V] [MeasurableSpace V] [BorelSpace V]`, `hν : ∀ s, IsBounded s → MeasurableSet s → ν s < ⊤` |
| Borel `A` with `m(A) < ∞` | `hB : MeasurableSet B`, `hνB : ν B < ⊤` |
| `A^r = {d_A < r}`, `M₋(A) = liminf_{r↓0} (m(A^r) − m(A))/r` | `Isoperimetry.minkowskiContent`, open `Metric.thickening`, `ENNReal` subtraction, `liminf` along `𝓝[>] 0` |
| `RelMin₋(A)`: inf over `A_h → A` in `m`-measure of `liminf M₋(A_h)` | `MetricBV.relaxedMinkowskiContent`: measurable `A_n`, `∫⁻ ‖1_{A_n} − 1_B‖ₑ → 0` |
| Definition 3.3: inf over `f_h ∈ Lip(X)`, `∫|f_h − χ_A| → 0` of `liminf ∫ |∇f_h|` | `MetricBV.lipschitzRelaxation`: globally Lipschitz real `f_n`, same `L¹` convergence in `ℝ≥0∞` |
| `|∇f|` slope, `0` at isolated points | `Energy.LocalSlope.apply` (same convention) |
| `RelMin₋(A) = Per(A)` | `certificate : relaxedMinkowskiContent ν B = lipschitzRelaxation ν B` |

Points for review:

1. Values are in `[0, ∞]` on both sides, and both infima are `⊤` for an empty class, as in the
   paper. Convergence in measure to a finite-mass target forces eventually finite masses, so the
   `ENNReal` subtraction in `minkowskiContent` agrees with the paper's difference on the tail.
2. For `A = ∅`, the paper's `d_∅` makes `A^r` empty; `Metric.thickening r ∅ = ∅` agrees.
3. The paper's approximating sets are implicitly Borel (contents are defined for Borel sets);
   Lean requires `MeasurableSet`, which is the same σ-algebra under `BorelSpace`.
4. `upper` additionally gives the relaxed upper content; with `certificate` it is Lemma 2.1's
   second clause. Neither statement claims a pointwise identity for individual sets.

## Evidence

- `lake build solutions.ThmRelaxedMinkowskiContentPerimeter` succeeds; the four `#guard_msgs`
  axiom reports show only `propext`, `Classical.choice`, `Quot.sound`.
- The composed statement was previously compiled strictly as the audit client
  `research/audits/MetricBVDefinitionClassAudit.lean`.
- Both library theorems were part of the `6ca1824` snapshot, whose remote Lean certification
  (run 36846629874) passed.
- The full local verifier passed for the working tree containing this certificate: 184 gates,
  173 strict audit clients, 371 axiom reports, 353 replayed modules
  (`build/verification/20261002T095750.910817Z/report.json`, local only). Only documentation
  changed afterwards.

## Independent review

An independent model review (gpt-5.6-luna, given the paper's Sections 2–3 LaTeX source and the
Lean definitions and certificate) judged the certificate faithful, with nothing weaker than the
paper. Its notes were points 1–3 above. It also suggested a note on σ-finiteness; this is not
needed: a metric space is the countable union of the balls `B_n(x₀)`, so finiteness on bounded
sets already gives σ-finiteness, as the paper states, and the theorem uses no further hypothesis.

## Remaining step

Push and tag `milestone/<name>` to run remote Lean certification for the exact commit, and record
the run in the handoff. Until then ADMG coverage rests on the local receipt.
