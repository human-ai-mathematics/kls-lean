# Target-scope reviews

Current scope reviews of the registered paper targets, referenced from `literature.json`. Each
section states the pinned source, the Lean statement that is certified, the correspondence
relation, and what is not covered. Full paper coverage lives in the
[literature register](LITERATURE.md); source-step narratives live in the
[proof path](PROOF-PATH.md).
The [statement review](statement-review.md) records the contract checks across all registered
certificates and distinguishes these from a review of every auxiliary proof.

## Bakry–Gentil–Ledoux, Corollary 4.8.2 (`thm:bakry-emery-poincare`, relation stronger)

Source: *Analysis and Geometry of Markov Diffusion Operators*, Grundlehren 348 (Springer 2014),
Corollary 4.8.2 (printed p. 212), with P(C) from Definition 4.2.1: `Var_μ(f) ≤ C E(f)` on `D(E)`.

| Book | Lean |
| --- | --- |
| `ℝⁿ` with Lebesgue measure | any finite-dimensional real inner product space `V` with `volume` (`n = 0` included) |
| `dμ = e^{-W} dx` a probability measure | `(ν : Measure V) = volume.tilted (-W)`; the book's case is `∫ e^{-W} = 1` |
| `W` smooth | `ContDiff ℝ 2 W` (weaker) |
| `∇∇W ≥ ρ Id`, `ρ > 0` | `∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ W x v v`, `0 < ρ` |
| P(1/ρ) on `D(E)` | `Solutions.ThmBakryEmeryPoincare.certificate`: `Poincare.LocalSlope.Intrinsic.constant ν ≤ ρ⁻¹`, the literature constant over locally Lipschitz tests; `smoothTest` gives the smooth-test form |

The reviewed extension allows `C²` potentials, automatic normalization and any finite-dimensional
inner product space. Locally Lipschitz finite-energy tests include smooth finite-energy tests;
this does not make them a larger class than the book's completed form domain `D(E)`, nor does
the certificate identify that abstract domain with the local test class. Log-concavity and full
support of `ν` are derived, not assumed. The proof follows the book's semigroup route (curvature
bound, finite-time decay, ergodicity from `ker T̄ = constants`). `Solutions.ThmBakryEmeryPoincare.gaussian`
instantiates the certificate on `volume.tilted (-(ρ/2)‖·‖²)` with every hypothesis discharged.
The separate `norm_center_sq_le_inv_mul` proves the inequality on the actual closed-gradient
domain; `closedWeightedOperator_id_constant_eq_literature` identifies its optimum with the
literature constant. These supply the local form-domain bridge, without formalizing the book's
general Markov-triple framework.
Not covered: the general Markov-triple framework, Proposition 4.8.1, `CD(ρ, n)` and the
log-Sobolev results.

## Ambrosio–Di Marino–Gigli, Theorem 3.6 (`thm:relaxed-minkowski-content-perimeter`)

Source: arXiv:1603.08412v1, Theorem 3.6 with Definition 3.3 and Lemma 2.1, for Borel measures
finite on bounded Borel sets.

`Solutions.ThmRelaxedMinkowskiContentPerimeter.certificate` states, for a metric space `V`, a
Borel measure `ν` finite on bounded sets and every measurable `B` with `ν B < ∞`, that the relaxed
lower Minkowski content equals the Definition 3.3 Lipschitz relaxation of the perimeter:
`MetricBV.relaxedMinkowskiContent ν B = MetricBV.lipschitzRelaxation ν B`. The left side relaxes
lower Minkowski content over measurable set sequences whose indicators converge to `1_B` in
global `L¹(ν)`; the right side relaxes integrated local slope over globally Lipschitz function
sequences converging to `1_B` in global `L¹(ν)`. The statement
retains measurable finite-mass targets and the bounded-set finiteness premise, with no properness
or finite-total-mass premise, and asserts no pointwise equality of content and perimeter. Not
covered: the other results of Section 4 and nonproper locally Lipschitz variants.

## Bizeul–Klartag–Lehec, Theorem 1.1 and the KLS target (`thm:bkl-poincare`, relation alternative)

Source: arXiv:2610.05474v1 (PDF SHA-256 `86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`), Theorem 1.1 (p. 2) with its proof
(p. 30): a universal `C > 0` with `C_P(μ) ≤ C` for every `n ≥ 1` and every isotropic log-concave
probability measure on `ℝⁿ`, where `C_P` is the least constant in (5) for locally Lipschitz
`f ∈ L²(μ)`.

**Certificate.** `Solutions.ThmBklPoincare.certificate` is the literal source form:
`∃ C : NNReal, 0 < C ∧ ∀ n, 1 ≤ n → ∀ μ, LogConcave μ → Isotropic μ → Intrinsic.constant μ ≤ C`.
One constant is chosen before every dimension and law; there is no compactness, regularity or
moment premise beyond isotropy; `C_P` is the literature local-slope constant, which agrees with
`‖∇f‖` almost everywhere for log-concave laws.

**Producer and condition.** The closed producer `KLS.BKL.Localization.exists_isotropicBound`
(`KLS/BKL/Poincare.lean`) applies the Theorem 3.1 criterion and Proposition 7.1 with the regular
reduction to `exists_cumulantBound_of_letwinCompact letwinCompactBound`, giving `C = 2 C_{3.1} K`. The conditional
`conjecture_of_letwinCompact` keeps the compact Letwin bound as an explicit hypothesis; the closed
`conjecture` discharges it with the proved `letwinCompactBound`, and `KLS.kls : KLS.Conjecture`
(`KLS/Target.lean`) is that producer composed with the affine/isotropic reduction. `KLS.Conjecture`
itself is unchanged: one `C` before every dimension and every log-concave law with finite second
moment, with `Intrinsic.constant μ ≤ C · ‖Cov μ‖_op`; dimension zero and singular or affine
supports are included.

**Relation.** The certificate states Theorem 1.1 itself; the map records it as *alternative*
because the proof runs through the finite-horizon cutoff stochastic-localization route and the
compact-to-general passage rather than the source's uncut Eldan process, and the bound extends to
every finite-dimensional inner product space. Coverage is decided by this registered certificate.

**Not claimed.** The uncut Eldan process (strong solution, uniqueness, non-explosion) and the
literal identities (68)–(73); the infinite-horizon (95); Lemmas 4.3, 5.1 and 5.2 along the uncut
process; Lemma 4.2 for every isotropic law; Letwin's noncompact Theorem 1.2; the four exploratory
routes, whose gates stay open.
