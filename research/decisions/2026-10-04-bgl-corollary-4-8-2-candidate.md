# BGL Corollary 4.8.2: certificate candidate for owner review

Date: 2026-10-04 (window 2 of the BGL ergodicity block). Status: **accepted and registered**
as `thm:bakry-emery-poincare` (see [Owner decision](#owner-decision)). The candidate text below is
kept as reviewed; registration followed the ADMG precedent: owner semantic review, then a
certificate entry point in `solutions/`.

## Source

Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators*, Grundlehren 348
(Springer 2014), Corollary 4.8.2, printed p. 212. P(C) is Definition 4.2.1 (printed p. 181):
`Var_μ(f) ≤ C E(f)` for every `f ∈ D(E)`.

## Statement correspondence

| Book | Lean |
| --- | --- |
| `ℝⁿ`, Lebesgue measure | any finite-dimensional real inner product space `V` with `volume` (`EuclideanSpace ℝ (Fin n)` is `ℝⁿ`; `n = 0` included) |
| `dμ = e^{-W} dx` a probability measure | `(ν : Measure V) = volume.tilted (-W)`, density `e^{-W} / ∫ e^{-W}`; the book's case is `∫ e^{-W} = 1` |
| `W` smooth | `ContDiff ℝ 2 W` (weaker) |
| `∇∇W ≥ ρ Id`, `ρ > 0` | `∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ W x v v`, `0 < ρ` |
| P(1/ρ) on `D(E)`, `E(f) = ∫ |∇f|² dμ` | `literatureConstant_le_inv_of_eq_tilted`: `C_P(ν) ≤ 1/ρ` for the literature constant (optimal constant over locally Lipschitz tests with the local slope) |
| (same, smooth functions) | `smoothTest_holds_inv_of_eq_tilted`: `Var_ν(f) ≤ ρ⁻¹ ∫ ‖∇f‖² dν` for smooth `f ∈ L²` with `‖∇f‖ ∈ L²` |
| (same, Dirichlet domain) | `norm_center_sq_le_inv_mul`: `Var(u) ≤ ρ⁻¹ ‖T̄ u‖²` for every `u ∈ D(T̄)`, in the heat model `ν = m.tilted (-U)` for any Haar `m` |

`D(T̄)` is the closure of `C_c^∞` in the energy norm (`C_c^∞` is a core by
`exists_seq_smooth_tendsto_graph`), which is the book's `D(E)` for this Markov triple, with
`‖T̄ u‖² = E(u)`. `closedWeightedOperator_id_constant_eq_literature` identifies the optimal constant
on `D(T̄)` with the literature constant, so the first and last rows state the same inequality.

## Points for review

1. The hypotheses are weaker than the book's: `C²` instead of smooth, any normalization, any
   finite-dimensional inner product space. The conclusion is the same inequality.
2. Log-concavity and full support of `ν` are derived (`Density/Tilted.lean`), not assumed.
3. No general Markov triple, manifold or `CD(ρ, ∞)` framework is claimed (Proposition 4.8.1 stays
   partial).
4. The proof follows the book's semigroup route: curvature bound, finite-time decay, ergodicity.
   Ergodicity comes from `ker T̄ = constants`, proved through the weak gradient and translation
   invariance (`Energy/Euclidean/ZeroGradient.lean`, `WeightedGradient/Kernel.lean`), together with
   strong convergence on `(ker T)ᗮ` (`Generated/Convergence.lean`).
5. Clients: `research/audits/BakryEmeryErgodicityAudit.lean`. It covers the unchanged conditional
   interface, the kernel on constants, the Dirichlet-domain form, `ℝⁿ` for every `n` and `n = 0`,
   and the scaled Gaussian `W = ρ‖x‖²/2` (Hessian form `ρ‖v‖²` proved there). It reports 22
   standard-only axiom sets. The client takes the Gaussian law as a hypothesis, and elaboration
   does not show sharpness.

## Proposed certificate (after acceptance)

`solutions/ThmBakryEmeryPoincare.lean` with `certificate := literatureConstant_le_inv_of_eq_tilted`
and `smoothTest := smoothTest_holds_inv_of_eq_tilted`, a ledger node, Blueprint node,
`CERTIFICATES` entry, Lake root, and `target_certificate` / `target_review` for BGL2014.

## Owner decision

2026-10-04: the owner accepted the statement review with relation `stronger` (`⇑`): the
hypotheses are weaker than the book's (`C²`, any normalization, any finite-dimensional real inner
product space) and the test class is larger, with the same inequality. The owner also asked for a
constructed nonvacuity witness before registration. `Solutions.ThmBakryEmeryPoincare.gaussian`
builds `volume.tilted (-(ρ/2)‖·‖²)` as a probability measure from Mathlib's
`GaussianFourier.integrable_cexp_neg_mul_sq_norm_add` and `isProbabilityMeasure_tilted`, proves
its Hessian form is exactly `ρ‖v‖²`, and applies `certificate` and `smoothTest` with every
hypothesis discharged, in every finite-dimensional real inner product space (examples on `ℝ³` and
`ℝ⁰`). This closes the gap noted in point 5: the audit client takes the law as a hypothesis, the
certificate does not.

Registered: `solutions/ThmBakryEmeryPoincare.lean` (three axiom guards, standard axioms only), the
ledger node, the Blueprint node in `45-shared-analytic-bridges.tex`, the `CERTIFICATES` entry, the
Lake root, the node record, and `target_certificate` / `target_review` / `target_declarations` for
BGL2014. Coverage refers to the selected Corollary 4.8.2 only; the book's general Markov-triple
framework, Proposition 4.8.1 (partial), `CD(ρ, n)` and log-Sobolev results are not covered, as
recorded in the paper's `remaining` field.
