# Relative perimeter, covariance core, and the fiber constant

**Date:** 2026-09-06. **Authorization:** the owner asked “then resolve these issues” after the proposal
to parameterize the fiber comparison and supply the covariance-core and relative-perimeter
arguments. This record appends to, rather than rewrites, the earlier Fable review and proof
acceptance. Work remains local on `main`; no commit or push is included.

## Outcome and reading order

The three issues now have concrete mathematical dispositions. The two missing identification
arguments are supplied in Blueprint Appendix A. The numerical route no longer depends on an
unverified factor 4: its comparison has a general finite input `κ`, with a checked published
choice `κ = 12`. The five reusable abstract implications have actual Lean proofs.

Read the statement in chapter 6, the detailed proofs in Appendix A, and then the parameterized
fiber comparison in chapter 7. The analytic statements are proof drafts for review, not Lean
certificates. Their `notready` markers preserve the separate human API-freeze stage. This turn
does not represent an independent peer review or a completed formalization of BV, weighted
Sobolev spaces, disintegration, or log-concavity.

| Review issue | Concrete resolution | Remaining certification boundary |
| --- | --- | --- |
| Relative boundary integral versus Minkowski content | Two inequalities between the infima, with an explicit expansion-and-convolution estimate excluding carrier-boundary charges | The analytic proof is written; concrete Lean formalization remains |
| CMH source domain versus local relaxation | Actual graph-norm approximation, closability, and equality of closed-operator energy with sequential relaxation | The analytic proof is written; concrete Lean formalization remains |
| Unverified universal factor 4 | Active statement uses the primary-source bound 12; the fiber bridge and endpoint are parameterized by `κ` | The numerical theorem and disintegration calculation are not yet Lean-certified; the stronger 4 is optional historical provenance |

## Relative perimeter proof

The smooth tests are domains that locally lie on one side of their smooth boundary. They can
cross the convex carrier boundary and need not be bounded. The integral is over `∂U ∩ Ω`.

The important new step is explicit. Choose `a` in the carrier interior and a closed ball about
`a` on which the density is bounded below by `b₀ > 0`. For `0 < s < 1`, expand the domain using
`v_s(x) = 1_U(a + s(x-a))`, then convolve at scale `ε` with `s ε/(1-s) < r`. If
`x = a + (y-a)/s + z`, then `y = s x + (1-s)b` for a point `b` in that interior ball.
Log-concavity gives

\[
\rho(x)\le (M/b_0)^{(1-s)/s}\rho(y),\qquad
\int |\nabla u_{s,\varepsilon}|\,d\nu
\le s^{1-n}(M/b_0)^{(1-s)/s}P_\rho(U).
\]

The averaged weight vanishes for `y` outside the carrier interior. The prefactor tends to one.
This controls unbounded boundaries and densities that are positive at the carrier boundary.
The appendix also proves the finite global bound `M` directly from log-concavity and total mass.

Minkowski coarea applied to these approximations gives one inequality between the infima.
For the converse, take distance cutoffs of a Borel set along radii realizing its lower Minkowski
content, convolve them, and apply weighted smooth coarea. Layer cake and the 1-Lipschitz function
`t ↦ min(t,1-t)` control the denominator. Finite lower Minkowski content implies that closure
does not add mass, which is used explicitly in the distance-cutoff step.

The external coarea input is Lemma 3.2 of Ambrosio–Di Marino–Gigli,
[Perimeter as relaxed Minkowski content in metric measure spaces](https://arxiv.org/pdf/1603.08412).
Its finite-measure hypothesis applies here, and smooth functions have Euclidean slope equal
to gradient norm. The published metadata were checked against DOI `10.1016/j.na.2016.03.010`.
The density-dependent dilation estimate and the two-infimum argument are provided locally.

A useful boundary check is the uniform law on `[0,1]` and `U=(0,1/2)`. The whole-boundary
integral with the upper-semicontinuous density is 2, while relative perimeter and outer
Minkowski content are 1. Outward dilation moves the unwanted endpoint outside the carrier.
No claim of testwise equality of the two original perimeters is needed.

## Covariance-core proof

The pinned upstream source is still
`kls-exploration@8185e46ffb040e04fea076953e5bcaeb4157d71a`,
`modules/kls/41-cmh-normalization.tex`, lines 165–210. It closes the restrictions of
`ℝ + C_c^∞(V)` in the `L² + covariance-energy` norm.

Appendix A first proves a more general approximation lemma. For any absolutely continuous
probability and fixed linear map `B`, a locally Lipschitz `g` with `g` and `B∇g` square integrable
is approximated by `C_c^∞(V)` in both norms. A spatial cutoff has derivative error bounded by
`‖B‖² c² R⁻² ∫_{|x|>R}|g|² dν`. For each fixed cutoff the function is globally Lipschitz;
convolution has uniformly bounded gradients converging Lebesgue-almost everywhere. Absolute
continuity and dominated convergence then give convergence in the weighted norm.

For the CMH law, let `T = Σ^(1/2)∇`. Positivity and continuity of the density on each compact
subset of the carrier interior allow distributional integration by parts in unweighted local
`L²`. If tests tend to zero while their images under `T` converge, the limiting vector field is
zero. The carrier boundary has zero measure, proving closability. This argument even allows
a positive semidefinite `Σ`; the covariance specialization is positive definite in positive
intrinsic dimension.

The approximation lemma identifies the closures of the actual two test classes. A weak
subsequence of a bounded-energy sequence and weak closedness of the closed linear graph give
the lower bound for the relaxed energy. Graph-norm approximation gives the converse. This
also handles points outside the operator domain: every approximating energy liminf is infinite.
Translation preserves the graph norm and variance, so the optimizer matches the centered source.

The boundary convention matters. For the uniform interval, `g(x)=x` is the restriction of an
ambient compactly supported smooth function and is therefore in the source core. Replacing the
core by `ℝ + C_c^∞((0,1))` would force equal endpoint traces after closure and exclude `g`.
The proof keeps the actual ambient core and imposes no such trace condition.

The same cutoff-and-convolution lemma also fills in the written proof of equality between the
smooth and locally Lipschitz Poincaré constants under the existing absolute-continuity hypothesis.
It does not claim raw ambient-gradient energy descends to `L²` for singular ambient measures.

## Numerical input and fiber route

Bobkov's original [1999 paper](https://www-users.cse.umn.edu/~bobko001/papers/1999_AOP_Isop.pdf)
was inspected at equation (1.3), p. 1904, and Corollary 4.3, p. 1915. They give exactly
`C_P ≤ 12 Var` for the locally Lipschitz normalization used here. Zero variance is handled
separately as a Dirac law.

The active one-dimensional theorem now states 12. The CG → Alonso-Gutiérrez–Bastero → KLS
factor-four chain remains identified as historical provenance. The book page was not obtained
and no independent proof of 4 is claimed. This is an explicit change of the numerical input,
not a proof of the earlier stronger statement; a verified smaller input can later be substituted
without changing the parameterized bridge.

The original `lem:conditional-fiber-form` now imports only the structural substatement of the
pinned upstream result. The new local `lem:conditional-fiber-energy-comparison` assumes a finite
universal fiber input `κ`, proves finite-domain inclusion, and gives the endpoint `κC`. Its
argument spells out finite-bound validity for the literature infimum, Fubini/Rademacher on
conditional lines, division only by positive finite variance, Tonelli, and the frame identity.
Conditional Dirac fibers contribute zero; finite second moment makes the infinite-second-moment
exception null.

The new `cor:conditional-fiber-twelve-bound` applies this to the log-concave conditional densities.
The sidecar explicitly lists the local comparison and the published numerical input in the
fiber branch. It does not attribute these new statements to the upstream agent review. The
local analytic comparison claims remain `open` on the review/formalization lifecycle axis with
no fabricated proof evidence; the numerical input is `imported` with its primary citation.
The test-independent frame question remains the original open KLS-route question.

## Lean changes and verification

Five generic theorems were added in existing modules:

- `Energy.PreEnergy.le_sequentialRelaxation_of_lowerSemicontinuous`;
- `Energy.PreEnergy.sequentialRelaxation_le_of_recovery_sequences`;
- `Energy.PreEnergy.sequentialRelaxation_eq_of_recovery_sequences`;
- `Poincare.HoldsL2Energy.of_energy_le_mul`;
- `Poincare.constantOfL2Energy_le_mul_of_energy_le_mul`.

The first works on arbitrary topological spaces; the two relaxation-comparison applications use
pseudometric spaces and different, possibly empty test classes. The last two require an energy
comparison only on the target's finite domain. This is deliberate: with `κ=0`, requiring a
global comparison would impose an unwanted condition at points where the target energy is
infinite. Finite source energy is derived before using its Poincaré bound.

The existing contraction-transfer proof now uses the same lower-semicontinuous comparison lemma;
its public signature is unchanged. The five new declarations have Blueprint anchors and guarded
transitive axiom checks. They do not instantiate the concrete analytic proofs by assumption or
introduce placeholder analytic declarations.

Verification completed:

- Default `lake build`: success, 3241 jobs; 27 foundation axiom guards.
- Elaborated declaration audit: all 735 previous types and universe lists unchanged, no removal;
  exactly five new declarations, total 740. No nonstandard axioms, unsafe or partial declarations.
- Ledger: six nodes, zero errors; all six certificate files and the ledger are byte-for-byte
  unchanged from the start of this turn.
- Blueprint: eight chapter files, 86 labels, four active routes, zero checker errors.
- All 63 Python tests pass; PDF, web and `checkdecls` pass.
- The 33-page PDF has no overfull boxes, unresolved references or bibliography warnings.
  Nine underfull warnings remain; the changed analytic, numerical, route and appendix pages
  were visually inspected without clipping or formula-layout defects.
- `git diff --check` passes. Unrelated working-tree changes and append-only historical records
  were preserved. No commit, reset or push was performed.

The turn snapshot, source PDFs, rendered QA pages and logs are in
`/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-analytic-bridges-aebi3_o3`.
