# Convex Dirichlet and unit Monge–Ampère interfaces

These modules support Letwin arXiv:2607.24164v1 Lemma 2.2 through
Berman–Berndtsson arXiv:1207.6128v1 Theorem 2.24(ii). The solution chain retains
its `FunctionalInequalities.Analysis.Dirichlet` namespace; family compactness
retains its existing `FunctionalInequalities.Analysis` declarations.

| Module | Responsibility |
| --- | --- |
| [Envelope](Envelope.lean) | Convex subsolutions, boundary barriers and the Perron envelope |
| [Regularization](Regularization.lean) | Lower tests and buffered Moreau regularization, retaining the same value/gradient expansion matrix |
| [Solution](Solution.lean) | The domain-generated unit solution, its measure, negativity and interior strict convexity |
| [Duality](Duality.lean) | Compact conjugates, dual measure identities and unique domain-supporting slopes for the same solution |
| [Regularity](Regularity.lean) | Interior C¹ of the same primal solution from unique supporting slopes |
| [Compactness](Compactness.lean) | Equicontinuity and subsequences for given Dirichlet families |

The solution chain reads from `Envelope` through `Regularization`, `Solution`,
`Duality` and `Regularity`. `Compactness` is separate family infrastructure.
Declarations retain their own dimension and domain hypotheses, including empty-domain
cases where stated. Interior C¹ and a.e. second-order data do not supply classical
C² solutions, everywhere positive Hessians, boundary inverses or the missing
continuity-method closure. See the [current source review](../../../../../research/progress/source-layout-review.md).
