# L6a, L7, L12: Lipschitz weighted coarea completion

2026-09-16. Head starting point and origin/main are both
`dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`, this round does notcommit, does not push, does not alter the true Git index.
The starting point verification receipt `20260915T181325.091264Z` passes, 486 entry, snapshot
`01eaccf7af20c08a011382e6c204b98c2613daa1e93f919da50c039cbee53e1c`, identical to the starting point source code.
All existing Lean files, historical decisions, and old audit clients remain unchanged in bytes.

## Exact Results

* **L6a**: `Analysis.LipschitzJet.exists_compact_jets`, in `Analysis/LipschitzJet.lean`. In finite-dimensional real normed spaces, with an arbitrary additive Haar measure and any globally Lipschitz real function, there exists a countable compact slice cover almost everywhere; on each slice, the function is differentiable, the ambient derivative field is continuous, and the first-order remainder is uniform.
* **L7**: `Analysis.exists_contDiff_pieces`, in `Analysis/LipschitzC1Pieces.lean`. In finite-dimensional real inner product spaces, there exists a countable collection of pairwise disjoint measurable slices covering almost every point; each slice has a global C¹ representative, and the antiderivative is differentiable on the slice, with the representative's value and the **ambient derivative** equal pointwise to the original function's value and ambient derivative.
* **L12**: `KLS.coarea_of_lipschitz`, in `KLS/Geometry/LipschitzCoarea.lean`. For any globally Lipschitz real function u, measurable set S, and measurable `g : V → ℝ≥0∞`, the slice integral's `AEMeasurable` **and** the full weighted coarea formula for the original path are provided.

No assumptions added regarding C¹, positive dimension, bounded domain, finite volume, finite weight, integrability, regular value, or `SFinite surfaceMeasure`; the empty set, zero-dimensional, and infinite weight are all within the original statement. The normalization of surfaceMeasure remains completely unchanged.
Public theorems do not separately list the CompleteSpace implied by finite-dimensional cases; new client `original_L6a`, `original_L7`, `original_L12`, and `original_T2` **verbatim retain the original route statement** and provide proofs.
These are neither `#check` nor new axioms.

## Implementation of L6a: Direct Regularization of the Remainder in the Environment

No need to establish a general Lusin theorem, nor is Lusin–Souslin misused. Take a fixed countable dense vector sequence q_i, and define

`goodSet u ε δ = {x | ∀i, ‖q_i‖<δ → ‖u(x+q_i)-u(x)-Du(x)q_i‖≤ε‖q_i‖}`.

1. `measurable_fderiv_apply_const` together with u being continuous provides goodSet measurability; it only quantifies countable sequences.
2. For fixed x, the condition on vector variables is a closed condition (the open ball condition implies a closed inequality), and is extended to all h by density.
3. At differentiable points, for each ε > 0, there exists some radius `1/(m+1)` satisfying the condition; as the radius decreases, goodSet increases.
4. For differentiable points in a measurable set A with finite measure, for each precision `1/(n+1)`, select a uniform radius from an increasing cover,
   discard exceptions with measure less than d_n, and pre-select `∑d_n<ε/2`. After intersecting over all precisions, then use tight inner regularity,
   discard those with measure less than ε/2, obtaining a compact set C ⊆ A, and `μ(A\C)<ε`.
5. A is taken as the intersection of the differentiable point set and a compact covering of the space, ε is taken as `1/(k+1)`, and (m,k) is reencoded as a natural number.
Rademacher assigns measure zero to the complement of the differentiable point set; any small loss of measure is assigned zero measure to the complement of the final countable compact piece.

This method yields a stronger estimate: the base point x lies in C, while the increment endpoint x+h may lie outside of C.
Thus, derivative continuity can be directly inferred: compare the two remainder terms at x and y for the same small increment h, and then use a global Lipschitz bound to control `u(x+h)-u(y+h)` and `u(x)-u(y)`. On the spherical shell in `δ/2≤‖h‖<δ`, we obtain a bound for the operator norm; `ContinuousLinearMap.opNorm_le_of_shell` provides uniform continuity of the derivative field on the patch.
This step does not require the patch to have an interior point, nor does it derive equality of ambient derivatives from equality of function values on the patch.

## Gluing of L7 and L12

L7 Apply the proven L6 to each compact jet, then take the `disjointed` difference slice. The difference slice remains measurable and lies within the original compact slice; its union remains invariant, so the exact value and derivative equality, as well as almost everywhere coverage, are preserved.

L12 Let P_j = S ∩ the j-th piece. L11 is used for the j-th C¹ representative; equal values identify slices, equal ambient derivatives identify gradients.

On both sides, the lintegral additivity of measurable, disjoint, countable unions is used; L11 assigns AEMeasurable to each slice, allowing exchange of outer integral and countable sum. The volume-null remainder outside the differentiability pieces is handled by the **L2 null-measure slice theorem**, and cannot be solely based on Rademacher. On both sides, the restriction measure is used a.e. set equality removes the complement, so infinite weights are not required for control.

The overall slice AEMeasurable of L12 is also directly provided by existing L5.

## Audit

`research/audits/LipschitzCoareaAudit.lean` Import a new hole-free module independently, prove the four statements of original L6a, L7, L12, and T2, and byte-by-byte compare the textual content of the statements in the original decision. 15 The report of new axioms includes only `propext`, `Classical.choice`, `Quot.sound`, without `sorryAx`.
Boundary clients include: real norm function (also proving it is not differentiable at 0), any weight on unbounded full space, constant function with constant ∞ weight (outer slice integral is 0), zero-dimensional space.

Three new modules and client compiled strictly; 23 audit clients (research/audits 16 of them, with build/audit 7 already existing)
All rerun. Each WIP is individually recompiled and remains **2/2/5**. The old client intentionally reports existing raw WIP holes;
The new client's T2 proof is distinct from the declaration under the old name, which still contains sorryAx; the two must not be conflated.
All commands, log hashes, original statement comparisons, and source integrity checks are at
`research/explorations/2026-09-16-lipschitz-coarea.json`. The final default build, complete verification,
198 local module kernel replays and exact source code binding are based on
`build/audit/lipschitz-coarea/final-snapshot.json`'s referenced verification receipt.

## Current Boundary and Next Step

**L6a, L7, L12 are completed. The mathematical proof of Lipschitz weighted coarea is completed.** The original T2 statement has been proven by the new client as the S=univ special case of L12, but the old
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` remains in
`KLS/WIP/AnalyticPrerequisites.lean`. This round ends at the user-specified L12, with no migration or rewriting of the old entry.

**The next step is to independently migrate T2**: compare signatures before and after migration, including CompleteSpace and parameter order, `pp.all`
Receive the full space special case of L12; then rerun the previous consumer axioms audit in order to reduce the direct proof hole count from 9 to 8.
Current source has a direct proof hole still **9 (2/2/5)**, certification **24**, perimeter infrastructure **missing**.
Sharp finite regularity Sard, two Cheeger comparisons, energy's 5 hole and dimension-free KLS remains open.
This round does not increase Blueprint leanok or certification, and does not mislabel completion of coarea as completion of KLS.
