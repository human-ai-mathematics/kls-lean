# L6: C¹ Extension Completion of First-Order Whitney Jets on Compact Sets

2026-09-16. The current round start HEAD/origin/main consists of
`dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`. Start verification receipt
`20260915T171518.856116Z` passed, 479 item, snapshot
`b531c9e4be6397d1d3e5893b4c57eb166ae63ded45f9064f1c4d5c039bb7f124`, consistent with the start source code.
Retain all existing Lean files and historical decisions in original bytes; do not commit, do not push, do not modify the real Git index.

## Exact Conclusion

`FunctionalInequalities.Analysis.WhitneyJet.exists_contDiff_extension`, located at
`formalization/FunctionalInequalities/Analysis/WhitneyConstruction.lean`: in a finite-dimensional real inner product space,
S is compact, F is continuous on S, and (f,F) satisfies the raw L6 uniform first-order remainder condition, then there exists a global C¹ function v,
equal to f exactly on S, and possessing the **ambient derivative** `fderiv ℝ v x = F x` at each point.

No additional assumptions of non-empty, positive-dimensional, interior points, convexity, or finite set are introduced. The public theorem even does not require the raw energy `ContinuousOn f S` (the remainder already entails this continuity), nor does it need to explicitly list CompleteSpace, MeasurableSpace, or BorelSpace. `research/audits/WhitneyConstructionAudit.lean`'s `original_L6` verbatim retains the original L6 proposition text and all instances and assumptions, and provides a proof.
This is the required **compact set** extension along the original route; no additional claim is made regarding a local Whitney condition version on any non-compact closed set.

Combined with the existing `Analysis.uniform_jet_remainder_of_contDiff`, the necessity and sufficiency of the raw consistency remainder condition are now both proven. The "unproven" text in the existing FirstOrderJet and WhitneyExtension audit clients is a snapshot from their historical versions and does not overwrite sources that are already bound to hashes; the current state is governed by this decision and the new client.

## Construction and Estimation

All four new modules rely solely on analyzing module dependencies in Mathlib, without importing KLS or WIP.

1. **WhitneyCover**: Let `r(x)=min(1,dist(x,S))/20`. Vitali extraction yields a collection of pairwise disjoint balls,
   The five-fold ball covers the complement. The eight-fold closed ball remains within the complement and is locally finite with respect to the subspace topology of the complement.
   The eight-fold ball intersecting `ball y (r(y))`, whose center z satisfies
   `r(y)/2 ≤ r(z) ≤ 2r(y)`, `dist(z,y) ≤ 20r(y)`.
   Haar volume comparison provides local cardinality bounds `N=81^finrank`. Cap radius allows handling unbounded complements; does not claim constant sharpness.
2. **WhitneyBump**: Scale a smooth bump with inner radius 5 and outer radius 8.
   The value lies in [0,1], five times the ball is 1, supported within eight times closed ball; there exists a uniform M > 0, with derivative norm ≤ M/r.
   By bounding the derivative of the basic bump with compact support and continuity, the chain rule gives scaling; the zero-dimensional case also holds.
3. **WhitneyPartition**: Sum over the above cover and normalize. The sum is at least 1; we obtain non-negative smooth weights φ,
   Locally finite, summing to 1, and there exists K > 0, `‖Dφ_z(y)‖ ≤ K/r(y)`. A clear proof shows equality on local neighborhoods.
   A finite sum with at most N terms, then take derivative; not mistaking pointwise finite overlap for local finiteness.
4. **WhitneyConstruction**: For each center, choose the closest point p_z on S, and let
   `w(y)=∑ φ_z(y) (f(p_z)+F(p_z)(y-p_z))`. w-smooth on the complement.
   When d = dist(y, S) < 1/2, then r(y) = d/20; related p_z is at most 3d from y, and the closest point a to y is at most 4d.
   Uniform continuity and jet remainder on compact sets of F gives affine difference ≤7ηd.
   Value error uses non-negative weights and 1; derivative error uses `∑Dφ_z=0` to eliminate common affine values.
   The two terms yield `7ηd` and `η+140NKη`, take `η=ε/(8+140NK)`, i.e., giving the desired result
   `εd` and `ε` provide consistent estimates. A global C¹ extension is constructed from this boundary gluing theorem.
   The empty set branch directly takes a constant 0, without using the non-existent nearest point.

## Verification and Evidence

Four new modules and new client compiled with `-DwarningAsError=true`; new client 13 reports only axioms `propext`, `Classical.choice`, `Quot.sound`, none of `sorryAx`. The client includes raw complete L6, empty set, derivative at an arbitrary environment point, zero-dimensional, and the jet of a square function over an infinite compact interval.
22 audit clients were all re-run (research/audits 15, with build/audit 7 already completed), and three WIPs were individually recompiled and remain as 2/2/5. The LevelSetMeasurableAudit has 4 entries, IsoperimetryCoareaAudit has 6 entries, and SuperlevelSardScope has 2 sorryAx reports intentionally retained as open holes in audit.

Per-item logs, commands, hashes, and source code are kept in sync with `research/explorations/2026-09-16-whitney-extension.json`. The final default build, full verification, reexecution of the 195 local module kernels, and precise source code binding are taken as conclusive against the receipt pointed to by `build/audit/whitney-extension/final-snapshot.json`.
The progress diagram is generated using a temporary Git index and a temporary object directory, while the actual index remains unchanged.

## Future boundary

**L6 completed; L6a, L7, L12, and Lipschitz coarea not completed.** Next step is raw L6a:
Extract a countable compact set from Lipschitz functions, covering almost every point, preserving simultaneously differentiability, continuity of derivatives, and uniformly first-order remainder. Then invoke the current L6 piecewise to obtain the exact C¹ piecewise of L7, followed by L12.
The exact quantifiers of L6a remain as determined in the original weighted-coarea-route; Lusin–Souslin is not required for the Lusin extraction.

Direct proof hole **9 (2/2/5)**, certificate **24**, perimeter infrastructure **missing**, all remain unchanged.
Sharp finite regularity Sard, two Cheeger comparisons, dimension-free KLS still open. Progress chart WHIT merged nodes
Also includes unfinished exact C¹ piecewise, thus retains ◐, does not mark the entire Whitney–Lusin path as complete.
