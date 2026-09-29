# Start L6: Boundary Gluing of Jet Compact Sets

2026-09-16. A completes first: `20260915T170113.583163Z`, 10 gates, 190 local module replays,
475 entries, snapshot `051483acb993b037ccccd2682cb0c735a9d373ce20cc399defc54a384b10fa09`.
B starts with HEAD and origin/main both being `dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`.
Not commit, not push, raw FirstOrderJet two files, other existing Lean files and historical decisions unchanged.

## The completed step is boundary analysis

New file `formalization/FunctionalInequalities/Analysis/WhitneyExtension.lean`, namespace
`FunctionalInequalities.Analysis.WhitneyJet`. Depends on Mathlib only through FirstOrderJet, does not depend on KLS/WIP.

* `affine f F a y = f a + F a (y-a)`, is an affine polynomial given a jet.
* `norm_affine_sub_le`: The difference between two affine polynomials is controlled by the jet remainder and the difference of derivatives.
`dist_nearest_le`: If a is the closest point of y over S, x ∈ S, then dist(a,x) ≤ 2 dist(y,x).
`hasFDerivWithinAt`: The remainder condition provides the derivative within the set; **does not** identify the fderivWithin on sparse sets,
  Also does not claim the original function is differentiable in the ambient space.
`hasFDerivAt_of_nearby_affine`: The candidate function equals f on S and the affine jet at the relative nearest point on the complement
  With an error of o(dist(y,S)), its ambient derivative at every point of S is exactly F.
`continuousAt_of_nearby_field`: The derivative field on S equals F, and on the complement it equals F with respect to the nearest point.
  The difference is consistently o(1), then the field is continuous at every point of S.
`contDiff_of_nearby_jet`: By combining the differentiability on the complement and the continuity of the derivative, we obtain global C¹ and exact derivative.
`exists_contDiff_of_compl_approx`: Only input the w that is C¹ on the complement; let v take the value f on S and on Sᶜ
  Take w, the derivative field is also piecewise concatenated. These two estimates ensure that v is globally C¹ and exactly realizes f, F.
  **w can be discontinuous and have incorrect values on S**, so there is no assumption of the existence of a global extension.

These local analysis theorems only require real normed spaces and S compactness; **no need for finite dimensionality, nonemptiness, interior point, or positive dimension**.
compactness is used for the existence and closedness of nearest points; continuity of F on S suffices at the boundary. The original L6
`ContinuousOn f S` does not need to participate in this step (the remainder is already given for interior differentiability), the original objective remains unchanged.
At point x∈S, select nearest point a, and use dist(a,x) ≤ 2 dist(y,x). The value error is split into three terms:
candidate value error, the remainder of f between x and a, and the action of F_a - F_x on y-a; taking each ε/4 yields total error ε dist(y,x).
Derivative continuity uses the triangle inequality and ε/3. Finally invoke `contDiff_one_iff_hasFDerivAt`.

## Unfinished Precise Statements

The following is only the **statement type checking** in the client. It is not a new axiom, not a declaration placeholder, and not a previously proven lemma.
All assumptions of original L6 remain unchanged; proving it allows invocation of `exists_contDiff_of_compl_approx` to obtain original L6.

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ},
    IsCompact S → ContinuousOn f S → ContinuousOn F S →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖) →
    ∃ w : V → ℝ, ContDiffOn ℝ 1 w Sᶜ ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
          ‖w y - WhitneyJet.affine f F a y‖ ≤ ε * infDist y S ∧
            ‖fderiv ℝ w y - F a‖ ≤ ε)
```

## Next-step construction and acceptance points

Construct a Whitney ball/cube cover on Sᶜ with scale rᵢ comparable to distance to S; choose the nearest point pᵢ ∈ S, and construct a smooth partition of unity φᵢ. It must be proven that the cover is locally finite, with quantitative overlap bounds and derivative bounds O(1/rᵢ), and it is not sufficient to invoke the general partition of unity interface lacking these quantitative estimates.
Let `w(y) = ∑ᵢ φᵢ(y) * affine f F pᵢ y`. For the nearest point a to y,
`∑φᵢ=1` gives value error; in the derivative comparison, use `∑Dφᵢ=0` to cancel the common affine term f F a y.
The remaining two types of derivative errors are `∑φᵢ(F pᵢ-F a)` and
`∑Dφᵢ * (affine f F pᵢ y - affine f F a y)`.
The recently proved affine comparison, jet remainder, and derivative continuity individually control these, and must collectively yield the above **two** estimates.
The empty set is treated separately with a constant candidate; no additional assumptions about S having interior points, convexity, finiteness, or V having positive dimension are allowed.

## Check and Status

`research/audits/WhitneyExtensionAudit.lean` Strictly compile and audit 7 library lemma and 6 client theorems,
13 axiom reports contain only propext, Classical.choice, Quot.sound. Client includes: empty set, arbitrary point ambient derivative, zero-dimensional, and the complement candidate with incorrect value on S. Additional counterexamples prove: a constant function can have id as within-derivative within a point, but its ambient fderiv remains 0; the equality of derivatives cannot be derived from equal values on a sparse set. No new form holes, no new axioms, no expansion of certificate/Blueprint leanok scope.

A The 20 client and 3 WIP source codes have been re-run with byte-level preservation; B's new module and client are separately and strictly compiled.
The final default build, complete verification, and replay of 191 modules are finalized based on the final verification receipt, with exact paths and snapshots cross-checked and stored in `build/audit/whitney-boundary/final-snapshot.json`, and individual evidence stored in `research/explorations/2026-09-16-whitney-boundary.json`.

**L6 incomplete, L6a/L7/L12/Lipschitz coarea incomplete.** Direct proof hole still 9 (2/2/5), certification 24,
perimeter infrastructure missing; sharp finite regularity for Sard and Cheeger, two comparisons, dimension-free KLS remain open.
Progress chart marked with ◐ for partial boundary work, cannot regard it as complete L6 or complete Whitney–Lusin pathway completion.
