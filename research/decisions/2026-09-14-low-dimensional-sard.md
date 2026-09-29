# Sard's zero-dimensional and one-dimensional base cases, and corrections to the old route

Date: 2026-09-14. HEAD `2965b32bc79bdb24921c633df12102450eaedcc4`.
Initial independent verification `build/verification/20260913T182956.860385Z/report.json` is passed;
recomputed confirms all 384 files, HEAD, and snapshot are identical, snapshot SHA256 is
`5da779982b20637487bfaf6fbb8aa98ea7c1671485373d9aae6c4b4204077817`.
All uncommitted and untracked results are retained; no commit or push in this round. Historical decisions are not rewritten.

## Completed Independent Theorems

In the new module `formalization/FunctionalInequalities/Analysis/Sard.lean`:


```lean
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem sard_of_finrank_le_one {u : V → ℝ}
    (hdim : Module.finrank ℝ V ≤ 1)
    (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0
```

Complete name is `FunctionalInequalities.Analysis.sard_of_finrank_le_one`.
Only `propext / Classical.choice / Quot.sound`, no direct proof hole or transitive `sorryAx`.
No new auxiliary public theorems added, no copying of Mathlib's zero derivative image set conclusions.
The module only imports Mathlib's Jacobian, ContDiff.Basic, FiniteDimension; local closure imports are empty,
no import of KLS or WIP, no migration, no compatibility aliasing, no certificate aggregation import changes.

* Dimension 0: `Module.finrank_zero_iff` to `Subsingleton V`; the image of any subset under `u` is contained in the single point `{u 0}`, and by `measure_mono_null` it has zero measure. This branch does not use `hu` to establish differentiability, does not require C¹, and even its image set argument applies to any function.
* Dimension 1: `ContinuousLinearEquiv.ofFinrankEq` to `e : ℝ ≃L[ℝ] V`.
  Take `f = u ∘ e` and `S = {z | fderiv ℝ u (e z) = 0}`.
  By C¹, we obtain differentiability of `u`, and then apply the chain rule to each `z ∈ S`'s `HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) z`.
  Convert to within derivative, apply `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume`;
  specify the determinant of zero derivative using `simp`. Finally, use `e.symm` / surjectivity to obtain `f '' S = u '' {x | fderiv ℝ u x = 0}`.
* The measure is always Lebesgue measure on the target ℝ. No need for a measure structure on the domain, inner product, isometry, compact support, boundedness, or measurability of the image of critical sets/critical values. The conclusion is indeed that the set of critical values has zero measure.

## Correction for the previous round

[Regular superlevel set decision](2026-09-14-regular-superlevel-smooth-domain.md) retains original text; its final low-dimensional path
is replaced by this decision. Continuous linear equivalence is sufficient, without needing `LinearIsometryEquiv.measurePreserving`.
The original `fderiv ℝ u x : V →L[ℝ] ℝ` is not a self-map, so its determinant cannot be directly discussed; in this round, the zero derivative on ℝ → ℝ uses the same-dimensional Jacobian theorem, completely without needing the auxiliary lemma "determinant zero if and only if derivative zero".

Original `build/audit/AreaFormulaAudit.lean` has been filled in;
`import FunctionalInequalities.Analysis.Divergence`; test content fully preserved, without disabling checks.
`WIP/CheegerInfimum.lean` only changed the docstring `ae_exists_superlevel` `u - t` to `t - u`,
aligning with the actual negative sublevel set convention used in construction; declarations and proofs unchanged.
HANDOFF, LEAN_DESIGN, two current READMEs, verification, and tasks current statuses have been updated.
Old date cycles are not considered current; historical decisions unchanged.

## Independent Verification and Boundaries

* New module and `Analysis/AreaFormula`, `Analysis/Divergence`, `KLS/Geometry/SmoothDomain` all re-run `lake env lean -DwarningAsError=true` with no diagnostics.
* `build/audit/SardLowDimAudit.lean` strictly passes: 7 clients and target theorem collectively report 8 statements, all standard three axioms.
  Covers general one-dimensional real normed spaces, arbitrary functions on `Fin 0 → ℝ`, C¹ functions on ℝ, constant functions, square functions,
  and independently proves the square function is critical at zero and not constant. General space clients have no inner product or measure instances.
* The repaired AreaFormulaAudit strictly passes, all 6 reports follow standard three axioms.
  Additionally, rerun SuperlevelDomainAudit, SuperlevelSardScope, SardBaseRouteReview, BoundaryChartAudit,
  CheegerInfimumAudit, CutoffRouteReview, DilationAudit, DistanceCutoffAudit, GaussGreenAudit,
  MinkowskiCoareaAudit, MinkowskiConstantAudit, MollifiedBoundaryScope, PerimeterInterfaceAudit,
RecoveryAudit, SubgraphDivergenceAudit; all 16 existing clients strictly pass.
* SuperlevelSardScope reports axioms for `Analysis.sard`, `Analysis.ae_forall_fderiv_ne_zero`, and `SmoothDomain.ae_exists_superlevel`; **all three still contain `sorryAx`**.
  `frontier_superlevel_subset` still only has standard three axioms.
* Each of the three WIP files is compiled in ordinary mode; only **3 / 3 / 5** direct proof hole warnings, no other diagnostics.
  New low-dimensional results do not eliminate the original **11** holes.
* Default `lake build` passes (3393 jobs). The final result of root directory `python3 research/verify.py` is taken as `build/verification/latest.json`; post-verification, all final files and newly added modules' replay scopes are cross-compared.
  Audit clients are located in ignored build directories and do not claim formal certification; their source files and log hashes remain in `research/explorations/2026-09-14-sard-low-dimensional-audit.json`.
* Formal certification remains **24**; the perimeter infrastructure remains **missing**.
  General Sard, weighted coarea, level set measurability, reverse `h_S ≤ h_M`, Cheeger constant equality, and full comparison chain have not been proven. Local verification does not imply remote CI.

## What gaps remain between general Sard and this?

Existing tools already provide the chain rule, continuous/higher-order derivatives, inverse/implicit function theorems, and countable neighborhood covers for second-countable spaces.
Mathlib `Analysis/Calculus/TaylorIntegral.lean` **has multi-dimensional**
`map_add_eq_sum_add_integral_iteratedFDeriv`, it is not appropriate to list the multi-dimensional Taylor expansion as completely missing.
`ContDiff.continuous_iteratedFDeriv` provides continuity of higher-order derivatives;
`Topology/Bases.lean`'s `countable_cover_nhdsWithin` provides countable cover tools.
This repository `Analysis/ImplicitGraph.lean`'s current geometric interface is oriented toward C∞ regular level sets,
and it cannot be taken for granted that all finite-order interfaces required for C^n critical stratifications are fully provided without justification.

Still need to construct and control the layers of `C_j = {x | D^k u(x)=0, 1≤k≤j}`:

1. For the non-flat part `C_j \ C_{j+1}`, construct a local hypersurface from the first derivative of a component of some j-th order derivative, which is non-zero,
   Reduce the critical value problem to one lower dimension, then perform countable gluing. **Must track regularity loss**:
   The charts obtained from the j-th order derivatives of functions on C^n are typically only C^(n-j), which is insufficient for direct use when j > 1.
   apply the induction hypothesis, which requires C^(n-1), to `u ∘ chart`. The rough composition/extension argument under higher-order flatness
   (Or an alternative argument avoiding this loss) still needs to be established; having the implicit function theorem does not equal completing the descent.
2. For the final flat part C_n, derive **uniform** o(r^n) oscillation control on compact sets from Taylor tools,
   Together with the finite covering count of O(r^(-n)) small pieces, use the length of the target interval to control the outer measure,
   Finally countable exhaustion. The existing countable cover API itself does not provide this quantitative zero-measure argument.

Therefore, the general Sard proof foundation cannot be concluded from low-dimensional results and "inductive routes".

### Minimum Next Lemma: Uniform Second-Order Remainder for Flat Points (Unproven)

Suggest first doing an independent `Analysis.exists_uniform_quadratic_remainder` (to be named upon actual API search).
Assume a general finite-dimensional real normed space V, `u : V → ℝ` is C², `K : Set V` is compact.
The precise conclusion is:

```lean
∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ x ∈ K, fderiv ℝ u x = 0 → iteratedFDeriv ℝ 2 u x = 0 →
    ∀ y : V, ‖y - x‖ < δ → |u y - u x| ≤ ε * ‖y - x‖ ^ 2
```

No requirement for K to be pointwise flat; the quantifier uniformly uses the same δ for x in K satisfying the two zero derivative conditions.
y need not belong to K. Empty K, zero-dimensional, and y = x are all included; no domain measure or inner product assumptions are made.
`build/audit/SardNextStatement.lean` **Only strictly verify the type of this proposition** and the existing Taylor API,
no declared theorems are asserted, and `sorry` or axiom placeholders are not used.

It can be proven using the integral-type Taylor expansion (first-order polynomial, second-order remainder), uniform control of second derivatives in a K-neighborhood, and estimates for line integrals, without relying on any WIP results. It is an independent estimate required for the two-dimensional flat layer covering argument, **it does not yet prove that critical values form a null set**, and it does not address descent in non-flat layers or in general dimensions.
