# Linear algebra for codimension-m coarea: the coarea Jacobian

2026-09-16. This round **proves new lemmas**, defining `Analysis.coareaJacobian` and its basic theory as the
**first round of the vector-valued (codimension-m) coarea program**. **No coarea formula is proved this round**;
no hole migration, commit, or push. Direct holes remain **8 (1/2/5)**; certificates remain **24**.

Starting point: `HEAD = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`, also `origin/main`;
starting passed receipt: `build/verification/20260916T120611.840573Z/report.json`: 10 gates,
199 local modules replayed by the kernel, 506 entries, snapshot
`edbda70a4b2d1c0fa48ceabdaa0a88c1d5daa66cc6dcff34e9e14a017aff9762`.

The starting HEAD is **no longer** `dcc158d`: a concurrent session committed `34b9269 docs: add KLS literature map
through July 2026` (documentation only, not pushed). This round leaves its content untouched.

## Boundary

The log-concave Cheeger–Buser line (aligning definitions of the isoperimetric constant through the two-sided
comparison with the Poincaré constant, including the two remaining holes in `KLS/WIP/CheegerInfimum.lean`)
belongs to collaborator **Haocheng Wang** and was deliberately untouched.

## Key finding: Mathlib already has the rectangular volume factor

`Mathlib/Analysis/InnerProductSpace/NormDet.lean` already defines
`LinearMap.normDet f = √det(fᵀ ∘ f)` (the “norm determinant”), with proofs of
`normDet_sq`, `normDet_nonneg`, `normDet_eq_prod_singularValues`,
`normDet_eq_zero_iff_ker_ne_bot`, and that **it is the Hausdorff-measure volume factor**
(`LinearMap.hausdorffMeasure_image`).

`normDet` is the Jacobian for the **area** formula (maps from finite-dimensional spaces).
The coarea Jacobian is its adjoint dual: `coareaJacobian L = normDet Lᵀ`.
This round uses that definition **without rebuilding determinant theory**, so little new linear algebra is needed for the codimension-m program.

## Exact results

`Analysis/CoareaJacobian.lean` (**depends only on Mathlib**; its local import closure contains only itself):

```lean
def coareaJacobian (L : V →L[ℝ] W) : ℝ :=
  LinearMap.normDet (LinearMap.adjoint (L : V →ₗ[ℝ] W))
```

* `coareaJacobian_nonneg`.
* `coareaJacobian_sq`: `J² = det (L ∘ₗ Lᵀ)`. The determinant is on the **target**, hence an `m × m`
  Gram determinant, not `n × n`. This is a defining property.
* `adjoint_one`: the adjoint of a real-valued functional sends `1` to its Riesz representative.
* `coareaJacobian_eq_norm_toDual_symm`: the coarea Jacobian of a real-valued functional is the norm of its Riesz representative.
* **`coareaJacobian_fderiv`**: `coareaJacobian (fderiv ℝ u x) = ‖gradient u x‖`.
* `ker_adjoint`: `ker Lᵀ = (range L)ᗮ`.
* `coareaJacobian_eq_zero_iff` / `coareaJacobian_ne_zero_iff`:
  **`J ≠ 0 ↔ L is surjective`**. This identifies the regular set for the codimension-m formula; for `W = ℝ`, it becomes nonvanishing gradient.

## Why `coareaJacobian_fderiv` is central to this round

It shows that **the already proved and audited scalar theory is the `m = 1` case of this density**:
the integrand `‖gradient u x‖` in L11/L12/L13 equals the newly defined coarea Jacobian pointwise.
Subsequent codimension-m work therefore requires no rewriting, restating, or weakening of existing conclusions;
the scalar chain remains unchanged. This compatibility is proved, not merely asserted.

## Work excluded from this round

* **No coarea formula is proved**. The vector-valued coarea equality remains unproved and is not marked complete.
* No area formula for dimension-reducing maps, codimension-m L1–L12, or codimension-m implicit-function normal form.
* No hole migration: direct holes remain **8 (1/2/5)**; sharp Sard, the two Cheeger comparisons, and the five Energy holes are untouched.
* No expansion of certificate or Blueprint `leanok` scope.
* **No commit or push**; the real Git index is unchanged.

## Next steps (within the program, without a time commitment)

1. Area formula for dimension-reducing maps: lift `LinearMap.hausdorffMeasure_image` to a local C¹ version.
2. Codimension-m regular case (analogous to L9): use a parametric implicit function theorem on the open set `J ≠ 0` to construct families of fiber graphs.
3. Codimension-m critical part (analogous to L10), then assemble the pieces.

The scalar L1–L13 chain took about ten rounds; this program makes no promise of being faster.

## Validation

* The new module and client compile with `-DwarningAsError=true`, without `sorry`.
* The 17 axiom reports in `research/audits/CoareaJacobianAudit.lean` use only
  `propext`, `Classical.choice`, and `Quot.sound`; boundary clients include identity and zero maps,
  subsingleton targets, and orthogonal projection on `EuclideanSpace ℝ (Fin 2)`.
* All 26 audit clients were rerun (19 in `research/audits`, 7 in `build/audit`) and passed strict checks.
* The three WIP files were compiled separately: direct holes remain **1/2/5, total 8**, as in the preceding round.
* Default `lake build` and root-level `python3 research/verify.py` pass. Evidence JSON:
  `research/explorations/2026-09-16-coarea-jacobian.json`; final snapshot check:
  `build/audit/coarea-jacobian/final-snapshot.json`.
