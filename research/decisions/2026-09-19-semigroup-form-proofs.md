# Semigroup generation route: `S1`–`S4` proved (partial implementation round)

2026-09-19, the sixteenth round of the day, following the [route round](2026-09-19-semigroup-generation-route.md).
`S1`, `S2`, `S3`, and `S4` are **all proved**; `S5`–`S8` are untouched. Direct holes remain **0**, certificates **26**. No commit or push.

Starting point: `HEAD = origin/main = 7986adf`.

## Results

New module `formalization/FunctionalInequalities/Analysis/Semigroup/Form.lean` (general real Hilbert spaces,
without measures, log-concavity, or KLS quantities):

| Obligation | Declaration | Description |
| --- | --- | --- |
| `S1` | `Analysis.Semigroup.completeSpace_graph` | Closed `T` implies complete `T.graph` |
| `S2` | `Analysis.Semigroup.min_one_mul_graphNormSq_le` | Coercivity in the graph norm, with constant `min 1 s` |
| `S4` | `Analysis.Semigroup.norm_le_of_weakResolvent`, `inner_nonneg_of_weakResolvent` | A weak resolvent solution satisfies the contraction bound and pairs nonnegatively with the data |

Also added: `WeakResolvent` (a predicate for the weak resolvent equation, without constructing a resolvent operator)
and `graphNormSq_eq_inner_of_weakResolvent` (the identity obtained by testing with `v = u`).

## Two departures from the route

* **`S1` is nearly immediate.** The route estimated 40 lines at low risk; the proof is one line.
  `LinearPMap.IsClosed` is **by definition** closedness of the graph as a set, and Mathlib's `IsClosed.completeSpace_coe` gives completeness directly.
* **`S2` does not need `s > 0`; the route included an unnecessary hypothesis.** The module's version holds for **every real `s`**:
  for `s ≤ 1`, reduce to `(s − 1)‖u‖² ≤ 0`; for `s > 1`, reduce to `‖Tu‖² ≤ s‖Tu‖²`.
  The audit restates and proves the original route statement with `0 < s`, accepting and discarding the assumption.
  This is **recorded explicitly**. It is a strictly stronger lemma, not a weakening of the route.

## Explicit limits

`S3` (existence and uniqueness of the resolvent, assembling Lax–Milgram) is not yet proved; this is the main work in the route.
`S5`–`S8` (Yosida approximation, strong convergence, semigroup law, generator) are unproved, and `S6` remains high risk.
**Even proving all of `S1`–`S8` would not prove the Buser half**: the semigroup is only the first of four prerequisites.
Gaps two (Markovianity), three (Bakry–Émery Γ), and four (small-time heat estimates) are untouched.
`thm:logconcave-cheeger-poincare-comparison` has no `\leanok`; gap entries in `tasks.json` are **unchanged**
(the first gap remains open as a whole). No new certificate or Blueprint change.

## Bookkeeping

The aggregate root `FunctionalInequalities.lean` imports the new module so that `lake build` and CI build it.
The repository already has 8 modules outside every library root's import closure; this does not add a ninth.

## Validation

`lake build` passes (3518 jobs). The module and audit pass `lake env lean -DwarningAsError=true`,
with **0 errors and 0 warnings**. The audit client `research/audits/SemigroupFormAudit.lean` restates and proves
`S1`, `S2`, and `S4` verbatim, plus two boundary cases (zero operator and zero data).
**All 10 `#print axioms` reports contain only `propext, Classical.choice, Quot.sound`, with 0 occurrences of `sorryAx`**;
log: `build/audit/semigroup-form-proofs/scope-audit.log`.

## Addendum: `S3` proved (same day, immediately after the above)

New module `Analysis/Semigroup/Resolvent.lean`; `existsUnique_weakResolvent` is `S3`:

| Result | Declaration | Status |
| --- | --- | --- |
| `S3` uniqueness | `weakResolvent_unique` | Proved without closedness, density, or Lax–Milgram: test the difference of two solutions against itself |
| `S3` existence | `exists_weakResolvent` | Proved **using orthogonal projection, not Lax–Milgram** |
| `S3` | `existsUnique_weakResolvent` | Proved |

**The proof changed and is shorter than the planned route.** The route proposed assembling Lax–Milgram:
package `B_s` as `G →L[ℝ] G →L[ℝ] ℝ`, prove `IsCoercive`, then apply Riesz.
Instead, use **orthogonal projection**: rescale the second coordinate by `√s`, setting `G_s = {(u, √s·Tu)}`. Then

```
⟪g, h⟫ = ⟪u,v⟫ + s⟪Tu,Tv⟫,    ⟪f,v⟫ = ⟪(f,0), h⟫
```

The ambient inner product **is exactly** the form, so the solution is the orthogonal projection of `(f,0)` onto `G_s`
(`Submodule.starProjection`; closedness follows from closedness of `T` by continuous preimage).
This needs **neither** `IsCoercive`, `bilinearComp`, the `→L⋆` interface of `innerSL`, nor Riesz,
avoiding the anticipated interface obstacle entirely. Thus **`S2` is unused** in the proof of `S3`
(it remains a valid prerequisite for the Lax–Milgram route, which this proof does not take).

**The `Dense (T.domain)` assumption in `S3` is redundant**, like `0 < s` in `S2`: uniqueness does not even need closedness,
and existence needs only closedness. Density is needed to express the solution as `(1 + sT*T)⁻¹f`, where the adjoint enters;
this module does not take that step. The audit restates and proves the original `route_S3` with `Dense`, accepting and discarding it.
