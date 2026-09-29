# L13: Local Lipschitz Weighted Coarea

2026-09-16. This round **proves a new theorem** `KLS.coarea_of_locallyLipschitz`, relaxing the scalar-weighted coarea from "global Lipschitz" to "**local Lipschitz**". No hole migration, no commit, no push, no rewriting of historical decisions. The direct proof hole remains **8 (1/2/5)**, the certification remains **24**, the perimeter infrastructure remains **missing**.

Starting HEAD and `origin/main` are both `dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`; starting verification receipt is
`build/verification/20260916T074938.349555Z/report.json`: 10 gates, 198 local module kernel replays,
495 entries, snapshot `115a7e19375062d43882a1ff2caa16b5ca52b0791af25734aacfff66ac61735c`.

## Boundary: Cheeger sets are outside the current scope

Two holes of `KLS/WIP/CheegerInfimum.lean` (`Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le` and `Isoperimetry.smoothConstant_le_minkowskiConstant`), as well as alignment among several definitions of isoperimetric constants and the Cheeger↔Poincaré bidirectional comparison, have been submitted to collaborator Haocheng Wang today. This round will not touch this line, but will instead advance the general coarea and `Analysis`/`Geometry` analysis foundations.

## Exact Results

`KLS/Geometry/LocallyLipschitzCoarea.lean`:

```lean
theorem FunctionalInequalities.KLS.coarea_of_locallyLipschitz
    {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞}
    (hu : LocallyLipschitz u) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ)
```

**This is a common generalization of L11 and L12.** `LipschitzWith K u → LocallyLipschitz u` Recover L12,
`ContDiff ℝ 1 u → LocallyLipschitz u` Recover L11 (`ContDiff.locallyLipschitz`),
so neither Lipschitz constant nor C¹ is needed. The statements, proofs, and positions of both original theorems remain **unchanged**,
neither are restated using L13, nor are any new aliases introduced.

**Generalization is strict.** The client provides `x ↦ x² + ‖x‖` and proves within the same file that it is locally Lipschitz,
**not globally Lipschitz for any constant** (contradicting `x = K+1` and `dist_le_mul`),
**not differentiable at 0** (otherwise `‖·‖ = witness - x²` would be differentiable at 0, contradicting `not_differentiableAt_norm_zero`). Thus it lies outside both L11 and L12, while L13 covers it.

No bounded, finite volume, finite weight, integrability, regular value, or `SFinite surfaceMeasure` assumptions are included;
`S` is an arbitrary measurable set, with weights possibly constant at ∞, zero-dimensional within the statement scope, and surface measure normalization is invariant.

## Proof: Reduction of Semi-Open Ring Band

`V` Finite-dimensional hence proper, closed ball compact.

1. `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact` gives `u` in
   `closedBall 0 (k+1)` Lipschitz constant on ; McShane extension `LipschitzOnWith.extend_real`
   Replace it with a **global** Lipschitz `v k`, and `EqOn u (v k) (closedBall 0 (k+1))`.
2. Take the half-open annular strips `A k = ball 0 (k+1) \ ball 0 k`. They are pairwise disjoint, measurable, and
   `x ∈ A ⌊‖x‖⌋₊`, hence covers the entire space. Let `P k = S ∩ A k`.
3. The key is `P k ⊆ ball 0 (k+1)` using an **open** ball: an open ball is a neighborhood of each point, where `u` and `v k` are equal on it,
   So `EventuallyEq.gradient_eq` gives pointwise `gradient u x = gradient (v k) x`,
   Rather than being equal only on a sparse set. The same reason makes `P k ∩ {v k = t} = P k ∩ {u = t}`.
4. For each `P k` use L12, then concatenate using the countable disjoint union of `lintegral_iUnion` and `lintegral_tsum`;
   The piecewise `AEMeasurable` required to interchange exterior integrals with countable sums is precisely the first component of L12.
5. Measurability of global slices is likewise obtained by decomposition: for each `t`,
   `∫⁻ y in S ∩ {u=t}, g` is the sum of integrals over countably many disjoint pieces (`{u=t}` is measurable due to `u` being continuous).
   Again use `AEMeasurable.tsum`. Here there is **no** assumption of unbounded `S` with global `LipschitzOnWith`,
   Therefore, L5 cannot be directly referenced and must proceed along this countable decomposition.

## Audit

`research/audits/LocallyLipschitzCoareaAudit.lean` Only import the new hole-free module, do not import any WIP.
10 The axiom report uses only `propext`, `Classical.choice`, `Quot.sound`:
Verbatim reproduction and named argument instantiation of `original_L13`; **do not mention** `coarea_of_lipschitz` but recover it from L13
L12's `recovers_L12`; **do not mention** `coarea_of_contDiff` but recover L11's `recovers_L11` from L13;
Three properties of the witness function and its coarea formula; constant ∞ weight; zero-dimensional.

The local import closure of the new module comprises 30 modules, none of which are WIP modules.

## What was not done in this round

* No touch on `KLS/WIP/CheegerInfimum.lean` two holes (assigned to Haocheng Wang).
* No migration of any holes; direct proof holes remain **8 (1/2/5)**; no proof of sharp `C^(finrank)` `Analysis.sard`, five holes of Energy, or dimension-free KLS.
* No expansion of certification or Blueprint `leanok` scope; no misattribution of coarea generalization as KLS progress.
* No claiming L13 as vector-valued coarea: the goal remains real-valued `u : V → ℝ`, with no coarea Jacobian.
* **No commit, no push**, actual Git index unchanged.

## Verification

* The new module and new client both compile successfully with `-DwarningAsError=true`, no `sorry`.
* All 25 audit clients are rerun (`research/audits` 18, `build/audit` 7), all passing strictly.
* Each of the three WIP files is compiled in practice, with direct proof holes respectively **1/2/5**, total 8, consistent with the previous round.
* Default `lake build` and root directory `python3 research/verify.py` pass; JSON evidence is
  `research/explorations/2026-09-16-locally-lipschitz-coarea.json`, final verification saved
  `build/audit/locally-lipschitz-coarea/final-snapshot.json`.

---

**Subsequent pointer (2026-09-16, same day later; body unchanged):** The next repository semantic alignment round updates
`lem:relative-perimeter-smoothing`'s infrastructure from `missing` to `available`,
and moves the genuinely missing Cheeger infrastructure to `lem:relative-perimeter-cheeger-infimum`
(still `missing`, 2 gaps). Thus the previous statement "perimeter infrastructure is still **missing**" was an accurate record at the time of this round's execution and was superseded shortly thereafter. By the convention of not rewriting historical decisions, the body retains its original form, with only a pointer added here.
This alignment round does not prove new theorems, does not modify mathematical statements, does not add certificates, and explicitly includes the current L13.
See [semantic alignment decision](2026-09-16-semantic-alignment.md).
