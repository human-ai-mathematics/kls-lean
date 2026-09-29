# Weighted coarea (L11) for general C¹ functions, proof of target T3

2026-09-16. This round **proves the L11 weighted coarea route**, and thereby in the audit client **proves the full statement of the third original goal T3**—that is, the statement of the direct proof hole `KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`. **No WIP files were modified**: migration was a separate decision, so the number of direct proof holes remained unchanged, and that hole remains a hole. Not commit, not pushed, not rewriting historical decisions.

HEAD starts at `737abc396576abfaa596a284e46a706e8e5fd383`; initial verification receipt is
`build/verification/20260915T113452.444474Z/report.json`, identical to the initial workspace:
450 files, SHA256 `856a6b6bd93a8fea3099878a5b65b2cfc4ecfdb0fd1407b60e976f8036f5ad60`.
The initial workspace contains four evidence closeouts from the previous round that were not yet commit, and this round continues upon them.

## Content of this round of proof

New module `formalization/FunctionalInequalities/KLS/Geometry/SmoothCoarea.lean`:


```lean
theorem FunctionalInequalities.KLS.isOpen_regular {u : V → ℝ} (hu : ContDiff ℝ 1 u) :
    IsOpen {x : V | fderiv ℝ u x ≠ 0}

/-- L11 -/
theorem FunctionalInequalities.KLS.coarea_of_contDiff {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞}
    (hu : ContDiff ℝ 1 u) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ)
```

Compared to route record L11, only removed `[CompleteSpace V]` that was never used, with no additional assumptions:
`u` Does not require Lipschitz, bounded, or compact support; `S` Only requires measurability, without requiring boundedness or finite volume;
`g` Allows unbounded, non-integrable, or constantly equal to `⊤`; **no non-degeneracy requirements on the derivative**—the critical set can be the entire space.
Client `target` uses the primitive statement with `[CompleteSpace V]` verbatim and proves it.

## How to connect the two halves, and why both halves are necessary

Let `C = {x | fderiv ℝ u x = 0}`, `R = Cᶜ`. `C` is closed (`isClosed_critical`, already proven in L10),
hence `R` is open (`isOpen_regular`).

* **Left end**: `S = (S ∩ R) ∪ (S ∩ C)` pairwise disjoint measurable, and `C` on `gradient u = 0`,
  Hence the integrand is identically zero on `S ∩ C`, `∫⁻_S ‖∇u‖ₑ·g = ∫⁻_{S∩R} ‖∇u‖ₑ·g`.
* **Right end**: By **L10**, almost every level `t` satisfies `surfaceMeasure V (C ∩ {u = t}) = 0`,
  Thus `(S∩R)∩{u=t}` and `S∩{u=t}` are equal under `surfaceMeasure V` a.e.
  ( `ae_eq_set` + `Measure.restrict_congr_set` ), the two slice integrals are equal almost everywhere with respect to `t`.
* **Intermediate**: For an open set `R` and a measurable subset `S ∩ R`, invoke **L9** to obtain the equality and `AEMeasurable`.
* The same a.e. equality moves the `AEMeasurable` component of L9 to the full slice function (`AEMeasurable.congr`),
  And connect the two integrals on the right-hand side (`lintegral_congr_ae`).

**L9 and L10 are indispensable**: L9 only covers open domains where the derivative is non-zero, L10 only states that slices of critical parts have zero measure; neither provides L11 alone.

## The statement of target T3 has been proven, but the hole remains unfilled.

Client `SmoothCoareaAudit.target_T3` verbatim repeats and proves the T3 of the route,
`SmoothCoareaAudit.wip_isoperimetry_statement` verbatim repeats and proves it with **named arguments**
in `KLS/WIP/CheegerInfimum.lean`

```lean
theorem Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
    {u : V → ℝ} (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ)
```

The statement: it is obtained from L11 taking `S = univ` and simplifying `Set.univ_inter`, **`hK` this Lipschitz assumption**
has not participated at all—this claim originally assumes `ContDiff ℝ 1 u`.

**This round did not move WIP**, so:

* Direct proof holes remain as **2/3/5**, total count **10**; this statement still carries **`sorry`**.
* The correct phrasing is "its statement has been proven based on the **hole-free** module and can be closed upon migration", not "the C¹ coarea hole has been filled". Migration will reduce **`KLS/WIP/CheegerInfimum.lean`** from a **3** hole to a **2** hole, total count **10** → **9**, following the **repository** convention (see the two migration decisions in **2026-09-15**).

## What was not done in this round

* **No proof in Lipschitz case**: `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  is stated for **globally Lipschitz** `u`, without assuming C¹, and remains a direct hole. It requires **L12**,
  And L12 requires the precise C¹ piecewise structure of L7, L7 requires the Whitney first-order jet extension of a closed set from L6—
  L6/L6a/L7 All unproven, no movement this round.
* No proof of sharpness `C^(finrank)` of `Analysis.sard` (still with `sorryAx`, still no downstream consumers).
* No proof of the sharpness of the Eilenberg constant, `smoothConstant_le_minkowskiConstant`,
  `smoothConstant_mul_lintegral_min_superlevel_le`, the two Cheeger constants are equal.
* No expansion of certification or Blueprint `leanok` scope; the certification remains **24**,
  perimeter infrastructure still **missing**.
* No modification made to any existing `.lean` source code (only added one module and one client).
* **No commit, no push.**

## Verification

* `KLS/Geometry/SmoothCoarea.lean` compiles successfully with `-DwarningAsError=true` alone.
* `research/audits/SmoothCoareaAudit.lean` (directly into version-controlled path) to
  `-DwarningAsError=true` Compilation passed: 1 statements `#check` (verbatim reproduction of route record L11) and 11 theorems
  ——`target`, `target_of_not_completeSpace`, `target_T3`, `wip_isoperimetry_statement`,
  `top_weight` (`g ≡ ⊤`), `empty_set`, `everywhere_critical` (constant function, critical set is the entire space),
  `constant_function` (independently of L11) core-certifying `⊤ · 0` boundary: the slice of a constant function on the chosen level is the entire
  The measure of lines and surfaces is infinite, while both sides of the equation are `0`, because exceptional level sets have Lebesgue measure zero).
  Two `preserved_*` named argument signature checks—along with 12 `#print axioms`.
  All  12 statements depend only on `propext`, `Classical.choice`, `Quot.sound`; **not on `sorryAx`**.
* Retest the remaining 16 audit client instances (`research/audits/` 10 entries containing the newly added ones + `build/audit/` 6 entries),
  All strictly compiled successfully, no modifications made; `LevelSetMeasurableAudit`, `SuperlevelSardScope` among the
  `sorryAx` is intentionally reported as an open hole.
* Three WIP files were successfully compiled in practice, with direct proof holes respectively **2/3/5**, total **10**.
* Default `lake build` is connected to the root directory `python3 research/verify.py`. Final verification receipt is
  `build/verification/latest.json`, exactly consistent with the final full code snapshot; evidence JSON is
  `research/explorations/2026-09-16-smooth-coarea.json`, final verification and save
  `build/audit/smoothcoarea-final-snapshot.json`.
