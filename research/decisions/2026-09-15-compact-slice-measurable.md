# Measurability of Sections of Compact Sets (L3)

2026-09-15. This round **proves L3 of the weighted coarea route**: for a continuous function on a compact set, the `surfaceMeasure` of its level slices is Borel measurable as a function of the level. No commit, no push, no alteration of historical decisions. The starting HEAD is
`2965b32bc79bdb24921c633df12102450eaedcc4`; the starting verification receipt is
`build/verification/20260914T213846.405397Z/report.json` (bit-for-bit identical to `build/verification/latest.json`), and the recomputed full snapshot matches the receipt: 416 files, SHA256
`c81cf7e5258b328c5c9546bf6d134b41a65ec626cd76137bdeaddb01c2acf373`. The bit-for-bit comparison here refers to per-file SHA256 (including deleted items) and consistent full snapshot structure, not merely the HEAD.

## Content of this round of proof

### New module `formalization/FunctionalInequalities/Analysis/HausdorffContent.lean`

Only depends on Mathlib, arbitrary `EMetricSpace`. Name the inner infimum of `Measure.hausdorffMeasure_apply`, and add a variant using only open set covers:

```lean
def FunctionalInequalities.Analysis.familyCost (d : ℝ) (T : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d

def FunctionalInequalities.Analysis.coverCost (d : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (T : ℕ → Set X) (_ : A ⊆ ⋃ i, T i) (_ : ∀ i, Metric.ediam (T i) ≤ r), familyCost d T

def FunctionalInequalities.Analysis.openCoverCost (d : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (T : ℕ → Set X) (_ : ∀ i, IsOpen (T i)) (_ : A ⊆ ⋃ i, T i)
    (_ : ∀ i, Metric.ediam (T i) ≤ r), familyCost d T
```

Two main conclusions:

```lean
theorem FunctionalInequalities.Analysis.iSup_openCoverCost_eq_hausdorffMeasure
    {d : ℝ} (hd : 0 ≤ d) (A : Set X) :
    ⨆ n : ℕ, openCoverCost d ((n : ℝ≥0∞) + 1)⁻¹ A = μH[d] A

theorem FunctionalInequalities.Analysis.measurable_hausdorffMeasure_inter_levelSet
    {d : ℝ} (hd : 0 ≤ d) {S : Set X} {u : X → ℝ}
    (hS : IsCompact S) (hu : Continuous u) :
    Measurable fun t : ℝ => μH[d] (S ∩ {x | u x = t})
```

Intermediate interfaces: `hausdorffMeasure_eq_iSup_coverCost`, `coverCost_le`, `openCoverCost_le`,
`openCoverCost_lt_iff`, `coverCost_mono_scale`, `coverCost_le_openCoverCost`,
`coverCost_le_hausdorffMeasure`, `exists_cover_familyCost_lt`, `exists_thickening_radius`,
`openCoverCost_le_hausdorffMeasure`, `isOpen_setOf_slice_subset`,
`upperSemicontinuous_openCoverCost_slice`.

### `KLS/Geometry/SurfaceSlicing.lean` New normalization packaging

```lean
theorem FunctionalInequalities.KLS.measurable_surfaceMeasure_inter_levelSet
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {u : V → ℝ} {S : Set V}
    (hu : Continuous u) (hS : IsCompact S) :
    Measurable fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t})
```

Compared to the L3 route record, removed `[CompleteSpace V]` **and `[FiniteDimensional ℝ V]`**
(`surfaceMeasure` only reads `Module.finrank`, without requiring finite dimensionality), no additional assumptions were added. The client `target`
verbatim restates and proves the original statement with these two instances, and `target_of_not_finiteDimensional` proves the version without both.
The zero-dimensional, one-dimensional, and subtraction boundaries of natural numbers are all covered by the same statement, no dimensional branching required.

## Proof design

**Cannot directly assert `μH[d]` upper semicontinuous** —— the route record explicitly warned against this, and this round did not do so either.
What actually holds is a two-layer structure:

1. **The open cover content is upper semicontinuous at fixed scale.** Key Lemma
   `isOpen_setOf_slice_subset`: If an open set `U` contains a level section of a compact set `S`, then it contains the sections of all nearby levels. The proof uses `S \ U` compactness (`IsCompact.diff`) and disjointness from that level, so the continuous function `|u - t|` attains a positive minimum on it (`IsCompact.exists_isMinOn`), and this minimum value is the allowable perturbation at that level. `S \ U = ∅` is handled separately.
   Thus: Given a collection of open covers of `openCoverCost d r (S ∩ {u = t}) < c`, the **same collection of covers** is valid for all nearby levels, so `{t | openCoverCost d r (S ∩ {u = t}) < c}` is open, i.e., `upperSemicontinuous_openCoverCost_slice`. **The reason this step holds is the restriction to open covers**: no compactness argument is available for arbitrary covers.

2. The scale limit of an open cover of content remains `μH[d]`. The `≥` direction is trivial (an open cover is a subfamily of a cover, so
   `coverCost ≤ openCoverCost`, then use `coverCost` for the anti-monotonicity in scale). The `≤` direction is the main work in this round
   `openCoverCost_le_hausdorffMeasure`: For any `ε > 0`, take cost on scale `r₀ = min (r/2) 1`
   a near-optimal cover of cost `< μH[d] A + ε/2` (`exists_cover_familyCost_lt`), thickening each piece to the open set
   `Metric.thickening (b i) (C i)`. `Metric.ediam_thickening_le` controls the diameter increase,
   absorbed by the slack from `r₀ + r₀ ≤ r`; the cost increase is controlled by the sequence supplied by `ENNReal.exists_pos_sum_of_countable`
   The summable positive sequence `σ i` is absorbed, block-by-block radius `b i` by `exists_thickening_radius`
   The continuity of `ENNReal.continuous_rpow_const` is attained on `𝓝[>] 0`. The empty block is used by
   `Metric.thickening_empty` Keep cost `0`. Finally `ENNReal.le_of_forall_pos_le_add` closeout.

   **On fixed scale `openCoverCost` is generally strictly greater than `coverCost`**, so this equality must pass through the scale limit, and cannot be arbitrarily substituted at a single scale.

3. L3 = measurability of countable supremum: `Measurable.iSup` plus `UpperSemicontinuous.measurable`.
   `d = 0` is protected by Mathlib's built-in `Nonempty` coverage (empty block cost `0`, not `0^(0:ℝ) = 1`).

## Relation to L1/L2

L3 is not a consequence of L1: L1 only asserts the measurability of the constructed dominating functions, making no claim about the measurability of the section functions themselves.
Conversely, L3 does not provide an integral bound. The client's `eilenberg_compact` will merge both into L4/L5 to consume in the form:

```lean
theorem CompactSliceAudit.eilenberg_compact (hu : LipschitzOnWith K u S)
    (hc : Continuous u) (hS : IsCompact S) :
    Measurable (fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t})) ∧
      (∫⁻ t, surfaceMeasure V (S ∩ {x | u x = t}) ∂(volume : Measure ℝ))
        ≤ (eilenbergConstant V : ℝ≥0∞) * (K : ℝ≥0∞) * volume S
```

The left-hand side is now a true integral of a measurable function. The client computes both endpoints on the unit interval of the real line:
`∫⁻ t, surfaceMeasure ℝ (Icc 0 1 ∩ {x | id x = t}) = 1` (each level has exactly one point, `ℋ⁰` counting),
and the Eilenberg bound is `eilenbergConstant ℝ · 1 · volume (Icc 0 1) = 2`. Both sides are evaluated concretely.

## What was not done in this round

* **L4 (Borel set sections a.e. measurable) and L5 (measurable weights)** remain unproven. L3 holds only for **compact** `S` sets, making no claims for general Borel sets; L4 requires Lebesgue inner regularity to decompose Borel sets into an increasing sequence of compact sets plus a volume-zero remainder term (the remainder is handled by already-proven L2), which was not carried out in this round.
* **Three original coarea holes** remain untouched: `Analysis.aemeasurable_lintegral_levelSet`, `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`, `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`.
  In particular, the first hole requires validity for **any** Borel set (the target is `univ`), so the compact set version cannot fill it.
* The sharp `C^(finrank)` `Analysis.sard` (now without downstream consumers) and `Analysis.ae_forall_fderiv_ne_zero` still carry `sorryAx`.
* `smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and the equality of the two Cheeger constants remains unproven.
* The `μH[d]` itself lacks its upper semicontinuity (generally not true), and there is no claim that `openCoverCost` equals `coverCost` at a fixed scale.
* No attention has been paid to L6/L6a/L7's Whitney extension and C¹ piecewise, nor to L8–L12.
* L3 does not fill any of the existing coarea holes: the direct hole remains as expected, 3/3/5, with a total count of 11.

## Verification

* `Analysis/HausdorffContent.lean` and `KLS/Geometry/SurfaceSlicing.lean` both are
  `-DwarningAsError=true` Compiles independently.
* `build/audit/CompactSliceAudit.lean` compiles with `-DwarningAsError=true`: 1 statements `#check`
  (The literal recitation of the route record L3) and 11 theorem—`target` (with `[CompleteSpace V]` and
  (`[FiniteDimensional ℝ V]`)'s original statement), `target_of_not_finiteDimensional`,
  `eilenberg_compact` (merged form of L1 + L3), `measurableSet_slice_lt`,
  `exp_not_lipschitz` (continuous but not globally Lipschitz `u`), three computations on a line
   (`surfaceMeasure_real_singleton`, `slice_Icc`, `lintegral_slice_Icc = 1`),
  `eilenberg_bound_Icc` (right end is `2`), two `preserved_*` named argument signature checks——
  And 29 item `#print axioms` (18 library declarations + 11 client declarations).
  All  29 statements depend only on `propext`, `Classical.choice`, `Quot.sound`; **not on `sorryAx`**.
* Retest `EilenbergMajorantAudit`, `NullSlicingAudit` (first two client rounds, unmodified),
  `WeightedCoareaRouteStatements`, `WeightedCoareaInfrastructure`, `AreaFormulaAudit`,
  `CheegerInfimumAudit`, `MinkowskiConstantAudit`, `SuperlevelSardScope`, `SmoothSardAudit`,
  `SmoothSardRouteStatements`, all strictly compiled successfully. `EilenbergMajorantAudit`'s four `preserved_*`
  Again confirm the previous two rounds' statements have not changed with named arguments.
* Three WIP files were successfully compiled in practice, with direct proof holes respectively **3/3/5, total 11**.
* Default `lake build` is connected to the root directory `python3 research/verify.py`. Final verification receipt is
  `build/verification/latest.json`, exactly equal to the final complete source code snapshot; evidence JSON is
  `research/explorations/2026-09-15-compact-slice-measurable.json`, final verification and save
  `build/audit/compactslice-final-snapshot.json`. `build/` is gitignored, hence `build/audit`
  The hash is bound solely by evidence JSON.
* Certification still **24**, perimeter infrastructure still **missing** (gap list updated in this round:
  L1, L2, L3 are now proven, L4 and L5 remain as gaps).
