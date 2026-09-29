# 2026-09-12 — Feasibility judgment of isoperimetric diameter inequalities, and next step (only statement) prompt

## 1. How much is missing from the isodiametric inequality in Mathlib?

### Mathlib already has

- `MeasureTheory.hausdorffMeasure_pi_real`: on `ι → ℝ` with `μH[card ι] = volume`.
  **But that is the sup norm**, Hausdorff measure depends on a metric, so it cannot be directly transferred to the Euclidean (inner product) norm.
- Instance in `Mathlib/MeasureTheory/Measure/Hausdorff.lean`: for any finite-dimensional real normed space `E`,
  `μH[finrank ℝ E]` **is an additive Haar measure** (`IsAddHaarMeasure`).
- Haar uniqueness (`Measure.isAddLeftInvariant_eq_smul`, `addHaarScalarFactor_pos_of_isAddHaarMeasure`),
  `LipschitzWith.hausdorffMeasure_image_le`, isometry invariance, `Measure.addHaar_smul`, volume of a ball.

Therefore **`μH[n] = c • volume` (existence of a unique `c ∈ (0,∞)`) is free**, and this repository has already used the same pattern before.

### Mathlib has absolutely nothing (zero hits in full library search)

- Isodiametric diameter inequality (isodiametric), Steiner symmetrization;
- Brunn–Minkowski and Prékopa–Leindler in arbitrary dimensions (this repository currently only implements the one-dimensional case, see `Probability/Line/BrunnMinkowski.lean`).

### Judgment

A gap is not "building a theory from scratch," but rather a precise thing: **fixing constants into `c = 2ⁿ/ωₙ`**,
i.e., proving `volume S ≤ ωₙ (diam S / 2)ⁿ`. Two classic approaches:

1. **Steiner symmetrization**: n-fold symmetrization, requires measure preservation, diameter non-increase, and measurability preservation. Classical, but heavy in Lean.
2. **Via Brunn–Minkowski**: `vol S ≤ vol(½(S − S)) ≤ vol(B(0, diam S / 2)) = ωₙ (diam S/2)ⁿ`,
   a key intermediate step is the n-dimensional Brunn–Minkowski. The standard proof of the n-dimensional Brunn–Minkowski uses induction on dimension + the n-dimensional Prékopa–Leindler, **whose one-dimensional base case has just been proven in the current round of our repository** (`Probability.Line.prekopaLeindler`, without boundedness assumptions). Thus, the route 2 has a ready-made starting point, and the intermediate results (n-dimensional PL / BM) themselves constitute an independent contribution at the Mathlib level.

### But it must be made clear: it unlocks nothing.

`hausdorffNormalized_finrank_eq_volume` (`KLS/WIP/RelativePerimeter.lean:119`)
In the **entire repository with no usage points**, the module documentation states that it is
"an obligation recording the convention". `relativePerimeter` uses
`surfaceMeasure = hausdorffNormalized (n−1)`, the n-dimensional one that is never called.

Thus: the isodiametric inequality is the most self-contained and most actionable piece in this chain, but also the most structurally weak.
What truly bottlenecks `lem:relative-perimeter-smoothing` → … → `thm:logconcave-cheeger-poincare-comparison`
(with 4 downstream nodes) are the other four: the local finiteness of `ℋ^{n−1}` on C^∞ hypersurfaces, Gauss–Green (the divergence theorem in Mathlib covering only rectangular boxes), the weighted coarea formula, and the general dimension Sard.

(Correction: In the previous oral suggestion to "first prove the isodiametric inequality," I overestimated its foundational weight. Take this section as the authoritative reference.)

## Step two (only statements) prompts

Thus, the next step worth taking is not to tackle isoperimetry alone, but to translate the entire chain of missing analytical premises into precise Lean statements, turning the prose gaps in `tasks.json` into typed obligations, each of which can be independently addressed (or directly targeted as Mathlib PRs).
This round involves only statements, not proofs.

---

```
Repository: /Users/lyuyuwei/Documents/ChatGPT/KLS (Lean 4 / Mathlib v4.33.0, Mathlib submission
db584cd6d46c92f209a44c0f1c829460d327499d; Lake root directory formalization/).
The local elan and all Lean toolchain components are natively arm64; git operations via lake work normally and no git wrapper scripts are required.

Task (only statement, no proof): Write the missing analytical assumptions of the relative perimeter chain as independent and precise Lean statements,
all proofs to be `sorry`, placed in a new WIP module. These statements must be **independent of KLS and stand on their own**,
i.e., formulated as general measure theory/geometric analysis propositions, not as specialized forms involving objects from this repository.

Background (read first):
- research/decisions/2026-09-12-relative-perimeter-prerequisites-statement-prompt.md (Section 1 of this document: feasibility judgment of isoperimetric diameter inequalities, and "which parts bear weight, which do not")
- research/decisions/2026-09-11-relative-perimeter-smoothing-statement.md and -proofs.md
- research/decisions/2026-09-11-relative-perimeter-cheeger-infimum-statement.md and -proofs.md
- research/decisions/2026-09-12-cheeger-infimum-sorry-progress.md (latest round of progress and per-item bottlenecks)
- formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean (`SmoothDomain`, `hausdorffNormalized`, `surfaceMeasure`, `relativePerimeter`, and 5 with sorry)
- formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean (9 with sorry, including Sard and coarea)
- research/verification.md (tasks.json field semantics and infrastructure three statuses)
- research/naming.md

The statements to be written, five groups (the group name suggests the section):

A. Isoperimetric diameter inequality
  A1. On a general finite-dimensional real inner product space `V`: `volume S ≤ ENNReal.ofReal (unitBallVolume n * (diam S / 2) ^ n)`,
       `n = finrank ℝ V`, `S` arbitrary (in outer measure form, no measurability required). Note `diam` is `Metric.diam`,
       unbounded sets give `0`, must be handled in the statement (restrict `Bornology.IsBounded S` or use `EMetric.diam`, choose one and specify).
  A2. Derived from A1 yields `μH[(n : ℝ)] = ENNReal.ofReal (2 ^ n / unitBallVolume n) • volume`,
       or equivalently the one already in this repository `hausdorffNormalized_finrank_eq_volume`. **Do not** alter
       the type of this theorem in `RelativePerimeter.lean`; write the general form of A2 in a new module, and document the relationship between the two.
  A3. (Optional, if you judge the path 2 more promising) the statements of n-dimensional Prékopa–Leindler and n-dimensional Brunn–Minkowski,
       and explicitly note that the one-dimensional base case is already `FunctionalInequalities.Probability.Line.prekopaLeindler`.

B. The area measure of C^∞ hypersurfaces is locally finite
  `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier` See RelativePerimeter.lean:418 for existing types.
  This round focuses on the **general proposition it relies on**: a subset locally represented as the image of a C^∞ map (or the regular zero level set of a C^∞ defined function),
  whose `μH[n−1]` is finite on compact sets. Reduce it to a bounded set using the Lipschitz image's `μH` upper bound (`LipschitzWith.hausdorffMeasure_image_le`).
  `ℝ^{n−1}`

C. Gauss–Green / Divergence theorem (beyond rectangular box)
   `SmoothDomain.enorm_gradient_mollified_le` The existing types are seen in RelativePerimeter.lean: 580.
   The general statement to be written this round: for a smooth domain `U` and a C^∞ vector field with compact support `F`,
   `∫ div F over U = ∫ ⟪F, ν⟫ over ∂U` (`ν` is the outward normal, and the area measure is standard `ℋ^{n−1}`),
   and thus we obtain the form: "the distribution gradient of the smooth domain indicator function = the area measure with outward normal."
   Mathlib's existing `MeasureTheory/Integral/DivergenceTheorem.lean` currently only covers rectangles, which should be explicitly noted in the documentation.

D. Weighted coarea formula
  `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` See CheegerInfimum.lean for existing types.
  Current statement to be written: for a C¹ (or Lipschitz) `u : V → ℝ` and measurable weight `w ≥ 0`,
  `∫ w ‖∇u‖ dvolume = ∫_ℝ (∫_{u = t} w dℋ^{n−1}) dt`.

E. Sard's theorem (general dimension)
  `SmoothDomain.ae_exists_superlevel` See CheegerInfimum.lean for existing types.
  Current statement to be written: The set of critical values of a C^∞ map has Lebesgue measure zero (this repository only requires `V → ℝ`, i.e., a.e. `t` is a regular value). Mathlib only has the case of equal dimensions `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`.

Rules:
1. **Only state the statements**. The proof body of each `theorem`/`def` is solely `sorry`. Do not attempt to prove any of them,
   Nor should we weaken it just because it "looks provable".
2. The statement should be independent of KLS: using a general `V` (a finite-dimensional real inner product space, Borel, second countable) and general assumptions,
   Do not appear `ProbabilityMeasure`, `IsBorellDensity`, `SmoothDomain` or any other repository-specific objects.
   Unless this group is inherently about `SmoothDomain` (groups B and C can use it).
3. **Do not modify any existing declarations in existing files** (including `RelativePerimeter.lean` and `CheegerInfimum.lean` in
   That 14 type of `sorry`). This round only adds files.
4. New file placed under `formalization/FunctionalInequalities/KLS/WIP/` (recommended
   `AnalyticPrerequisites.lean`, or split into several files by five groups, as you judge.
   **Not registered**: Not included in `FunctionalInequalities.lean` aggregate import, lakefile `Solutions` root,
   `research/a-series/ledger.yaml`, `research/check_blueprint.py`'s `CERTIFICATES`,
   `research/tasks.json`, Blueprint's `\lean{}`/`\leanok`.
5. The record is appended only: new `research/decisions/2026-09-1X-relative-perimeter-prerequisites-statement.md`,
   Specify the source of each statement (textbook/literature), its correspondence to the existing sorry in the repository, and your assessment of the feasibility of each.
   (What Mathlib has, what it lacks).
6. Do not git commit, do not git push.

Compile (in formalization/):
  lake build FunctionalInequalities.KLS.WIP.<new module name>   # First generate olean
  lake env lean FunctionalInequalities/KLS/WIP/<new module>.lean
Goal: No output except `declaration uses 'sorry'`; then run
  lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/<new module>.lean
Confirm no warnings (`omit ... in` must appear before the docstring; `unusedSectionVars` is reported per iteration, requiring multiple compilations to converge).

The final report should list: five groups, each specifying which statements were made and their full names; for each statement, indicate which `RelativePerimeter.lean` / `CheegerInfimum.lean` entry `sorry` it corresponds to (or explain if it does not correspond); a feasibility assessment and recommended path for each;
Group A: did you choose the Steiner or Brunn–Minkowski path and the reason; and if you believe any statement should not be presented in this form (for example, better suited for a direct PR to Mathlib, or fundamentally unnecessary for this repository), clearly state that and provide the reason—do not force inclusion.
```
