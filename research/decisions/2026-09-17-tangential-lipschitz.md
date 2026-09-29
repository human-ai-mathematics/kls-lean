# A small Lipschitz estimate on fibers: R4 (non-branching) routes of rank deficiency

2026-09-17. This round's **proof of a new theorem**: the **`R4`** on the rank-deficient path obligation list—marked as a **non-terminal point** in the previous round.
Together with `R1`, `R2`, `R3`, four out of the thirteen numbered items have been fulfilled.
**Only `R4` is proven**; `R0`, `R5`–`R10`, `N1`, `N2` remain unproven,
the rank-deficient part with coarea dimension m is still open. This round **proves no coarea formula, no slice theorem, no Sard theorem**.
No hole migration, no commit, no push. The direct proof hole remains **8 (1/2/5)**, and the certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260917T054703.943157Z/report.json`: 10 gates, 217 local module kernel replay,
581 entries, snapshot
`3b4bf8210086a351b6cef33b7a2be98ff069fbe0f0f5a07c8ad57e230be74425`, start workspace drift is empty.

## A concurrent session committed the worktree during this round: explicit record

After finishing this round of Lean and before closing out, the concurrent session commited the entire workspace:
`HEAD = origin/main` from `34b9269…` to
`e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`
(`feat: complete scalar coarea and advance vector coarea foundations [skip ci]`, 138 files).
The commit **absorbs all the results from the first four rounds of this session** (including `RankStratification.lean`, `RightInverseBound.lean`)
And its audit and record-keeping), therefore the "not commit" states from those rounds are no longer valid—**it belongs to collaborator commit, not to this session**.

The commit also conducted a "submission review", modifying two files that I had previously written:

* `research/audits/RankDeficientRouteStatements.lean`: Added a status statement at the file header
  (Proofs established in versions `R1`/`R2` and `R3`; proofs for `R0`, `R4`–`R10`, `N1`, `N2` remain open), and noted
  **No changes to any of the following statements**. The file still contains only `#check`, with no declarations, no proofs, no placeholder axioms.
* `research/audits/RightInverseBoundAudit.lean`: Clarified wording in the documentation of `constant_map`.

**These two changes were not made by this round, and this round has not rolled them back.** Therefore, this round cannot claim that the route statement file "preserves its original bytes"—
the accurate statement is: **this round did not modify it**, and it remains clean relative to the current `HEAD`.
All verification and hash checks for this round are being redone on the new `HEAD = e7c4403…`.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## What does "a point with no return" actually mean—let's get the facts straight first

The previous round marked `R4` as non-terminal, reasoning that: after `R2 + R3` is in place, `R4` is self-sufficient,
**if it cannot be established or if the constants are inconsistent, the entire path is wrong**.
Now `R4` **has been proven, and the constants are indeed independent of `ε`**.

This only shows that the route has not been falsified at its key analytical steps.
It does not show that `R0` holds, nor that the remaining `R5`–`R8` can be carried out:
the dimensions match, the estimates hold, but connecting them into slice zero-measure still requires
the finite `ℋ^{n−r}` measure of the fiber (`R5`), Fubini on the target space orthogonal decomposition (`R6`),
and the real work—layer-by-layer local assembly (`R7`, estimates 450–600 run, high risk).
**This round provides no proof of any part of the rank deficiency.**

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/TangentialLipschitz.lean`
 (137 line, local import closure **3 modules**, no WIP; depends on the same round's
`Analysis/RankStratification.lean` and `Analysis/RightInverseBound.lean`).

* **`norm_comp_apply_sub_le_of_approximatesLinearOn`**: chord between two points in the same fiber
  `b − a` satisfies `‖P (A (b − a))‖ ≤ ‖P‖ ε ‖b − a‖`.
  **This is the only place where the fiber assumption is used, and also the dividing line between the case where the derivative is zero**
  The string is not in the core; it is at most `‖P‖ ε ‖b − a‖` away from the core.
* **`exists_lipschitzOnWith_of_ker_bound`** (`R4`):
  If the linear model `A` dies on `ker (P ∘ A)` (by the conclusion of `R2`),
  and vectors almost annihilated by `P ∘ A` lie close to that kernel with constant `C` (the conclusion of `R3`),
  Then for each fiber, `Q ∘ f` is `c ε`-Lipschitz on `S ∩ {P ∘ f = s}`,
  **`c = ‖Q‖ (1 + ‖A‖ C ‖P‖)` Only depends on linear data, does not depend on `ε`, does not depend on `f`, does not depend on `S`, does not depend on fiber**.

  Estimate chain: from the previous step, the chord is almost in the core ⟹ by `R3` replace with actual core elements `w`, `‖(b−a) − w‖ ≤ C‖P(A(b−a))‖`
⟹ by `R2` obtain `A w = 0`, hence `‖A (b−a)‖ ≤ ‖A‖ C ‖P‖ ε ‖b−a‖`
⟹ substitute back and bound the approximation inequality by `‖f b − f a‖`, then apply `Q`.

  **Irrelevant to `ε` is the key point**: In Eilenberg's argument, each scale of `ε → 0` uses a different piecewise approximation,
the constant growing with the partition is utterly useless. This is directly evident in the sentence form `∃ c, ∀ ε, …`.

* **`exists_lipschitzOnWith_fibre`**: `R2 + R3 + R4` composition on sheaves of ranks——
  `P ∘ A` surjective and `finrank W₁ = rank A` when both assumptions are automatically satisfied.
  **This is a deduction from three already established obligations, not a new obligation, especially not `R7`**
  It does not involve measures, Hausdorff dimension, slicing, nor construct approximation piecewise.

`R4` itself does not use inner product, does not use measure, does not use completeness, does not use finite dimensionality; `f` arbitrary, `S` arbitrary.

## The assumption of `R2` is necessary—provide a counterexample, not assert it

`ker_hypothesis_necessary`: Take the identity, `A =` first coordinate, `P =` second coordinate, in the plane `Q =`.

* The assumption of `R3` holds (`P ∘ A` is surjective onto `ℝ`);
* The assumption of `R2` does not hold (the second basis vector is annihilated by `P ∘ A` but not by `A`);
* The conclusion of `R4` does not hold: take `ε = 0` and `f = A`, the conclusion would force the second coordinate along the second coordinate axis to be constant, which it is not.

So `R4` is not a statement about approximation itself; it precisely asserts that linear models die along the fiber direction.

## The assumptions of `R3` are not asserted to be necessary

`R3` provides constants, not restrictions: in finite dimensions, its conclusions hold for each linear map
(This round does not prove this point nor uses it). The other end by
`zero_model_recovers_vanishing_derivative` Note: when the rank-zero stratum `A = 0` both assumptions hold `C = 0`,
Constants collapse to `‖Q‖`, `R4` precisely reverts to the already proven case of derivative zero—there `f` is itself `ε`-Lipschitz.
**`R4` Nothing is added in `r = 0` layer.**

## Boundary cases

Empty set; `ε = 0` equipped with a real linear model; zero-dimensional projection target space `W₂` (`Q = 0`, all `0`-Lipschitz);
rank-zero model `A = 0`.

## What was not done in this round

* **No proof `R0`**: The rank-deficient part remained unchanged by a inch.
* **No proof `R5`** (finite `ℋ^{n−r}` measure of the fiber), **`R6`** (Fubini on target space decomposition), **`R7`** (layer-by-layer local assembly, high-risk reactivation), `R8`–`R10`, `N1`, `N2`.
* **No proof of any coarea formula**, nor any improvement to the applicability range of the m-codimensional coarea formula already established.
* **No proof of any Sard theorem**; no assertion made regarding the measure of the critical value set.
* No modification to any existing `.lean` (including `FunctionalInequalities.lean`, `RankDeficientRouteStatements.lean`, and `AreaFormulaRouteStatements.lean`, the latter two unchanged in this session—former added state annotations by concurrent session in commit, see above); no hole migration; no expansion of certificate or Blueprint `leanok` scope; no new compatible alias added; no weakening of established conclusions.
* **No commit, no push**, the real Git index remained unchanged.

## Next step

In original order is **`R5` and `R6`** (independent, parallel, each about 150 lines, medium risk),
then `R7`. `R7` remains the only high-risk item.

## Verification

* The new module and new client both compile successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **10 axiom report** for `research/audits/TangentialLipschitzAudit.lean` only uses `propext`, `Classical.choice`, and `Quot.sound`.
* Re-running all **44 existing audit clients** plus the new client, a total of **45**, all pass strictly, with 0 failures; the axiom report contains 604 entries, of which 12 entries `sorryAx` remain entirely within the four clients that intentionally report unresolved WIP results.
* Each of the three WIPs is compiled in practice, with direct proof holes **1/2/5, total 8**, unchanged; `research/check_ledger.py` issues **24** certificates.
* Default `lake build` and root directory `python3 research/verify.py` pass; the JSON evidence is
  `research/explorations/2026-09-17-tangential-lipschitz.json`,
  and the final verification is saved as `build/audit/tangential-lipschitz/final-snapshot.json`.
