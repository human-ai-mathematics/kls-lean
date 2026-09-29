# Borell Equivalence, Basic Definitions and Claude Proof Handoff

Date: 2026-09-07 (Asia/Shanghai). Baseline: `0451f2e`, clean working tree at start,
local `main` and `origin/main` tracking references in sync. Lean/Mathlib is v4.33.0, actual Mathlib
commit is `db584cd6d46c92f209a44c0f1c829460d327499d`.

User approved the previous analysis and explicitly added: "Okay, proceed that way, and still leave sorry; I'll have Claude prove it."
This decision adopts the new requirement: definitions and existing Dirac barrier grounding, Borell equivalence and conditional-fiber
well-definedness preserved with seven explicit `sorry`. No tasks were dispatched to Claude or any other agent.
This is a compilable proof handoff, not a completed proof or certification unlock of the Borell root node.

## Reading Order and Status

1. [HANDOFF](../../HANDOFF.md), [verification flow](../verification.md), [naming](../naming.md).
2. [LogConcaveBorel.lean](../../formalization/FunctionalInequalities/KLS/LogConcaveBorel.lean):
   `innerMeasure`, `BorelLogConcave`, and the sole pending main theorem `LogConcave.borel_iff`.
3. [Isotropic.lean](../../formalization/FunctionalInequalities/KLS/Isotropic.lean),
   [Isoperimetry.lean](../../formalization/FunctionalInequalities/KLS/Isoperimetry.lean),
   [RawEnergyObstruction.lean](../../formalization/FunctionalInequalities/Poincare/Euclidean/RawEnergyObstruction.lean).
4. [ConditionalFiber.lean](../../formalization/FunctionalInequalities/KLS/ConditionalFiber.lean):
   Read definitions first, then the six pending contracts.
5. [StatementChecks](../../solutions/StatementChecks.lean),
   [Borell Draft Entry](../../solutions/ThmCompactBorellLogconcavityEquivalence.lean) and
   [task metadata](../tasks.json).

ledger adds a new `drafted / checked_by: null` node, each of the original ten proved nodes remains identical.
Borell Draft Entry is included in the default Solutions target; currently there is no `certificate` wrapper, no `check_blueprint.CERTIFICATES` mapping accepting only proved nodes. Two definitions and the Dirac barrier have Blueprint
anchors and `leanok`; Borell equivalence and conditional-fiber as a whole have only anchors, no `leanok`.
No changes were made to existing route configurations, mathematical content of already proven statements, or any historical decision documents.

## Literature Verification and Evidence Boundaries

- Bobkov, *Isoperimetric and Analytic Inequalities for Log-Concave Probability Measures*,
  Ann. Probab. 27 (1999), 1903–1921,
  [Author-provided original](https://www-users.cse.umn.edu/~bobko001/papers/1999_AOP_Isop.pdf),
  Page 1917, equation (5.1) explicitly uses inner measure to handle possibly non-measurable Minkowski sums. Exchanging the two sets
  or replacing the parameter with `1-t` aligns with the exponential order of this repository. Subsequent discussion for non-Dirac laws does not constitute
  an assumption of the equivalent theorem. The definition on page 1903 uses the lower limit of mass increments of outer expansions.
- Borell, *Convex measures on locally convex spaces*, Ark. Mat. 12 (1974), 239–252,
  [Publisher record](https://link.springer.com/article/10.1007/BF02384761) verifies author, title,
  year, page numbers, and DOI `10.1007/BF02384761`. The complete PDF could not be read in this retrieval:
  Tsinghua public mirror returned HTTP 500, publisher returned subscription preview, Project Euclid returned access check page.
  Therefore, no claim is made to re-verify the exact coverage of its theorem on the combined conclusions about density representatives, local bounds, and moments.
  Historical acceptance records attribute absolute continuity to Theorem 1.1; the exact original paragraph corresponding to complete representatives and moments should still be
  verified in subsequent density work. This reading limitation is not a gap in Mathlib infrastructure, nor does it alter the mathematics classification.
- The specific proof path for Stage A is an independently checkable approximation argument within compact sets, without requiring a complete Borell density representation.

## Borell Equivalence: Exact Contract and Infrastructure

The space is an arbitrary finite-dimensional real normed space equipped with a Borel structure, where probability laws allow singular, zero-dimensional, and non-full-dimensional affine supports.
`innerMeasure μ S` is the supremum over the masses of all compact subsets on ENNReal, including the empty compact set; it is a set function, not packaged as a countably additive measure. `BorelLogConcave` quantifies two Borel sets and `0 < t < 1`, with the combination side using only this inner measure. No additional assumptions of second moments, absolute continuity, or nonempty interior of the support are required.

The current Mathlib starting point has been verified, with specific file SHA256 recorded in tasks.json at infrastructure.evidence:

| Work | Existing API / File |
| --- | --- |
| Regularity within compact sets | finite-dimensional instances of `Measure/Regular.lean` using `InnerRegular`, `InnerRegularCompactLTTop`; `MeasurableSet.measure_eq_iSup_isCompact` and `_of_ne_top` |
| More general inner regularity instances | finite measures of `Measure/RegularityCompacts.lean`, second-countable completely metrizable space instances |
| Compactness and measurability | compact product sets as continuous images via `(x,y) ↦ t • x + (1-t) • y`; `IsCompact.prod`, `IsCompact.image`, `IsCompact.measurableSet`; local `KLS/LogConcave.lean` has already used the same representation |
| Inclusion relations | `Set.image2_subset`; `Set.smul_subset_smul` and similar are specializations of image2 monotonicity; combinations can also be directly passed through quantified inclusion |
| Powers and suprema | `ENNReal.orderIsoRpow t ht`'s `map_iSup`, requiring `t > 0`; similarly used for `1-t` |
| Product of two independent suprema | `ENNReal.iSup_mul`, `ENNReal.mul_iSup`; no need to convert mass into real numbers |

Temporary probes actually checked the compactness/measurability of images of compact sets, inner regularity instances, and supremum/infimum operations; permanent named checks
`borell_innerRegular` use the normed space assumptions of the main theorem, `borell_rpow_iSup` and
`borell_mul_iSup` retain the key order operation verification. `Fin 0` and general `Fin n` also have type checks.
Evaluated as **available**; this only indicates that implementation prerequisites are in place. The only main proof hole remains in `LogConcave.borel_iff`.

Claude suggests first establishing inner measure monotonicity and equality to the original measure on measurable sets within the module, then handling both directions:
specialization to compact sets; double supremum after internal approximation of compact sets. Keep the original definition `LogConcave` unchanged to avoid introducing
equivalent circularities. Empty sets or zero mass are handled by the zero value in ENNReal for positive exponents, without requiring non-empty or positive mass assumptions.

## Implemented Definitions and Obstacles

- `KLS.Isotropic` explicitly includes `MemLp id 2`, zero vector integral, and local centralization `Covariance.operator = ContinuousLinearMap.id`. No uncentralized second-moment operator is used.
  `zero_dimension_isotropic` actually proves that zero-dimensional probability laws satisfy this structure.
- `KLS.Isoperimetry.carrierMeasure` uses an existing measurable retraction to send the probability law to a subtype of the actual affine support, employing induced distance. `boundaryContent` uses `Metric.thickening` and `𝓝[>] 0`; for positive radius, mass increments are non-negative. The results, division, and inverse remain in ENNReal.
  `constant` checks the zero-dimensional branch for the dimension of the affine support direction, returning `⊤`, and `inverseScale` returns zero.
  Zero-dimensional ambient spaces have been checked, as well as the case where the ambient space is the real line and the support is a single point Dirac law.
  No BV, density Cheeger, Poincare comparison, origin independence, or Cheeger energy certification is used.
- The original Dirac examples are left unchanged; new entries `dirac_raw_energy` and `dirac_toLp_zero_eq_id` are added to the library: the former packages a.e. equality together with distinct raw energies `0` and `1`; the latter packages two `MemLp` proofs and equality of the `toLp` classes. Both are added to the standard axioms guard of FoundationAxiomAudit, without increasing ledger nodes. The infrastructure hash of existing examples thus does not need migration.

## Conditional-fiber: Construction and Six Proof Holes

Mathlib already has the joint measurable Markov kernel `Measure.condKernel`, `Measure.disintegrate`, the conditional integral formula, and the conditional kernel a.e. uniqueness. Here `disintegrate` is the decomposition identity, constructed via `condKernel`. A fixed product base space uses `Direction E × E`; the joint pushforward measure of `coordinates (θ,x) = ((θ, x - ⟨x,θ⟩ θ), ⟨x,θ⟩)` is disintegrated just once.
Thus, there is no need to separately select a conditional version for each direction, which might not be jointly measurable.

`Admissible` includes positive dimension, the second moment of μ, the even symmetry of ρ, and the frame identity written in bilinear form. The integral function itself is defined everywhere; the effective input range of Blueprint is described by this predicate. The direction space is empty in zero dimension, and no zero-dimensional spherical probability law is constructed; named zero-dimensional checks state that admissibility is impossible.

`GoodFiber` explicitly checks `z ⟂ θ`, scalar coordinates `MemLp 2`, and non-zero conditional variance. When not satisfied, `fiberEnergy` returns zero, avoiding the use of fully defined real integrals on infinite second-moment fibers to generate numerical values. `energy` uses ENNReal integration; `form` employs the strongly measurable representative selected by Mathlib `Lp`; `domain` is the finite-energy domain of this extended-valued function. These definitions lack `sorry`. Providing a specific function expression does not imply that all representatives and versions declared in the original Blueprint have been identified.

| Order | Pending Statement | Specific Obligation |
| --- | --- | --- |
| 1 | `lintegral_baseLaw` | The fixed product base measure integral equals the iterated integral over directions and projection measures |
| 2 | `ae_memLp_id` | From the second moment of μ, the conditional scalar coordinates are almost everywhere in L² |
| 3 | `measurable_fiberEnergy` | The function composed of branching, conditional variance, and extended division is jointly measurable |
| 4 | `energyWith_eq` | Any Markov version satisfying the same decomposition identity yields the same integral |
| 5 | `energy_congr_ae` | Two Borel L² representatives are a.e. equal, the energy is the same |
| 6 | `form_toLp` | The selected L² representative function equals the original Borel test function formula |

During the proofs of these contracts, auxiliary results on a.e. reconstruction, support on orthogonal base points, and conditional L² tests may also be established. All six statements are currently `by sorry`; node evaluation is **missing**, with the specific gap being these local adaptation proofs, and no claim is made that Mathlib lacks disintegration theory. Optional infrastructure for definition nodes uses the same evidence/version validation and scheduling logic; three new regression tests are added to protect this extension and enforce the mandatory field requirements of the original published nodes. No proof of closed forms, Markov property, gradient comparison, or long path conclusions is provided.

## Density Representation is Only Evaluated

tasks.json Divide the gap into representative elements, local lower bounds, and moments of all orders. Already have
`LogConcave.intrinsic_absolutelyContinuous` and `intrinsic_frontier_support`,
local lower bounds for small balls and global upper bounds for small ball masses are also local. The Mathlib RN tool provides measurable extension densities, a.e. finiteness
and `withDensity` recovery identity, `IntegrableExpMul` provides tools for converting exponential integrability to moment integrability.

Still need to construct a density version that is finite everywhere, upper semicontinuous, and log-concave, establish a uniform lower bound on an internal compact set, and derive tail estimates/exponential norm integrability from log-concavity. `rnDeriv.toReal` itself does not provide these properties.
This batch does not introduce or prove any complete density representation theorems, nor does it modify its mathematical classification or add any additional analytic assumptions.

## Fact-checking, golden, and subsequent certification

Pre-verification receipt: `build/verification/20260906T181000.073185Z/report.json`, status **failed**.
Pre-verification source snapshot SHA256: `e51165ee9a812237e95b82c4220762ea678e072f855ede960a09774bca1ee595`.
This is a snapshot taken before the current decision and guideline update, not the delivery snapshot.

Actual completion: structure/ledger/Blueprint/atlas gate passed; 100 Python tests passed;
default `lake build` passed; statement snapshot and original golden comparison passed.
Received 143 axiom reports, all ten original certificates contained only `propext`, `Classical.choice`, and `Quot.sound`.
Twenty named StatementChecks and two Dirac results were additionally audited against standard axiom checks.
Final acceptance was rejected by exactly the seven drafts' `sorryAx`; this run did not enter kernel replay.
Compilation success here means that declarations and written definitions compile, not that all seven targets have been proven.

The original statement golden's 26 declarations and 221 external leaves remain consistent; the new definition is outside the old root closure.
No update to golden was performed, and no false claim was made that new definitions were included in this snapshot.
New objects are covered by Blueprint anchor points, named typed checks, and corresponding axiom guards.
Future expansion of the root closure should involve creating a separate baseline decision, then running the explicit verification.md update command.

After completing this decision, a full `python3 research/verify.py` should be executed again, followed by `atlas.py export` and `atlas.py ready`.
The final generated receipt should record its own actual source code SHA; it should not be written back to this decision to avoid invalidation.
The verifier continues auditing all Blueprint anchor points, including drafts not marked leanok; no relaxation of the axiom whitelist or hiding of draft anchors occurred.
Current failed receipts will trigger a ready requirement for verification, and will not equate completed definitions with completed proofs.

Baseline ready has 17 blocked items, of which 14 are downstream of Borell equivalence.
The current Borell root node retains `sorry`, which still does not provide dependency proofs, and density and subsequent paths remain blocked; the conditional-fiber remains blocked due to six unproven contracts, blocking two direct consumers.
The check status of implemented definitions and the full repository verification status should be reported separately.

After Claude completes the equivalence proof: provide a unique certificate in the designated Solutions file, add `check_blueprint.CERTIFICATES`, supplement standard axiom guards, synchronize ledger and Blueprint, and re-verify.
Only after completing six well-definedness contracts can the entire conditional-fiber node be marked leanok.
No interface freezing is required beforehand.
This handover does not include commit/push, remote CI, CL, or Pages deployments; local drafts that are checkable are to be reviewed first.

## Source file SHA256

The table below records the source files implemented/checked in this batch; individual file hashes for all infrastructure sources are listed separately in tasks.json.

| Source | SHA256 |
| --- | --- |
| `formalization/FunctionalInequalities/KLS/LogConcaveBorel.lean` | `5660f390c133f093e7f913e3024bd60b9357338507c2e8f96abc34d3ce6e8044` |
| `formalization/FunctionalInequalities/KLS/Isotropic.lean` | `dd0d5ca09b40742ce0bc9f59b292a1d7903ce5f936fa654525164163534a3962` |
| `formalization/FunctionalInequalities/KLS/Isoperimetry.lean` | `db185cf4fe869347881fff739e0dd0808a6ad7dd8a160c28b5aa0b74bc4e4248` |
| `formalization/FunctionalInequalities/KLS/ConditionalFiber.lean` | `618996843d53d904ec7b34688fb2a3b608e2d7796b9253d5f582cbcfcedfd205` |
| `formalization/FunctionalInequalities/Poincare/Euclidean/RawEnergyObstruction.lean` | `9b70f06c372a3387a63798444714e1cc1f7929ea3de4927da9e51711c790e5c6` |
| `solutions/ThmCompactBorellLogconcavityEquivalence.lean` | `b6ee0bc34ada93951d9f636e8870944ca233399f7e49a5a644e8918ff2df84d8` |
| `solutions/StatementChecks.lean` | `27fd9cd6cb8ddf123cdff17f6aab76ebabe1b513f3160847ed230532a3c0a59f` |
| `solutions/FoundationAxiomAudit.lean` | `178e51727ecf18ffe589727c46cd84998bba4fca02bdf2c0754cdf55bfb90841` |
