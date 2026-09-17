# Repository semantic alignment — 2026-09-16

## Scope and outcome

This review aligns the current Lean statements and proof dependencies, the 24 ledger
certificates, all 75 Blueprint nodes, task infrastructure assessments, progress views and
current documentation. It includes the incoming locally Lipschitz coarea theorem L13.
It does not prove a new theorem, change an existing mathematical statement, create a
certificate, or mark the dimension-free KLS conjecture complete.

The mathematical statements of all 24 certificate entry points were compared with their
ledger and Blueprint descriptions. No scope mismatch was found in those registered
statements. The corrections concern stale documentation, comments and infrastructure
metadata, especially claims that already proved coarea and recovery results were missing.
Historical decision and exploration files are preserved; dated handoff sections are
explicitly distinguished from current status.

## Certificate scope review

Every row refers to the existing certificate, not a new certification claim. Full hypotheses
remain in the [ledger](../a-series/ledger.yaml) and the linked entry point.

| Certificate entry point | Scope checked |
| --- | --- |
| [Linear-test lower bound](../../solutions/LemLinearTestLower.lean) | Second-moment hypotheses, centered covariance, finite constants and extended infimum. |
| [Binary tensorization](../../solutions/LemPoincareTensorization.lean) | Independent probability factors, Hilbert product norm and smooth finite-energy test domain. |
| [Finite tensorization](../../solutions/LemPoincareFiniteTensorization.lean) | Dependent finite Hilbert products, empty index, zero-dimensional factors and infinite optimal constants. |
| [One-dimensional Gaussian](../../solutions/LemPoincareGaussianOneDimensional.lean) | Exact variance parameter, arbitrary mean, zero variance and unchanged test domain. |
| [Ambient/intrinsic comparison](../../solutions/LemAmbientIntrinsicPoincareComparison.lean) | Relaxed energies and constants, including singular laws and proper affine supports. |
| [Legacy/relaxed comparison](../../solutions/LemLegacyRelaxedPoincareComparison.lean) | Raw tests versus relaxation; no unconditional Cheeger identification. |
| [Covariance test-core density](../../solutions/LemCovarianceTestCoreDensity.lean) | Absolute continuity, arbitrary Haar normalization and singular covariance weighting. |
| [Smooth/literature equivalence](../../solutions/ThmSmoothLipschitzConstantEquivalence.lean) | Local-slope convention, absolute continuity and the explicit intrinsic hypothesis. |
| [Intrinsic absolute continuity](../../solutions/LemLogConcaveIntrinsicAbsoluteContinuity.lean) | Log-concave laws on their affine support, including dimension zero. |
| [Selected/literature equivalence](../../solutions/ThmSelectedLiteratureConstantEquivalence.lean) | Log-concavity discharges intrinsic absolute continuity; infinite constants are retained. |
| [Compact/Borell equivalence](../../solutions/ThmCompactBorellLogconcavityEquivalence.lean) | Compact and Borel formulations, inner measure and support restrictions. |
| [Borell density](../../solutions/ThmBorellLogconcaveDensity.lean) | Intrinsic representation and affine-support scope; no unjustified ambient density. |
| [Ambient/intrinsic covariance](../../solutions/LemAmbientIntrinsicCovariance.lean) | Centered covariance and moment assumptions under intrinsic transport. |
| [Covariance core closure](../../solutions/LemCovarianceCoreClosure.lean) | Weighted closed form and core realization; no KLS estimate inferred from closure. |
| [Affine/covariance relaxation](../../solutions/ThmAffineCovarianceRelaxationClosed.lean) | Corresponding energies and constants under the recorded support and moment hypotheses. |
| [Translation invariance](../../solutions/LemAffinePoincareTranslationInvariance.lean) | Probability transport and centered covariance convention. |
| [Affine/isotropic reduction](../../solutions/ThmAffineIsotropicReduction.lean) | Equivalence at a fixed proposed bound; it does not produce a universal bound. |
| [Dirichlet relaxation](../../solutions/ThmSmoothGradientRelaxationDirichlet.lean) | General Borel probability scope and normal-contraction property. |
| [One-dimensional log-concave bound](../../solutions/ThmOneDimensionalLogConcavePoincare.lean) | The upper bound is `4 Var`; optimality across all laws is not a separate certificate. |
| [Raw/core agreement](../../solutions/ThmSmoothGradientRawCoreAgreementDensity.lean) | The exact density/core hypotheses; no unrestricted singular-law conclusion. |
| [Conditional-fiber form](../../solutions/LemConditionalFiberForm.lean) | Constructed conditional form with its stated full-dimensional hypotheses. |
| [Conditional-fiber energy comparison](../../solutions/LemConditionalFiberEnergyComparison.lean) | Specified conditional energies; no universal frame bound follows. |
| [Conditional-fiber bound](../../solutions/CorConditionalFiberTwelveBound.lean) | Current coefficient is four; “Twelve” survives only in the historical identifier. |
| [Twice Cheeger energy](../../solutions/CorAbsolutelyContinuousRelaxationTwoCheeger.lean) | Intrinsic absolute continuity and the local-slope convention, hence log-concave laws. |

## Analytic and open-boundary review

- `KLS.Conjecture` chooses one finite `C : NNReal` before quantifying over dimensions and
  log-concave probability laws. Neither an equivalence theorem nor a one-dimensional result
  supplies this constant. All four active sufficient routes retain their separate unresolved
  inputs; conditional and upstream results are not local Lean completion markers.
- The Whitney extension is for **compact** first-order jets, with exact ambient derivatives.
  Empty, sparse and zero-dimensional cases are retained; no general noncompact closed-set
  theorem is claimed.
- L11, L12 and L13 provide both weighted coarea and slice a.e. measurability, respectively for
  C¹, globally Lipschitz and locally Lipschitz real functions. The measurable set may be
  unbounded and the nonnegative extended weight may have infinite integral. Normalized
  Hausdorff surface measure and dimension zero are retained; no `SFinite` surface-measure
  hypothesis is added. L13 glues extensions on open neighborhoods, so agreement of gradients
  is justified, rather than inferred from agreement on sparse pieces.
- Original targets T1–T3 are wired to proved modules. The T2 and T3 old/new elaborated types
  were also compared in full pretty-print mode. Sharp finite-regularity `Analysis.sard`
  remains open; proved smooth Sard already suffices for regular superlevels.
- `KLS.RelativePerimeter.exists_smooth_recovery_sequence` is already proved in
  `KLS/Geometry/PerimeterRecovery.lean` under its original log-concave density and finite
  relative-perimeter hypotheses, including unbounded and zero-dimensional cases. Accordingly,
  `lem:relative-perimeter-smoothing` now records **available infrastructure with no mathematical
  infrastructure gaps**. After checking the exact statement and strict client, its existing
  proof is linked and marked `leanok` in Blueprint. The aggregate imports its proved module
  so the normal declaration audit covers the new link. No ledger certificate is added.
- `lem:relative-perimeter-cheeger-infimum` remains **missing** precisely the integrated
  superlevel bound and reverse comparison. Its proved inputs include recovery, coarea,
  smooth regular-superlevel construction and the forward comparison. The two missing proofs
  belong to the Cheeger–Buser workstream assigned to Wang Haocheng; this alignment does not
  edit their proof bodies.
- The three isolated WIP modules retain 8 direct holes, distributed 1/2/5 between sharp Sard,
  Cheeger-infimum and Energy. General singular-law identities and the change from local slope
  to the alternative asymptotic-Lipschitz convention must not be confused with the proved
  absolutely-continuous `E^can = 2 Ch` result.

## Changes and verification

Current guides and source comments now describe completed results as completed, identify the
actual remaining comparisons, and separate local auxiliary proofs from registered certificates.
Task evidence hashes were refreshed against current files. Broken local documentation links
were repaired. Progress metadata now gives compact Whitney scope, keeps completed L13 out of
the next-step highlight, and highlights the pending Cheeger superlevel integral bound.
Generated progress views use a disposable Git index containing the intended canonical inputs;
the user's staged contents are preserved. The index byte hash changed during the session, but
its staged tree remains equal to HEAD as at baseline; an index stat/cache refresh is not a
staged source change.

The verification artifacts are under `build/audit/semantic-alignment-20260916/` (ignored local
evidence). `final.json` identifies the final source snapshot, root verification receipt,
client results and preservation checks. The full-library scan covers 2,934 local declarations
in 193 modules with declarations, including generated and private declarations. Exactly 12
declarations depend on `sorryAx`, all in the three WIP modules; no additional axiom, unsafe
declaration, partial declaration or non-WIP `sorryAx` dependency was found. All 25 audit
clients pass with `-DwarningAsError=true`; some deliberately print the known WIP dependencies.

The root verifier separately checks ledger/Blueprint consistency, tests, build, statement
goldens, certificate axioms and local kernel replay. This is local snapshot-bound evidence;
it is not a fresh remote CI result or a clean rebuild of all pinned Mathlib dependencies.
The source comments edited by this alignment are checked to preserve Lean code after comment
removal. The only non-comment Lean change is the aggregate import of the already proved recovery
module; no declaration body changes. No commit, push, new ledger certificate or historical-record
rewrite is part of this round.
