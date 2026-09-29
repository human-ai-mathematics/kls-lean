# 2026-09-12 — Current state audit, document synchronization and WIP retention

Owner explicitly requires, following the current statement/mathematical semantics audit: the existing `sorry` shall be retained, with documentation updated first, then committed.
This commit organizes and verifies the current achievements and documentation; this round does not include proofs, does not modify Lean statement, definitions, or proof bodies, does not list WIP as proven nodes, and does not push to remote. Existing decisions are preserved as historical snapshots from their respective dates.

## Current certification scope

`research/a-series/ledger.yaml` has 24 nodes of type `proved / checked_by: lean`. The core KLS is defined.
Quantifiers involve first selecting a uniform finite constant, then covering all dimensions and measures; covariance uses centered `covarianceBilin`.
The local slope test domain retains the L² and finite energy conditions, and the zero energy and zero-dimensional cases are not excluded.

Usage boundaries of new achievements:

- A one-dimensional log-concave certificate yields `C_P^lit(ν) ≤ 4 Var_ν(id)`, including Dirac. The certificate only proves an upper bound for the coefficients 4, without formally establishing the "coefficient non-improvability"; it does not imply that every one-dimensional law achieves equality, nor does it prove the general high-dimensional KLS.
- The conditional fiber form is closed and Markov, and the fiber log-concavity together with the one-dimensional bound yields `D(f) ≤ 4 ∫‖∇f‖²`. To obtain `C_P^lit(μ) ≤ 4 C`, further input of `Var(f) ≤ C D(f)` on all finite form domains is still required. The existence of a framework independent of the test function and a uniform finite C for all dimensions and isotropic log-concave laws remains an open problem.
- When the intrinsic law is absolutely continuous with respect to Haar measure, the smooth gradient relaxation equals the local slope relaxation, hence `E^can = 2 Ch`; all log-concave laws satisfy this intrinsic absolute continuity condition. This range has been registered as `cor:absolutely-continuous-relaxation-two-cheeger`.
  Unconditional comparisons on general singular laws, asymptotic Lipschitz convention equivalence, and isoperimetric Cheeger–Buser comparisons are distinct problems and cannot be jointly completed by this certificate.

## Retained proofs work

| File | Direct `sorry` number | Current boundary |
| --- | ---: | --- |
| `KLS/WIP/RelativePerimeter.lean` | 5 | Hausdorff normalization, boundary local finiteness pending connection; convolution and recovery sequence after Gauss–Green still pending completion |
| `KLS/WIP/CheegerInfimum.lean` | 9 | Sard, coarea, Minkowski coarea, smooth approximation access and downstream infimum comparison |
| `KLS/WIP/AnalyticPrerequisites.lean` | 5 | measurability of coarea and formula, Sard, two Gauss–Green statements |
| `Energy/WIP/Cheeger.lean` | 5 | Comparison of two main singular laws and three derived objectives |
| Total | 24 | Fully retained; direct hole count does not equal the number of independent mathematical problems |

None of these files are officially aggregated via entry points or imported by 24 certificates. `AnalyticPrerequisites` original 17 obligations,
among which 12 proof bodies have been filled: Prékopa–Leindler, two versions of Brunn–Minkowski, isodiametric inequality, Hausdorff comparison and normalization, local Lipschitz graphs, local finiteness of regular level sets, consistency of outward normals, and unit length collectively 10 items, all based solely on standard axioms; additionally, two other proof bodies `ae_forall_fderiv_ne_zero` and `gradient_mollifiedIndicator_eq` remain dependent on Sard or Gauss–Green via transitive dependencies `sorryAx`.
"The proof body is filled" and "transitive dependency has no sorry" must be stated separately.

Geometric inputs already exist in the companion file and should not be further listed as "17 statement only". However, the file currently imports `RelativePerimeter`, and cannot reverse import back these lemmas to form a cycle. Future work can split foundational definitions and general geometric theorems by dependency; no such splitting is performed in this round, and no placeholder is eliminated as a result.

The input for `CheegerInfimum.exists_smooth_approximation_lipschitz` is actually sufficient: the formal library's
`Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1` simultaneously provides L¹ convergence of functions and gradients, along with the `[0,1]` norm and Lipschitz property. Implementing the gradient sequence into `Lp V 1 ν`, obtaining convergence via `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`, and then using `Filter.Tendsto.enorm`, `Lp.enorm_toLp`, and `eLpNorm_one_eq_lintegral_enorm` to achieve the required integral convergence of gradient norms.
A local independent audit client has proven this implication under warnings-as-errors, relying solely on the standard three axioms, without importing WIP.
The `sorry` in the source code is retained as instructed by owner, with status recorded as pending integration.

Two historical distance-cutoff defects have been corrected in previous work: the non-empty hypothesis prevents counterexamples from the empty set, and indicator convergence includes measurability and the assumption that taking the closure does not increase mass. This round of review confirms that their current proofs do not contain `sorryAx`, and thus the signature is not modified.

## Boundary Verification

Audit verification receipt prior to document update is `build/verification/20260912T104945.225719Z/report.json`:
103 Python test cases, default Lake build, 26 local dependency declarations' KLS statement golden,
349 selected declarations' transitive axioms checks, 149 local module core replays all passed. Another environment-level check covers
formal aggregation entrypoints and all certificate imports for 2,042 local declarations (including 1,631 theorems, with auxiliary generation terms),
no non-standard axioms, unsafe, or partial declarations. Manual review covers 24 certificate types, key definitions, and 24 explicit WIP hole statements;
no line-by-line manual inspection of all auxiliary proofs.

Four WIP files are re-elaborated in an isolated, complete local module view: normal mode exits 0, exactly as above
24 `declaration uses sorry` warnings; `-DwarningAsError=true` upgrades them to error, exits 1,
with no other diagnostics. Thus the text "warningAsError no warnings passed" in the history cannot be taken literally as evidence.
The kernel replay itself is acceptable with respect to items depending on `sorryAx`; only combined with transitive axioms checking can the range of hole-free be confirmed.

All evidence trusting a fixed version of third-party compiled dependencies does not imply independent rebuilding of Mathlib, remote CI or
Blueprint PDF/web layout passed. After updating the document and task metadata, rerun `python3 research/verify.py`
Obtain a verification receipt for the final workspace snapshot. Audit scripts, logs, and generated caches are left in the ignored `build/`, not included in the commit.

During audit, the local HEAD is `5e5c704`, and the real-time `origin/main` is `12f828f`; the two have 2 and 3 commits respectively. This round only authorizes local commits, without merging or rewriting remote history. The dimension-free KLS bound remains open. The completion ratio of the entire KLS plan cannot be represented by the 24/24 proven proportion in the ledger.
