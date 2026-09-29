# Smooth Gradient Relaxation's Dirichlet Property: statement, semantic alignment and proof

Date: 2026-09-10 (Asia/Shanghai). Baseline: local `main` commit `5e5c704` (after namespace refactoring and blank space cleanup),
working tree initially had untracked `research/weekly/`. The local branch was ahead of `origin/main` by two commits, lagging three document commits;
user instructed not to commit, not to push. Lean/Mathlib is v4.33.0, Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`.
User approved starting from HANDOFF next phase item 1 "Dirichlet witness".

## Verification and Node Selection

Before start: default `lake build` passed (3359 jobs); 2026-09-09's receipt passed but the code snapshot expired due to subsequent commits,
atlas shows "failed or stale verification". Nodes on the affine chain have all been certified or marked as missing; among the remaining eligible nodes,
`thm:smooth-gradient-relaxation-dirichlet` is HANDOFF's explicitly listed next-phase work, and the required infrastructure is in the library:
Conditional contraction transfer `PreEnergy.RelaxedContractionBound.sequentialRelaxation_comp_le`,
`LipschitzApproximation.mollify` and its smooth, Lipschitz, and uniform approximation lemmas, `Energy.Dirichlet`/`NormalContraction`
Definition, `SmoothGradient.relaxation_closedQuadratic`. Mathlib already has `LipschitzWith.compLp` (with Lipschitz property),
`fderiv_comp`, `norm_fderiv_le_of_lipschitz`, `Lp.norm_le_of_ae_bound`. No new Mathlib interfaces are required, hence
`unchecked → available` and prove simultaneously.

## Statement Design

Blueprint: For each finite-dimensional Borel probability measure μ, the ambient smooth gradient relaxation is Markovian: every normal contraction in the L²(μ) class leads to a relaxation energy that is non-increasing; together with a closed quadratic structure, it forms Dirichlet energy. The blueprint proof is marked "Open," suggesting the use of the contraction transfer theorem combined with a "smooth approximation uniformly controlling the relaxation energy."

A single new module [Energy/SmoothGradient/Dirichlet.lean](../../formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean):

| Statement | Content |
| --- | --- |
| `Energy.NormalContraction.smoothed φ j` | φ is smoothed on ℝ with Lebesgue measure, radius `radius j` |
| `contDiff_smoothed`, `lipschitzWith_smoothed`, `norm_smoothed_sub_le`, `norm_fderiv_smoothed_le` | After mollification, smooth, still 1-Lipschitz, uniformly distance ≤ 2·radius j, derivative norm ≤ 1 |
| `SmoothGradient.Test.norm_gradient_comp_le` | Smooth 1-Lipschitz real function ψ composed with smooth test function f: ‖∇(ψ∘f)‖ ≤ ‖∇f‖ pointwise |
| `SmoothGradient.Test.compSmoothed f φ j` | Composite `φ.smoothed j ∘ f` is smooth test (smooth, L², gradient square integrable) |
| `energy_compSmoothed_le`, `norm_toL2_compSmoothed_sub_le` | Composite test energy ≤ energy of f; its L² class is at distance ≤ 2·radius j |
| `SmoothGradient.relaxedContractionBound μ φ` | Each implemented test satisfies the relaxed contraction bound |
| `SmoothGradient.markovian μ`, `SmoothGradient.dirichlet μ` | `Energy.Markovian μ (relaxation μ)`, `Energy.Dirichlet μ (relaxation μ)` |
| `SmoothGradient.Intrinsic.toIntrinsicL2_compL2`, `Intrinsic.markovian`, `Intrinsic.dirichlet` | Intrinsic coordinates and contraction exchange; intrinsic affine relaxation (pulled back to ambient L²) with Markov and Dirichlet properties |

Certificate `Solutions.ThmSmoothGradientRelaxationDirichlet.certificate μ`: Markov property, Dirichlet property of ambient relaxation, Dirichlet property of intrinsic relaxation. Three `example`: `Fin n` on any normal contraction and L² class contraction inequalities, `Fin 0`, Dirac measure on ℝ.

**What is claimed.** The table above states all assertions and certifications, for any Borel probability measure (including singular and zero-dimensional measures). **What is not claimed.** No claim is made regarding the relaxation on the test space being equal to the raw energy (raw/core agreement), or to the Cheeger energy or 2 Ch, nor any Poincaré inequality, the Markov property of covariance-weighted relaxation, self-adjoint generators, or spectral gap. **Finiteness scope and dimension zero.** The space is finite-dimensional; the test function is globally C∞; the normal contraction, as defined in the repository, is 1-Lipschitz and fixes 0; in the zero-dimensional case, all classes are constant, and the contraction inequality degenerates to 0 ≤ 0, yet is uniformly proven.

## Semantic alignment

| Blueprint clause | Lean | Conclusion |
| --- | --- | --- |
| each finite-dimensional Borel probability measure μ | any `ProbabilityMeasure E`, E finite-dimensional real Hilbert, Borel, second-countable | Aligned |
| smooth gradient relaxation | `Energy.SmoothGradient.relaxation μ` | Aligned |
| Normal contraction on L²(μ) class | `Energy.NormalContraction`, acts on `φ.compL2 μ` via Mathlib `LipschitzWith.compLp`, no choice of representatives | Aligned |
| Contraction reduces "relaxation energy" (non-increasing) | `Energy.Markovian`: `relaxation (φ.compL2 μ f) ≤ relaxation f` | Consistent (Blueprint "decreases" interpreted as ≤, consistent with `Markovian` definition) |
| Forms Dirichlet energy together with a closed quadratic structure | `Energy.Dirichlet μ (relaxation μ)` = `ClosedQuadratic ∧ Markovian`; closed quadraticity comes from `thm:smooth-gradient-relaxation-closed`'s `relaxation_closedQuadratic` | Consistent |
| Proof hint: "contraction transfer theorem + smooth approximation compatible with relaxed energy" | Approximate the contraction φ by mollification, rather than the test; pointwise bounds control the energy of composed tests, uniform approximation gives L² convergence, and transfer uses the existing `RelaxedContractionBound.sequentialRelaxation_comp_le` | Aligned (concrete implementation of the hint) |
| (Blueprint not listed) intrinsic affine relaxation | `Intrinsic.dirichlet`: `Energy.SmoothGradient.Intrinsic.energy μ` is also Dirichlet | Lean is stronger, records |

No weakening of Lean statements relative to Blueprint was found. `\uses{thm:smooth-gradient-relaxation-closed}` Used in practice within Lean. The Blueprint block tail supplements Lean's contracted expressions, intrinsic inferences, and the "without absolute continuity assumption" remark; the "Open." has been removed from the proof. The Dirac barrier of `obs:dirac-raw-energy` does not conflict with this conclusion: Markov property is a property of relaxed energy (functions in L² class).

## Proof path

- **Smoothing contraction.** `mollify volume (radius j) φ`: `contDiff_mollify` (φ continuous), `lipschitzWith_mollify` (K = 1),
  `norm_mollify_sub_le` gives ‖φ_j t − φ t‖ ≤ 1·(2·radius j); derivative bounds from `norm_fderiv_le_of_lipschitz`.
- **Composite test.** Smoothness `ContDiff.comp`; L²: ‖φ_j(f x)‖ ≤ ‖φ_j 0‖ + ‖f x‖ (1-Lipschitz), `MemLp.of_le` for
  constant plus ‖f‖; gradient: `norm_gradient_eq_norm_fderiv`, `fderiv_comp`, `opNorm_comp_le` gives ‖∇(φ_j∘f)‖ ≤ ‖∇f‖,
  square-integrability from `Integrable.mono` (measurability via `aestronglyMeasurable_gradient`).
- **Relaxed contraction bound.** ‖[φ_j∘f] − φ.compL2 [f]‖ ≤ 2·radius j: a.e. pointwise difference is φ_j(f x) − φ(f x),
  `Lp.norm_le_of_ae_bound` plus probability measure `measureUnivNNReal = 1`; `radius → 0` gives L² convergence;
  the energy of the approximating sequence liminf ≤ energy f (`liminf_le_liminf` + `liminf_const`).
- **Transfer.** `φ.compL2 μ` continuous (`lipschitzWith_compLp`), `sequentialRelaxation_comp_le` derived from relaxation's lower semicontinuity
  extended to the entire L² class.
- **Intrinsic.** `toIntrinsicL2 μ (φ.compL2 f) = φ.compL2 (toIntrinsicL2 f)`: both sides a.e. equal to v ↦ φ(f(reconstruct v))
  (`Lp.coeFn_compMeasurePreserving`, `quasiMeasurePreserving.ae_eq_comp`, `coeFn_compL2`), `Lp.ext`; then use the ambient version for intrinsic law.

Pitfalls: the point notation of `RelaxedContractionBound.sequentialRelaxation_comp_le` causes parameter misalignment, requiring explicit writing of `PreEnergy.` full name
and making `preEnergy μ` the first argument; the forced type conversion target of `(x : Measure _)` still needs full type specification;
when section variables are used inconsistently across theorems, use `omit ... in` instead of closing linter (following 2026-09-08 naming convention's scope rules).

## Metadata Synchronization

- ledger adds `thm:smooth-gradient-relaxation-dirichlet` (proved / lean, `kind: lemma` according to repository retention rules),
  eighteen proved nodes; `check_blueprint.CERTIFICATES` adds a mapping; lakefile `Solutions` root adds certificate module;
  `Poincare/Foundation.lean` imports a new module (root aggregate imported via Foundation).
- Blueprint theorem block anchors thirteen statements and certificates, statements and proofs marked `leanok`; `\uses` unchanged. route-composition.yaml has no claim for this node, `check_blueprint` passed.
- tasks.json: node changed to `available`, registered new module and `Energy/Dirichlet.lean`, `Relaxation/Contraction.lean`,
  `LipschitzApproximation.lean`, `SmoothGradient/{Basic,Closed}.lean`, `SmoothGradient/Intrinsic/{Basic,Closed}.lean`,
  and Mathlib `LpSpace/Basic`, `Convolution`, `FDeriv/Basic`, `FDeriv/Comp` hashes; all existing evidence hashes match.
- Current guide: HANDOFF (new section, eighteen counting, tables, mathematical boundaries and next stage list), README, `verification.md`,
  `solutions/README.md`, `formalization/README.md`, `blueprint/README.md`, `Energy/README.md`,
  `Poincare/README.md`, `naming.md`, root module and `Foundation` document highlights. statement golden, `STATEMENT_CHECKS`,
  route configuration unchanged.

## Evidence Boundary

`lake build` passed (3361 jobs), the certification is guarded by eleven library-level declarations with standard axioms; `check_ledger`, `check_blueprint`, `atlas check`, and 100 Python test cases passed. The final verification receipt was generated by `python3 research/verify.py` after this record and all guideline edits, with its source code SHA recorded within the receipt itself and not written back to this file. Local kernel replay trusts third-party compiled imports; no isolated rebuild, remote CI, commit, or push was performed; the fork between local and remote branches (two local refactoring commits, three remote documentation commits) is left for user handling.
