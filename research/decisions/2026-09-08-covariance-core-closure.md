# Covariance Kernel Closure: Statement, Semantic Alignment, and Proof

Date: 2026-09-08 (Asia/Shanghai). Base: uncommitted working tree on top of `575c82c`, immediately followed by
[affine constant definition record](2026-09-07-affine-poincare-constant-definition.md). Lean/Mathlib is v4.33.0,
Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. User instruction: "Temporarily do not commit, proceed next",
i.e., continue to the next node via atlas. This decision does not involve commit, push, remote CI, or release.

## Node Selection

After `def:affine-poincare-constant` certification, atlas has no `formalize` items, and all remaining leaf nodes are
theorems of `inspect_infrastructure`. `lem:covariance-core-closure` is the only unverified premise of `thm:affine-covariance-relaxation-closed`,
thereby unlocking `lem:affine-poincare-translation-invariance`, `thm:affine-isotropic-reduction`, and two CMH path nodes, thus prioritized.

## Statement Design

Blueprint: ν = ρ dx is log-concave in full dimension, Σ ⪰ 0 is a constant self-adjoint operator, T g = Σ^{1/2}∇g is densely defined and closable on globally Lipschitz L²(ν) functions, the graph closure equals the graph closure of the restriction to ℝ + C_c^∞(V), and the sequence relaxation of ‖Tg‖² is given by Q(f) = ‖T̄f‖² (f ∈ Dom T̄), +∞ otherwise.

Lean is divided into five modules, starting with general and progressing to specific.

| module | declaration | content |
| --- | --- | --- |
| [Energy/Relaxation/LinearPMap.lean](../../formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean) | `Energy.exists_mem_of_isClosed_of_frequently_norm_le` | Hilbert selection lemma: if a closed subspace G ⊆ X × H contains (xₙ, yₙ) with xₙ → x₀ and ‖yₙ‖ ≤ L frequently, then G contains (x₀, y₀) and ‖y₀‖ ≤ L; using the minimal norm element of the tail convex hull and the parallelogram law, without weak topology |
| | `Energy.PreEnergy.ofLinearPMap T` | Pre-energy f ↦ ‖T f‖², realized via the inclusion map; `ofLinearPMap_quadratic`, `ofLinearPMap_denseRealization_iff` |
| | `sequentialRelaxation_ofLinearPMap_of_mem` / `_of_notMem` / `_toAmbient` | Closable T: the relaxation on Dom T̄ equals ‖T̄ f‖², outside is ⊤, and the test upper equals the original energy |
| | `Energy.isClosable_of_graph_closure_snd_eq_zero`, `mem_graph_topologicalClosure_iff`, `IsClosable.closure_domRestrict_eq`, `_of_le` | closability criterion, sequential characterization of graph closure, equality of closure of graph norm dense kernels, and monotonicity |
| [Energy/Euclidean/WeakDerivative.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/WeakDerivative.lean) | `integral_fderiv_apply_eq_zero`, `integral_mul_fderiv_apply`, `integral_mul_inner_gradient` | The Haar integral of directional derivatives of C¹ functions with compact support is zero (translation invariance + parameter integral differentiation); smooth partial integration; weak derivative identity for globally Lipschitz g: ∫φ⟪∇g,w⟫ = −∫ g (Dφ)w (smoothing + dominated convergence) |
| [Energy/Euclidean/CovarianceGradient/Operator.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Operator.lean) | `weightedGradient B g`, `IsGradientTest ν B g`, `gradientGraph`, `gradientOperator ν B hac` | Test: globally Lipschitz, L²(ν), B∇g ∈ L²(ν;V); the graph {([g],[B∇g])} is a submodule under ν ≪ Haar (Rademacher gives a.e. linear), and is a function graph on the boundary of support with zero measure; `Submodule.toLinearPMap` gives the operator; characterization of domain and range |
| | `covarianceRelaxation_eq_sequentialRelaxation_ofLinearPMap` | If ∀v, ⟪Σv,v⟫ = ‖Bv‖², then the covariance relaxation of the node equals the relaxation of the operator |
| | `gradientOperator_apply_eq_zero_of_subsingleton`, `domain_gradientOperator_eq_top_of_subsingleton` | Zero-dimensional: the operator is zero, the domain is the full space |
| [Energy/Euclidean/CovarianceGradient/Closable.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Closable.lean) | `Probability.LocallyDominates ν m` | On each compact subset inside the support, m|_K ≤ C·ν|_K |
| | `gradientOperator_isClosable` | Premise ν ≪ m, ν(∂supp) = 0, LocallyDominates: the operator is closable |
| [Energy/Euclidean/CovarianceGradient/Core.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Core.lean) | `smoothCore ν`, `dense_smoothCore`, `dense_domain_gradientOperator` | The class of smooth compactly supported functions forms a submodule, dense in L²(ν) (Mathlib), hence the domain is dense, and the law holds for any rule |
| | `closure_domRestrict_smoothCore`, `closure_domRestrict_eq_of_smoothCore_le` | By previously proven `exists_smooth_weighted_L2_approximation`: the smooth kernel and the full space have the same closure; any kernel in between also shares this property |
| [KLS/LogConcave/CovarianceClosure.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/CovarianceClosure.lean) | `hν.absolutelyContinuous_haar`, `hν.frontier_support_eq_zero`, `hν.locallyDominates` | The full-dimensional log-concave law satisfies three premises; local domination is obtained from Borell density of compact sets with positive lower bound |
| | `hν.gradientOperator m B hi`, `_isClosable`, `dense_domain_`, `closure_domRestrict_eq_of_smoothCore_le`, `sequentialRelaxation_gradientOperator_of_mem/_of_notMem/_toAmbient`, `covarianceRelaxation_eq` | Log-concave version of the five conclusions of Blueprint |
| | `hμ.intrinsicGradientOperator m B`, `_isClosable`, `dense_domain_`, `closure_domRestrict_`, `hμ.affine_energy_eq` | Intrinsic version of the law for any log-concave μ, including zero-dimensional; `Energy.Affine.energy μ` equals the operator relaxation |

Certificate `Solutions.LemCovarianceCoreClosure.certificate`: for full-dimensional log-concave ν, any Haar m, and any B, the domain is dense, closable, and core-independent (for any smooth core ≤ S ≤ Dom of S), the relaxation on Dom Ṫ is ‖Ṫf‖², and outside is ⊤.
Three `example`: the intrinsic law of any log-concave law on Fin n, Fin 0 (operator zero and domain ⊤), and the equality of `Energy.Affine.energy`.

**What is claimed.** The table above lists all assertions and certifications. **What is not claimed.** No claim is made regarding the Poincaré inequality or translation invariance of Q,
Isotropic reduction, existence of Σ^{1/2} (downstream nodes construct B using spectral theorem), any agreement beyond raw/core
the Dirichlet/Markov property, comparison of `Energy.Affine.energy` with `Energy.Canonical.energy`, or KLS.
**Finite range and zero-dimensional.** The space is finite-dimensional; test global Lipschitz; B is arbitrary (including zero and singular); the direction space of zero-dimensional contains
In each conclusion, at this point the operator is zero, the domain is the entire space, and the relaxation is always zero.

## Semantic alignment

| Blueprint clause | Lean | Conclusion |
| --- | --- | --- |
| ν = ρ dx full log-concave law | `hν : LogConcave ν`, `hi : (interior ν.support).Nonempty`; density generated internally by Borell representation, no assumption made | uniform (Lean premise is weaker: no need to assume ρ) |
| Σ ⪰ 0 symmetric and self-adjoint, T g = Σ^{1/2}∇g | for any `B : V →L[ℝ] V`, T g = B∇g; Σ = B†B | Lean is stronger (for arbitrary B), recorded; the existence of Σ^{1/2} is left to the consumer |
| Densely defined on globally Lipschitz L²(ν) functions | `IsGradientTest` (also requires B∇g ∈ L², matching Blueprint's domain of T); `dense_domain_gradientOperator` holds for any law | Aligned (density is more general) |
| closable | `gradientOperator_isClosable`, under the condition ν ≪ m, ν(∂supp)=0, LocallyDominates; the log-concave full dimension law is satisfied | uniformly |
| Graph closure equals the graph closure of ℝ + C_c^∞(V) restriction | `closure_domRestrict_eq_of_smoothCore_le`: any submodule S containing smooth compactly supported classes and contained in the domain; ℝ + C_c^∞ is one of them | Lean is stronger (any intermediate kernel), recorded; ℝ + C_c^∞ is not individually named as a Lean object |
| Q(f) = ‖T̄f‖² on Dom T̄, +∞ elsewhere | `sequentialRelaxation_gradientOperator_of_mem` / `_of_notMem` , general form holds for any closable operator | Uniform (Lean is more general) |
| Final proof sentence: in dimension zero all functions are constant and gradients vanish | `domain_gradientOperator_eq_top_of_subsingleton`, `gradientOperator_apply_eq_zero_of_subsingleton` | Aligned |
| Proof of "smooth compactly supported functions are dense in L²(ν)" | Mathlib `Lp.dense_hasCompactSupport_contDiff` | Uniform |
| Weak compactness argument in proof (weak convergence subsequence, graph weak closed) | Replaced with Hilbert selection lemma (tail convex hull minimal norm element + parallelogram law), no weak topology | Same conclusion, different proof method, recorded |

No weakening of Lean statements relative to Blueprint was found. The `thm:borell-logconcave-density` in Blueprint's \uses is indeed used in Lean (`exists_isBorellDensity_of_interior_support_nonempty` and `exists_bounds_of_isCompact` provide local domination), and `lem:covariance-test-core-density` is used for equality of nuclear closures.

## Proof path

- **Selection Lemma.** Pₙ = {(x_j,y_j) : j ≥ n}, Cₙ = closure(convexHull(snd '' Pₙ)), zₙ is the element of minimal norm in Cₙ (`exists_norm_eq_iInf_of_complete_convex`). ‖zₙ‖ is monotone bounded → S ≤ L; the midpoint (zₙ+zₘ)/2 ∈ Cₙ and the parallelogram law gives ‖zₙ − zₘ‖² ≤ 2(‖zₘ‖² − ‖zₙ‖²), hence Cauchy → z₀. Take a convex combination pₙ ∈ convexHull Pₙ ⊆ G such that (pₙ).2 approximates zₙ, and (pₙ).1 lies in the contraction closed ball about x₀ (`LinearMap.image_convexHull`); G is closed ⇒ (x₀,z₀) ∈ G.
- **Relaxation identification.** ≤: (x, T̄x) ∈ closure(graph T) (`IsClosable.graph_closure_eq_closure_graph`), take a sequence of graph points.
  ≥ and ⊤: liminf < L² yields frequent ‖T fₙ‖ ≤ L (`frequently_lt_of_liminf_lt`), the selection lemma gives (x, y₀) ∈ graph T̄.
- **Weak derivative.** A compactly supported C¹ function u: F(t) = ∫ u(t•w + x) dm is constant (`integral_add_left_eq_self`), `hasDerivAt_integral_of_dominated_loc_of_deriv_le` differentiation yields ∫ (Du) w = 0; the product rule gives smooth partial integration; for Lipschitz g, use `mollify m (radius j) g`: `tendsto_gradient_mollify` (at differentiable points) + Rademacher + uniform bound K, `norm_mollify_sub_le` gives uniform convergence, and after applying dominated convergence to both sides, uniqueness of the limit yields the identity.
- **closability.** (0, y) ∈ closure(graph): fₙ → 0, T fₙ → y. For a test function φ ∈ C_c^∞ with support tsupport ⊆ Ω: local domination turns L²(ν) convergence into L¹(m) control on supp φ (`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`), ∫ φ•(T fₙ) → ∫ φ•y; ∫ φ•B∇gₙ = B(∫ φ•∇gₙ), ‖∫ φ•∇gₙ‖² = −∫ gₙ (Dφ)(∫φ•∇gₙ) ≤ ‖∫φ•∇gₙ‖·∫‖gₙ‖‖Dφ‖, and by local domination → 0. Hence ∫ φ•y dm = 0, `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives y = 0 m-a.e on Ω, ν ≪ m and ν(Ωᶜ) = 0 gives y = 0.
- **Kernel and dense.** Smooth compact support ⇒ Lipschitz (`lipschitzWith_of_nnnorm_fderiv_le`), bounded ⇒ test; Mathlib density; `exists_smooth_weighted_L2_approximation` gives graph norm approximation.
- **Log-concave premise.** ν ≪ Haar (already proved); ∂supp is the boundary of a convex set, Haar null (`Convex.addHaar_frontier`); Borell density ρ ≥ a > 0 on compact set K ⇒ m(s ∩ K) ≤ a⁻¹ ∫_{s∩K} ρ dm = a⁻¹ ν(s ∩ K).

## Metadata Synchronization

- ledger adds `lem:covariance-core-closure` (proved / lean, `solutions/LemCovarianceCoreClosure.lean`),
  fourteen proved nodes; `check_blueprint.CERTIFICATES` adds a mapping; lakefile `Solutions` root adds a certificate module.
- Blueprint lemma block anchors fourteen statements and certificates, statements and proofs marked `leanok`; tail supplements B instead of Σ^{1/2}, arbitrary intermediate kernels,
  and affine relaxation equality explanations; `\uses` unchanged.
- Root aggregation module imports `KLS.LogConcave.CovarianceClosure`; `Poincare/Foundation.lean` imports five new Energy modules and
  updates document highlights.
- tasks.json: node changed to `available`, registers new modules, `LipschitzApproximation.lean`, `BorellRepresentation.lean`
  and Mathlib `LinearPMap`, `Projection/Minimal`, `ParametricIntegral`, `AEEqOfIntegralContDiff`, `SmoothApprox`, `MeanValue` hashes;
  evidence hash of other tasks touched by this edit is synchronized.
- Current guide: HANDOFF, README, `verification.md`, `solutions/README.md`, `formalization/README.md`, `blueprint/README.md`, `Energy/README.md`, `KLS/LogConcave/README.md`, `naming.md`.
  statement golden, `STATEMENT_CHECKS`, route configuration unchanged.

## Evidence Boundary

`lake build` passed, certificate and eleven library-level statements have standard axioms guarding. Final verification receipt generated by `python3 research/verify.py`
after this record and all guide edits, with its source code SHA recorded in the receipt itself, not written back to this file. Local kernel replay trusts
third-party compiled imports; no isolated rebuild, remote CI, or release performed.
