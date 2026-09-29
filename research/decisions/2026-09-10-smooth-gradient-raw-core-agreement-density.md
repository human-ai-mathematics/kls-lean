# Local density assumption and raw/sequential-core agreement: statement, semantic alignment and proof

Date: 2026-09-10 (Asia/Shanghai). Baseline: local `main` commit `5e5c704`, working tree contains concurrently uncommitted Dirichlet witnesses, one-dimensional `12·Var`, normal obstacle work. User decides to proceed with one-dimensional coefficients 4 (awaiting collaborator to provide KLS 1995 original), during which first performs node work unrelated to that line; this node is HANDOFF's long-standing "not yet provided" raw/core consistency, independent of one-dimensional constants. User instructs not to commit, not to push.

## Verification and Node Selection

`thm:smooth-gradient-raw-core-agreement-density` (Blueprint Chapter 30) in tasks.json for `local_argument / unchecked`,
atlas `ready` lists it as `inspect_infrastructure`. Inspection found the infrastructure largely in place: closability from `Energy/WeightedGradient/Closable.lean`,
the identification of a closable operator's relaxation with the squared norm of its closure in `Relaxation/LinearPMap.lean`, truncation approximation from `LipschitzApproximation.
exists_compactSupport_weighted_L2`, and recovery-sequence comparison in `Relaxation/LowerSemicontinuous.lean`.
The only gap: closability theorem takes "interior support" as an open set, while Blueprint allows any open set Ω (Ω can be smaller than the interior support, for example by removing a
point where density tends to zero), and local domination holds only on compact subsets of Ω. Hence, extend `LocallyDominates` to
`LocallyDominatesOn ν m Ω`, generalize closability to `operator_isClosable_of_isOpen`. No new Mathlib interfaces are needed.
`unchecked → available` and prove simultaneously.

## Statement Design

New module [Energy/SmoothGradient/Core.lean](../../formalization/FunctionalInequalities/Energy/SmoothGradient/Core.lean),
namespace `FunctionalInequalities.Energy.SmoothGradient`; see below for the generalization of [Probability/LocalDomination.lean](../../formalization/FunctionalInequalities/Probability/LocalDomination.lean)
and [Energy/WeightedGradient/Closable.lean](../../formalization/FunctionalInequalities/Energy/WeightedGradient/Closable.lean).

| Statement | Content |
| --- | --- |
| `Probability.LocallyDominatesOn ν m Ω` | Every compact subset of Ω satisfies `m ≤ C·ν`; `LocallyDominates ν m` is abbreviated to `Ω = interior support` (`abbrev`), and the lemma is moved into the `LocallyDominatesOn` namespace and generalized |
| `WeightedGradient.operator_isClosable_of_isOpen hac hfr hΩ hΩν hloc` | When ν is supported on an open set Ω and m is dominated by ν on compact subsets of Ω, the weighted gradient operator is closable; the original `operator_isClosable` becomes a corollary |
| `structure LocalDensity ν m` | Blueprint's density assumption: `Ω` open, `ν Ωᶜ = 0`, `ν.restrict Ω = (m.restrict Ω).withDensity (ofReal ρ)`, `ρ` measurable, `ρ > 0` m-a.e. on Ω, `ρ⁻¹` is essentially bounded on compact subsets of Ω |
| `LocalDensity.measure_eq`, `absolutelyContinuous`, `subset_support`, `subset_interior_support`, `frontier_support_null`, `locallyDominatesOn` | From the density assumption, we derive `ν ≪ m`, `Ω ⊆ interior support`, support boundary zero measure, local domination |
| `lipschitzOperator ν m D`, `lipschitzOperator_isClosable` | Unit-weight Lipschitz gradient operator and its closability |
| `Test.memLp_gradient`, `Test.exists_domain_sequence_tendsto`, `Test.toL2_mem_closure_domain` | The square of the gradient of smooth test functions is integrable; truncated sequences converge in graph norm; smooth test functions belong to the domain of closure and the closure value is their gradient |
| `Test.coe_energy_eq_norm_toLp_sq`, `Test.energy_eq_nnnorm_sq` | Raw energy equals the square of the L² norm of the gradient |
| `lipschitzRelaxation_le_relaxation` | Recovery sequence: Lipschitz relaxation ≤ smooth relaxation |
| `preEnergy_agreesOnTests`, `preEnergy_isSequentialCoreFor` | `(preEnergy ν).AgreesOnTests (relaxation ν)`, `IsSequentialCoreFor` |
| `Intrinsic.preEnergy_agreesOnTests`, `Intrinsic.preEnergy_isSequentialCoreFor` | An instance of the intrinsic law `intrinsicMeasure μ` |

Certificate `Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate ν m D`: The conjunction of two conclusions. Three `example`:
Intrinsic law instance, on Euclidean families "the relaxation energy of smooth test classes equals the raw energy", and the energies of two smooth tests in the same L² class are equal.

**What is claimed.** All statements and certificates above, for any finite-dimensional real inner product space with a local density probability law. **What is not claimed.** Without the density assumption, no assertions are made (`obs:dirac-raw-energy`, `obs:normal-direction-raw-energy` explain this is impossible); no equivalence to Cheeger energy or graph-norm core is claimed; no Poincaré inequality is claimed; no equality between Lipschitz relaxation and smooth relaxation is claimed (only ≤ is proven, the other side is not used).
**Finiteness scope and dimension zero.** The space is finite-dimensional; on zero-dimensional spaces, the Haar measure and the density representation of the probability law require `m = ν`; when the structure is instantiable, the theorem holds as usual, but the certificate does not list the zero-dimensional case separately.

## Semantic alignment

| Blueprint clause | Lean | Conclusion |
| --- | --- | --- |
| Affine support `A = a + V`, ν is an intrinsic law | General `ν : ProbabilityMeasure V`, V is a finite-dimensional inner product space; intrinsic law is an instance of `Intrinsic.*` | Lean is stronger (any law), intrinsic instances are preserved |
| Open set Ω ⊆ V, `ν(V ∖ Ω) = 0` | `LocalDensity.Ω`, `isOpen`, `compl_null` | Consistent |
| Borel `ρ : V → [0,∞)`, `ν(B) = ∫_B ρ dLeb` for Borel `B ⊆ Ω` | `ρ : V → ℝ` measurable, `restrict_eq` (`ENNReal.ofReal ρ` density); Lebesgue measure replaced by any Haar measure `m` | Consistent (`ofReal` cut off negative values, positivity a.e. makes them indistinguishable; Haar generalization is stronger in Lean) |
| `ρ > 0` a.e. on Ω | `pos : ∀ᵐ x ∂m, x ∈ Ω → 0 < ρ x` | Consistent |
| `ρ, ρ⁻¹ ∈ L^∞_loc(Ω)` | Only assumes `inv_locallyBounded` (`ρ⁻¹` is essentially bounded on compact subsets); `ρ ∈ L^∞_loc` is not assumed | Lean is stronger (fewer assumptions), already documented in Blueprint block and document description |
| "explicit positivity premise is retained: real inversion sends zero to zero" | `pos` and `inv_locallyBounded` are separated | Consistent |
| `P_ν.AgreesOnTests(E_ν)` | `preEnergy_agreesOnTests` | Consistent |
| `IsSequentialCoreFor`, `SequentiallyGenerates` definitional | `preEnergy_isSequentialCoreFor := ⟨_, rfl⟩` | Consistent |

No weakening of Lean statements relative to Blueprint was found. `\uses` unchanged. Blueprint originally had no proof block; this addition includes `\begin{proof}\leanok …\end{proof}`
Record local route, and in the theorem block tail describe Lean's assumption structure and the scope of "any law".

## Proof route

1. **Assumption derivation.** `measure_eq`: `ν s = ∫⁻_s ofReal ρ dm` (`s ⊆ Ω` is measurable), by `restrict_eq` and
   `withDensity_apply`, `restrict_restrict`.`absolutelyContinuous`: `ν s = ν (s ∩ Ω) + ν (s ∖ Ω)`, the former is
   The integral over the m-zero set, the latter ≤ `ν Ωᶜ = 0`. `subset_support`: Every neighborhood of a point in Ω contains a non-empty open set `W ⊆ Ω`.
   `ν W = ∫⁻_W ofReal ρ > 0` (`setLIntegral_pos_iff` plus Haar's `IsOpen.measure_pos` and a.e. positivity).
   `frontier_support_null`: `frontier support ⊆ (interior support)ᶜ ⊆ Ωᶜ`. `locallyDominatesOn`: compact `K ⊆ Ω` on
   `ρ⁻¹ ≤ C'` (`C' = max C 1 > 0`) and positive gives `1 ≤ C' ρ` a.e., hence `m (s ∩ K) ≤ C' ν (s ∩ K)`.
2. **closability Extension.** The auxiliary lemma of `Closable.lean` replaces `K ⊆ interior support` with `K ⊆ Ω`, `operator_isClosable_of_isOpen`
   The proof body is modified in two places: `Ω` is given by the parameter (`IsOpen Ω`), and the last step uses `ν Ωᶜ = 0` to obtain a.e. `x ∈ Ω`. The original theorem for `Ω = interior
   support` is retained; the sole external consumer, `KLS.LogConcave.locallyDominates`, needs no change because this is an `abbrev`.
3. **Truncation.** `exists_compactSupport_weighted_L2` (B = id) gives a globally Lipschitz compactly supported `g_j`, which are
   `WeightedGradient.IsTest`, its class within the operator domain, `(g_j, ∇g_j) → (f, ∇f)` at `L²(ν) × L²(ν;V)`
   (`Lp.edist_toLp_toLp` plus `ENNReal.tendsto_toReal`).
4. **Closure.** `mem_graph_topologicalClosure_iff` plus `IsClosable.graph_closure_eq_closure_graph` and `LinearPMap.mem_graph_iff`
   Given `f ∈ dom T̄`, `T̄ f = ∇f`.
5. **Relaxation comparison.** `sequentialRelaxation_le_of_recovery_sequences (preEnergy ν) (ofLinearPMap T)`: The truncated sequence energies
   `‖T g_j‖²` converge to `‖∇f‖² = energy f` (`Tendsto.liminf_eq`), hence Lipschitz relaxation ≤ smooth relaxation.
6. **Assembly.** `energy f = ‖T̄ f‖² = relax_Lip f ≤ relax_smooth f ≤ energy f`.

Pit: `WeightedGradient/Core.lean` does not import `Closable.lean`; explicit import is required; section variables of `theorem` are included by statement, `D` appears in the conclusion of a theorem only if `include D in` is applied; `(preEnergy ν).Test` and `Test ν` are not equal under the implicit transparency of `rw`, use `exact` to pass `Test.energy_eq_nnnorm_sq`; `Lp.edist_toLp_toLp` must first `rw [Test.toL2]` expand; the components of `LinearPMap.mem_graph_iff` appear in `(pair).1` form, first `have` restate then use `▸`; `measure_inter_add_diff` is deprecated, use `measure_inter_add_sdiff` instead; the first explicit argument of `ContDiff.inner` is the domain `ℝ`.

## Metadata Synchronization

- ledger adds `thm:smooth-gradient-raw-core-agreement-density` (proved / lean, `kind: lemma` according to repository legacy rules),
  twenty proved nodes; `check_blueprint.CERTIFICATES` adds a mapping; lakefile `Solutions` root adds a certificate module;
  `Poincare/Foundation.lean` imports `Energy.SmoothGradient.Core` (alongside the same-day `NormalDirection`).
- Blueprint theorem block anchors fifteen statements and certificates, statements and proofs marked `leanok`; route-composition.yaml has no claim for this node, unchanged.
- tasks.json: node changed to `available`, registers new module and internal/library, Mathlib dependency hashes; `Closable.lean`, `LocalDomination.lean`
  after changes, two evidence hashes for `lem:covariance-core-closure` are synchronized and refreshed.
- Current guide: HANDOFF (new section, twenty count, certificate table, boundary text), README, `verification.md`, `solutions/README.md`,
  `formalization/README.md`, `Energy/README.md`, `Poincare/README.md`, `blueprint/README.md`, `naming.md`
  (`LocallyDominatesOn`, `LocalDensity`, normal coordinate three lines), `Foundation` document highlights. statement golden,
  `STATEMENT_CHECKS`, route configuration unchanged.

## Evidence Boundary

Default `lake build` passes; certificates and eleven library-level statements are guarded by standard axioms. Final verification receipt is generated by `python3 research/verify.py` after this record
and all guide edits, with its source code SHA recorded in the receipt itself, not written back to this file. Local kernel replay trusts third-party compiled imports;
no isolated rebuild, remote CI, commit, or push performed.
