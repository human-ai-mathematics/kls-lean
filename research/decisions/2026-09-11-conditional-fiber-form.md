# Closed Conditional Fiber Forms `lem:conditional-fiber-form`: Review, Statement, and Semantic Alignment with Proof

Date: 2026-09-11 (Asia/Shanghai). Baseline: local `main` commit `5e5c704`, working tree contains 2026-09-10 four nodes not yet committed
(Dirichlet witness, one-dimensional `12·Var`, normal obstacle, raw/core consistency); untracked `research/weekly/`; local branch leads
`origin/main` by two commits and trails it by three documentation commits, the divergence and commits are left to the user. Lean/Mathlib v4.33.0, Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. User instruction: pause the one-dimensional transition from constant 12 to 4, first perform node operations unrelated to it,
Check in order `lem:conditional-fiber-form`, `prop:weighted-spectator-obstruction`, `lem:relative-perimeter-smoothing`;
No commit, no push. Before starting, `git status --short` is consistent with user description, with no other session modifications.

## Verification and Node Selection

`lem:conditional-fiber-form` (Blueprint Chapter 50 "Conditional-fiber frame route") in tasks.json is
`local_argument / unchecked`, atlas `ready` listed as `inspect_infrastructure`; the route sidecar's claim is upstream
`proved / checked_by: agent`. Verification: infrastructure **available**, no Mathlib gaps.

- Inside: six contracts of `KLS/ConditionalFiber.lean` and `kernel := (jointLaw μ ρ).condKernel`,
  `compProd_baseLaw_kernel` (`Measure.disintegrate`), `ae_restrict_congr` (transferring the μ-a.e. property to a.e. fiber template),
  `measurable_energyAt`; `Energy.ClosedQuadratic`/`Markovian`/`Dirichlet`; `WeightedGradient.dense_smoothCore`
  (The C_c^∞ dense class of any finite-dimensional Borel probability measure) and `lipschitzWith_of_contDiff_hasCompactSupport`.
- Mathlib: `Measure.ae_ae_of_ae_compProd`, `lintegral_liminf_le` (Fatou), `tendstoInMeasure_of_tendsto_eLpNorm`
  With `TendstoInMeasure.exists_seq_tendsto_ae` (L² convergence taking a.e. subsequence), `measurableSet_tendsto`,
  `Lp.tendsto_Lp_iff_tendsto_eLpNorm'`, `lowerSemicontinuous_iff_frequently`, `evariance_mul`,
  `lintegral_prod`/`lintegral_prod_swap`/`Measure.prod_swap`, `ENNReal.le_liminf_mul`,
  `ENNReal.mul_div_mul_left`, `ContDiff.lipschitzWith_of_hasCompactSupport`.
- Need a new, unique tool: the two-point variance identity `2·eVar[X] = ∬‖X t − X s‖ₑ² d(ν⊗ν)`. Mathlib only has the one with the covariance term
  `variance_sub`; The extended real version (both sides equal ⊤ when X ∉ L²) serves as a common tool for closedness, Markov, parallelogram, and Lipschitz bounds.

Thus `unchecked → available`, with the proof completed in the same round.

## Statement Design

New module (all within `formalization/FunctionalInequalities/`):

| module | declaration | content |
| --- | --- | --- |
| `Probability/TwoPointVariance.lean` | `Probability.integral_sub_sq_prod ν hX` | X ∈ L²: `∫(X t − X s)² d(ν⊗ν) = 2 Var X` |
| | `Probability.two_mul_evariance_eq_lintegral_prod ν hX` | a.e. strongly measurable X: `2·eVar[X] = ∫⁻‖X p.1 − X p.2‖ₑ² d(ν⊗ν)`, when X ∉ L², both sides are ⊤ |
| `KLS/ConditionalFiber/Closed.lean` | `twoPointMeasure κ b := (κ b).prod (κ b)` (abbrev), `twoPointMeasure_swap`, `lintegral_twoPointMeasure_swap` | Fiber two-point measure and its exchange invariance (reversibility) |
| | `jump κ b f` | `∫⁻‖f(rec b p.1) − f(rec b p.2)‖ₑ² d(twoPointMeasure κ b)` |
| | `two_mul_evariance_eq_jump`, `two_mul_evariance_id`, `energyAt_of_not_nondegenerate`, `energyAt_eq_jump_div` | non-degenerate fiber `energyAt κ b f = jump κ b f / (2·eVar[id])`; degenerate fiber 0 |
| | `jump_le_of_lipschitzWith`, `energyAt_le_of_lipschitzWith`, `energy_le_of_lipschitzWith`, `energy_ne_top_of_lipschitzWith` | Global L-Lipschitz test: fiber energy ≤ L², total energy ≤ d·L² |
| | `energyAt_zero`, `energyAt_mul`, `energyAt_add_sub`, `energyAt_comp_le`, `energyAt_le_liminf` | zero, quadratic homogeneity, parallelogram, contraction not increasing, Fatou |
| | `functional μ ρ := ⟨form μ ρ⟩`, `functional_apply`, `domain_functional`, `form_eq_energy_of_ae_eq` | Form as `Energy.Functional`; domain is `domain μ ρ` |
| | `smoothCore_subset_domain`, `dense_domain` | C_c^∞ classes lie in the finite-energy domain; domain dense |
| | `form_zero`, `form_smul`, `form_parallelogram`, `form_compL2_le`, `markovian` | Quadratic identities and Markov property of the form on L² classes |
| | `energy_le_liminf`, `lowerSemicontinuous_form` | Fatou for a.e.-convergent sequences; lower semicontinuity on L² |
| | `closedQuadratic`, `dirichlet` | `Energy.ClosedQuadratic (functional μ ρ)`, `Energy.Dirichlet μ (functional μ ρ)` |

`KLS/ConditionalFiber.lean` Only change `measurable_coordinates`, `measurable_reconstruct` from `private` to public,
and add `measurable_reconstruct_left`; the definitions and six contracts remain unchanged.

Certificate `Solutions.LemConditionalFiberForm.certificate μ ρ`: (1) `Energy.Dirichlet μ (functional μ ρ)`;
(2) a Markov kernel, base point, and Borel test have jump representations on non-degenerate fibers; (3) exchange invariance of two-point measures on each fiber;
(4) a global Lipschitz test has a `d·L²` bound. Five `example`: Blueprint scope (log-concave, second moment, admissible framework—no theorems used),
a dense domain on `Fin (n+1)` and lower semicontinuous, Markov inequality, C_c^∞ core within the domain, and no spherical probability law on `Fin 0`.

**What is claimed.** The table above states and certifies, for any Borel probability measure μ on a finite-dimensional real inner product space and any probability measure ρ on the sphere.

**What is not claimed.** No comparison with gradient energy (`lem:conditional-fiber-energy-comparison`), no conditional fiber Poincaré input, no frame bounds, no Poincaré inequality or KLS; no explicit construction of the bilinear polarization form (`ClosedQuadratic` already contains quadratic structure, polarization symmetry follows automatically); no Lipschitz relaxation or any other energy equal to this form. **Finiteness scope and dimension zero.** The space is finite-dimensional (`dense_smoothCore` required); in zero dimension, `Direction E` is empty, ρ does not exist, the statement holds vacuously, consistent with the Blueprint "d ≥ 1", and the certificate is recorded with the example `IsEmpty`.

## Semantic alignment

| Blueprint clause | Lean | Conclusion |
| --- | --- | --- |
| `d ≥ 1`, log-concave full-dimensional, with density, finite second moment probability measure | for any `μ : ProbabilityMeasure E`, for any `ρ`; Blueprint scope is type application in the certificate | Lean is stronger (removing the listed log-concavity, density, and moment assumptions) |
| form `D_{μ,ρ}` | `functional μ ρ`, value `form μ ρ` (the `def:conditional-fiber-form`'s `form`) | consistent |
| dense definition | `dense_domain : Dense (functional μ ρ).domain`, domain is `domain μ ρ` | consistent |
| closed | `lowerSemicontinuous_form`, and synthesized `ClosedQuadratic` (containing `zero`, `smul`, parallelogram) | consistent (Lean provides a quadratic identity) |
| Symmetric | Jump representation `energyAt_eq_jump_div`: the integrand is symmetric in (t,s), and polarization of the quadratic form automatically yields symmetry | Consistent (by Blueprint proof, reading the original "symmetric jump form") |
| Markov | `markovian : Energy.Markovian μ (functional μ ρ)` (all normal contractions, acting on L² class) | Aligned |
| reversible | `twoPointMeasure_swap : map swap (κ b ⊗ κ b) = κ b ⊗ κ b` and `lintegral_twoPointMeasure_swap` | consistent (Blueprint proof original statement "Symmetry of the two-point measure gives reversibility") |
| Proof: `(2σ²)⁻¹∬(f(t)−f(s))²` | `two_mul_evariance_eq_jump`, `energyAt_eq_jump_div` | Aligned |
| Proof: a.e. subsequence, disintegration, Fatou | `exists_seq_tendsto_ae`, `ae_ae_of_ae_compProd`, two applications of `lintegral_liminf_le` | Aligned |
| Proof: Lipschitz contractions decrease squared differences | `energyAt_comp_le`, pointwise `edist_le_mul` | Aligned |
| Proof: L-Lipschitz ⇒ `D ≤ d L²`; C_c^∞ lies in the domain and is dense | `energy_le_of_lipschitzWith`, `smoothCore_subset_domain`, `dense_smoothCore` | Aligned (Lean needs no second moments: C_c^∞ is bounded, hence in L²) |

No weakening of Lean statements relative to Blueprint was found. `\uses{def:conditional-fiber-form}` Actual usage in Lean. The Blueprint lemma block supplements
Lean reading (`functional`, `Energy.Dirichlet`, two-point symmetric/reversible representation, arbitrary law range, empty-dimensional triviality holds), and proof blocks append local paths;
the opening of Chapter 50 changes "the only leanok in this chapter is the definition" to "definition and this lemma"; the "Pinned provenance" section records additional Lean evidence beyond upstream agent review;
in Chapter 00, a note is added to the conditional fiber sentence: "structural form lemma is Lean-certified".

## Proof path

1. **Two-point identity.** X ∈ L²: let Y = X − E X, `(X t − X s)² = Y t² + Y s² − 2 Y t Y s`, `Integrable.comp_fst_iff`/
   `comp_snd_iff` / `mul_prod` for integrability, `integral_prod_mul` and `∫Y = 0` eliminate the cross terms, `integral_prod` adding a constant integral yields
   `2∫Y² = 2 Var`; again `ofReal_integral_eq_lintegral_ofReal` and `enorm_pow`/`Real.enorm_of_nonneg` converted to `‖·‖ₑ²`.
   X ∉ L²: `evariance_eq_top` give the left ⊤; if the right is finite, Tonelli afterwards `ae_lt_top'` take a point x₀ such that `t ↦ X x₀ − X t ∈ L²`,
   Subtracting a constant gives X ∈ L², contradiction.
2. **Jump representation.** `energyAt` expands to `if Nondegenerate then eVar/σ² else 0`; use identity when non-degenerate.
   `ENNReal.mul_div_mul_left` write `eVar/σ²` as `jump/(2σ²)`.
3. **Lipschitz bound.** `rec b t − rec b s = (t − s)•θ`, `‖θ‖ = 1`, hence the integrand ≤ L²‖t − s‖ₑ², and integrating yields
   `jump ≤ L²·(2σ²)`, `ENNReal.div_le_iff` yields `energyAt ≤ L²`; the base law is a probability law, `energy ≤ d·L²`.
4. **Quadratic identity.** Homogeneous use of `evariance_mul` (with c = 0, in ENNReal `0·⊤ = 0`); parallelogram at jump level pointwise in real numbers
   `(a+b)² + (a−b)² = 2a² + 2b²` after `ofReal` transformation, `lintegral_add_left`/`lintegral_const_mul` assembly, then `ENNReal.add_div`,
   `mul_div_assoc`. Pass to representatives of L² classes with `Lp.coeFn_add/sub/smul` and `energy_congr_ae`.
5. **Markov.** `φ.coeFn_compL2` replace representatives; jump layers pointwise `φ.lipschitz.edist_le_mul`, `ENNReal.div_le_div_right`.
6. **Closedness.** `lowerSemicontinuous_iff_frequently` + `exists_seq_forall_of_frequently` takes a sequence f_n → f and
   `form f_n ≤ y`; `tendsto_Lp_iff_tendsto_eLpNorm'` → `tendstoInMeasure_of_tendsto_eLpNorm` →
   `exists_seq_tendsto_ae` Take a.e. a convergent subsequence. `energy_le_liminf`: convergence written as `f_n − f → 0`, `measurableSet_tendsto`
   Given measurability, `ae_map_iff` is derived via `coordinates` to the joint law, `compProd_baseLaw_kernel` + `ae_ae_of_ae_compProd` leads to
   a.e. fiber; fiber to two-point space `quasiMeasurePreserving_fst/snd.tendsto_ae` pushed, `Tendsto.liminf_eq` +
   `lintegral_liminf_le` gets `jump f ≤ liminf jump f_n`, `ENNReal.le_liminf_mul` handles division by a constant; base law once again
   `lintegral_mono_ae` + `lintegral_liminf_le` + `le_liminf_mul` . Finally `liminf_le_of_le` yields `form f ≤ y` .
7. **Assembly.** `closedQuadratic` Five-field, `dirichlet := ⟨closedQuadratic, markovian⟩`.

Pit: `omit` cannot remove `[MeasurableSpace E]` referenced by `Kernel (Direction E × E) ℝ`, it can only omit `BorelSpace` / `SecondCountableTopology` / `InnerProductSpace`; `Measurable.add` / `Measurable.mul` provide the Pi form of `f + g` and `(fun _ ↦ c) * f`; when used as parameters in `rw` lemma, the λ form must be fixed via named argument `(f := fun x ↦ f x + g x)`; after `unfold jump`, an un-β-reduced `(fun x ↦ …) (reconstruct b p.1)` appears, requiring first `beta_reduce` then `rw`; `zero_le` has implicit parameters on ENNReal, written as `exact zero_le`; `mul_le_mul_left'` no longer exists, use `mul_le_mul' le_rfl`; `ofReal_norm_eq_enorm` is deprecated, changed to `ofReal_norm`; the `E p μ` of `Lp.coeFn_zero` is an explicit parameter; `probReal_univ` is the name of the probability law `μ.real univ = 1`.

## Metadata Synchronization

- ledger adds `lem:conditional-fiber-form` (proved / lean, `kind: lemma` according to repository legacy rules), twenty-one proved nodes;
  `check_blueprint.CERTIFICATES` adds a mapping; lakefile `Solutions` root adds certificate module; root aggregate `FunctionalInequalities.lean`
  imports `KLS.ConditionalFiber.Closed` (transitive import of `Probability.TwoPointVariance`).
- Blueprint lemma block anchors fifteen statements and certificates, statements and proofs marked `leanok`; route-composition.yaml's claim maintains `proved`,
  adding new `kind: lean` evidence outside upstream `agent_review` (`check_blueprint` requires Lean evidence source to be local `kls-lean`,
  ledger node proved/lean, and `\lean{}` contains this statement). The synthesis fixture for `research/tests/test_check_blueprint.py` is equipped with Lean evidence (the fixture automatically generates `\leanok` blocks for labels in `CERTIFICATES`, only reviewed evidence will be rejected by the checker), 103 test passes.
- tasks.json: node changed to `available`, registers two new modules, certificates, `ConditionalFiber.lean`, `Energy/Dirichlet.lean`,
  `Energy/ClosedQuadratic.lean`, `WeightedGradient/Core.lean`, and the Mathlib file hash used; `def:conditional-fiber-form`'s `ConditionalFiber.lean` evidence hash is refreshed synchronously.
- Current guide: HANDOFF (new section, twenty-one count, certificate table, conditional fiber route status and next phase text, boundary segment), README,
  `verification.md`, `solutions/README.md`, `formalization/README.md` (Probability row, KLS row, base segment),
  `KLS/README.md` (two rows), `blueprint/README.md`, `naming.md` (two rows), root module document highlights. statement golden,
  `STATEMENT_CHECKS`, `FoundationAxiomAudit` unchanged.

## Evidence Boundary

Default `lake build` passes; certification is guarded by standard axioms of eleven library-level statements. Final verification receipt is generated by `python3 research/verify.py` after this record and all guideline edits, with its source code SHA recorded within the receipt itself, not written back to this file. Local kernel replay trusts third-party compiled imports; no isolated rebuild, remote CI, commit, or push is performed. Downstream `lem:conditional-fiber-energy-comparison`, `cor:conditional-fiber-twelve-bound`, and `q:conditional-fiber-frame` do not receive new proofs.
