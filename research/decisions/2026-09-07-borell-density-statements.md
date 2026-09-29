# Borell Density Representation: Statement Drafting and Semantic Alignment

Date: 2026-09-07 (Asia/Shanghai). Baseline: uncommitted working tree atop `0451f2e`, locally `main` and
`origin/main` consistent. Lean/Mathlib is v4.33.0, Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. User instruction: "Temporarily hold off on release, complete the first step's work, then help me write the second step's statement in a style consistent with formech, and afterwards verify once for semantic alignment." This decision does not involve commit, push, remote CI, or Pages deployment.

## Step One: Closing the Loops, No Release

The previous round of analysis identified two textual inconsistencies with completed proofs. Corrections made here:

1. The module documentation for `formalization/FunctionalInequalities.lean` still states Borell equivalence and conditional-fiber
"contains `sorry`, pending Claude proof." Revised to indicate both have been proven, and note that the only draft with a placeholder is the new module `KLS/BorellRepresentation.lean`.
2. Row 7 of `blueprint/src/chapters/50-kls-routes.tex` still claims this chapter has no node carrying `leanok`. Revised to:
All upstream statements lack Lean certification; the only `leanok` in this chapter is the implemented definition `def:conditional-fiber-form`; all theorems, lemmas, assumptions, and problems do not carry `leanok`.

The previous receipt `build/verification/20260907T083402.818470Z` was in state passed, but its snapshot hash has expired, due to only the deletion of Prove2Me file and lakefile modifications. After this decision, `verify.py` will be rerun to ensure the receipt matches the current source code; the result is not prewritten. Release (CL, commit, push, remote CI) is postponed as per user request.

## Step Two: Lean Statement for `thm:borell-logconcave-density`

### Reading Entry

1. [HANDOFF](../../HANDOFF.md), [verification workflow](../verification.md), [naming](../naming.md).
2. Blueprint [00 Chapter](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex)
`thm:borell-logconcave-density`'s original statement.
3. [KLS/BorellRepresentation.lean](../../formalization/FunctionalInequalities/KLS/BorellRepresentation.lean):
First read `IsBorellDensity`, then read the five `sorry` obligations and two proven identities.
4. [Default build entry point](../../solutions/ThmBorellLogconcaveDensity.lean): prints eight signatures, provides
type applications for `Fin n` and `Fin 0`, and adds standard axiomatic guards to the two proven identities. No `certificate`.

### Writing Conventions

HANDOFF designates `lyw-ops/formech@d0bb1913` as the reference writing style. This batch follows several practices from its README and AGENTS.md: for each declaration, the documentation first states the conclusion and under which model it holds, then separately notes what is not claimed; proposition-level specifications and executable objects are separated, here manifested as `IsBorellDensity` being a `Prop` structure, with existence, positivity, boundedness, and moments as independent theorems; finite ranges are explicitly stated, e.g., zero-dimensional, any Haar reference measure; drafts are not presented as theorems. Custom notation or `Bool` predicates from formech are not adopted, as the objects in this repository are not finite and enumerable.

### Declaration Table

The following table omits the common prefix `FunctionalInequalities.KLS`. Type variables: `F` is a finite-dimensional, complete real inner product space, Borel, second-countable; `V := (Probability.affineSupport μ).direction`; `ν := Probability.intrinsicMeasure μ`; `m` is any additive Haar measure on `V`.

| Number | Statement | Status | Precise content |
| --- | --- | --- | --- |
| 0 | `IsBorellDensity ν m ρ` | definition, no placeholder | `ρ : V → ℝ` measurable, non-negative, upper semicontinuous, pointwise real power log-concave `ρ x ^ t * ρ y ^ (1 - t) ≤ ρ (t • x + (1 - t) • y)` (`0 < t < 1`), and `m.withDensity (ENNReal.ofReal ∘ ρ) = ν` |
| 1 | `LogConcave.exists_isBorellDensity` | `sorry` | For each Haar `m`, there exists `ρ` such that `IsBorellDensity ν m ρ` |
| 2 | `IsBorellDensity.pos_of_mem_interior_support` | `sorry` | Any representative element of the probability law is pointwise positive on `interior ν.support` |
| 3 | `IsBorellDensity.exists_bounds_of_isCompact` | `sorry` | for any compact subset `K` of `interior ν.support`, there exists `0 < a` and `b` such that `a ≤ ρ x ≤ b` holds on `K` |
| 4 | `LogConcave.intrinsic_integrable_exp_norm` | `sorry` | there exists `t > 0` such that `exp (t * ‖v‖)` is integrable with respect to `ν` |
| 5 | `LogConcave.intrinsic_integrable_norm_pow` | `sorry` | For each `p : ℕ`, `‖v‖ ^ p` is integrable with respect to `ν` |
| 6 | `LogConcave.closure_convexHull_intrinsic_support` | proven | `closure (convexHull ℝ ν.support) = ν.support` |
| 7 | `LogConcave.intrinsic_interior_support_compl` | proven | `ν (interior ν.support)ᶜ = 0` |

Section 2, 3 states that for any Borel finite-dimensional `V` over a probability measure and any representative element statement, it is independent of intrinsic constructions; Section 1, 4, 5 assumes `hμ : LogConcave μ` and invokes `hμ.`. Section 6, 7 is directly obtained from existing `LogConcave.intrinsicMeasure`, `convex_support`, `intrinsic_frontier_support` and Mathlib's `Measure.isClosed_support`, `measure_compl_support`, and the proofs are actually completed here.

### Quantifiers and Boundaries

- The reference measure is an arbitrary Haar measure `m`, not a fixed Lebesgue measure; each `m` has its own `ρ`. In zero dimension,
  `V` is a point, the Haar measure is a positive multiple of a Dirac mass, `ρ` is a positive constant, and the counting measure mentioned in Blueprint is one such case. Thus, the Dirac measure is included without requiring a positive dimension.
- `Ω` takes `interior ν.support`. Blueprint writes it as the interior of the closed convex hull; the 6th statement proves their equivalence.
- The log-concave is written pointwise by `Real.rpow`, allowing `ρ` to be zero, `0 ^ t = 0` (`t > 0`); `{ρ > 0}` is thus a convex set. The combination with `KLS.LogConcave` follows the order of `t • x + (1 - t) • y`.
- The 3rd statement provides pointwise two-sided bounds on compact sets, stronger than Blueprint's `ρ, ρ⁻¹ ∈ L^∞_loc(Ω)` and implying it; it is trivially true when `K = ∅` holds.
- The 4th statement is not in the original Blueprint; it is the actual form of a moment conclusion given in the literature, listed as a library-level intermediate goal; the 5th statement is the actual moment conclusion for nodes. There is no moment statement with respect to the ambient measure `μ`; `Conjecture` already takes the second moment as a premise.
- No assumptions on density, second moment, full-dimensional support of the environment, or raw/core agreement; no claims about Cheeger, Dirichlet, spectral gap, or KLS.

### Existing Tools and Proof Boundaries

- `LogConcave.intrinsic_absolutelyContinuous` (proven) with Mathlib `measurable_rnDeriv`, `withDensity_rnDeriv_eq`, `rnDeriv_lt_top`: provides a.e. density. The gap in obligation 1 is the selection of a finite-valued version of upper semicontinuous log-concave functions; `rnDeriv.toReal` itself lacks these properties.
- `LogConcave.exists_eventually_closedBall_le` and `Probability/BallDomination.lean`: the ratio of small balls is uniformly bounded, usable for upper and positivity transfer in obligations 2 and 3.
- Mathlib `UpperSemicontinuousOn.exists_isMaxOn`, `UpperSemicontinuousOn.bddAbove_of_isCompact`: upper bound in obligation 3. Continuity of finite concave functions on open convex sets provides a lower bound, requiring local arguments.
- Mathlib `Probability/Moments/IntegrableExpMul.lean`'s `integrable_pow_abs_of_integrable_exp_mul` family: obligation 4 implies obligation 5. Obligation 4 itself requires deriving exponential tails from log-concavity; absolute continuity is insufficient.
- Borell (1974) original PDF was not read in the previous round and is not being attempted now; correspondence between complete representatives and moments still needs verification. This does not affect the mathematics classification.

`tasks.json` preserves `published / missing`, with new evidence including the hash of this module. Three gaps are rewritten as corresponding named obligations. The verifier continues auditing all Blueprint anchor points: this node only anchors the non-placeholder `IsBorellDensity` and statements 6, 7, and five `sorry` obligations do not enter `\lean{}`, otherwise the axioms audit would fail due to `sorryAx`. The node does not carry `leanok`.

### ledger and metadata

- ledger adds `thm:borell-logconcave-density`, `drafted / checked_by: null`, `lean_solution` as default build entry points; eleven proven nodes remain unchanged individually. `meta.scope` is appended with one additional sentence.
- The Solutions root of `lakefile.toml` gains `solutions.ThmBorellLogconcaveDensity`; the aggregated root imports a new module and updates the documentation.
- Three new anchor points are added to the Blueprint theorem block, with proof text explaining the actual scope and non-claims of the Lean draft.
- HANDOFF, `verification.md`, `solutions/README.md` are synchronized with a brief explanation. `check_blueprint.CERTIFICATES`, golden, `STATEMENT_CHECKS`, and `FoundationAxiomAudit` remain unchanged.

## Semantic alignment check

The following compares each clause of the Blueprint original with the complete signature printed in `lake env lean`.

| Blueprint clause | Lean correspondence | Conclusion |
| --- | --- | --- |
| `ν` is a finite-dimensional log-concave `μ` on the affine support direction space `V` | The instance set of variable `F` coincides with the intrinsic section of `LogConcaveDensity.lean`; `ν = ↑(Probability.intrinsicMeasure μ)`, under premise `KLS.LogConcave μ` | Consistent |
| `K_ν` is the support closed convex hull, `Ω = int_V K_ν` | Using `interior (↑ν).support`; Proof `closure (convexHull ℝ supp) = supp` in statement 6, entry file provides type application of `interior (closure (convexHull ℝ supp)) = interior supp` | Consistent, proven by identity |
| There exists an upper semicontinuous log-concave Borel `ρ : V → [0,∞)` | `IsBorellDensity`'s `measurable`, `nonneg`, `upperSemicontinuous`, `logConcave`; range is `ℝ`, nonnegativity is a proposition, finite values hold automatically | Consistent |
| `ν(V ∖ Ω) = 0` | Statement 7, `↑ν (interior (↑ν).support)ᶜ = 0` | Consistent, proven |
| `dν = ρ dLeb_V` | `m.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) = ν`, `m` for any Haar measure | Lean is more general: for each Haar `m`, a separate `ρ` is provided, Lebesgue is one of them |
| `ρ > 0` on `Ω` | Statement 2 holds for any `ρ` satisfying `IsBorellDensity` | Lean is stronger: for all representatives, not just one |
| `ρ, ρ⁻¹ ∈ L^∞_loc(Ω, Leb_V)` | Statement 3: on each compact `K ⊆ Ω`, `0 < a ≤ ρ ≤ b` | Lean is stronger: pointwise bounds imply local essential boundedness |
| `ν` has finite moments of all orders | Statement 5, `∀ p : ℕ, Integrable (fun v ↦ ‖v‖ ^ p) ↑ν`; Statement 4 for exponential moments as an intermediate goal | Consistent; Statement 4 is a stronger library-level statement outside Blueprint |
| Lebesgue is the counting measure at a point in zero dimension, including Dirac measure | No positive dimension assumption added; zero-dimensional Haar measure is a positive multiple of Dirac mass, counting measure is included; entry file has type application `Fin 0` | Consistent |

No Lean clause is weaker than its Blueprint counterpart. Three differences are all stronger or more general on the Lean side, and are all marked in the table above;
No modification to the Blueprint statement is needed, and no `\notready` is required. The choice in statement 4 regarding ambient moments is explained in "Quantifiers and Boundaries". The parameter order of `IsBorellDensity` in the signature is `(ν m : Measure V) (ρ : V → ℝ)`, and both entry file and Blueprint anchor points refer to it accordingly.

## Local Evidence

- `lake build`: Default goal passes, new module and entry report several "declaration uses sorry" warnings, as expected.
- `check_ledger.py`: 1 ledger, 12 nodes, 0 errors. `check_blueprint.py`: 8 chapter, 87 labels, 4 active routes, 0 errors. `atlas.py check`: 74 mathematical nodes, 11 certificates, acyclic. Python tests 100 pass.
- Two proven identities are guarded by standard axioms in the entry file; five obligations of transitive axioms should include `sorryAx`, and must not be treated as proof acceptance.
- After completion of this record, the final working tree is run with `python3 research/verify.py`, followed by `atlas.py export` and `ready`. The source SHA256 of the receipt is recorded within the receipt itself and is not written back to this file. The passage of draft elaboration in default builds does not imply that the five obligations have been proven. Local kernel replay trusts third-party compiled imports; no isolated rebuild, remote CI, or release was performed.
