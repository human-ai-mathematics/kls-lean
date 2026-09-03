# Certificate deduplication and current finite candidate review

Date: 2026-09-03. This append-only record follows the user's explicit request to remove the
repeated `Project/` and `solutions/` wrappers. It supersedes the layout in
`2026-09-03-module-layout.md` and the public-name list in the original
`../decisions/2026-09-03-finite-tensorization-candidate.md` for the pending human review.
Those earlier records remain unchanged as history.

Status: the finite node remains **drafted / checked_by: null**. This is neither human statement
freeze nor mathematical proof completion. HEAD remains
`4801ca958778ae02cc0d81fc7ec805a4e96a894c` on `main`; all unfinished work remains local and
uncommitted. No skeleton has been pushed.

## One mathematical library, one entry point per node

The reusable mathematics remains in `formalization/FunctionalInequalities/Poincare/`.
The three `Project/` files have been deleted. Each proved ledger node now has exactly one
`Solutions.*.certificate` directly combining reusable library conclusions:

- `Solutions.LemLinearTestLower.certificate` combines `Poincare.rayleigh_le_constant` and
  `Covariance.lambdaMax_le_constant` with the original Euclidean finite-second-moment assumptions.
- `Solutions.LemPoincareTensorization.certificate` combines `Poincare.Holds.prod` and
  `Poincare.constant_prod_le` with the original Hilbert and factor-probability assumptions.

Both certificate types, including implicit and typeclass parameters, are byte-for-byte equal
to their pre-deduplication output. Their proof terms now refer to the library directly.
The binary Euclidean certificate was a redundant specialization; its exact conclusion is
checked by a typed application of the retained certificate in the same solution file.
The root aggregate imports only proved mathematics and never imports solutions or drafts.

In total, Lean source files decreased from **17 to 14**, and **18 named wrapper theorems** were
removed. No replacement aliases or forwarding modules were added.

## Removed public wrappers

The following names are retired, rather than preserved in another directory:

| Former namespace | Removed declarations |
| --- | --- |
| `FunctionalInequalities.Project.LinearTestLower` | `covariance`, `certificate`, `euclidean` |
| `FunctionalInequalities.Project.PoincareTensorization` | `fixed_constant`, `optimal_constant`, `certificate`, `euclidean_fixed_constant`, `euclidean_optimal_constant`, `euclidean_certificate` |
| `FunctionalInequalities.Project.PoincareFiniteTensorization` | The eight Euclidean declarations listed below |
| `Solutions.LemPoincareTensorization` | `euclidean_certificate` |

No `Project.*` name is part of the explicit binary freeze snapshot. The preserved frozen names
are `FunctionalInequalities.Poincare.Holds.prod` and
`FunctionalInequalities.Poincare.constant_prod_le`; the frozen ledger statement and the existing
Poincaré definitions and linear-test/covariance library API are unchanged.

## Candidate surface: 45 public declarations, eight specialization checks

The original 53-name draft consisted of 45 reusable declarations and eight duplicate Euclidean
specializations. Only the 45 reusable names remain public. Their types are **exactly the first
45 blocks of the original signature snapshot**, without renaming or changing any binder.
All underlying mathematical obligations remain in the reusable library. Removing the eight
specialization wrappers reduces the placeholder count from 52 to **44**, not by proving any new
mathematical obligation.

`solutions/LemPoincareFiniteTensorization.lean` now directly imports the finite-product library.
It contains 45 named `#check @...` commands, eight anonymous fully quantified typed applications,
and six additional boundary applications: 59 checks, no new named theorem, `example`, or
placeholder. Each of the eight applications preserves the former declaration's parameters,
probability assumptions, encoding, and conclusion:

| Former suffix under `FunctionalInequalities.Project.PoincareFiniteTensorization` | Current numbered application |
| --- | --- |
| `euclidean_fixed_constant` | 1: dependent finite NNReal-supremum bound, cast to real |
| `euclidean_optimal_constant` | 2: ENNReal indexed-supremum equality |
| `euclidean_binary_reverse` | 3: both fixed-constant reverse bounds with separate factor probabilities |
| `euclidean_binary_optimal_constant` | 4: ENNReal binary maximum equality |
| `euclidean_empty` | 5: arbitrary empty dependent family, fixed and optimal zero, no probability premise |
| `euclidean_singleton` | 6: Fin 1 family, any natural dimension |
| `euclidean_zero_dimensional` | 7: all zero-dimensional factors, fixed and optimal zero |
| `euclidean_zero_factor` | 8: a selected factor with `hi : d i = 0` in an arbitrary mixed family |

The empty-family probability instance is supplied locally by elimination of an index in
`Fin 0`, so no factor normalization hypothesis is added. The mixed-zero check transports the
standard subsingleton instance using its existing dimension equality. These are type
instantiations of the draft API, not certificates of its unproved mathematics. Additional
checks retain `(0,n)`, `(n,0)`, singleton-zero, empty fixed/optimal, and two-zero-factor cases.

The mathematical ledger statement and the source/domain boundaries remain unchanged.
The infimum argument requires no assumed attainment witness; no example of finite infimum
nonattainment is claimed. Infinity stays in ENNReal. BGL's binary upper-bound/finite-iteration
correspondence and the independent coordinate reverse direction remain as recorded in
`2026-09-03-finite-tensorization-design.md` and the semantic review.

## Validation and invariants

After the edits:

```text
python3 research/check_ledger.py
1 ledger(s), 3 nodes. 0 error(s).

python3 -m unittest discover -s research/tests -p 'test_*.py'
Ran 24 tests; OK.

cd formalization && lake build
Build completed successfully (2956 jobs).
```

Exactly 44 build warnings report the remaining draft placeholders; there are no other warnings.
An independent read-only comparison confirmed that all ten reusable library source files are
byte-for-byte unchanged from before deduplication. All 35 protected hashes match, covering the
pre-existing decisions/explorations, library, ledger, checker/tests, Lake configuration,
toolchain, and manifest. The two proved nodes keep their original ledger objects and default
solution paths. Their static certificate/import checks pass with no exemption.

The root, Issue #2 certificate, and Issue #6 certificate have local import closures of 7, 3,
and 6 files respectively. They have no dependency on the draft modules or removed Project layer.
The two certificate types were compared byte-for-byte before and after this refactor.

Transitive axiom checks were rerun for the two certificates and four directly used core results:

```lean
import solutions.LemLinearTestLower
import solutions.LemPoincareTensorization
#print axioms Solutions.LemLinearTestLower.certificate
#print axioms Solutions.LemPoincareTensorization.certificate
#print axioms FunctionalInequalities.Poincare.rayleigh_le_constant
#print axioms FunctionalInequalities.Covariance.lambdaMax_le_constant
#print axioms FunctionalInequalities.Poincare.Holds.prod
#print axioms FunctionalInequalities.Poincare.constant_prod_le
```

All six use only `propext`, `Classical.choice`, and `Quot.sound`.
Previously audited wrapper names that were removed are not retained merely to preserve the
old audit count. Their reusable results and the two actual node certificates remain checked.

| Checked output | SHA-256, including final newline |
| --- | --- |
| 45 current public candidates | `1dbb986f5764f752adb516ea108ff771cd6058021ade292da727b451f541ce66` |
| Two retained certificate types, before and after | `81c99ab13552a477214158f5fb6cdf45b090e66ed77d425258fd0a6cb6a6dbee` |
| Two frozen binary public types | `75e576722a02a1c49588534389331ed1f493fec233ee21756e348c23f8424d0a` |

## Reproduce the current output

From `formalization/`, `lake env lean ../solutions/LemPoincareFiniteTensorization.lean` prints
all 45 signatures followed by the 14 application checks. To print only the named public types,
copy the 45 `#check @...` lines into a temporary Lean file after:

```lean
import solutions.LemPoincareFiniteTensorization
set_option pp.universes true
set_option format.width 100
```

Run that file using `lake env lean`. The exact raw public output is also saved as
[2026-09-03-finite-tensorization-signatures-v2.txt](2026-09-03-finite-tensorization-signatures-v2.txt).
Both it and the complete check source are reproduced below for human review. Freeze should
refer to this current 45-name surface, its encodings and checks, and the unchanged ledger claim.
No freeze is recorded here; the separate proof agent starts only after human approval.

## Complete current ledger node

The statement string retains SHA-256
`61ff1d1a7e1258d7cc3e68dae5ebc8111fefb9ac4d4baab1e10b797c948366ab` (UTF-8, no added newline).

```json
{
  "id": "lem:poincare-finite-tensorization",
  "kind": "lemma",
  "status": "drafted",
  "source": "GitHub Issue #7 (sub-issue of #1), https://github.com/numina-functional-inequalities/kls-lean/issues/7; BGL (2014), Proposition 4.3.1 for the binary upper bound and its finite iteration; coordinate lifting independently supplies reverse bounds and equality; upstream prop:products at 8185e46ffb040e04fea076953e5bcaeb4157d71a; detailed source/API/route audit in research/explorations/2026-09-03-finite-tensorization-design.md",
  "statement": "All constants below refer to the unchanged Poincare.Admissible class of globally smooth real-valued L2 tests with integrable squared canonical Hilbert gradient, with normalization Var_mu(f) <= C integral ||gradient f||^2 dmu. Holds includes probability and nonnegativity of its finite real constant; constant is the ENNReal infimum over finite NNReal constants satisfying Holds. Binary case: let E and F be complete real inner product spaces with second-countable norm topologies and Borel measurable structures, and assume separately that mu on E and nu on F are probability measures. Put rho = prodMeasure mu nu = (mu.prod nu).map (WithLp.toLp 2) on WithLp 2 (E x F). For every real C, Holds rho C implies both Holds mu C and Holds nu C. Each of constant mu and constant nu is at most constant rho, and constant rho = max (constant mu) (constant nu). Probability of rho alone is not the factor normalization hypothesis. Finite case: let iota be any type with a Fintype instance, and let E : iota -> Type be a dependent family of complete real inner product spaces, each with Borel measurable structure and second-countable norm topology. Let mu i be a probability measure on E i for every i. Define piMeasure mu = (Measure.pi mu).map (WithLp.toLp 2) on PiLp 2 E, whose squared Hilbert norm is the finite sum of squared factor norms; the ordinary function-space maximum norm is not used as the Hilbert norm. For every C : iota -> NNReal, if Holds (mu i) (C i : Real) for all i, then Holds (piMeasure mu) ((Finset.univ.sup C : NNReal) : Real). For every real c and i : iota, Holds (piMeasure mu) c implies Holds (mu i) c. For each i, constant (mu i) <= constant (piMeasure mu); moreover constant (piMeasure mu) <= iSup_i constant (mu i), and hence constant (piMeasure mu) = iSup_i constant (mu i), all in ENNReal. No nonempty-index hypothesis is imposed: the empty finite supremum in NNReal and empty indexed supremum in ENNReal are zero, and the empty product satisfies Holds at zero and has optimal constant zero. A Unique index recovers constant (mu default). A probability measure on a subsingleton Hilbert space has fixed and optimal constant zero; arbitrary zero-dimensional factors are allowed, and a family consisting entirely of such factors has optimal constant zero. Any factor constant equal to infinity forces the product constant to equal infinity. Euclidean specializations use E i = EuclideanSpace Real (Fin (d i)) for arbitrary natural-number dimensions d i, with empty, singleton, mixed zero-dimensional and all-zero-dimensional families included. The supporting transport interfaces assert, under the same ambient assumptions, exact admissibility, variance and energy correspondence and invariance of Holds and constant under a real linear isometry equivalence and pushforward of a probability law. For a continuous real linear projection q between these Hilbert spaces, with isometric adjoint and a measure-preserving map between the two probability laws, admissible factor tests lift by composition with q with unchanged variance and energy; L2 and real-energy identities retain their MemLp or Admissible hypotheses. Dependent reindexing and Option splitting preserve the specified product laws and Hilbert norms. No second-moment, density, positive-dimension, finite-optimal-constant or infimum-attainment assumption is imposed. Infinite constants are handled only in ENNReal, never converted to real fixed constants. No equivalence with a Sobolev, closed Dirichlet or spectral-gap test domain and no Gaussian, LSI, Bakry-Emery, Cheeger comparison or full KLS result is claimed.",
  "lean_solution": "solutions/LemPoincareFiniteTensorization.lean",
  "checked_by": null
}
```

## Complete 45 public signatures

```text
@FunctionalInequalities.Poincare.contDiff_comp_projection.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E] [SecondCountableTopology.{u_1} E]
  [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F] [CompleteSpace.{u_2} F]
  [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F] [SecondCountableTopology.{u_2} F]
  (q : ContinuousLinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F) {f : F → ℝ},
  ContDiff.{0, u_2, 0} ℝ Top.top.{0} f → ContDiff.{0, u_1, 0} ℝ Top.top.{0} (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑q)
@FunctionalInequalities.Poincare.gradient_comp_projection.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] (q : ContinuousLinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F) {f : F → ℝ}
  {x : E},
  DifferentiableAt.{0, u_2, 0} ℝ f (q x) →
    Eq.{u_1 + 1} (gradient.{0, u_1} (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑q) x)
      ((ContinuousLinearMap.adjoint.{0, u_1, u_2} q) (gradient.{0, u_2} f (q x)))
@FunctionalInequalities.Poincare.norm_gradient_comp_projection.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] (q : ContinuousLinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F) {f : F → ℝ}
  {x : E},
  Isometry.{u_2, u_1} ⇑(ContinuousLinearMap.adjoint.{0, u_1, u_2} q) →
    DifferentiableAt.{0, u_2, 0} ℝ f (q x) →
      Eq.{1} (HPow.hPow.{0, 0, 0} (norm.{u_1} (gradient.{0, u_1} (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑q) x)) 2)
        (HPow.hPow.{0, 0, 0} (norm.{u_2} (gradient.{0, u_2} f (q x))) 2)
@FunctionalInequalities.Poincare.memLp_comp_projection.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E] [SecondCountableTopology.{u_1} E]
  [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F] [CompleteSpace.{u_2} F]
  [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F] [SecondCountableTopology.{u_2} F]
  (q : ContinuousLinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F) {ρ : MeasureTheory.Measure.{u_1} E}
  {μ : MeasureTheory.Measure.{u_2} F} [MeasureTheory.IsProbabilityMeasure.{u_1} ρ]
  [MeasureTheory.IsProbabilityMeasure.{u_2} μ],
  MeasureTheory.MeasurePreserving.{u_1, u_2} (⇑q) ρ μ →
    ∀ {f : F → ℝ},
      MeasureTheory.MemLp.{u_2, 0} f 2 μ → MeasureTheory.MemLp.{u_1, 0} (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑q) 2 ρ
@FunctionalInequalities.Poincare.integrable_gradient_comp_projection.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] (q : ContinuousLinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F)
  {ρ : MeasureTheory.Measure.{u_1} E} {μ : MeasureTheory.Measure.{u_2} F} [MeasureTheory.IsProbabilityMeasure.{u_1} ρ]
  [MeasureTheory.IsProbabilityMeasure.{u_2} μ],
  Isometry.{u_2, u_1} ⇑(ContinuousLinearMap.adjoint.{0, u_1, u_2} q) →
    MeasureTheory.MeasurePreserving.{u_1, u_2} (⇑q) ρ μ →
      ∀ {f : F → ℝ},
        FunctionalInequalities.Poincare.Admissible.{u_2} μ f →
          MeasureTheory.Integrable.{0, u_1}
            (fun x =>
              HPow.hPow.{0, 0, 0} (norm.{u_1} (gradient.{0, u_1} (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑q) x)) 2)
            ρ
@FunctionalInequalities.Poincare.Admissible.comp_projection.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] (q : ContinuousLinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F)
  {ρ : MeasureTheory.Measure.{u_1} E} {μ : MeasureTheory.Measure.{u_2} F} [MeasureTheory.IsProbabilityMeasure.{u_1} ρ]
  [MeasureTheory.IsProbabilityMeasure.{u_2} μ],
  Isometry.{u_2, u_1} ⇑(ContinuousLinearMap.adjoint.{0, u_1, u_2} q) →
    MeasureTheory.MeasurePreserving.{u_1, u_2} (⇑q) ρ μ →
      ∀ {f : F → ℝ},
        FunctionalInequalities.Poincare.Admissible.{u_2} μ f →
          FunctionalInequalities.Poincare.Admissible.{u_1} ρ (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑q)
@FunctionalInequalities.Poincare.variance_comp_projection.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E] [SecondCountableTopology.{u_1} E]
  [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F] [CompleteSpace.{u_2} F]
  [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F] [SecondCountableTopology.{u_2} F]
  (q : ContinuousLinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F) {ρ : MeasureTheory.Measure.{u_1} E}
  {μ : MeasureTheory.Measure.{u_2} F} [MeasureTheory.IsProbabilityMeasure.{u_1} ρ]
  [MeasureTheory.IsProbabilityMeasure.{u_2} μ],
  MeasureTheory.MeasurePreserving.{u_1, u_2} (⇑q) ρ μ →
    ∀ {f : F → ℝ},
      MeasureTheory.MemLp.{u_2, 0} f 2 μ →
        Eq.{1} (ProbabilityTheory.variance.{u_1} (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑q) ρ)
          (ProbabilityTheory.variance.{u_2} f μ)
@FunctionalInequalities.Poincare.energy_comp_projection.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] (q : ContinuousLinearMap.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F)
  {ρ : MeasureTheory.Measure.{u_1} E} {μ : MeasureTheory.Measure.{u_2} F} [MeasureTheory.IsProbabilityMeasure.{u_1} ρ]
  [MeasureTheory.IsProbabilityMeasure.{u_2} μ],
  Isometry.{u_2, u_1} ⇑(ContinuousLinearMap.adjoint.{0, u_1, u_2} q) →
    MeasureTheory.MeasurePreserving.{u_1, u_2} (⇑q) ρ μ →
      ∀ {f : F → ℝ},
        FunctionalInequalities.Poincare.Admissible.{u_2} μ f →
          Eq.{1} (FunctionalInequalities.Poincare.energy.{u_1} ρ (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑q))
            (FunctionalInequalities.Poincare.energy.{u_2} μ f)
@FunctionalInequalities.Poincare.admissible_map_linearIsometryEquiv_iff.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] (e : LinearIsometryEquiv.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F)
  (μ : MeasureTheory.Measure.{u_1} E) [MeasureTheory.IsProbabilityMeasure.{u_1} μ] {f : F → ℝ},
  FunctionalInequalities.Poincare.Admissible.{u_2} (MeasureTheory.Measure.map.{u_1, u_2} (⇑e) μ) f ↔
    FunctionalInequalities.Poincare.Admissible.{u_1} μ (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑e)
@FunctionalInequalities.Poincare.variance_map_linearIsometryEquiv.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E] [SecondCountableTopology.{u_1} E]
  [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F] [CompleteSpace.{u_2} F]
  [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F] [SecondCountableTopology.{u_2} F]
  (e : LinearIsometryEquiv.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F) (μ : MeasureTheory.Measure.{u_1} E)
  [MeasureTheory.IsProbabilityMeasure.{u_1} μ] {f : F → ℝ},
  MeasureTheory.MemLp.{u_2, 0} f 2 (MeasureTheory.Measure.map.{u_1, u_2} (⇑e) μ) →
    Eq.{1} (ProbabilityTheory.variance.{u_2} f (MeasureTheory.Measure.map.{u_1, u_2} (⇑e) μ))
      (ProbabilityTheory.variance.{u_1} (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑e) μ)
@FunctionalInequalities.Poincare.energy_map_linearIsometryEquiv.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] (e : LinearIsometryEquiv.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F)
  (μ : MeasureTheory.Measure.{u_1} E) [MeasureTheory.IsProbabilityMeasure.{u_1} μ] {f : F → ℝ},
  FunctionalInequalities.Poincare.Admissible.{u_2} (MeasureTheory.Measure.map.{u_1, u_2} (⇑e) μ) f →
    Eq.{1} (FunctionalInequalities.Poincare.energy.{u_2} (MeasureTheory.Measure.map.{u_1, u_2} (⇑e) μ) f)
      (FunctionalInequalities.Poincare.energy.{u_1} μ (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑e))
@FunctionalInequalities.Poincare.holds_map_linearIsometryEquiv_iff.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] (e : LinearIsometryEquiv.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F)
  (μ : MeasureTheory.Measure.{u_1} E) [MeasureTheory.IsProbabilityMeasure.{u_1} μ] {C : ℝ},
  FunctionalInequalities.Poincare.Holds.{u_2} (MeasureTheory.Measure.map.{u_1, u_2} (⇑e) μ) C ↔
    FunctionalInequalities.Poincare.Holds.{u_1} μ C
@FunctionalInequalities.Poincare.constant_map_linearIsometryEquiv.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] (e : LinearIsometryEquiv.{0, 0, u_1, u_2} (RingHom.id.{0} ℝ) E F)
  (μ : MeasureTheory.Measure.{u_1} E) [MeasureTheory.IsProbabilityMeasure.{u_1} μ],
  Eq.{1} (FunctionalInequalities.Poincare.constant.{u_2} (MeasureTheory.Measure.map.{u_1, u_2} (⇑e) μ))
    (FunctionalInequalities.Poincare.constant.{u_1} μ)
@FunctionalInequalities.Poincare.holds_zero_of_subsingleton.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E]
  [inst_1 : InnerProductSpace.{0, u_1} ℝ E] [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E]
  [BorelSpace.{u_1} E] [SecondCountableTopology.{u_1} E] [Subsingleton.{u_1 + 1} E] (μ : MeasureTheory.Measure.{u_1} E)
  [MeasureTheory.IsProbabilityMeasure.{u_1} μ], FunctionalInequalities.Poincare.Holds.{u_1} μ 0
@FunctionalInequalities.Poincare.constant_eq_zero_of_subsingleton.{u_1} : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E] [inst_2 : CompleteSpace.{u_1} E]
  [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E] [SecondCountableTopology.{u_1} E] [Subsingleton.{u_1 + 1} E]
  (μ : MeasureTheory.Measure.{u_1} E) [MeasureTheory.IsProbabilityMeasure.{u_1} μ],
  Eq.{1} (FunctionalInequalities.Poincare.constant.{u_1} μ) 0
@FunctionalInequalities.Poincare.isometry_adjoint_fstL.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F],
  Isometry.{u_1, max u_1 u_2} ⇑(ContinuousLinearMap.adjoint.{0, max u_1 u_2, u_1} (WithLp.fstL.{0, u_1, u_2} 2 ℝ E F))
@FunctionalInequalities.Poincare.isometry_adjoint_sndL.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F],
  Isometry.{u_2, max u_1 u_2} ⇑(ContinuousLinearMap.adjoint.{0, max u_1 u_2, u_2} (WithLp.sndL.{0, u_1, u_2} 2 ℝ E F))
@FunctionalInequalities.Poincare.measurePreserving_prod_fst.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E] [SecondCountableTopology.{u_1} E]
  [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F] [CompleteSpace.{u_2} F]
  [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F] [SecondCountableTopology.{u_2} F]
  {μ : MeasureTheory.Measure.{u_1} E} {ν : MeasureTheory.Measure.{u_2} F} [MeasureTheory.IsProbabilityMeasure.{u_1} μ]
  [MeasureTheory.IsProbabilityMeasure.{u_2} ν],
  MeasureTheory.MeasurePreserving.{max u_1 u_2, u_1} (⇑(WithLp.fstL.{0, u_1, u_2} 2 ℝ E F))
    (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν) μ
@FunctionalInequalities.Poincare.measurePreserving_prod_snd.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E] [SecondCountableTopology.{u_1} E]
  [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F] [CompleteSpace.{u_2} F]
  [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F] [SecondCountableTopology.{u_2} F]
  {μ : MeasureTheory.Measure.{u_1} E} {ν : MeasureTheory.Measure.{u_2} F} [MeasureTheory.IsProbabilityMeasure.{u_1} μ]
  [MeasureTheory.IsProbabilityMeasure.{u_2} ν],
  MeasureTheory.MeasurePreserving.{max u_1 u_2, u_2} (⇑(WithLp.sndL.{0, u_1, u_2} 2 ℝ E F))
    (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν) ν
@FunctionalInequalities.Poincare.Holds.of_prod_left.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] {μ : MeasureTheory.Measure.{u_1} E} {ν : MeasureTheory.Measure.{u_2} F}
  [MeasureTheory.IsProbabilityMeasure.{u_1} μ] [MeasureTheory.IsProbabilityMeasure.{u_2} ν] {C : ℝ},
  FunctionalInequalities.Poincare.Holds.{max u_2 u_1} (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν) C →
    FunctionalInequalities.Poincare.Holds.{u_1} μ C
@FunctionalInequalities.Poincare.Holds.of_prod_right.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] {μ : MeasureTheory.Measure.{u_1} E} {ν : MeasureTheory.Measure.{u_2} F}
  [MeasureTheory.IsProbabilityMeasure.{u_1} μ] [MeasureTheory.IsProbabilityMeasure.{u_2} ν] {C : ℝ},
  FunctionalInequalities.Poincare.Holds.{max u_2 u_1} (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν) C →
    FunctionalInequalities.Poincare.Holds.{u_2} ν C
@FunctionalInequalities.Poincare.constant_left_le_prod.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] {μ : MeasureTheory.Measure.{u_1} E} {ν : MeasureTheory.Measure.{u_2} F}
  [MeasureTheory.IsProbabilityMeasure.{u_1} μ] [MeasureTheory.IsProbabilityMeasure.{u_2} ν],
  LE.le.{0} (FunctionalInequalities.Poincare.constant.{u_1} μ)
    (FunctionalInequalities.Poincare.constant.{max u_2 u_1}
      (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν))
@FunctionalInequalities.Poincare.constant_right_le_prod.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] {μ : MeasureTheory.Measure.{u_1} E} {ν : MeasureTheory.Measure.{u_2} F}
  [MeasureTheory.IsProbabilityMeasure.{u_1} μ] [MeasureTheory.IsProbabilityMeasure.{u_2} ν],
  LE.le.{0} (FunctionalInequalities.Poincare.constant.{u_2} ν)
    (FunctionalInequalities.Poincare.constant.{max u_2 u_1}
      (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν))
@FunctionalInequalities.Poincare.constant_prod_eq.{u_1,
    u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
  [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
  [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
  [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
  [SecondCountableTopology.{u_2} F] {μ : MeasureTheory.Measure.{u_1} E} {ν : MeasureTheory.Measure.{u_2} F}
  [MeasureTheory.IsProbabilityMeasure.{u_1} μ] [MeasureTheory.IsProbabilityMeasure.{u_2} ν],
  Eq.{1}
    (FunctionalInequalities.Poincare.constant.{max u_2 u_1}
      (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν))
    (max.{0} (FunctionalInequalities.Poincare.constant.{u_1} μ) (FunctionalInequalities.Poincare.constant.{u_2} ν))
@FunctionalInequalities.Poincare.piMeasure.{u_1,
    u_2} : {ι : Type u_1} →
  [Fintype.{u_1} ι] →
    {E : ι → Type u_2} →
      [inst : (i : ι) → MeasurableSpace.{u_2} (E i)] →
        ((i : ι) → MeasureTheory.Measure.{u_2} (E i)) → MeasureTheory.Measure.{max u_2 u_1} (PiLp.{u_1, u_2} 2 E)
@FunctionalInequalities.Poincare.piMeasure_isProbabilityMeasure.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2} [inst_1 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  (μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)) [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)],
  MeasureTheory.IsProbabilityMeasure.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ)
@FunctionalInequalities.Poincare.adjoint_pi_proj.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  [inst_7 : DecidableEq.{u_1 + 1} ι] (i : ι) (v : E i),
  Eq.{max (u_1 + 1) (u_2 + 1)} ((ContinuousLinearMap.adjoint.{0, max u_1 u_2, u_2} (PiLp.proj.{0, u_1, u_2} 2 E i)) v)
    (PiLp.single.{u_1, u_2} 2 i v)
@FunctionalInequalities.Poincare.isometry_adjoint_pi_proj.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)] (i : ι),
  Isometry.{u_2, max u_1 u_2} ⇑(ContinuousLinearMap.adjoint.{0, max u_1 u_2, u_2} (PiLp.proj.{0, u_1, u_2} 2 E i))
@FunctionalInequalities.Poincare.measurePreserving_pi_proj.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  (μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)) [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)] (i : ι),
  MeasureTheory.MeasurePreserving.{max u_1 u_2, u_2} (⇑(PiLp.proj.{0, u_1, u_2} 2 E i))
    (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ) (μ i)
@FunctionalInequalities.Poincare.piCongrLeft.{u_1, u_2,
    u_3} : {ι : Type u_1} →
  {κ : Type u_2} →
    [inst : Fintype.{u_1} ι] →
      [inst_1 : Fintype.{u_2} κ] →
        (E : ι → Type u_3) →
          [inst_2 : (i : ι) → NormedAddCommGroup.{u_3} (E i)] →
            [inst_3 : (i : ι) → InnerProductSpace.{0, u_3} ℝ (E i)] →
              (e : Equiv.{u_2 + 1, u_1 + 1} κ ι) →
                LinearIsometryEquiv.{0, 0, max u_3 u_2, max u_3 u_1} (RingHom.id.{0} ℝ)
                  (PiLp.{u_2, u_3} 2 fun j => E (e j)) (PiLp.{u_1, u_3} 2 E)
@FunctionalInequalities.Poincare.piCongrLeft_apply.{u_1, u_2,
    u_3} : ∀ {ι : Type u_1} {κ : Type u_2} [inst : Fintype.{u_1} ι] [inst_1 : Fintype.{u_2} κ] (E : ι → Type u_3)
  [inst_2 : (i : ι) → NormedAddCommGroup.{u_3} (E i)] [inst_3 : (i : ι) → InnerProductSpace.{0, u_3} ℝ (E i)]
  (e : Equiv.{u_2 + 1, u_1 + 1} κ ι) (x : PiLp.{u_2, u_3} 2 fun j => E (e j)) (j : κ),
  Eq.{u_3 + 1} (WithLp.ofLp.{max u_1 u_3} ((FunctionalInequalities.Poincare.piCongrLeft.{u_1, u_2, u_3} E e) x) (e j))
    (WithLp.ofLp.{max u_2 u_3} x j)
@FunctionalInequalities.Poincare.map_piMeasure_piCongrLeft.{u_1, u_2,
    u_3} : ∀ {ι : Type u_1} {κ : Type u_2} [inst : Fintype.{u_1} ι] [inst_1 : Fintype.{u_2} κ] (E : ι → Type u_3)
  [inst_2 : (i : ι) → NormedAddCommGroup.{u_3} (E i)] [inst_3 : (i : ι) → InnerProductSpace.{0, u_3} ℝ (E i)]
  [∀ (i : ι), CompleteSpace.{u_3} (E i)] [inst_5 : (i : ι) → MeasurableSpace.{u_3} (E i)]
  [∀ (i : ι), BorelSpace.{u_3} (E i)] [∀ (i : ι), SecondCountableTopology.{u_3} (E i)]
  (e : Equiv.{u_2 + 1, u_1 + 1} κ ι) (μ : (i : ι) → MeasureTheory.Measure.{u_3} (E i))
  [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_3} (μ i)],
  Eq.{max (u_1 + 1) (u_3 + 1)}
    (MeasureTheory.Measure.map.{max u_2 u_3, max u_1 u_3}
      (⇑(FunctionalInequalities.Poincare.piCongrLeft.{u_1, u_2, u_3} E e))
      (FunctionalInequalities.Poincare.piMeasure.{u_2, u_3} fun j => μ (e j)))
    (FunctionalInequalities.Poincare.piMeasure.{u_1, u_3} μ)
@FunctionalInequalities.Poincare.piOptionEquivProd.{u_1,
    u_2} : {ι : Type u_1} →
  [inst : Fintype.{u_1} ι] →
    (E : Option.{u_1} ι → Type u_2) →
      [inst_1 : (i : Option.{u_1} ι) → NormedAddCommGroup.{u_2} (E i)] →
        [inst_2 : (i : Option.{u_1} ι) → InnerProductSpace.{0, u_2} ℝ (E i)] →
          LinearIsometryEquiv.{0, 0, max u_2 u_1, max u_2 u_1} (RingHom.id.{0} ℝ) (PiLp.{u_1, u_2} 2 E)
            (WithLp.{max u_2 u_1} 2
              (Prod.{u_2, max u_2 u_1} (E none.{u_1}) (PiLp.{u_1, u_2} 2 fun i => E (some.{u_1} i))))
@FunctionalInequalities.Poincare.piOptionEquivProd_apply.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] (E : Option.{u_1} ι → Type u_2)
  [inst_1 : (i : Option.{u_1} ι) → NormedAddCommGroup.{u_2} (E i)]
  [inst_2 : (i : Option.{u_1} ι) → InnerProductSpace.{0, u_2} ℝ (E i)] (x : PiLp.{u_1, u_2} 2 E),
  Eq.{max (u_1 + 1) (u_2 + 1)} ((FunctionalInequalities.Poincare.piOptionEquivProd.{u_1, u_2} E) x)
    (WithLp.toLp.{max u_1 u_2} 2
      (Prod.mk.{u_2, max u_1 u_2} (WithLp.ofLp.{max u_1 u_2} x none.{u_1})
        (WithLp.toLp.{max u_1 u_2} 2 fun i => WithLp.ofLp.{max u_1 u_2} x (some.{u_1} i))))
@FunctionalInequalities.Poincare.map_piMeasure_piOptionEquivProd.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] (E : Option.{u_1} ι → Type u_2)
  [inst_1 : (i : Option.{u_1} ι) → NormedAddCommGroup.{u_2} (E i)]
  [inst_2 : (i : Option.{u_1} ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [∀ (i : Option.{u_1} ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : Option.{u_1} ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : Option.{u_1} ι), BorelSpace.{u_2} (E i)] [∀ (i : Option.{u_1} ι), SecondCountableTopology.{u_2} (E i)]
  (μ : (i : Option.{u_1} ι) → MeasureTheory.Measure.{u_2} (E i))
  [∀ (i : Option.{u_1} ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)],
  Eq.{max (u_1 + 1) (u_2 + 1)}
    (MeasureTheory.Measure.map.{max u_1 u_2, max u_1 u_2}
      (⇑(FunctionalInequalities.Poincare.piOptionEquivProd.{u_1, u_2} E))
      (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ))
    (FunctionalInequalities.Poincare.prodMeasure.{u_2, max u_2 u_1} (μ none.{u_1})
      (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} fun i => μ (some.{u_1} i)))
@FunctionalInequalities.Poincare.Holds.pi.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  {μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)} [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)]
  {C : ι → NNReal},
  (∀ (i : ι), FunctionalInequalities.Poincare.Holds.{u_2} (μ i) ↑(C i)) →
    FunctionalInequalities.Poincare.Holds.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ)
      ↑(Finset.sup.{0, u_1} Finset.univ.{u_1} C)
@FunctionalInequalities.Poincare.Holds.of_pi.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  {μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)} [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)] {C : ℝ},
  FunctionalInequalities.Poincare.Holds.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ) C →
    ∀ (i : ι), FunctionalInequalities.Poincare.Holds.{u_2} (μ i) C
@FunctionalInequalities.Poincare.constant_le_pi.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  {μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)} [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)] (i : ι),
  LE.le.{0} (FunctionalInequalities.Poincare.constant.{u_2} (μ i))
    (FunctionalInequalities.Poincare.constant.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ))
@FunctionalInequalities.Poincare.constant_pi_le.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  {μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)} [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)],
  LE.le.{0}
    (FunctionalInequalities.Poincare.constant.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ))
    (⨆ i, FunctionalInequalities.Poincare.constant.{u_2} (μ i))
@FunctionalInequalities.Poincare.constant_pi_eq.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  {μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)} [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)],
  Eq.{1}
    (FunctionalInequalities.Poincare.constant.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ))
    (⨆ i, FunctionalInequalities.Poincare.constant.{u_2} (μ i))
@FunctionalInequalities.Poincare.holds_pi_empty.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  {μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)} [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)]
  [IsEmpty.{u_1 + 1} ι],
  FunctionalInequalities.Poincare.Holds.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ) 0
@FunctionalInequalities.Poincare.constant_pi_empty.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  {μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)} [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)]
  [IsEmpty.{u_1 + 1} ι],
  Eq.{1}
    (FunctionalInequalities.Poincare.constant.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ)) 0
@FunctionalInequalities.Poincare.constant_pi_unique.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  {μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)} [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)]
  [inst_8 : Unique.{u_1 + 1} ι],
  Eq.{1}
    (FunctionalInequalities.Poincare.constant.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ))
    (FunctionalInequalities.Poincare.constant.{u_2} (μ default.{u_1 + 1}))
@FunctionalInequalities.Poincare.constant_pi_of_subsingleton.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  {μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)} [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)]
  [∀ (i : ι), Subsingleton.{u_2 + 1} (E i)],
  Eq.{1}
    (FunctionalInequalities.Poincare.constant.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ)) 0
@FunctionalInequalities.Poincare.constant_pi_eq_top_of_factor.{u_1,
    u_2} : ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] {E : ι → Type u_2}
  [inst_1 : (i : ι) → NormedAddCommGroup.{u_2} (E i)] [inst_2 : (i : ι) → InnerProductSpace.{0, u_2} ℝ (E i)]
  [inst_3 : ∀ (i : ι), CompleteSpace.{u_2} (E i)] [inst_4 : (i : ι) → MeasurableSpace.{u_2} (E i)]
  [∀ (i : ι), BorelSpace.{u_2} (E i)] [∀ (i : ι), SecondCountableTopology.{u_2} (E i)]
  {μ : (i : ι) → MeasureTheory.Measure.{u_2} (E i)} [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_2} (μ i)] (i : ι),
  Eq.{1} (FunctionalInequalities.Poincare.constant.{u_2} (μ i)) Top.top.{0} →
    Eq.{1}
      (FunctionalInequalities.Poincare.constant.{max u_2 u_1} (FunctionalInequalities.Poincare.piMeasure.{u_1, u_2} μ))
      Top.top.{0}
```

## Complete Euclidean and boundary check source

This source follows the direct library import and the 45 public signature checks in the
solution entry point. It includes every implicit parameter and typeclass assumption in the
application binders, and all target types. `pp.funBinderTypes` also exposes the finite index
types in the printed function expressions.

```lean
/-! ## Euclidean application checks

These anonymous typed applications check that the reusable candidate API specializes to the
eight former Euclidean statements. Each expression binds every assumption explicitly, so its
printed type exposes the complete statement. They create no public declarations and certify no
new mathematics: their reusable inputs remain part of the unproved candidate.
-/

set_option pp.funBinderTypes true

open MeasureTheory
open FunctionalInequalities

-- 1. Finite fixed-constant upper bound, including an empty index type.
#check (fun {ι : Type*} [Fintype ι] {d : ι → ℕ}
    {μ : ∀ i, Measure (EuclideanSpace ℝ (Fin (d i)))}
    [∀ i, IsProbabilityMeasure (μ i)] {C : ι → NNReal}
    (h : ∀ i, Poincare.Holds (μ i) (C i : ℝ)) ↦
  (Poincare.Holds.pi h :
    Poincare.Holds (Poincare.piMeasure μ) ((Finset.univ.sup C : NNReal) : ℝ)))

-- 2. Finite extended-optimal-constant equality, with no finiteness hypothesis.
#check (fun {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (μ : ∀ i, Measure (EuclideanSpace ℝ (Fin (d i))))
    [∀ i, IsProbabilityMeasure (μ i)] ↦
  (Poincare.constant_pi_eq (μ := μ) :
    Poincare.constant (Poincare.piMeasure μ) = ⨆ i, Poincare.constant (μ i)))

-- 3. Binary reverse bounds retain both independent factor probability assumptions.
#check (fun {m n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin m))}
    {ν : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : ℝ} (h : Poincare.Holds (Poincare.prodMeasure μ ν) C) ↦
  (⟨Poincare.Holds.of_prod_left h, Poincare.Holds.of_prod_right h⟩ :
    Poincare.Holds μ C ∧ Poincare.Holds ν C))

-- 4. Binary extended-optimal-constant equality for arbitrary natural dimensions.
#check (fun {m n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] ↦
  (Poincare.constant_prod_eq (μ := μ) (ν := ν) :
    Poincare.constant (Poincare.prodMeasure μ ν) =
      max (Poincare.constant μ) (Poincare.constant ν)))

-- 5. An arbitrary empty dependent family needs no factor probability premise.
#check (fun {d : Fin 0 → ℕ}
    (μ : ∀ i, Measure (EuclideanSpace ℝ (Fin (d i)))) ↦
  letI : ∀ i : Fin 0, IsProbabilityMeasure (μ i) := fun i ↦ Fin.elim0 i
  (⟨Poincare.holds_pi_empty (μ := μ), Poincare.constant_pi_empty (μ := μ)⟩ :
    Poincare.Holds (Poincare.piMeasure μ) 0 ∧
      Poincare.constant (Poincare.piMeasure μ) = 0))

-- 6. A singleton family recovers its sole factor, including dimension zero.
#check (fun {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] ↦
  (Poincare.constant_pi_unique (μ := fun _ : Fin 1 ↦ μ) :
    Poincare.constant (Poincare.piMeasure (fun _ : Fin 1 ↦ μ)) = Poincare.constant μ))

-- 7. Every factor may be zero-dimensional; the index type may also be empty.
#check (fun {ι : Type*} [Fintype ι]
    (μ : ∀ _ : ι, Measure (EuclideanSpace ℝ (Fin 0)))
    [∀ i, IsProbabilityMeasure (μ i)] ↦
  (⟨Poincare.holds_zero_of_subsingleton (Poincare.piMeasure μ),
      Poincare.constant_pi_of_subsingleton (μ := μ)⟩ :
    Poincare.Holds (Poincare.piMeasure μ) 0 ∧
      Poincare.constant (Poincare.piMeasure μ) = 0))

-- 8. A selected zero-dimensional factor in an otherwise arbitrary dependent family.
#check (fun {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (μ : ∀ i, Measure (EuclideanSpace ℝ (Fin (d i))))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) (hi : d i = 0) ↦
  letI : Subsingleton (EuclideanSpace ℝ (Fin (d i))) :=
    hi.symm ▸ (inferInstance : Subsingleton (EuclideanSpace ℝ (Fin 0)))
  (Poincare.constant_eq_zero_of_subsingleton (μ i) : Poincare.constant (μ i) = 0))

/-! ## Additional boundary applications

These six checks retain the concrete `(0, n)`, `(n, 0)`, singleton-zero, empty, and two-zero-factor
applications. They are elaboration checks of the same candidate API.
-/

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀]
    {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] ↦
  (Poincare.constant_prod_eq (μ := μ₀) (ν := ν) :
    Poincare.constant (Poincare.prodMeasure μ₀ ν) =
      max (Poincare.constant μ₀) (Poincare.constant ν)))

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀]
    {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] ↦
  (Poincare.constant_prod_eq (μ := ν) (ν := μ₀) :
    Poincare.constant (Poincare.prodMeasure ν μ₀) =
      max (Poincare.constant ν) (Poincare.constant μ₀)))

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀] ↦
  (Poincare.constant_pi_unique (μ := fun _ : Fin 1 ↦ μ₀) :
    Poincare.constant (Poincare.piMeasure (fun _ : Fin 1 ↦ μ₀)) = Poincare.constant μ₀))

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀] ↦
  (Poincare.constant_pi_empty (μ := fun _ : Fin 0 ↦ μ₀) :
    Poincare.constant (Poincare.piMeasure (fun _ : Fin 0 ↦ μ₀)) = 0))

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀] ↦
  (Poincare.holds_pi_empty (μ := fun _ : Fin 0 ↦ μ₀) :
    Poincare.Holds (Poincare.piMeasure (fun _ : Fin 0 ↦ μ₀)) 0))

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀] ↦
  (Poincare.constant_pi_of_subsingleton (μ := fun _ : Fin 2 ↦ μ₀) :
    Poincare.constant (Poincare.piMeasure (fun _ : Fin 2 ↦ μ₀)) = 0))
```

## Issue synchronization

[Issue #7](https://github.com/numina-functional-inequalities/kls-lean/issues/7) was updated and
read back successfully with the current module paths, 45-name public surface, specialization
checks, and validation results. It explicitly retains the draft/unfrozen/unpublished status.
Its infimum wording now states that no attainment witness is assumed, without asserting a
finite-nonattainment example. No Git commit or push accompanies this Issue update.
