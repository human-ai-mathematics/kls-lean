# Finite Poincaré tensorization statement freeze

**Approval date:** 2026-09-03 (Asia/Shanghai).

**Human reviewer/approver:** the repository user in Codex task
`01a065af-7638-70e0-98d1-dc77718ee3e9`. After the candidate implementation, source review,
semantic audit, directory cleanup, and complete review package were presented, the user said:
“I think it is ready; make one final check that the semantics align, then we can move to the next step”. The requested
final review passed in two independent read-only audits. This instruction ratifies the reviewed
candidate at acceptance time. It does not backdate a freeze to the earlier skeleton or proof stage.

**Recorder and technical reviewer:** Codex, with independent reviews of
geometry/admissibility and variance/tensorization.

**Repository baseline:** `4801ca958778ae02cc0d81fc7ec805a4e96a894c` on `main`.
The complete finite-tensorization candidate was present as uncommitted working-tree changes at
this baseline. The baseline commit itself contains only the already accepted work through Issue
#6. Publication evidence for the new accepted commit belongs in Issue #7 and the acceptance
record, not in this statement freeze.

## Approved mathematical scope

The approved claim is exactly ledger node `lem:poincare-finite-tensorization`. It preserves the
existing `Poincare.Admissible`, `energy`, `Holds`, and `constant` definitions: globally smooth
real-valued L² tests with integrable squared canonical Hilbert gradient, normalized by
`Var(f) ≤ C ∫ ‖gradient f‖²`. `constant` remains the `ENNReal` infimum over finite `NNReal`
valid constants.

The binary part assumes the two factor measures are probabilities separately. It recovers each
factor's fixed inequality from the Hilbert-product inequality and proves both optimal lower
bounds and exact maximum equality. The finite dependent part allows every `Fintype`, including
the empty type, and proves the fixed `NNReal` supremum bound, coordinate recovery, both optimal
bounds, and the `ENNReal` indexed-supremum equality. Empty, singleton, subsingleton, arbitrary
zero-dimensional, and infinite-factor-constant cases are included.

The support interfaces preserve admissibility, variance, energy, `Holds`, and optimal constants
under the stated measure-preserving projections and linear isometry equivalences. Dependent
reindexing and the Option split preserve both the Hilbert norm and the product law. No moment,
density, positive-dimension, finite-optimal-constant, infimum-attainment, Sobolev/Dirichlet,
spectral-gap, Gaussian, LSI, Cheeger, or full KLS claim is approved here.

## Frozen encodings

The binary and finite carriers and laws are:

```lean
prodMeasure μ ν := (μ.prod ν).map (WithLp.toLp 2)
-- carrier: WithLp 2 (E × F)

piMeasure μ := (Measure.pi μ).map (WithLp.toLp 2)
-- carrier: PiLp 2 E
```

Their norms are the Hilbert sum-of-squares norms. The ordinary product and function-space maximum
norms are not substituted for these Hilbert norms. `piCongrLeft E e` maps a source coordinate
`j` to target coordinate `e j`; `piOptionEquivProd E` splits an Option-indexed family in the
order `(none, tail)`:

```lean
piCongrLeft E e x (e j) = x j
piOptionEquivProd E x = WithLp.toLp 2 (x none, WithLp.toLp 2 (fun i ↦ x (some i)))
```

The following accepted source-file SHA-256 values pin the existing semantic definitions and
encoding implementations. Proof refactoring that preserves the public contract still requires
the usual review; a change to the displayed encodings requires human resolution.

```text
Poincare/Basic.lean:                  7e82ab8da1b07541b94a870e583deb1a95bf73c7882ce4eac27513fe448242e0
Poincare/Product/Geometry.lean:       07feec16ac98cd33425b79fb56861bd5725bb0ece6c37711ff59035cb7b25dfc
Poincare/FiniteProduct/Geometry.lean: aff2119f2b5629c7a882b5787335cd8acc16500a5cd51d0044042ce3b20d59bb
```

## Complete approved public declaration types

The 45 blocks below are the exact output of `#check @...` under pinned Lean/Mathlib v4.33.0.
Implicit parameters and typeclass arguments are exposed. SHA-256 of the UTF-8 output, including
its final newline, is `1dbb986f5764f752adb516ea108ff771cd6058021ade292da727b451f541ce66`.
The eight fully quantified Euclidean application families and six concrete boundary checks in
`solutions/LemPoincareFiniteTensorization.lean` are also part of the approved application surface;
they add no duplicate declarations.

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

## Complete approved ledger statement

The node's `statement` field is frozen verbatim. Its UTF-8 SHA-256, without an extra newline, is
`61ff1d1a7e1258d7cc3e68dae5ebc8111fefb9ac4d4baab1e10b797c948366ab`.
Lifecycle and source metadata are outside this mathematical statement snapshot.

```json
{
  "id": "lem:poincare-finite-tensorization",
  "statement": "All constants below refer to the unchanged Poincare.Admissible class of globally smooth real-valued L2 tests with integrable squared canonical Hilbert gradient, with normalization Var_mu(f) <= C integral ||gradient f||^2 dmu. Holds includes probability and nonnegativity of its finite real constant; constant is the ENNReal infimum over finite NNReal constants satisfying Holds. Binary case: let E and F be complete real inner product spaces with second-countable norm topologies and Borel measurable structures, and assume separately that mu on E and nu on F are probability measures. Put rho = prodMeasure mu nu = (mu.prod nu).map (WithLp.toLp 2) on WithLp 2 (E x F). For every real C, Holds rho C implies both Holds mu C and Holds nu C. Each of constant mu and constant nu is at most constant rho, and constant rho = max (constant mu) (constant nu). Probability of rho alone is not the factor normalization hypothesis. Finite case: let iota be any type with a Fintype instance, and let E : iota -> Type be a dependent family of complete real inner product spaces, each with Borel measurable structure and second-countable norm topology. Let mu i be a probability measure on E i for every i. Define piMeasure mu = (Measure.pi mu).map (WithLp.toLp 2) on PiLp 2 E, whose squared Hilbert norm is the finite sum of squared factor norms; the ordinary function-space maximum norm is not used as the Hilbert norm. For every C : iota -> NNReal, if Holds (mu i) (C i : Real) for all i, then Holds (piMeasure mu) ((Finset.univ.sup C : NNReal) : Real). For every real c and i : iota, Holds (piMeasure mu) c implies Holds (mu i) c. For each i, constant (mu i) <= constant (piMeasure mu); moreover constant (piMeasure mu) <= iSup_i constant (mu i), and hence constant (piMeasure mu) = iSup_i constant (mu i), all in ENNReal. No nonempty-index hypothesis is imposed: the empty finite supremum in NNReal and empty indexed supremum in ENNReal are zero, and the empty product satisfies Holds at zero and has optimal constant zero. A Unique index recovers constant (mu default). A probability measure on a subsingleton Hilbert space has fixed and optimal constant zero; arbitrary zero-dimensional factors are allowed, and a family consisting entirely of such factors has optimal constant zero. Any factor constant equal to infinity forces the product constant to equal infinity. Euclidean specializations use E i = EuclideanSpace Real (Fin (d i)) for arbitrary natural-number dimensions d i, with empty, singleton, mixed zero-dimensional and all-zero-dimensional families included. The supporting transport interfaces assert, under the same ambient assumptions, exact admissibility, variance and energy correspondence and invariance of Holds and constant under a real linear isometry equivalence and pushforward of a probability law. For a continuous real linear projection q between these Hilbert spaces, with isometric adjoint and a measure-preserving map between the two probability laws, admissible factor tests lift by composition with q with unchanged variance and energy; L2 and real-energy identities retain their MemLp or Admissible hypotheses. Dependent reindexing and Option splitting preserve the specified product laws and Hilbert norms. No second-moment, density, positive-dimension, finite-optimal-constant or infimum-attainment assumption is imposed. Infinite constants are handled only in ENNReal, never converted to real fixed constants. No equivalence with a Sobolev, closed Dirichlet or spectral-gap test domain and no Gaussian, LSI, Bakry-Emery, Cheeger comparison or full KLS result is claimed."
}
```

## Preservation and acceptance rule

The proof implementation already existed when this approval was recorded. Acceptance therefore
compares the current declaration-type output and ledger statement byte for byte with this record,
adds one named node certificate without altering the approved mathematical library, audits its
transitive axioms, and runs the ledger, regression, and default Lean checks. Only after those
checks pass may the ledger become `proved` / `checked_by: lean`. The final published commit must
pass its own GitHub Actions run; an earlier run is not publication evidence for Issue #7.
