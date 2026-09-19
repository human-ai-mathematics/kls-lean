import FunctionalInequalities.KLS.Statement
import FunctionalInequalities.KLS.LogConcave.Borel
import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.KLS.Isoperimetry
import FunctionalInequalities.KLS.ConditionalFiber.Basic
import FunctionalInequalities.Poincare.Euclidean.RawEnergyObstruction
import FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic
import FunctionalInequalities.KLS.LogConcave.Covariance

/-!
# Literal KLS statement checks

These typed checks unfold the conjecture and test-domain contract. They are not a proof of
the conjecture. Source snapshots also cover referenced definitions: unchanged surface syntax
alone is not a semantic-stability guarantee. Mathematical scope changes remain reviewable.

The existing Dirac representative checks are in `examples/PoincareFoundation.lean`.
Gaussian variance-normalized bounds and their transfer to the intrinsic smooth relaxation are
already checked in `solutions/LemLegacyRelaxedPoincareComparison.lean`. A Gaussian bound for
`Poincare.LocalSlope.Intrinsic.constant` can now use the proved smooth/locally-Lipschitz comparison after
discharging intrinsic absolute continuity for the concrete Gaussian law. That specialization
is not included among these definition checks.
-/

noncomputable section

open MeasureTheory ProbabilityTheory FunctionalInequalities

example : KLS.Conjecture ↔
    ∃ C : NNReal, ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      KLS.LogConcave μ → MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ ≤
          (C : ENNReal) *
            ENNReal.ofReal ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖ := Iff.rfl

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E) (f : E → ℝ) :
    FunctionalInequalities.Energy.LocalSlope.Admissible μ f ↔
      LocallyLipschitz f ∧ MemLp f 2 (μ : Measure E) ∧ FunctionalInequalities.Energy.LocalSlope.energy μ f ≠ ⊤ :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

example (c : ℝ) :
    FunctionalInequalities.Energy.LocalSlope.apply (fun _ : EuclideanSpace ℝ (Fin 0) ↦ c) 0 = 0 := by simp

example (f : EuclideanSpace ℝ (Fin 0) → ℝ) (x : EuclideanSpace ℝ (Fin 0)) :
    FunctionalInequalities.Energy.LocalSlope.apply f x = 0 := FunctionalInequalities.Energy.LocalSlope.apply_eq_zero_of_subsingleton f x

example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ = 0 := FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton μ

namespace Solutions.StatementChecks

/-- Normalization: every constant has zero literature energy in every allowed coordinate space. -/
theorem constant_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] (c : ℝ) (μ : ProbabilityMeasure E) :
    FunctionalInequalities.Energy.LocalSlope.energy μ (fun _ ↦ c) = 0 := by simp [FunctionalInequalities.Energy.LocalSlope.energy]

/-- Test domain: finite-energy tests include constants, even when their energy is zero. -/
theorem constant_admissible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] (c : ℝ) (μ : ProbabilityMeasure E) :
    FunctionalInequalities.Energy.LocalSlope.Admissible μ (fun _ ↦ c) :=
  ⟨LocallyLipschitz.const c, memLp_const c, by simp [FunctionalInequalities.Energy.LocalSlope.energy]⟩

/-- Dimension convention: the covariance operator on the zero-dimensional space has norm zero. -/
theorem zero_dimension_covariance (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin 0)))‖ = 0 := by
  have h : Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin 0))) = 0 :=
    Subsingleton.elim _ _
  simp [h]

/-- Quantifier boundary: the literal KLS inequality holds in dimension zero for every finite C. -/
theorem zero_dimension_bound (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) (C : NNReal) :
    FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ ≤ (C : ENNReal) *
      ENNReal.ofReal ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin 0)))‖ := by
  rw [FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton, zero_dimension_covariance]
  simp

/-- Nonzero normalization: the ambient real identity has pointwise local slope one. -/
theorem localSlope_id (x : ℝ) : FunctionalInequalities.Energy.LocalSlope.apply id x = 1 := by
  unfold FunctionalInequalities.Energy.LocalSlope.apply
  apply le_antisymm
  · apply iInf_le_of_le (1 : ℝ)
    apply iInf_le_of_le zero_lt_one
    apply iSup_le fun y ↦ iSup_le fun _ ↦ ?_
    simpa using ENNReal.ofReal_le_ofReal (div_self_le_one (dist y x))
  · apply le_iInf fun r ↦ le_iInf fun hr ↦ ?_
    have hdist : dist (x + r / 2) x = r / 2 := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    apply le_iSup_of_le (x + r / 2)
    apply le_iSup_of_le (by rw [hdist]; linarith)
    simp [hdist, ne_of_gt (show 0 < r / 2 by positivity)]

/-- Carrier convention: ambient slope energy at a Dirac atom need not vanish for its L² class.
The literature constant instead takes the intrinsic law, removing ambient normal directions. -/
theorem ambient_dirac_identity_energy :
    FunctionalInequalities.Energy.LocalSlope.energy (Probability.ofMeasure (Measure.dirac (0 : ℝ))) id = 1 := by
  simp [FunctionalInequalities.Energy.LocalSlope.energy, localSlope_id]

end Solutions.StatementChecks

namespace Solutions.StatementChecks

/-- Infrastructure: inner regularity under the exact normed-space assumptions of the Borell draft. -/
theorem borell_innerRegular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : ProbabilityMeasure E) :
    Measure.InnerRegular (μ : Measure E) := inferInstance

/-- Infrastructure: positive ENNReal powers commute with arbitrary indexed suprema. -/
theorem borell_rpow_iSup {I : Type*} (f : I → ENNReal) (t : ℝ) (ht : 0 < t) :
    (⨆ i, f i) ^ t = ⨆ i, f i ^ t := (ENNReal.orderIsoRpow t ht).map_iSup f

/-- Infrastructure: products distribute over the two independent approximation suprema. -/
theorem borell_mul_iSup {I J : Type*} (a : I → ENNReal) (b : J → ENNReal) :
    (⨆ i, a i) * (⨆ j, b j) = ⨆ i, ⨆ j, a i * b j := by
  simp_rw [ENNReal.iSup_mul, ENNReal.mul_iSup]

/-- The isotropic fields use finite second moment and the centered operator, in every dimension. -/
theorem isotropic_fields (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) :
    KLS.Isotropic μ ↔
      MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) = 0 ∧
      Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n))) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The unique zero-dimensional probability law really satisfies isotropy. -/
theorem zero_dimension_isotropic (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    KLS.Isotropic μ := by
  refine ⟨?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hid : (id : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) = fun _ ↦ 0 :=
    funext fun _ ↦ Subsingleton.elim _ _
  rw [hid]
  exact memLp_const 0

/-- Typed definition check for the Borel predicate; this uses no draft equivalence theorem. -/
theorem borel_logconcavity_fields (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) :
    KLS.BorelLogConcave μ ↔
      ∀ (B₀ B₁ : Set (EuclideanSpace ℝ (Fin n))), MeasurableSet B₀ → MeasurableSet B₁ →
        ∀ t : ℝ, 0 < t → t < 1 →
          (μ : Measure (EuclideanSpace ℝ (Fin n))) B₀ ^ t *
            (μ : Measure (EuclideanSpace ℝ (Fin n))) B₁ ^ (1 - t) ≤
          KLS.innerMeasure (μ : Measure (EuclideanSpace ℝ (Fin n)))
            {z | ∃ x ∈ B₀, ∃ y ∈ B₁, z = t • x + (1 - t) • y} := Iff.rfl

/-- The inner-measure definition quantifies over compact subsets even in dimension zero. -/
theorem zero_dimension_innerMeasure (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)))
    (B : Set (EuclideanSpace ℝ (Fin 0))) :
    KLS.innerMeasure (μ : Measure (EuclideanSpace ℝ (Fin 0))) B =
      ⨆ (K : Set (EuclideanSpace ℝ (Fin 0))) (_ : K ⊆ B) (_ : IsCompact K),
        (μ : Measure (EuclideanSpace ℝ (Fin 0))) K := rfl

/-- Inversion remains in ENNReal, including both endpoints. -/
theorem isoperimetric_inverse (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) :
    KLS.Isoperimetry.inverseScale μ = (KLS.Isoperimetry.constant μ)⁻¹ := rfl

/-- The zero-dimensional affine carrier gives infinity and inverse scale zero. -/
theorem zero_dimension_isoperimetry (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    KLS.Isoperimetry.constant μ = ⊤ ∧ KLS.Isoperimetry.inverseScale μ = 0 := by
  have hdim : Module.finrank ℝ (Probability.affineSupport μ).direction = 0 :=
    Module.finrank_zero_of_subsingleton
  simp [KLS.Isoperimetry.inverseScale, KLS.Isoperimetry.constant, hdim]

/-- A Dirac law in a positive-dimensional ambient space still has zero-dimensional carrier. -/
theorem ambient_dirac_isoperimetry :
    KLS.Isoperimetry.constant (Probability.ofMeasure (Measure.dirac (0 : ℝ))) = ⊤ ∧
      KLS.Isoperimetry.inverseScale (Probability.ofMeasure (Measure.dirac (0 : ℝ))) = 0 := by
  let μ := Probability.ofMeasure (Measure.dirac (0 : ℝ))
  have hA : Probability.affineSupport μ ≤ affineSpan ℝ ({0} : Set ℝ) := by
    apply Probability.affineSupport_le_of_ae_mem μ _ (AffineSubspace.closed_of_finiteDimensional _)
    change ∀ᵐ x ∂(Measure.dirac (0 : ℝ)), x ∈ affineSpan ℝ ({0} : Set ℝ)
    simp
  have hdir : (Probability.affineSupport μ).direction = ⊥ := by
    apply bot_unique
    simpa only [direction_affineSpan, vectorSpan_singleton] using
      AffineSubspace.direction_le hA
  have hdim : Module.finrank ℝ (Probability.affineSupport μ).direction = 0 := by
    rw [hdir]
    simp
  change KLS.Isoperimetry.constant μ = ⊤ ∧ KLS.Isoperimetry.inverseScale μ = 0
  simp [KLS.Isoperimetry.inverseScale, KLS.Isoperimetry.constant, hdim]

/-- The boundary-content filter approaches zero through positive radii in every dimension. -/
theorem isoperimetric_boundary_fields (n : ℕ)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (B : Set (Probability.affineSupport μ)) :
    KLS.Isoperimetry.boundaryContent μ B =
      Filter.liminf (fun r : ℝ ↦
        (((KLS.Isoperimetry.carrierMeasure μ : Measure (Probability.affineSupport μ))
          (Metric.thickening r B)) -
          (KLS.Isoperimetry.carrierMeasure μ : Measure (Probability.affineSupport μ)) B) /
            ENNReal.ofReal r) (nhdsWithin 0 (Set.Ioi 0)) := rfl

/-- The frame contract explicitly excludes zero dimension. No zero-dimensional frame is built. -/
theorem conditional_zero_dimension_excluded
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)))
    (ρ : ProbabilityMeasure (KLS.ConditionalFiber.Direction (EuclideanSpace ℝ (Fin 0)))) :
    ¬ KLS.ConditionalFiber.Admissible μ ρ := by
  intro h
  simpa using h.positive_dimension

/-- The maximal conditional domain is exactly finite extended energy, in any positive dimension. -/
theorem conditional_domain_fields (n : ℕ)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin (n + 1))))
    (ρ : ProbabilityMeasure (KLS.ConditionalFiber.Direction (EuclideanSpace ℝ (Fin (n + 1)))))
    (f : Lp ℝ 2 (μ : Measure (EuclideanSpace ℝ (Fin (n + 1))))) :
    f ∈ KLS.ConditionalFiber.domain μ ρ ↔ KLS.ConditionalFiber.form μ ρ f ≠ ⊤ := Iff.rfl

/-- The affine constant is the generic `L²` optimizer of the intrinsic law at the sequential
relaxation of the covariance pre-energy, in every dimension. -/
theorem affine_constant_unfold (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) :
    FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant μ =
      Poincare.L2Energy.constant (Probability.intrinsicMeasure μ)
        ((FunctionalInequalities.Energy.CovarianceGradient.preEnergy
          (Probability.intrinsicMeasure μ)).sequentialRelaxation) := rfl

/-- The affine test class is exactly: globally Lipschitz, `L²`, and integrable covariance-weighted
squared gradient. No differentiability premise is part of the structure. -/
theorem affine_test_fields (n : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∃ f : FunctionalInequalities.Energy.CovarianceGradient.Test ν, f.toFun = g) ↔
      (∃ K : NNReal, LipschitzWith K g) ∧ MemLp g 2 (ν : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (FunctionalInequalities.Energy.CovarianceGradient.density ν g)
          (ν : Measure (EuclideanSpace ℝ (Fin n))) :=
  ⟨fun ⟨f, hf⟩ ↦ hf ▸ ⟨f.lipschitz, f.memLp_two, f.integrable⟩,
    fun h ↦ ⟨⟨g, h.1, h.2.1, h.2.2⟩, rfl⟩⟩

/-- The finite affine energy is the real integral `∫ ⟪Σ ∇g, ∇g⟫ dν` with `Σ` the covariance
operator of `ν`; no factor of one half is introduced. -/
theorem affine_energy_integral (n : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (f : FunctionalInequalities.Energy.CovarianceGradient.Test ν) :
    (f.energy : ℝ) =
      ∫ x, inner ℝ (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))
        (gradient f.toFun x)) (gradient f.toFun x) ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) :=
  rfl

/-- Dimension zero: the affine covariance Poincaré constant is zero. -/
theorem zero_dimension_affine_constant (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant μ = 0 :=
  FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_eq_zero_of_subsingleton μ

/-- A Dirac law in a positive-dimensional ambient space has zero-dimensional affine support and
therefore affine constant zero; the ambient dimension is irrelevant. -/
theorem ambient_dirac_affine_constant :
    FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant (Probability.ofMeasure (Measure.dirac (0 : ℝ))) = 0 := by
  let μ := Probability.ofMeasure (Measure.dirac (0 : ℝ))
  have hA : Probability.affineSupport μ ≤ affineSpan ℝ ({0} : Set ℝ) := by
    apply Probability.affineSupport_le_of_ae_mem μ _ (AffineSubspace.closed_of_finiteDimensional _)
    change ∀ᵐ x ∂(Measure.dirac (0 : ℝ)), x ∈ affineSpan ℝ ({0} : Set ℝ)
    simp
  have hdir : (Probability.affineSupport μ).direction = ⊥ := by
    apply bot_unique
    simpa only [direction_affineSpan, vectorSpan_singleton] using
      AffineSubspace.direction_le hA
  exact FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_eq_zero_of_direction_eq_bot μ hdir

/-- All excluded fibers contribute zero before extended division. -/
theorem conditional_bad_fiber (n : ℕ)
    (κ : Kernel (KLS.ConditionalFiber.Direction (EuclideanSpace ℝ (Fin (n + 1))) ×
      EuclideanSpace ℝ (Fin (n + 1))) ℝ)
    (b : KLS.ConditionalFiber.Direction (EuclideanSpace ℝ (Fin (n + 1))) ×
      EuclideanSpace ℝ (Fin (n + 1))) (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (h : ¬ FunctionalInequalities.KLS.ConditionalFiber.Nondegenerate κ b) : KLS.ConditionalFiber.energyAt κ b f = 0 := by
  simp [KLS.ConditionalFiber.energyAt, h]

end Solutions.StatementChecks

/-- info: 'Solutions.StatementChecks.constant_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.constant_energy

/-- info: 'Solutions.StatementChecks.constant_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.constant_admissible

/-- info: 'Solutions.StatementChecks.zero_dimension_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.zero_dimension_covariance

/-- info: 'Solutions.StatementChecks.zero_dimension_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.zero_dimension_bound

/-- info: 'Solutions.StatementChecks.localSlope_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.localSlope_id

/-- info: 'Solutions.StatementChecks.ambient_dirac_identity_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.ambient_dirac_identity_energy

/-- info: 'Solutions.StatementChecks.borell_innerRegular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.borell_innerRegular

/-- info: 'Solutions.StatementChecks.borell_rpow_iSup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.borell_rpow_iSup

/-- info: 'Solutions.StatementChecks.borell_mul_iSup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.borell_mul_iSup

/-- info: 'Solutions.StatementChecks.isotropic_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.isotropic_fields

/-- info: 'Solutions.StatementChecks.zero_dimension_isotropic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.zero_dimension_isotropic

/-- info: 'Solutions.StatementChecks.borel_logconcavity_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.borel_logconcavity_fields

/-- info: 'Solutions.StatementChecks.zero_dimension_innerMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.zero_dimension_innerMeasure

/-- info: 'Solutions.StatementChecks.isoperimetric_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.isoperimetric_inverse

/-- info: 'Solutions.StatementChecks.zero_dimension_isoperimetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.zero_dimension_isoperimetry

/-- info: 'Solutions.StatementChecks.ambient_dirac_isoperimetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.ambient_dirac_isoperimetry

/-- info: 'Solutions.StatementChecks.isoperimetric_boundary_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.isoperimetric_boundary_fields

/-- info: 'Solutions.StatementChecks.conditional_zero_dimension_excluded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.conditional_zero_dimension_excluded

/-- info: 'Solutions.StatementChecks.conditional_domain_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.conditional_domain_fields

/-- info: 'Solutions.StatementChecks.conditional_bad_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.conditional_bad_fiber

/-- info: 'Solutions.StatementChecks.affine_constant_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.affine_constant_unfold

/-- info: 'Solutions.StatementChecks.affine_test_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.affine_test_fields

/-- info: 'Solutions.StatementChecks.affine_energy_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.affine_energy_integral

/-- info: 'Solutions.StatementChecks.zero_dimension_affine_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.zero_dimension_affine_constant

/-- info: 'Solutions.StatementChecks.ambient_dirac_affine_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.StatementChecks.ambient_dirac_affine_constant

/-- info: 'FunctionalInequalities.KLS.LogConcave.intrinsic_memLp_id_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsic_memLp_id_two

/-- info: 'FunctionalInequalities.KLS.LogConcave.intrinsic_ae_hasGradientAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsic_ae_hasGradientAt

/-- info: 'FunctionalInequalities.KLS.LogConcave.intrinsic_gradient_ae_eq_of_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsic_gradient_ae_eq_of_ae_eq

/-- info: 'FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_energy_eq_of_toL2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_energy_eq_of_toL2_eq

/-- info: 'FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_eq_zero_of_direction_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic.constant_eq_zero_of_direction_eq_bot

/-- info: 'FunctionalInequalities.KLS.ConditionalFiber.lintegral_baseLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.lintegral_baseLaw

/-- info: 'FunctionalInequalities.KLS.ConditionalFiber.ae_memLp_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.ae_memLp_id

/-- info: 'FunctionalInequalities.KLS.ConditionalFiber.measurable_energyAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.measurable_energyAt

/-- info: 'FunctionalInequalities.KLS.ConditionalFiber.energyWithKernel_eq_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.energyWithKernel_eq_energy

/-- info: 'FunctionalInequalities.KLS.ConditionalFiber.energy_congr_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.energy_congr_ae

/-- info: 'FunctionalInequalities.KLS.ConditionalFiber.form_toLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.ConditionalFiber.form_toLp
