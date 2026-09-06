import FunctionalInequalities.KLS.Statement

/-!
# Literal KLS statement checks

These typed checks unfold the conjecture and test-domain contract. They are not a proof of
the conjecture. Source snapshots also cover referenced definitions: unchanged surface syntax
alone is not a semantic-stability guarantee. Mathematical scope changes remain reviewable.

The existing Dirac representative checks are in `examples/PoincareFoundation.lean`.
Gaussian variance-normalized bounds and their transfer to the intrinsic smooth relaxation are
already checked in `solutions/LemLegacyRelaxedPoincareComparison.lean`. A Gaussian bound for
`KLS.literatureConstant` can now use the proved smooth/locally-Lipschitz comparison after
discharging intrinsic absolute continuity for the concrete Gaussian law. That specialization
is not included among these definition checks.
-/

noncomputable section

open MeasureTheory ProbabilityTheory FunctionalInequalities

example : KLS.Conjecture ↔
    ∃ C : NNReal, ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      KLS.LogConcave μ → MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
        KLS.literatureConstant μ ≤
          (C : ENNReal) *
            ENNReal.ofReal ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖ := Iff.rfl

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E) (f : E → ℝ) :
    KLS.LiteratureAdmissible μ f ↔
      LocallyLipschitz f ∧ MemLp f 2 (μ : Measure E) ∧ KLS.literatureEnergy μ f ≠ ⊤ :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

example (c : ℝ) :
    KLS.localSlope (fun _ : EuclideanSpace ℝ (Fin 0) ↦ c) 0 = 0 := by simp

example (f : EuclideanSpace ℝ (Fin 0) → ℝ) (x : EuclideanSpace ℝ (Fin 0)) :
    KLS.localSlope f x = 0 := KLS.localSlope_eq_zero_of_subsingleton f x

example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    KLS.literatureConstant μ = 0 := KLS.literatureConstant_eq_zero_of_subsingleton μ

namespace Solutions.StatementChecks

/-- Normalization: every constant has zero literature energy in every allowed coordinate space. -/
theorem constant_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] (c : ℝ) (μ : ProbabilityMeasure E) :
    KLS.literatureEnergy μ (fun _ ↦ c) = 0 := by simp [KLS.literatureEnergy]

/-- Test domain: finite-energy tests include constants, even when their energy is zero. -/
theorem constant_admissible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] (c : ℝ) (μ : ProbabilityMeasure E) :
    KLS.LiteratureAdmissible μ (fun _ ↦ c) :=
  ⟨LocallyLipschitz.const c, memLp_const c, by simp [KLS.literatureEnergy]⟩

/-- Dimension convention: the covariance operator on the zero-dimensional space has norm zero. -/
theorem zero_dimension_covariance (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin 0)))‖ = 0 := by
  have h : Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin 0))) = 0 :=
    Subsingleton.elim _ _
  simp [h]

/-- Quantifier boundary: the literal KLS inequality holds in dimension zero for every finite C. -/
theorem zero_dimension_bound (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) (C : NNReal) :
    KLS.literatureConstant μ ≤ (C : ENNReal) *
      ENNReal.ofReal ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin 0)))‖ := by
  rw [KLS.literatureConstant_eq_zero_of_subsingleton, zero_dimension_covariance]
  simp

/-- Nonzero normalization: the ambient real identity has pointwise local slope one. -/
theorem localSlope_id (x : ℝ) : KLS.localSlope id x = 1 := by
  unfold KLS.localSlope
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
    KLS.literatureEnergy (Probability.ofMeasure (Measure.dirac (0 : ℝ))) id = 1 := by
  simp [KLS.literatureEnergy, localSlope_id]

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
