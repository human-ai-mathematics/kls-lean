import FunctionalInequalities.Analysis.Cutoff.Translation
import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
import FunctionalInequalities.Analysis.Convex.HessianIncrement
import FunctionalInequalities.Analysis.Convex.HessianRegularity
import FunctionalInequalities.Analysis.WeakDerivative.Basic
import FunctionalInequalities.Analysis.WeakDerivative.Mollification
import FunctionalInequalities.Analysis.WeakDerivative.Approximation
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff RealInnerProductSpace
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
namespace WeakHessianRegularityAudit.Geometry

/-- Actual consumer orientation: a produced compact C2 test with an integrable
weight and one domination estimate uniform over all small translates. -/
theorem exists_integrable_weighted_majorant {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ} (hu : Continuous u)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ η : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 2 η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧
      Integrable (fun x => η x * Real.exp (-u x)) ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x, (χ (x + t • v)) ^ 2 ≤ η x * Real.exp (-u x) := by
  obtain ⟨η, hη, hηc, hη0, hdom⟩ :=
    exists_smooth_compact_translate_majorant hu hχ hχc v
  have hη2 : ContDiff ℝ 2 η := (contDiff_infty.mp hη) 2
  refine ⟨η, hη2, hηc, hη0,
    (hη2.continuous.mul (Real.continuous_exp.comp hu.neg)).integrable_of_hasCompactSupport
      hηc.mul_right, ?_⟩
  intro t ht x
  have hb := mul_le_mul_of_nonneg_right (hdom t ht x) (Real.exp_pos (-u x)).le
  have he : Real.exp (u x) * Real.exp (-u x) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa only [mul_assoc, he, mul_one] using hb

/-- Produce the SAME genuine cutoff for all small translates, then consume the
original canonical N11b estimate at every shift; the energy is not a premise. -/
theorem exists_uniform_original_energy_tests {n : ℕ} {u V χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧ Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ (x h : EuclideanSpace ℝ (Fin n)),
      u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ η : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 2 η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧
      (∀ t : ℝ, |t| ≤ 1 → ∀ x, (χ (x + t • v)) ^ 2 ≤ η x * Real.exp (-u x)) ∧
      ∀ h : EuclideanSpace ℝ (Fin n),
        Integrable (fun x => η x * ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
          ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) * Real.exp (-u x)) ∧
        (∫ x, η x * ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
          ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) * Real.exp (-u x)) ≤
        2 * K ^ 2 * (D * ‖h‖ ^ 2) * ∫ x,
          |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
            fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x) := by
  obtain ⟨η, hη, hηc, hη0, _, hdom⟩ :=
    exists_integrable_weighted_majorant hu.continuous hχ.continuous hχc v
  refine ⟨η, hη, hηc, hη0, hdom, ?_⟩
  intro h
  exact ⟨integrable_hessian_increment_energy hu.continuous hG hη.continuous hηc h,
    integral_mul_hessian_increment_le hu hconv hG hV hVc hF hK hdata hη hηc hη0 h
      (fun x => hw x h)⟩

end WeakHessianRegularityAudit.Geometry


noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
namespace WeakHessianRegularityAudit.EntryLp

/-- Actual canonical criterion consumption. The difference bound is explicitly
an undischarged consumer input here, to be produced by the next energy adapter. -/
theorem consume_global_criterion {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (v : EuclideanSpace ℝ (Fin n)) {C : ℝ}
    (hdiff : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      (∫ x, (χ (x + t • v) * hessianMatrix u (x + t • v) i j -
        χ x * hessianMatrix u x i j) ^ 2) ≤ C * t ^ 2) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HasWeakDerivAlong (fun x => χ x * hessianMatrix u x i j) g v ∧
      MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact exists_hasWeakDerivAlong_of_sq_difference_le
    (memLp_cutoff_mul_hessianMatrix_entry hG i j hχ.continuous hχc) v hdiff

/-- The actual canonical gluing boundary consumes both new L2 interfaces.
This is conditional on cutoff difference bounds; it is not original N11d. -/
theorem consume_cutoff_gluing {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    (v : EuclideanSpace ℝ (Fin n))
    (hdiff : ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 χ → HasCompactSupport χ → ∃ C : ℝ,
        ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
          (∫ x, (χ (x + t • v) * hessianMatrix u (x + t • v) i j -
            χ x * hessianMatrix u x i j) ^ 2) ≤ C * t ^ 2) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) g v ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  apply exists_hasWeakDerivAlong_of_forall_cutoff
    (fun S hS => memLp_hessianMatrix_entry_of_isCompact hG i j hS) v
  intro χ hχ hχc
  obtain ⟨C, hC⟩ := hdiff χ hχ hχc
  exact consume_global_criterion hG i j hχ hχc v hC

end WeakHessianRegularityAudit.EntryLp


noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff RealInnerProductSpace
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
namespace WeakHessianRegularityAudit.DifferenceEnergy

/-- Actual original PDE data now produce the cutoff weak derivative; the
difference bound, L2 membership and envelope are all conclusions of supports. -/
theorem consume_cutoff_criterion {n : ℕ}
    {u V χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (i j : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HasWeakDerivAlong (fun x => χ x * hessianMatrix u x i j) g v ∧
      MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨C, _hC0, hC⟩ := exists_hessian_cutoff_sq_difference_bound
    hu hconv hG hV hVc hF hK hdata hw hχ hχc i j v
  exact exists_hasWeakDerivAlong_of_sq_difference_le
    (memLp_cutoff_mul_hessianMatrix_entry hG i j hχ.continuous hχc) v hC

/-- Produce actual entry-wise weak derivatives from original N11d hypotheses
using canonical cutoff gluing. No desired difference/tensor/H1 premise. -/
theorem consume_original_gluing {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2)
    (i j : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) g v ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  apply exists_hasWeakDerivAlong_of_forall_cutoff
    (fun S hS => memLp_hessianMatrix_entry_of_isCompact hG i j hS) v
  intro χ hχ hχc
  exact consume_cutoff_criterion hu hconv hG hV hVc hF hK hdata hw hχ hχc i j v

end WeakHessianRegularityAudit.DifferenceEnergy


noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
namespace WeakHessianRegularityAudit.Tensor

/-- Canonical N11e now consumes an actual produced tensor, rather than taking
the desired third tensor as a hypothesis. No promotion from C1 to C2. -/
theorem produced_symmetric_locally_l2_tensor {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    ∃ T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ,
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => T x k i j) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ k i j, T x k i j = T x i k j ∧ T x k i j = T x k j i) := by
  obtain ⟨T, hT⟩ := exists_weak_third_derivative hu hconv hG hV hVc hF hK hdata hw
  exact ⟨T, hT, ae_weak_third_derivative_symm hu hG (fun k i j => (hT k i j).1)⟩

/-- The produced derivatives supply locally integrable test densities and
the actual weak integration identity, ready for subsequent chain-rule work. -/
theorem produced_weak_testing_identity {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    ∃ T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ,
      ∀ k i j, LocallyIntegrable (fun x => T x k i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
          (∫ x, hessianMatrix u x i j * fderiv ℝ ψ x
            (EuclideanSpace.basisFun (Fin n) ℝ k)) =
            -∫ x, T x k i j * ψ x := by
  obtain ⟨T, hT⟩ := exists_weak_third_derivative hu hconv hG hV hVc hF hK hdata hw
  exact ⟨T, fun k i j => ⟨(hT k i j).1.2.1, (hT k i j).1.2.2⟩⟩

end WeakHessianRegularityAudit.Tensor

#print axioms FunctionalInequalities.Analysis.exists_smooth_compact_translate_majorant
#print axioms FunctionalInequalities.Probability.Stein.memLp_hessianMatrix_entry_of_isCompact
#print axioms FunctionalInequalities.Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry
#print axioms FunctionalInequalities.Analysis.exists_hessian_cutoff_sq_difference_bound
#print axioms FunctionalInequalities.Analysis.exists_weak_third_derivative
#print axioms WeakHessianRegularityAudit.Geometry.exists_integrable_weighted_majorant
#print axioms WeakHessianRegularityAudit.Geometry.exists_uniform_original_energy_tests
#print axioms WeakHessianRegularityAudit.EntryLp.consume_global_criterion
#print axioms WeakHessianRegularityAudit.EntryLp.consume_cutoff_gluing
#print axioms WeakHessianRegularityAudit.DifferenceEnergy.consume_cutoff_criterion
#print axioms WeakHessianRegularityAudit.DifferenceEnergy.consume_original_gluing
#print axioms WeakHessianRegularityAudit.Tensor.produced_symmetric_locally_l2_tensor
#print axioms WeakHessianRegularityAudit.Tensor.produced_weak_testing_identity
