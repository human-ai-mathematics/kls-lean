module

public import FunctionalInequalities.Analysis.MetricBV.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Strict clients for finite test cost without finite total mass. The general client uses
exactly finite mass on bounded Borel sets, with no properness assumption. On proper spaces
Mathlib's finite-on-compacts condition suffices. Real Lebesgue measure supplies a genuine
infinite-total-mass instance. These estimates do not prove the ADMG relaxation endpoint. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MetricBVSupportCostAudit
open FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The paper's bounded-Borel-set condition suffices on every metric space. -/
theorem finiteOnBounded (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s ≠ ⊤)
    (f : Test X) : cost ν f < ⊤ :=
  (cost_ne_top_of_support_measure ν f
    (hν _ f.boundedSupport.closure isClosed_closure.measurableSet)).lt_top

/-- Properness is explicitly required for the finite-on-compacts specialization. -/
theorem properFiniteOnCompacts [ProperSpace X] (ν : Measure X)
    [IsFiniteMeasureOnCompacts ν] (f : Test X) : cost ν f < ⊤ :=
  (cost_ne_top_of_support_measure ν f f.boundedSupport.closure.measure_lt_top.ne).lt_top

/-- A concrete infinite-total-mass measure: every bounded-support test still has finite cost. -/
theorem realVolume (f : Test ℝ) :
    (volume : Measure ℝ) univ = ⊤ ∧ cost (volume : Measure ℝ) f < ⊤ :=
  ⟨by simp, properFiniteOnCompacts volume f⟩

/-- The bound keeps closure mass, including atoms on the boundary of function support. -/
theorem boundaryAtom (a : ℝ) (f : Test ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    cost (Measure.dirac a) f ≤ K * (Measure.dirac a) (closure (Function.support f)) ∧
      cost (Measure.dirac a) f < ⊤ :=
  ⟨cost_le_mul_measure_closure_support _ f hK, (cost_ne_top _ f).lt_top⟩

/-- At a finite measure every test has finite cost (`cost_ne_top`). -/
theorem finiteRegression (ν : Measure X) [IsFiniteMeasure ν] (f : Test X) : cost ν f ≠ ⊤ :=
  cost_ne_top ν f

/-- Zero and empty-support tests are included without a total-mass assumption. -/
theorem emptySupport (ν : Measure X) (f : Test X) (hf : Function.support f = ∅) :
    cost ν f = 0 := by
  obtain ⟨K, hK⟩ := f.lipschitz
  exact le_antisymm (by simpa [hf] using cost_le_mul_measure_closure_support ν f hK) bot_le

theorem zeroTest (ν : Measure X) : cost ν Test.zero = 0 := cost_zero ν

#print axioms cost_le_mul_measure_closure_support
#print axioms cost_ne_top_of_support_measure
#print axioms finiteOnBounded
#print axioms properFiniteOnCompacts
#print axioms realVolume
#print axioms boundaryAtom
#print axioms finiteRegression
#print axioms emptySupport
#print axioms zeroTest
end MetricBVSupportCostAudit
