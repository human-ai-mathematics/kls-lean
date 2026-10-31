module

public import FunctionalInequalities.Analysis.MetricBV.Approximation

/-! Arbitrary-function pointwise truncation needs only a metric space. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FunctionalInequalities
open FunctionalInequalities.KLS.MetricBV
open scoped ENNReal

namespace SourceLayout

theorem pointwise_truncation {X : Type*} [MetricSpace X]
    (x₀ : X) (R : ℝ) (f : X → ℝ) (B : Set X) (x : X) :
    Energy.LocalSlope.apply (truncateFun x₀ R f) x ≤
        Energy.LocalSlope.apply f x + (Metric.ball x₀ R)ᶜ.indicator 1 x ∧
      ‖truncateFun x₀ R f x - B.indicator (1 : X → ℝ) x‖ₑ ≤
        ‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (Metric.ball x₀ R)ᶜ.indicator 1 x :=
  ⟨apply_truncateFun_le x₀ R f x, enorm_truncateFun_sub_le x₀ R f B x⟩

#print axioms SourceLayout.pointwise_truncation

end SourceLayout
