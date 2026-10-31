module

public import FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative
public import Lean
meta import Lean

@[expose] public section

open Filter Topology Set FunctionalInequalities.Analysis.Semigroup

namespace SourceLayout
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

/-- Backward convergence uses arbitrary Hilbert data, without a measure or Markov premise. -/
theorem backward_limit (f : H₀) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun a => Generated.apply T hT hd (t - a) f) (𝓝[>] 0)
      (𝓝 (Generated.apply T hT hd t f)) :=
  Generated.tendsto_apply_sub_zero T hT hd f ht

/-- Continuity includes the endpoint with zero forward time. -/
theorem backward_continuous (f : H₀) {a t : ℝ} :
    ContinuousOn (fun r => Generated.apply T hT hd (t - r) f) (Icc a t) :=
  Generated.continuousOn_apply_sub T hT hd f

#print axioms backward_limit
#print axioms backward_continuous
run_cmd do
  let env ← Lean.getEnv
  if env.contains `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator then
    throwError "A log-concave heat specialization leaked into the generic semigroup owner"
end SourceLayout
