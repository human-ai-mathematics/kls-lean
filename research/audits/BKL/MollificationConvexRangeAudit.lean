import FunctionalInequalities.Analysis.Mollification.Basic
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology Convolution
open FunctionalInequalities.Analysis
namespace CodexW3b2aClient

section FiniteDimensional

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
variable {ι : Type*}
variable [Fintype ι]
theorem exact_frozen_statement
    {f : ι → E → ℝ} (hf : ∀ k, LocallyIntegrable (f k) (volume : Measure E))
    {C : Set (ι → ℝ)} (hCc : Convex ℝ C) (hCcl : IsClosed C) {S : Set E} {r : ℝ}
    (hfC : ∀ᵐ x ∂((volume : Measure E).restrict (cthickening r S)), (fun k => f k x) ∈ C)
    (φ : ContDiffBump (0 : E)) (hφ : φ.rOut ≤ r) {x : E} (hx : x ∈ S) :
    (fun k => convolution (φ.normed volume) (f k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) ∈ C := by
  exact convolution_mem_of_ae_mem hf hCc hCcl hfC φ hφ hx

theorem nonnegative_coordinates
    {f : ι → E → ℝ} (hf : ∀ k, LocallyIntegrable (f k) (volume : Measure E))
    {S : Set E} {r : ℝ}
    (hfC : ∀ᵐ x ∂((volume : Measure E).restrict (cthickening r S)), ∀ k, 0 ≤ f k x)
    (φ : ContDiffBump (0 : E)) (hφ : φ.rOut ≤ r) {x : E} (hx : x ∈ S) :
    ∀ k, 0 ≤ convolution (φ.normed volume) (f k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have hfc : ∀ᵐ y ∂((volume : Measure E).restrict (cthickening r S)),
      (fun k => f k y) ∈ Set.Ici (0 : ι → ℝ) := by
    simpa only [Set.mem_Ici, Pi.le_def, Pi.zero_apply] using hfC
  have hc := convolution_mem_of_ae_mem hf (convex_Ici (0 : ι → ℝ)) isClosed_Ici hfc φ hφ hx
  exact hc
#print axioms FunctionalInequalities.Analysis.convolution_mem_of_ae_mem
#print axioms exact_frozen_statement
#print axioms nonnegative_coordinates

end FiniteDimensional
end CodexW3b2aClient
