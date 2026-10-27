import FunctionalInequalities.Analysis.LocalExtension

/-! Finite-order and smooth extension through the shared local core. -/
set_option autoImplicit false
open FunctionalInequalities Filter Topology
open scoped ContDiff
namespace SourceLayout

theorem local_extension {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ∞} {f : E → F} {O : Set E} {z : E}
    (hO : IsOpen O) (hf : ContDiffOn ℝ k f O) (hz : z ∈ O) :
    ∃ (r : ℝ) (g : E → F), 0 < r ∧ Metric.ball z r ⊆ O ∧
      ContDiff ℝ k g ∧ Set.EqOn g f (Metric.ball z r) :=
  Analysis.exists_contDiff_eqOn_ball hO hf hz

theorem smooth_extension {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {O : Set E} {z : E}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hz : z ∈ O) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 z] f :=
  Analysis.exists_contDiff_eventuallyEq hO hf hz

#print axioms SourceLayout.local_extension
#print axioms SourceLayout.smooth_extension
end SourceLayout
