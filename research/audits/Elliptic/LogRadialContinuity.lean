module

public import FunctionalInequalities.Analysis.LogRadial.Continuity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Clients of the logarithmic barrier continuity and normal slope

* `shifted_singular_point_client`: in `ℝ²` with `p = y₀`, `q = y₁`, `β = 1`, the piece `-y₁ log((y₀
  - 1)² + y₁²)`
  is continuous everywhere, in particular at the singular point `(1, 0)` where the logarithm's
  argument
  vanishes; its value there is `0`.
* `scalar_continuous_not_differentiable_client`: on `ℝ` with `p = 0`, `q = id`, `β = 0`, `ε = 1`,
  the function
  `t ↦ -t log t²` is continuous (first main theorem) but not differentiable at `0`: a derivative
  would make the
  slope converge, while by the second main theorem the positive slope tends to `+∞`.
* `fin_zero_singleton_client`: on the one-point space `ℝ⁰` with `p = q = 0` and any `β`, the first
  main theorem
  applies.
-/

@[expose] public section

noncomputable section
open Filter
open scoped Topology

namespace FunctionalInequalities.Analysis.LogRadialContinuityClient

open FunctionalInequalities.Analysis

/-- **`ℝ²`, shift `β = 1`: continuity through the singular point `(1, 0)`.** -/
theorem shifted_singular_point_client :
    Continuous
        (fun y : EuclideanSpace ℝ (Fin 2) => -(y 1) * Real.log ((y 0 - 1) ^ 2 + (y 1) ^ 2)) ∧
      ContinuousAt
          (fun y : EuclideanSpace ℝ (Fin 2) => -(y 1) * Real.log ((y 0 - 1) ^ 2 + (y 1) ^ 2))
          (WithLp.toLp 2 ![1, 0]) ∧
        ((WithLp.toLp 2 ![(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 0 - 1) ^ 2 +
              ((WithLp.toLp 2 ![(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 1) ^ 2 =
            0 ∧
          (fun y : EuclideanSpace ℝ (Fin 2) => -(y 1) * Real.log ((y 0 - 1) ^ 2 + (y 1) ^ 2))
              (WithLp.toLp 2 ![1, 0]) =
            0 := by
  have h :
    Continuous
      (fun y : EuclideanSpace ℝ (Fin 2) => -(y 1) * Real.log ((y 0 - 1) ^ 2 + (y 1) ^ 2)) :=
    continuous_log_radial_barrier
      (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
      (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) 1
  exact ⟨h, h.continuousAt, by simp, by simp⟩

/-- **`t ↦ -t log t²` is continuous but not differentiable at `0`.** -/
theorem scalar_continuous_not_differentiable_client :
    Continuous (fun t : ℝ => -(1 * t) * Real.log (t ^ 2)) ∧
      ¬DifferentiableAt ℝ (fun t : ℝ => -(1 * t) * Real.log (t ^ 2)) 0 := by
  have hc := continuous_log_radial_barrier (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) 0
  have hfun :
    (fun y : ℝ =>
        -((ContinuousLinearMap.id ℝ ℝ) y) *
          Real.log (((0 : ℝ →L[ℝ] ℝ) y - 0) ^ 2 + ((ContinuousLinearMap.id ℝ ℝ) y) ^ 2)) =
      fun t => -(1 * t) * Real.log (t ^ 2) := by
    funext t
    simp
  rw [hfun] at hc
  refine ⟨hc, fun hd => ?_⟩
  have hs := tendsto_log_radial_positive_normal_slope (ε := 1) one_pos
  have hslope :=
    hasDerivWithinAt_iff_tendsto_slope.mp (hd.hasDerivAt.hasDerivWithinAt (s := Set.Ioi 0))
  rw [Set.sdiff_singleton_eq_self (show (0 : ℝ) ∉ Set.Ioi 0 from Set.self_notMem_Ioi)] at hslope
  have heq :
    slope (fun t : ℝ => -(1 * t) * Real.log (t ^ 2)) 0 =ᶠ[𝓝[>] (0 : ℝ)] fun t =>
      (-(1 * t) * Real.log (t ^ 2)) / t :=
    Eventually.of_forall fun t => by simp [slope_def_field]
  exact not_tendsto_nhds_of_tendsto_atTop hs _ (hslope.congr' heq)

/-- **The one-point space `ℝ⁰`**, `p = q = 0`, any shift. -/
theorem fin_zero_singleton_client (β : ℝ) :
    Continuous (fun y : EuclideanSpace ℝ (Fin 0) =>
      -((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y) *
        Real.log (((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y - β) ^ 2 +
          ((0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) y) ^ 2)) :=
  continuous_log_radial_barrier 0 0 β

end FunctionalInequalities.Analysis.LogRadialContinuityClient

#print axioms
  FunctionalInequalities.Analysis.LogRadialContinuityClient.shifted_singular_point_client
#print axioms
  FunctionalInequalities.Analysis.LogRadialContinuityClient.scalar_continuous_not_differentiable_client
#print axioms FunctionalInequalities.Analysis.LogRadialContinuityClient.fin_zero_singleton_client
