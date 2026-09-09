import FunctionalInequalities

/-! # Mathematical API calls and carrier boundaries

These typed applications use the public objects directly, including proof receivers and the
zero-dimensional carrier. They are compiled by the default Examples target.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

universe u

section FiniteDimensional

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (ν : ProbabilityMeasure V)

example (f : Energy.CovarianceGradient.Test ν) : NNReal := f.energy
example (f : Energy.CovarianceGradient.Test ν) : Lp ℝ 2 (ν : Measure V) := f.toL2
example (f : Energy.SmoothGradient.Test ν) : NNReal := f.energy
example (f : Energy.SmoothGradient.Test ν) : Lp ℝ 2 (ν : Measure V) := f.toL2

example (B : V →L[ℝ] V) {g : V → ℝ} (hg : Energy.WeightedGradient.IsTest ν B g) :
    MemLp g 2 (ν : Measure V) := hg.memLp

example (B : V →L[ℝ] V) {g : V → ℝ} (hg : Energy.WeightedGradient.IsTest ν B g) :
    MemLp (Energy.WeightedGradient.apply B g) 2 (ν : Measure V) := hg.memLp_apply

example (c : ℝ) (x : V) : Energy.LocalSlope.apply (fun _ : V ↦ c) x = 0 :=
  Energy.LocalSlope.apply_const c x

example (hν : KLS.LogConcave ν) :
    Poincare.SmoothGradient.Intrinsic.constant ν = Poincare.LocalSlope.Intrinsic.constant ν :=
  hν.intrinsicSmooth_constant_eq_localSlope

example : ∃ B : V →L[ℝ] V,
    ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2 :=
  Covariance.exists_inner_eq_norm_sq _

example (c : V) (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    L2.Translation.pullback ν c f =ᵐ[(ν : Measure V)] fun x ↦ f (c + x) :=
  L2.Translation.pullback_coeFn ν c f

example (c : V) :
    Poincare.CovarianceGradient.Intrinsic.constant (Probability.translateLaw ν c) =
      Poincare.CovarianceGradient.Intrinsic.constant ν :=
  Poincare.CovarianceGradient.Intrinsic.constant_translateLaw ν c

example (T : V ≃L[ℝ] V) (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V)) :
    L2.ContinuousLinearEquiv.pullback ν T f =ᵐ[(ν : Measure V)] fun x ↦ f (T x) :=
  L2.ContinuousLinearEquiv.pullback_coeFn ν T f

-- The zero operator is a legitimate external weight; no positive-definiteness assumption.
example : Energy.WeightedGradient.IsTest ν (0 : V →L[ℝ] V) (fun _ ↦ (3 : ℝ)) :=
  Energy.WeightedGradient.IsTest.const 3

end FiniteDimensional

section ZeroDimension

abbrev ZeroSpace := EuclideanSpace ℝ (Fin 0)

example (ν : ProbabilityMeasure ZeroSpace) : Poincare.LocalSlope.Intrinsic.constant ν = 0 :=
  Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton ν

example (ν : ProbabilityMeasure ZeroSpace) (B : ZeroSpace →L[ℝ] ZeroSpace)
    (m : Measure ZeroSpace) [m.IsAddHaarMeasure] (hac : (ν : Measure ZeroSpace) ≪ m) :
    (Energy.WeightedGradient.operator ν B hac).domain = ⊤ :=
  Energy.WeightedGradient.domain_operator_eq_top_of_subsingleton ν B hac

end ZeroDimension
