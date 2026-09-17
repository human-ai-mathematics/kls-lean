import FunctionalInequalities.Analysis.GraphJacobian
import FunctionalInequalities.KLS.Geometry.LinearAreaFormula

/-!
# Route statements for the nonlinear area formula

**This file contains only `#check`s.**  It declares nothing, proves nothing, and introduces no
placeholder axiom.  Each proposition below is an obligation of the route recorded in
`research/decisions/2026-09-16-area-formula-route.md` for the Federer area formula, which the
codimension-`m` coarea program needs and which **nothing in this repository proves**.

The same convention as `WeightedCoareaRouteStatements.lean`: a proposition type-check is not a
proof, and none of these is claimed to hold in Lean yet.
-/

noncomputable section

open MeasureTheory Set FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal RealInnerProductSpace

/-! ### A0 — the target -/

#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {g : H → V} {s : Set H}, ContDiff ℝ 1 g → Set.InjOn g s → MeasurableSet s →
    μH[(Module.finrank ℝ H : ℝ)] (g '' s)
      = ∫⁻ y in s, ENNReal.ofReal (LinearMap.normDet ((fderiv ℝ g y : H →ₗ[ℝ] V)))
          ∂(volume : Measure H))

/-! ### A1 — the integrand is measurable, via continuity of `normDet` -/

#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V],
    Continuous (fun A : H →L[ℝ] V => LinearMap.normDet (A : H →ₗ[ℝ] V)))

#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {g : H → V}, ContDiff ℝ 1 g →
    Measurable (fun y : H => LinearMap.normDet ((fderiv ℝ g y : H →ₗ[ℝ] V))))

/-! ### A2 — countable additivity on the image side -/

#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {g : H → V} {s : Set H} {t : ℕ → Set H},
    ContDiff ℝ 1 g → Set.InjOn g s → (∀ n, MeasurableSet (t n)) →
    Pairwise (Function.onFun Disjoint t) → s = ⋃ n, t n →
    μH[(Module.finrank ℝ H : ℝ)] (g '' s)
      = ∑' n, μH[(Module.finrank ℝ H : ℝ)] (g '' t n))

/-! ### A3 — two-sided comparison against an injective linear model

This is the main new analytic content.  Mathlib's `ApproximatesLinearOn.antilipschitz` requires the
linear model to be a continuous linear **equivalence**, so it does not apply when
`finrank H < finrank V`. -/

#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (A : H →L[ℝ] V), Function.Injective A →
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ {g : H → V} {s : Set H}, ApproximatesLinearOn g A s ε →
        μH[(Module.finrank ℝ H : ℝ)] (g '' s)
            ≤ ENNReal.ofReal ((1 + δ) * LinearMap.normDet (A : H →ₗ[ℝ] V))
              * μH[(Module.finrank ℝ H : ℝ)] s
          ∧ ENNReal.ofReal ((1 - δ) * LinearMap.normDet (A : H →ₗ[ℝ] V))
              * μH[(Module.finrank ℝ H : ℝ)] s
            ≤ μH[(Module.finrank ℝ H : ℝ)] (g '' s))

/-! ### A4 — the degenerate part carries no measure -/

#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {g : H → V} {s : Set H}, ContDiff ℝ 1 g → MeasurableSet s →
    (∀ y ∈ s, ¬ Function.Injective ((fderiv ℝ g y : H →ₗ[ℝ] V))) →
    μH[(Module.finrank ℝ H : ℝ)] (g '' s) = 0)

/-! ### A5 — localization: a local area formula patches to a global one -/

#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {g : H → V} {s : Set H}, ContDiff ℝ 1 g → Set.InjOn g s → MeasurableSet s →
    (∀ y ∈ s, ∃ u : Set H, IsOpen u ∧ y ∈ u ∧
        ∀ t : Set H, MeasurableSet t → t ⊆ s ∩ u →
          μH[(Module.finrank ℝ H : ℝ)] (g '' t)
            = ∫⁻ z in t, ENNReal.ofReal (LinearMap.normDet ((fderiv ℝ g z : H →ₗ[ℝ] V)))
                ∂(volume : Measure H)) →
    μH[(Module.finrank ℝ H : ℝ)] (g '' s)
      = ∫⁻ y in s, ENNReal.ofReal (LinearMap.normDet ((fderiv ℝ g y : H →ₗ[ℝ] V)))
          ∂(volume : Measure H))

/-! ### B1 — the recommended route: the nonlinear codimension-`m` graph area formula

The repository proved the codimension-**one** graph case in `Analysis/AreaFormula.lean`.  This is
its codimension-`m` analogue, with the volume factor supplied by `normDet_graphMapLinear`.  Here
the map is injective by construction and the parameter projection `ιᵀ` is an explicit left inverse,
which is exactly what `A3` lacks in general. -/

#check (∀ {H K V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V), (∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) →
    ∀ {γ : H → K} {s : Set H}, ContDiff ℝ 1 γ → MeasurableSet s →
    μH[(Module.finrank ℝ H : ℝ)] ((fun y => ι y + κ (γ y)) '' s)
      = ∫⁻ y in s, ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.id +
          LinearMap.adjoint ((fderiv ℝ γ y : H →ₗ[ℝ] K)) ∘ₗ (fderiv ℝ γ y : H →ₗ[ℝ] K))))
          ∂(volume : Measure H))

/-! ### B2 — the normalized form actually consumed by the program -/

#check (∀ {H K V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V), (∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) →
    ∀ {γ : H → K} {s : Set H}, ContDiff ℝ 1 γ → MeasurableSet s →
    KLS.hausdorffNormalized V (Module.finrank ℝ H) ((fun y => ι y + κ (γ y)) '' s)
      = ∫⁻ y in s, ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.id +
          LinearMap.adjoint ((fderiv ℝ γ y : H →ₗ[ℝ] K)) ∘ₗ (fderiv ℝ γ y : H →ₗ[ℝ] K))))
          ∂(volume : Measure H))
