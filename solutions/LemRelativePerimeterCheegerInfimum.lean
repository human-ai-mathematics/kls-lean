import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import FunctionalInequalities.KLS.Definitions

/-!
# Lean certificate: `lem:relative-perimeter-cheeger-infimum`

For a probability law `ν` on a finite-dimensional real inner-product space with a Borell density
`ρ` relative to Lebesgue measure, the sole `certificate` packages the Blueprint lemma: the
Minkowski Cheeger infimum `h_M` over Borel sets of intermediate mass equals the relative-perimeter
Cheeger infimum `h_S` over smooth domains of intermediate mass,

`inf_{0 < ν(B) < 1} ν⁺(B) / m(ν(B)) = inf_{U smooth, 0 < ν(U) < 1} P_ρ(U) / m(ν(U))`,

with `m(t) = min {t, 1 − t}` and both sides `⊤` when no admissible set exists (dimension zero
included). Lean is stronger than the Blueprint's "full-dimensional log-concave probability": any
law with a Borell density is allowed. `intrinsic` is the log-concave case on the affine support,
the `h_μ = h_ν^{sm,rel}` and `Ψ_KLS(μ) = ψ_ν` clauses of
`thm:klartag-density-frontend-identification`.

`h_M ≤ h_S` is smooth recovery of a smooth domain and the Minkowski coarea inequality
(Ambrosio–Di Marino–Gigli 2017, Lemma 3.2); `h_S ≤ h_M` is distance cutoffs of a Borel set of
finite content, their mollification, smooth Sard and the weighted `C¹` coarea formula for the
density. The statement compares infima, not the two perimeters of each test set; no Poincaré
inequality, no BV-perimeter identification and no Cheeger–Buser comparison follows from it.
-/

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS

namespace Solutions.LemRelativePerimeterCheegerInfimum

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The Blueprint lemma on the coordinate space: for every probability law with a Borell density
relative to Lebesgue measure, the two Cheeger infima agree. -/
theorem certificate {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    Isoperimetry.minkowskiConstant ν =
      Isoperimetry.smoothConstant ρ (interior (ν : Measure V).support) ν :=
  Isoperimetry.minkowskiConstant_eq_smoothConstant hρ

/-- The affine-support form: for a log-concave law with a Borell density of its intrinsic law,
the isoperimetric constant `h_μ` of `def:isoperimetric-cheeger-scale` is the smooth
relative-perimeter Cheeger infimum of the intrinsic law, and the inverse scales agree. -/
theorem intrinsic {μ : ProbabilityMeasure V} (hμ : LogConcave μ)
    {ρ : (Probability.affineSupport μ).direction → ℝ}
    (hρ : IsBorellDensity (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) volume ρ) :
    Isoperimetry.constant μ =
        Isoperimetry.smoothConstant ρ
          (interior (Probability.intrinsicMeasure μ :
            Measure (Probability.affineSupport μ).direction).support)
          (Probability.intrinsicMeasure μ) ∧
      Isoperimetry.inverseScale μ =
        (Isoperimetry.smoothConstant ρ
          (interior (Probability.intrinsicMeasure μ :
            Measure (Probability.affineSupport μ).direction).support)
          (Probability.intrinsicMeasure μ))⁻¹ :=
  ⟨Isoperimetry.constant_eq_smoothConstant_intrinsic hμ hρ,
    Isoperimetry.inverseScale_eq_inv_smoothConstant_intrinsic hμ hρ⟩

/-- The two one-sided comparisons, each available on its own. -/
example {ν : ProbabilityMeasure V} {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    Isoperimetry.minkowskiConstant ν ≤
        Isoperimetry.smoothConstant ρ (interior (ν : Measure V).support) ν ∧
      Isoperimetry.smoothConstant ρ (interior (ν : Measure V).support) ν ≤
        Isoperimetry.minkowskiConstant ν :=
  ⟨Isoperimetry.minkowskiConstant_le_smoothConstant hρ,
    Isoperimetry.smoothConstant_le_minkowskiConstant hρ⟩

/-- Dimension zero: both infima are `⊤`. -/
example [Subsingleton V] {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (_hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    Isoperimetry.minkowskiConstant ν = ⊤ ∧
      Isoperimetry.smoothConstant ρ (interior (ν : Measure V).support) ν = ⊤ :=
  ⟨Isoperimetry.minkowskiConstant_eq_top_of_subsingleton ν,
    Isoperimetry.smoothConstant_eq_top_of_subsingleton _ _ _⟩

/-- Typed application on the Euclidean family in every dimension. -/
example (n : ℕ) {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : IsBorellDensity (ν : Measure (EuclideanSpace ℝ (Fin n))) volume ρ) :
    Isoperimetry.minkowskiConstant ν =
      Isoperimetry.smoothConstant ρ (interior (ν : Measure (EuclideanSpace ℝ (Fin n))).support) ν :=
  certificate hρ

/--
info: 'Solutions.LemRelativePerimeterCheegerInfimum.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemRelativePerimeterCheegerInfimum.certificate

/--
info: 'Solutions.LemRelativePerimeterCheegerInfimum.intrinsic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemRelativePerimeterCheegerInfimum.intrinsic

/--
info: 'FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant

/--
info: 'FunctionalInequalities.KLS.Isoperimetry.smoothConstant_le_minkowskiConstant'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_le_minkowskiConstant

end Solutions.LemRelativePerimeterCheegerInfimum
