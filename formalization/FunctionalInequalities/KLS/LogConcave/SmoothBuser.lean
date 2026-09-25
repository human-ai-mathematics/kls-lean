import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Correlation
import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import FunctionalInequalities.KLS.LogConcave.Poincare
import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Intrinsic

/-!
# Pi Buser comparison in the smooth convex tilted model

The actual heat correlation and pi-coefficient perimeter estimate imply a bound on the
inverse smooth relative-perimeter Cheeger constant. The law is explicitly represented by a
smooth convex potential. No passage to an arbitrary nonsmooth log-concave law is asserted.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace FunctionalInequalities.KLS.LogConcave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

include hν hi in
/-- The inverse smooth Cheeger constant obeys the pi Buser coefficient whenever a positive
finite constant bounds the intrinsic literature Poincare optimum of a smooth convex tilted law.
The smooth Cheeger infimum includes the empty admissible family and infinite perimeters. -/
theorem inv_smoothConstant_sq_le_pi_mul
    {U : V → ℝ} (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    (Isoperimetry.smoothConstant ρ (interior (ν : Measure V).support) ν)⁻¹ ^ 2 ≤
      ENNReal.ofReal (Real.pi * (C : ℝ)) := by
  let k : ENNReal := ENNReal.ofReal (Real.sqrt (Real.pi * (C : ℝ)))
  have hkpos : 0 < k := ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr
    (mul_pos Real.pi_pos (by exact_mod_cast hC)))
  have hktop : k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmass (D : SmoothDomain V) :
      min ((ν : Measure V) D.carrier) (1 - (ν : Measure V) D.carrier) ≤
        k * relativePerimeter ρ (interior (ν : Measure V).support) D := by
    let d : ENNReal := min ((ν : Measure V) D.carrier) (1 - (ν : Measure V) D.carrier)
    have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
      ((min_le_left _ _).trans prob_le_one)
    have hmtop : (ν : Measure V) D.carrier ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
    have hctop : 1 - (ν : Measure V) D.carrier ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (tsub_le_self)
    have hdreal : d.toReal = min ((ν : Measure V).real D.carrier)
        (1 - (ν : Measure V).real D.carrier) := by
      dsimp [d]
      rw [ENNReal.toReal_min hmtop hctop,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
      simp [measureReal_def]
    by_cases hP : relativePerimeter ρ (interior (ν : Measure V).support) D = ⊤
    · rw [hP, ENNReal.mul_top hkpos.ne']
      exact le_top
    have hreal := HeatSemigroup.min_mass_le_sqrt_pi_mul_perimeter m hν hi
      hνU hU hconv C hC hLit hρ D hP
    rw [← hdreal] at hreal
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_toReal hdtop, ENNReal.ofReal_mul
      (Real.sqrt_nonneg _), ENNReal.ofReal_toReal hP] at h
    exact h
  have hlow : k⁻¹ ≤ Isoperimetry.smoothConstant ρ
      (interior (ν : Measure V).support) ν := by
    unfold Isoperimetry.smoothConstant
    refine le_iInf fun D => le_iInf fun hpos => le_iInf fun hlt => ?_
    let d : ENNReal := min ((ν : Measure V) D.carrier) (1 - (ν : Measure V) D.carrier)
    have hdpos : 0 < d := lt_min hpos (tsub_pos_of_lt hlt)
    have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
      ((min_le_left _ _).trans prob_le_one)
    have hmul : k⁻¹ * d ≤ relativePerimeter ρ (interior (ν : Measure V).support) D := by
      calc
        k⁻¹ * d ≤ k⁻¹ * (k * relativePerimeter ρ (interior (ν : Measure V).support) D) :=
          mul_le_mul' le_rfl (hmass D)
        _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hkpos.ne' hktop, one_mul]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hdpos.ne') (Or.inl hdtop)).mpr hmul
  have hinv : (Isoperimetry.smoothConstant ρ (interior (ν : Measure V).support) ν)⁻¹ ≤ k := by
    simpa using ENNReal.inv_le_inv.mpr hlow
  have hsq := pow_le_pow_left₀ (by positivity) hinv 2
  rw [show k ^ 2 = ENNReal.ofReal (Real.pi * (C : ℝ)) by
    dsimp [k]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
      Real.sq_sqrt (mul_nonneg Real.pi_pos.le (by exact_mod_cast hC.le))]] at hsq
  exact hsq

include hν hi in
/-- The same pi comparison for the full-dimensional Minkowski Cheeger constant, using the
proved equality with the smooth relative-perimeter infimum. -/
theorem inv_minkowskiConstant_sq_le_pi_mul
    {U : V → ℝ} (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    (Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2 ≤
      ENNReal.ofReal (Real.pi * (C : ℝ)) := by
  rw [Isoperimetry.minkowskiConstant_eq_smoothConstant hρ]
  exact inv_smoothConstant_sq_le_pi_mul m hν hi hνU hU hconv C hC hLit hρ

include hν hi in
/-- The smooth convex tilted model satisfies the pi Buser comparison at the exact extended
literature optimum. The zero and infinite optimum cases follow by order limits and triviality,
respectively. -/
theorem inv_minkowskiConstant_sq_le_pi_literature
    {U : V → ℝ} (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    (Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant ν := by
  let L := Poincare.LocalSlope.Intrinsic.constant ν
  let X := (Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2
  by_cases htop : L = ⊤
  · have hpi : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.mpr Real.pi_pos).ne'
    change X ≤ ENNReal.ofReal Real.pi * L
    rw [htop, ENNReal.mul_top hpi]
    exact le_top
  by_cases hzero : L = 0
  · have hX : X ≤ 0 := by
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      let C : NNReal := ε / 4
      have hC : 0 < C := by dsimp [C]; positivity
      have hLit : L ≤ (C : ENNReal) := by rw [hzero]; exact bot_le
      have h := inv_minkowskiConstant_sq_le_pi_mul m hν hi hνU hU hconv C hC hLit hρ
      have hreal : Real.pi * (C : ℝ) ≤ (ε : ℝ) := by
        have hp := Real.pi_le_four
        have hε0 : 0 ≤ (ε : ℝ) := NNReal.coe_nonneg ε
        dsimp [C]
        nlinarith [mul_nonneg (sub_nonneg.mpr hp) hε0]
      have hεbound : ENNReal.ofReal (Real.pi * (C : ℝ)) ≤ (ε : ENNReal) := by
        simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hreal
      simpa [X] using h.trans hεbound
    simpa [L, hzero, X] using hX
  · let C : NNReal := L.toNNReal
    have hC : 0 < C := by
      apply NNReal.coe_pos.mp
      have hLpos : 0 < L := pos_iff_ne_zero.mpr hzero
      have hcoe : (C : ENNReal) = L := ENNReal.coe_toNNReal htop
      have hCpos : (0 : ENNReal) < (C : ENNReal) := by rw [hcoe]; exact hLpos
      exact_mod_cast hCpos
    have hLit : L ≤ (C : ENNReal) := (ENNReal.coe_toNNReal htop).ge
    have h := inv_minkowskiConstant_sq_le_pi_mul m hν hi hνU hU hconv C hC hLit hρ
    have hcoe : (C : ENNReal) = L := ENNReal.coe_toNNReal htop
    rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_coe_nnreal, hcoe] at h
    exact h

end FunctionalInequalities.KLS.LogConcave

namespace FunctionalInequalities.KLS.LogConcave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- Transport the smooth convex tilted pi comparison from the intrinsic law to the original
law's affine-support isoperimetric scale. The intrinsic space may have dimension zero. -/
theorem inverseScale_sq_le_pi_literature_of_intrinsic_smooth_tilt
    {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    {U : (Probability.affineSupport μ).direction → ℝ}
    (hμU : (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) =
      (volume : Measure (Probability.affineSupport μ).direction).tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U) :
    Isoperimetry.inverseScale μ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant μ := by
  let ν := Probability.intrinsicMeasure μ
  obtain ⟨ρ, hρ⟩ := hμ.exists_isBorellDensity volume
  have hmain := (hμ.intrinsicMeasure).inv_minkowskiConstant_sq_le_pi_literature
    volume hμ.interior_intrinsic_support_nonempty hμU hU hconv hρ
  have hP : Poincare.LocalSlope.Intrinsic.constant ν =
      Poincare.LocalSlope.Intrinsic.constant μ := by
    rw [← (hμ.intrinsicMeasure).smoothTest_constant_eq_localSlope]
    exact (hμ.smoothTest_constant_eq_intrinsic_and_localSlope).2
  rw [hP] at hmain
  simpa only [Isoperimetry.inverseScale,
    Isoperimetry.constant_eq_minkowskiConstant_intrinsic] using hmain

omit [CompleteSpace E] in
/-- The exact pi comparison is unconditional when the affine support has dimension zero:
the isoperimetric constant is top and its inverse scale is zero. -/
theorem inverseScale_sq_le_pi_literature_of_finrank_eq_zero
    {μ : ProbabilityMeasure E}
    (hdim : Module.finrank ℝ (Probability.affineSupport μ).direction = 0) :
    Isoperimetry.inverseScale μ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant μ := by
  have htop : Isoperimetry.constant μ = ⊤ := by
    unfold Isoperimetry.constant
    rw [if_pos hdim]
  simp [Isoperimetry.inverseScale, htop]

end FunctionalInequalities.KLS.LogConcave
