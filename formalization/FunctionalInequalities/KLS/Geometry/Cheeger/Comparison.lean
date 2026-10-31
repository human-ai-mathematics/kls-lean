module

public import FunctionalInequalities.KLS.Geometry.Cheeger.Inequality
public import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Buser
public import FunctionalInequalities.KLS.LogConcave.Isotropic
public import FunctionalInequalities.KLS.LogConcave.Line.Buser
public import FunctionalInequalities.KLS.LogConcave.Line.SharpPoincare
public import FunctionalInequalities.KLS.ConditionalFiber.EnergyComparison
public import FunctionalInequalities.Probability.Covariance.Positivity

/-!
# The ambient isoperimetric constant and the Cheeger–Buser comparison

Source: B. Letwin, *The KLS constant is O(log^{1/4} n)*, arXiv:2607.24164v1, Section 1: the
display defining `1/ψ_μ` and `ψ_n`, the comparison display `1/4 ≤ ψ_μ² / C_P(μ) ≤ π` (quoted there
from Cheeger, Buser, Ledoux and De Ponti–Mondino), and the two equivalent statements of the KLS
conjecture.

* `Isoperimetry.constant_eq_smoothConstant_univ` and
  `Isoperimetry.inverseScale_eq_inv_smoothConstant_univ`: for a probability law with a Borell
  density `ρ` relative to Lebesgue measure, `h_μ` is the
  infimum over open sets with smooth boundary of `∫_{∂A} ρ dℋ^{n-1} / min {μ(A), 1 - μ(A)}`, the
  boundary charged everywhere, and `Isoperimetry.inverseScale μ = ψ_μ`. The Borell density is the
  upper-semicontinuous log-concave representative; the boundary integral depends on the
  representative, since `∂A` is Lebesgue null.
* `LogConcave.literatureConstant_le_four_mul_inv_smoothConstant_univ_sq` and
  `LogConcave.inv_smoothConstant_univ_sq_le_pi_literature`: the two halves of the comparison in
  this normalization, for every log-concave law with a Borell density.
* `LogConcave.inv_smoothConstant_univ_sq_div_literatureConstant_mem_Icc`: the ratio form on
  `ℝⁿ`, `n ≥ 1`, with `0 < C_P(μ) < ∞`. Positivity comes from a linear test and full affine
  support; finiteness is taken from the KLS proposition `hKLS : KLS.Conjecture`, a premise that
  the proved theorem `KLS.kls` discharges outside this object family.
* `KLS.conjecture_iff_inverseScale`: `KLS.Conjecture ↔ sup_{n ≥ 2} ψ_n < ∞`, with
  `ψ_n = ⨆ μ isotropic log-concave on ℝⁿ, Isoperimetry.inverseScale μ`. Dimension one is handled
  by the sharp one-dimensional bound `C_P ≤ 4 Var`, dimension zero by `C_P = 0`. No proof of the
  conjecture is used.

`C_P(μ)` is `Poincare.LocalSlope.Intrinsic.constant μ`; for a log-concave law with a density it is
the paper's Equation (1.1) by `LogConcave.localSlope_constant_eq_ambient_gradient`.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

namespace KLS.Isoperimetry

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- **Letwin's isoperimetric constant** (arXiv:2607.24164v1, Section 1, display defining
`1/ψ_μ`): for a probability law with a Borell density `ρ` relative to Lebesgue measure, the
affine-support isoperimetric constant `h_μ` is the infimum, over open sets `A` with smooth boundary
and `0 < μ(A) < 1`, of `∫_{∂A} ρ dℋ^{n-1} / min {μ(A), 1 - μ(A)}`. Absolute continuity forces full
affine support, so no intrinsic coordinates appear on the right. -/
theorem constant_eq_smoothConstant_univ {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : IsBorellDensity (μ : Measure E) volume ρ) :
    constant μ = smoothConstant ρ Set.univ μ := by
  have hac : (μ : Measure E) ≪ volume := by
    rw [← hρ.withDensity_eq]
    exact withDensity_absolutelyContinuous _ _
  rw [constant_eq_minkowskiConstant
      (ConditionalFiber.affineSupport_eq_top_of_absolutelyContinuous μ volume hac),
    minkowskiConstant_eq_smoothConstant_univ hρ]

/-- `ψ_μ` in Letwin's ambient smooth-boundary convention is `Isoperimetry.inverseScale μ`. -/
theorem inverseScale_eq_inv_smoothConstant_univ {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : IsBorellDensity (μ : Measure E) volume ρ) :
    inverseScale μ = (smoothConstant ρ Set.univ μ)⁻¹ := by
  rw [inverseScale, constant_eq_smoothConstant_univ hρ]

end KLS.Isoperimetry

namespace KLS.LogConcave

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- A log-concave law with full affine support in positive dimension has a positive literature
Poincaré constant: a nonzero linear test has positive variance and positive energy. -/
theorem localSlope_constant_pos_of_affineSupport_eq_top [Nontrivial E] {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (htop : Probability.affineSupport μ = ⊤) :
    0 < Poincare.LocalSlope.Intrinsic.constant μ := by
  rw [← hμ.smoothTest_constant_eq_localSlope]
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have h2 := hμ.memLp_id_two
  have hadm := Poincare.SmoothTest.linear_admissible inferInstance h2 v
  have hen : 0 < Poincare.SmoothTest.energy (μ : Measure E) (Poincare.SmoothTest.linear v) := by
    rw [Poincare.SmoothTest.energy_linear]
    exact pow_pos (norm_pos_iff.mpr hv) 2
  have hvar : 0 < variance (Poincare.SmoothTest.linear v) (μ : Measure E) := by
    rw [← Covariance.operator_self_eq_variance h2]
    exact Covariance.inner_operator_self_pos_of_affineSupport_eq_top μ h2 htop hv
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (div_pos hvar hen))
    (Poincare.SmoothTest.realRayleigh_le_constant hadm hen)

/-- Under the KLS proposition every log-concave law on `ℝⁿ` has a finite literature constant:
its finite second moment gives `C_P(μ) ≤ C ‖Cov μ‖ < ∞`. -/
theorem localSlope_constant_lt_top_of_conjecture (hKLS : Conjecture) {n : ℕ}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hμ : LogConcave μ) :
    Poincare.LocalSlope.Intrinsic.constant μ < ⊤ := by
  obtain ⟨C, hC⟩ := hKLS
  exact (hC n μ hμ hμ.memLp_id_two).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)

/-- Cheeger half of Letwin's comparison display in the ambient smooth-boundary normalization:
`C_P(μ) ≤ 4 ψ_μ²`. -/
theorem literatureConstant_le_four_mul_inv_smoothConstant_univ_sq {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) {ρ : E → ℝ} (hρ : IsBorellDensity (μ : Measure E) volume ρ) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤
      4 * (Isoperimetry.smoothConstant ρ Set.univ μ)⁻¹ ^ 2 := by
  rw [← Isoperimetry.inverseScale_eq_inv_smoothConstant_univ hρ]
  exact hμ.literatureConstant_le_four_mul_inverseScale_sq

/-- Buser half of Letwin's comparison display in the ambient smooth-boundary normalization:
`ψ_μ² ≤ π C_P(μ)`. -/
theorem inv_smoothConstant_univ_sq_le_pi_literature {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) {ρ : E → ℝ} (hρ : IsBorellDensity (μ : Measure E) volume ρ) :
    (Isoperimetry.smoothConstant ρ Set.univ μ)⁻¹ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant μ := by
  rw [← Isoperimetry.inverseScale_eq_inv_smoothConstant_univ hρ]
  exact hμ.inverseScale_sq_le_pi_literature

/-- **Letwin's comparison display** (arXiv:2607.24164v1, Section 1):
`1/4 ≤ ψ_μ² / C_P(μ) ≤ π` for a log-concave probability law on `ℝⁿ`, `n ≥ 1`, with a Borell density
`ρ`, where `ψ_μ = (h_S)⁻¹` is the ambient smooth-boundary constant. The ratio is meaningful because
`0 < C_P(μ) < ∞`; finiteness uses the KLS proposition `hKLS`. -/
theorem inv_smoothConstant_univ_sq_div_literatureConstant_mem_Icc (hKLS : Conjecture) {n : ℕ}
    (hn : n ≠ 0) {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hμ : LogConcave μ)
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : IsBorellDensity (μ : Measure (EuclideanSpace ℝ (Fin n))) volume ρ) :
    0 < Poincare.LocalSlope.Intrinsic.constant μ ∧ Poincare.LocalSlope.Intrinsic.constant μ < ⊤ ∧
      (Isoperimetry.smoothConstant ρ Set.univ μ)⁻¹ ^ 2 /
          Poincare.LocalSlope.Intrinsic.constant μ ∈ Set.Icc 4⁻¹ (ENNReal.ofReal Real.pi) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  have hac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume := by
    rw [← hρ.withDensity_eq]
    exact withDensity_absolutelyContinuous _ _
  have hpos := hμ.localSlope_constant_pos_of_affineSupport_eq_top
    (ConditionalFiber.affineSupport_eq_top_of_absolutelyContinuous μ volume hac)
  have hfin := hμ.localSlope_constant_lt_top_of_conjecture hKLS
  refine ⟨hpos, hfin, ?_, ENNReal.div_le_of_le_mul
    (hμ.inv_smoothConstant_univ_sq_le_pi_literature hρ)⟩
  rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl hfin.ne)]
  calc 4⁻¹ * Poincare.LocalSlope.Intrinsic.constant μ
      ≤ 4⁻¹ * (4 * (Isoperimetry.smoothConstant ρ Set.univ μ)⁻¹ ^ 2) :=
        mul_le_mul_right (hμ.literatureConstant_le_four_mul_inv_smoothConstant_univ_sq hρ) _
    _ = (Isoperimetry.smoothConstant ρ Set.univ μ)⁻¹ ^ 2 := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- An isotropic log-concave law on `EuclideanSpace ℝ (Fin 1)` has literature constant at most
`4`: transport to `ℝ` by a linear isometry and apply the sharp bound `C_P ≤ 4 Var`. -/
theorem localSlope_constant_le_four_of_isotropic_fin_one
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 1))} (hμ : LogConcave μ) (hiso : Isotropic μ) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 := by
  obtain ⟨e⟩ := nonempty_linearIsometryEquiv_real (V := EuclideanSpace ℝ (Fin 1))
    (by rw [finrank_euclideanSpace_fin])
  let μ' := Probability.mapContinuousLinearEquiv μ e.toContinuousLinearEquiv
  have hμ' : LogConcave μ' := hμ.mapContinuousLinearEquiv _
  have hiso' : Isotropic μ' := hiso.map_linearIsometryEquiv e
  have hconst : Poincare.LocalSlope.Intrinsic.constant μ' =
      Poincare.LocalSlope.Intrinsic.constant μ := by
    rw [← hμ'.smoothTest_constant_eq_localSlope, ← hμ.smoothTest_constant_eq_localSlope,
      Probability.coe_mapContinuousLinearEquiv]
    exact Poincare.SmoothTest.constant_map_linearIsometryEquiv e _
  have hvar : variance id (μ' : Measure ℝ) = 1 := by
    have h := Covariance.operator_self_eq_variance hiso'.memLp_two (1 : ℝ)
    rw [hiso'.covariance_identity] at h
    have hlin : Poincare.SmoothTest.linear (1 : ℝ) = id := by
      funext x; simp [Poincare.SmoothTest.linear]
    rw [hlin] at h
    rw [← h]; simp
  rw [← hconst]
  refine hμ'.localSlope_constant_le_four_variance.trans (le_of_eq ?_)
  rw [hvar, mul_one]
  norm_num

end KLS.LogConcave

namespace KLS

/-- **The KLS conjecture in isoperimetric form** (Letwin arXiv:2607.24164v1, Section 1):
`KLS.Conjecture` holds if and only if `sup_{n ≥ 2} ψ_n < ∞`, where
`ψ_n = ⨆ {Isoperimetry.inverseScale μ : μ isotropic log-concave on ℝⁿ}`. The forward direction uses
the Buser half `ψ² ≤ π C_P`, the converse the Cheeger half `C_P ≤ 4 ψ²` for `n ≥ 2` and the
one-dimensional bound `C_P ≤ 4 Var` for `n = 1`. -/
theorem conjecture_iff_inverseScale :
    Conjecture ↔ ∃ C : NNReal, ∀ n : ℕ, 2 ≤ n →
      (⨆ (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (_ : LogConcave μ)
        (_ : Isotropic μ), Isoperimetry.inverseScale μ) ≤ (C : ENNReal) := by
  rw [conjecture_iff_isotropic]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨1 + Real.pi.toNNReal * C, fun n _ ↦ ?_⟩
    refine iSup_le fun μ ↦ iSup_le fun hμ ↦ iSup_le fun hiso ↦ ?_
    have hsq : Isoperimetry.inverseScale μ ^ 2 ≤ ((Real.pi.toNNReal * C : NNReal) : ENNReal) := by
      calc Isoperimetry.inverseScale μ ^ 2
          ≤ ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant μ :=
            hμ.inverseScale_sq_le_pi_literature
        _ ≤ ENNReal.ofReal Real.pi * (C : ENNReal) := mul_le_mul_right (hC n μ hμ hiso) _
        _ = ((Real.pi.toNNReal * C : NNReal) : ENNReal) := by
            rw [ENNReal.coe_mul]; rfl
    rcases le_total (Isoperimetry.inverseScale μ) 1 with h1 | h1
    · exact h1.trans (by rw [ENNReal.coe_add, ENNReal.coe_one]; exact le_self_add)
    · calc Isoperimetry.inverseScale μ ≤ Isoperimetry.inverseScale μ ^ 2 := by
            rw [pow_two]; exact le_mul_of_one_le_right' h1
        _ ≤ _ := hsq
        _ ≤ _ := by rw [ENNReal.coe_add]; exact le_add_self
  · rintro ⟨C, hC⟩
    refine ⟨4 * (C ^ 2 + 1), fun n μ hμ hiso ↦ ?_⟩
    rcases lt_or_ge n 2 with hn | hn
    · interval_cases n
      · rw [Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton]
        exact zero_le
      · refine (hμ.localSlope_constant_le_four_of_isotropic_fin_one hiso).trans ?_
        simp only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_ofNat]
        exact le_mul_of_one_le_right' le_add_self
    · have h1 : Isoperimetry.inverseScale μ ≤ ⨆ (_ : Isotropic μ), Isoperimetry.inverseScale μ :=
        le_iSup_of_le hiso le_rfl
      have h2 : (⨆ (_ : Isotropic μ), Isoperimetry.inverseScale μ) ≤
          ⨆ (_ : LogConcave μ) (_ : Isotropic μ), Isoperimetry.inverseScale μ :=
        le_iSup_of_le hμ le_rfl
      have h3 := le_iSup (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) ↦
        ⨆ (_ : LogConcave ν) (_ : Isotropic ν), Isoperimetry.inverseScale ν) μ
      have hψ : Isoperimetry.inverseScale μ ≤ (C : ENNReal) :=
        ((h1.trans h2).trans h3).trans (hC n hn)
      calc Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * Isoperimetry.inverseScale μ ^ 2 :=
            hμ.literatureConstant_le_four_mul_inverseScale_sq
        _ ≤ 4 * (C : ENNReal) ^ 2 := by gcongr
        _ ≤ _ := by
            simp only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_ofNat,
              ENNReal.coe_pow]
            exact mul_le_mul_right le_self_add _

end KLS

end FunctionalInequalities
