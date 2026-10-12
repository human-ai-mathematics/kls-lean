import FunctionalInequalities.KLS.BKL.Localization.Coefficients
import FunctionalInequalities.Probability.Diffusion.Transport

/-!
# The cutoff Eldan localization process

`IsEldanCutoff μ hc W ℱ hW γ p`: the parameter process `p_t = (c_t, Q_t)` solves the cutoff localization equations
(67) (drift `γ² (A⁻¹a, A⁻¹)`, noise `γ (A^{-1/2} e_k, 0)`, start `0`) in coordinates; existence for every admissible
cutoff, continuity of paths, initial value, and Dynkin's identity `E F(p_T) − F(0) = E ∫₀ᵀ γ(p_s)² 𝓛F(p_s) ds` for
every `C²` function (BKL arXiv:2610.05474v1, Section 4, cutoff stage). Proof bodies: GPT (S-line sub-controller
task S-5d2a); statements by the S-line sub-controller; placement: Claude.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/-- **The cutoff Eldan process** (BKL arXiv:2610.05474v1, (67), with cutoff coefficients `γ² · drift`, `γ · noise`)
in parameter-space form: its coordinates under `stateEquiv (Param n)` form an `IsDiffusion` with the transported cutoff coefficients, started at `p₀ = (0, 0)`. -/
def IsEldanCutoff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ) (γ : Param n → ℝ)
    (p : ℝ → Ω → Param n) : Prop :=
  IsDiffusion W ℱ hW (transportDrift (stateEquiv (Param n)) (cutoffDrift μ hc γ))
    (transportNoise (stateEquiv (Param n)) (cutoffNoise μ hc γ)) (stateEquiv (Param n) 0)
    (fun t ω => stateEquiv (Param n) (p t ω))

/-- **Existence of the cutoff Eldan process** on any Brownian setup with a usual filtration, for a compactly
supported isotropic prior and an admissible cutoff. -/
theorem exists_isEldanCutoff (hiso : KLS.Isotropic μ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    [ℱ.IsRightContinuous] (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {γ : Param n → ℝ} (hγ : IsCutoff γ) :
    ∃ p : ℝ → Ω → Param n, IsEldanCutoff μ hc W ℱ hW γ p := by
  classical
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  obtain ⟨⟨K, hK, hKσ⟩, ⟨B, hB⟩, _, _⟩ :=
    cutoffCoefficients_admissible μ hc hiso hγ
  let K' : ℝ≥0 :=
    ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖₊ *
      (K * ‖(Φ.symm : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] Param n)‖₊)
  have hbt :
      LipschitzWith K'
        (transportDrift Φ (cutoffDrift μ hc γ)) := by
    change LipschitzWith K'
      (fun y => Φ (cutoffDrift μ hc γ (Φ.symm y)))
    have he :
        (⇑(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ)) ∘
            cutoffDrift μ hc γ ∘
            ⇑(Φ.symm : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] Param n)) =
          (fun y => Φ (cutoffDrift μ hc γ (Φ.symm y))) := by
      funext y
      rfl
    rw [← he]
    exact
      (ContinuousLinearMap.lipschitz
        (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))).comp
        (hK.comp
          (ContinuousLinearMap.lipschitz
            (Φ.symm : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] Param n)))
  have hσt :
      ∀ k, LipschitzWith K'
        (fun y => transportNoise Φ (cutoffNoise μ hc γ) y k) := by
    intro k
    change LipschitzWith K'
      (fun y => Φ (cutoffNoise μ hc γ (Φ.symm y) k))
    have he :
        (⇑(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ)) ∘
            (fun p => cutoffNoise μ hc γ p k) ∘
            ⇑(Φ.symm : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] Param n)) =
          (fun y => Φ (cutoffNoise μ hc γ (Φ.symm y) k)) := by
      funext y
      rfl
    rw [← he]
    exact
      (ContinuousLinearMap.lipschitz
        (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))).comp
        ((hKσ k).comp
          (ContinuousLinearMap.lipschitz
            (Φ.symm : (Fin (Module.finrank ℝ (Param n)) → ℝ) →L[ℝ] Param n)))
  have hbtB :
      ∀ y, ‖transportDrift Φ (cutoffDrift μ hc γ) y‖ ≤
        ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ * B := by
    intro y
    calc
      ‖transportDrift Φ (cutoffDrift μ hc γ) y‖ =
          ‖Φ (cutoffDrift μ hc γ (Φ.symm y))‖ := rfl
      _ ≤ ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ *
          ‖cutoffDrift μ hc γ (Φ.symm y)‖ :=
        ContinuousLinearMap.le_opNorm
          (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ)) _
      _ ≤ ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ * B :=
        mul_le_mul_of_nonneg_left (hB (Φ.symm y)).1
          (norm_nonneg
            (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ)))
  have hσtB :
      ∀ y k, ‖transportNoise Φ (cutoffNoise μ hc γ) y k‖ ≤
        ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ * B := by
    intro y k
    calc
      ‖transportNoise Φ (cutoffNoise μ hc γ) y k‖ =
          ‖Φ (cutoffNoise μ hc γ (Φ.symm y) k)‖ := rfl
      _ ≤ ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ *
          ‖cutoffNoise μ hc γ (Φ.symm y) k‖ :=
        ContinuousLinearMap.le_opNorm
          (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ)) _
      _ ≤ ‖(Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ))‖ * B :=
        mul_le_mul_of_nonneg_left ((hB (Φ.symm y)).2 k)
          (norm_nonneg
            (Φ : Param n →L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ)))
  obtain ⟨Y, hY⟩ :=
    FunctionalInequalities.Probability.Diffusion.exists_isDiffusion
      W ℱ hW hℱ0 hnull hbt hσt hbtB hσtB (Φ 0)
  refine ⟨fun t ω => Φ.symm (Y t ω), ?_⟩
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (Φ.symm (Y t ω)))
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hY

section Process

variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {γ : Param n → ℝ} {p : ℝ → Ω → Param n}

/-- Paths of the cutoff Eldan process are continuous everywhere. -/
theorem IsEldanCutoff.continuous (h : IsEldanCutoff μ hc W ℱ hW γ p) (ω : Ω) :
    Continuous fun t => p t ω := by
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (p t ω)) at h
  have hp := IsDiffusion.continuous_path h ω
  have hp' := Φ.symm.continuous.comp hp
  have he :
      (Φ.symm ∘ (fun t => Φ (p t ω))) =
        (fun t => Φ.symm (Φ (p t ω))) := by
    funext t
    rfl
  rw [he] at hp'
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hp'

/-- The cutoff Eldan process starts at `p₀ = 0` almost surely. -/
theorem IsEldanCutoff.ae_initial (h : IsEldanCutoff μ hc W ℱ hW γ p) :
    ∀ᵐ ω ∂P, p 0 ω = 0 := by
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (p t ω)) at h
  filter_upwards [IsDiffusion.ae_initial h] with ω hω
  apply Φ.injective
  simpa only [Function.comp_apply] using hω

/-- **Dynkin's identity for the cutoff Eldan process**: for every `C²` `F : Param n → ℝ` (no growth condition:
the cutoff coefficients have compact support), `F(p_T)` is integrable and
`E F(p_T) − F(0) = E ∫₀ᵀ γ(p_s)² 𝓛F(p_s) ds` with the uncut generator `𝓛` of (67). -/
theorem IsEldanCutoff.dynkin (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) {F : Param n → ℝ} (hF : ContDiff ℝ 2 F)
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => F (p T ω)) P ∧
      ∫ ω, F (p T ω) ∂P - F 0 =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s ω) ^ 2 * generator μ hc F (p s ω) ∂volume ∂P := by
  classical
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  obtain ⟨⟨_, hK, hKσ⟩, _, hbs, hσs⟩ :=
    cutoffCoefficients_admissible μ hc hiso hγ
  have hbc : Continuous (cutoffDrift μ hc γ) := hK.continuous
  have hσc : ∀ k, Continuous fun p => cutoffNoise μ hc γ p k := by
    intro k
    exact (hKσ k).continuous
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (p t ω)) at h
  obtain ⟨hInt, hEq⟩ :=
    FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_transport
      (W := W) (ℱ := ℱ) (hW := hW) (Y := p) (x₀ := 0)
      Φ hℱ0 hnull hbc hσc hbs hσs h hF hT
  refine ⟨hInt, ?_⟩
  calc
    ∫ ω, F (p T ω) ∂P - F 0 =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T,
          diffusionGenerator (cutoffDrift μ hc γ) (cutoffNoise μ hc γ) F
            (p s ω) ∂volume ∂P := hEq
    _ = ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T,
          γ (p s ω) ^ 2 * generator μ hc F (p s ω) ∂volume ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            apply integral_congr_ae
            filter_upwards [] with s
            rw [diffusionGenerator_cutoff]

end Process

end FunctionalInequalities.KLS.BKL.Localization
