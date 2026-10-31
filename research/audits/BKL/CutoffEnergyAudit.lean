module

public import solutions.LemBklCutoffEnergy
public import FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.ToCumulant
public import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
Independent source specification and substantive clients of the BKL cutoff endpoint.
The handwritten specification retains all quantifiers, the exact half, universal153,
(d!)² and the cutoff square. The actual Brownian setup/strong cutoff process is
constructed; the downstream compact cumulant consumer is checked separately.
No uncut process or unconditional BKL main theorem is registered here.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities.KLS.BKL FunctionalInequalities.KLS.BKL.Localization
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open scoped RealInnerProductSpace
namespace BklCutoffEnergyAudit

/-- Independent full source-form finite-horizon cutoff (95), with m = d+1. -/
def Expected (d : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support),
    FunctionalInequalities.KLS.Isotropic μ →
    FunctionalInequalities.KLS.LogConcave μ →
    ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
    ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, 0 ≤ T →
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
        (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ),
        (∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) →
        (∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) →
        ∀ {p : ℝ → Ω → Param n},
        IsEldanCutoff μ hc W ℱ hW (ballCutoff R) p →
        cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) d u +
          (1 / 2 : ℝ) *
            (∫ ω, ∫ s in Set.Ioc (0 : ℝ) T,
              ballCutoff R (p s ω) ^ 2 *
              cumulantEnergy
                (compactPosterior μ hc (p s ω).1 (p s ω).2 :
                  Measure (EuclideanSpace ℝ (Fin n))) (d + 1) u ∂volume ∂P) ≤
          (d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d + ε

/-- Match the registered certificate against the complete independent specification. -/
theorem exactCertificate (d : ℕ) (hd : 1 ≤ d) : Expected d :=
  Solutions.LemBklCutoffEnergy.certificate d hd

/-- The process family quantified in the endpoint is inhabited for each compact
isotropic prior and every cutoff radius, on an actual usual Brownian setup. -/
theorem actualProcess (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hiso : FunctionalInequalities.KLS.Isotropic μ) (R : ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
      (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ),
      ℱ.IsRightContinuous ∧
      (∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) ∧
      (∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) ∧
      ∃ p : ℝ → Ω → Param n, IsEldanCutoff μ hc W ℱ hW (ballCutoff R) p := by
  obtain ⟨Ω, _, P, _, W, _⟩ := exists_brownianSetup n
  let ℱ : Filtration ℝ ‹MeasurableSpace Ω› := usualFiltration W
  have hright : ℱ.IsRightContinuous := by dsimp [ℱ]; infer_instance
  have hW : ∀ k, IsBrownianFiltration (W.W k) ℱ := fun k => usualFiltration_brownian W k
  have hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t :=
    fun t ht => usualFiltration_le_of_nonpos W t ht
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s :=
    fun s hs hz => usualFiltration_null W s hs hz
  obtain ⟨p, hp⟩ := @exists_isEldanCutoff n μ hc hiso Ω _ P _ W ℱ hright hW
    hℱ0 hnull (ballCutoff R) (isCutoff_ballCutoff R)
  exact ⟨Ω, inferInstance, P, inferInstance, W, ℱ, hW, hright, hℱ0, hnull, p, hp⟩

/-- Exact compact cumulant interface consumed by the compact cumulant step, derived
from the cutoff certificate, with arbitrary direction (no unit-vector premise). -/
theorem handoff (d : ℕ) (hd : 1 ≤ d) :
    ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.Isotropic μ →
      FunctionalInequalities.KLS.LogConcave μ →
      IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support →
      ∀ u : EuclideanSpace ℝ (Fin n),
        (∑ J : Fin d → Fin n,
          cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2) ≤
          ((d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d) * ‖u‖ ^ 2 := by
  have h := cumulantBoundCompact_of_cutoffEnergyClaim (K := 153)
    (by norm_num : (0 : ℝ) ≤ 153) (Solutions.LemBklCutoffEnergy.bound d hd)
  intro n μ hiso hLC hc u
  simpa only [envelope_succ_eq] using h n μ hiso hLC hc u

#print axioms exactCertificate
#print axioms actualProcess
#print axioms handoff
end BklCutoffEnergyAudit
