import FunctionalInequalities.KLS.BKL.CumulantBound
import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
import FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic
import FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.ToCumulant
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Lean supporting certificate: `lem:bkl-cutoff-energy`

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Sections 4–6, (95), in the
finite-horizon cutoff form. The paper's E_m has m=d+1. The exact half,
(d!)² normalization and a universal K = 153 are retained. The actual proved
compact Letwin constant 8 is used, with no inequality, induction step or
Lyapunov estimate assumed. The cutoff parameter process is a genuine
strong diffusion from the existing Brownian setup and Picard construction.

This is a sufficient alternative localization route for BKL Theorem 4.1;
it does not construct the uncut process, uniqueness or non-explosion,
or prove the literal stochastic identities (68)–(73). No BKL main theorem
or KLS certificate is registered by this supporting endpoint.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities.KLS.BKL FunctionalInequalities.KLS.BKL.Localization
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open scoped RealInnerProductSpace
namespace Solutions.LemBklCutoffEnergy

/-- The named all-order cutoff energy claim, with its actual compact8 input discharged. -/
theorem bound (d : ℕ) (hd : 1 ≤ d) : CutoffEnergyClaim 153 d :=
  cutoffEnergyClaim_153 d hd

/-- BKL (95), explicitly in finite-horizon cutoff form; the uncut assertion is not claimed. -/
theorem certificate (d : ℕ) (hd : 1 ≤ d) :
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
          (d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d + ε := by
  intro n μ hc hiso hLC u hu ε hε T hT
  obtain ⟨R₀, hR₀⟩ := bound d hd n μ hc hiso hLC u hu ε hε T hT
  refine ⟨R₀, ?_⟩
  intro R hR Ω mΩ P inst W ℱ hW hℱ0 hnull p hp
  have h := hR₀ R hR W ℱ hW hℱ0 hnull hp
  simpa only [weightedEnergyIntegral, envelope_succ_eq] using h

/--
info: 'Solutions.LemBklCutoffEnergy.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemBklCutoffEnergy.bound

/--
info: 'Solutions.LemBklCutoffEnergy.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemBklCutoffEnergy.certificate

end Solutions.LemBklCutoffEnergy
