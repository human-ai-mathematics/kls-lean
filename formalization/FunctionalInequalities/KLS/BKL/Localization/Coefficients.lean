import FunctionalInequalities.KLS.BKL.PosteriorCovariance
import FunctionalInequalities.Probability.Diffusion.Generator
import FunctionalInequalities.Probability.Diffusion.Cutoff

/-!
# Coefficients and generator of the Eldan localization equations

Bizeul–Klartag–Lehec arXiv:2610.05474v1, (67), compact-prior stage: the parameter space `p = (c, Q)`, the posterior
covariance `A(p)`, the drift `(A⁻¹ a, A⁻¹)`, the noise columns `(A^{-1/2} e_k, 0)`, the generator
`𝓛F = DF[(A⁻¹a, A⁻¹)] + ½ Σ_k D²F[(A^{-1/2}e_k, 0), (A^{-1/2}e_k, 0)]`, and the cutoff coefficients
`γ² · drift`, `γ · noise` for an admissible cutoff `γ`. Definitions only; statements and placement: Claude
(BKL Claude-controller goal).
-/

noncomputable section

open MeasureTheory
open scoped NNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

/-- Parameter space `p = (c, Q)` of the Eldan localization equations (BKL arXiv:2610.05474v1, (67));
`Q` is not required to be symmetric. -/
abbrev Param (n : ℕ) :=
  EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/-- The posterior covariance `A(p) = Cov μ_{c,Q}`. -/
def cov (p : Param n) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))

/-- Drift of (67): `(A⁻¹ a, A⁻¹)`. -/
def drift (p : Param n) : Param n :=
  (Ring.inverse (cov μ hc p) (posteriorMean μ p.1 p.2), Ring.inverse (cov μ hc p))

/-- Noise columns of (67): `(A^{-1/2} e_k, 0)`. -/
def noise (p : Param n) (k : Fin n) : Param n :=
  (inverseSqrt (cov μ hc p) (EuclideanSpace.single k 1), 0)

/-- The generator `𝓛` of (67): `𝓛F = DF[(A⁻¹a, A⁻¹)] + ½ Σ_k D²F[(A^{-1/2}e_k, 0), (A^{-1/2}e_k, 0)]`. -/
def generator (F : Param n → ℝ) (p : Param n) : ℝ :=
  diffusionGenerator (drift μ hc) (noise μ hc) F p

/-- Cutoff drift `γ² · (A⁻¹ a, A⁻¹)`. -/
def cutoffDrift (γ : Param n → ℝ) (p : Param n) : Param n := (γ p) ^ 2 • drift μ hc p

/-- Cutoff noise `γ · (A^{-1/2} e_k, 0)`. -/
def cutoffNoise (γ : Param n → ℝ) (p : Param n) (k : Fin n) : Param n := γ p • noise μ hc p k

/-- An admissible cutoff: Lipschitz, compactly supported, `[0, 1]`-valued. -/
structure IsCutoff (γ : Param n → ℝ) : Prop where
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K γ
  compactSupport : HasCompactSupport γ
  mem_Icc : ∀ p, γ p ∈ Set.Icc (0 : ℝ) 1

end FunctionalInequalities.KLS.BKL.Localization
