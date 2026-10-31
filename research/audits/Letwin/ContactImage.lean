module

public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Convex.ContactImage
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
public import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped RealInnerProductSpace Topology
namespace LetwinContactImageAudit
open FunctionalInequalities.Analysis
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Actual quadratic MA equation, C1 and convexity are constructed, with no
null-image, residual contraction or Lipschitz-factor premise. -/
theorem quadratic_null_contact_image {t : ℝ} (ht : 0 < t)
    {Γ N : Set E} (hΓ : Γ ⊆ ball (0 : E) 1)
    (hc : ∀ x ∈ Γ, ∀ y ∈ ball (0 : E) 1,
      quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 x - (t / 2) * ‖x‖ ^ 2 +
        ⟪gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0) x - t • x, y - x⟫ ≤
      quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 y - (t / 2) * ‖y‖ ^ 2)
    (hN : N ⊆ Γ) (hzero : volume N = 0) :
    volume ((fun x : E =>
      gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0) x - t • x) '' N) = 0 := by
  apply volume_image_residual_eq_zero_of_quadratic_contacts
    (convexOn_quadraticAt Matrix.PosSemidef.one (0 : E) 0 0)
    ((contDiff_quadraticAt _ _ _ _).of_le (by norm_num)) isOpen_ball (C := 1) zero_le_one
    ?_ ht hΓ hc N hN hzero
  intro G hG _
  rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one (0 : E) 0 0 hG.measurableSet,
    Matrix.det_one, ENNReal.ofReal_one, one_mul]

/-- The original literal source chooses one normalized transporting Holder
potential. Its continuous MA density produces the finite upper bound on every
ball; no MA/regularity/null-image estimate of that potential is an input. -/
theorem source_null_contact_image (hn : 0 < n)
    {K : Set E} (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K)
    (hKne : K.Nonempty) {W : E → ℝ} (hW : ContinuousOn W (closure K))
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = volume.withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ContDiff ℝ 1 u ∧ (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient u x) ∧
      (∀ Q : Set E, IsCompact Q → ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
        ∀ x ∈ Q, ∀ y ∈ Q, ‖gradient u y - gradient u x‖ ≤ C * ‖y - x‖ ^ α) ∧
      ∀ (R t : ℝ), 0 < R → 0 < t → ∀ (Γ : Set E), Γ ⊆ ball (0 : E) R →
        (∀ x ∈ Γ, ∀ y ∈ ball (0 : E) R,
          u x - (t / 2) * ‖x‖ ^ 2 + ⟪gradient u x - t • x, y - x⟫ ≤
          u y - (t / 2) * ‖y‖ ^ 2) →
        ∀ N : Set E, N ⊆ Γ → volume N = 0 →
          volume ((fun x => gradient u x - t • x) '' N) = 0 := by
  obtain ⟨u, L, hs, hl, hn', hm, hC1, he, hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  refine ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, ?_⟩
  intro R t _hR ht Γ hΓ hc
  let f : E → ℝ := fun x => Real.exp (-u x + W (gradient u x))
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    hf.continuousOn
  let C : ℝ := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  apply volume_image_residual_eq_zero_of_quadratic_contacts hs.convexOn hC1 isOpen_ball
    hC ?_ ht hΓ hc
  intro G hG hGb
  rw [hMA G hG]
  calc
    ∫⁻ y in G, ENNReal.ofReal (f y) ≤ ∫⁻ _y in G, ENNReal.ofReal C := by
      apply setLIntegral_mono' hG.measurableSet
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      exact (le_abs_self (f y)).trans
        ((hM y (ball_subset_closedBall (hGb hy))).trans (le_max_left _ _))
    _ = ENNReal.ofReal C * volume G := setLIntegral_const G _

/-- The generic theorem also applies in dimension zero, with an actual finite
MA upper bound and supporting contact data. -/
theorem zero_dimensional_client {u : EuclideanSpace ℝ (Fin 0) → ℝ}
    (hu : ConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u)
    {Ω Γ N : Set (EuclideanSpace ℝ (Fin 0))} (hΩ : IsOpen Ω)
    (hMA : ∀ G, IsOpen G → G ⊆ Ω → volume (subgradientImage u G) ≤ volume G)
    {t : ℝ} (ht : 0 < t) (hΓ : Γ ⊆ Ω)
    (hc : ∀ x ∈ Γ, ∀ y ∈ Ω,
      u x - (t / 2) * ‖x‖ ^ 2 + ⟪gradient u x - t • x, y - x⟫ ≤
      u y - (t / 2) * ‖y‖ ^ 2)
    (hN : N ⊆ Γ) (hz : volume N = 0) :
    volume ((fun x => gradient u x - t • x) '' N) = 0 := by
  apply volume_image_residual_eq_zero_of_quadratic_contacts hu hC1 hΩ
    (C := 1) zero_le_one ?_ ht hΓ hc N hN hz
  simpa using hMA

end LetwinContactImageAudit
#print axioms FunctionalInequalities.Analysis.gradient_le_increment
#print axioms FunctionalInequalities.Analysis.volume_image_residual_eq_zero_of_quadratic_contacts
#print axioms LetwinContactImageAudit.quadratic_null_contact_image
#print axioms LetwinContactImageAudit.source_null_contact_image
#print axioms LetwinContactImageAudit.zero_dimensional_client
