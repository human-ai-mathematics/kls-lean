module

public import FunctionalInequalities.Analysis.Convex.ContactMeasure
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
public import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped RealInnerProductSpace Topology
namespace LetwinContactQuadraticAudit
open FunctionalInequalities.Analysis
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The quadratic reference's actual unit MA equation is constructed; the
unknown convex solution supplies its actual equation, not a Hessian or contact
determinant estimate. -/
theorem quadratic_reference_ae_contact (hn : 0 < n) {u f : E → ℝ}
    (hu : ConvexOn ℝ univ u) (hf : ContinuousOn f (ball 0 1))
    (hfpos : ∀ x ∈ ball (0 : E) 1, 0 < f x)
    (hMAu : ∀ G : Set E, IsOpen G → G ⊆ ball (0 : E) 1 →
      volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y))
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 ≤ ε)
    (hupper : ∀ x ∈ ball (0 : E) 1, f x ≤ (1 + ε) ^ n) :
    ∀ᵐ x ∂(volume.restrict (ball (0 : E) 1)),
      ∃ U B : Matrix (Fin n) (Fin n) ℝ,
        U.PosDef ∧ U.det = f x ∧ B.PosDef ∧ B.det = 1 ∧
        ∀ p : E,
          (∀ᶠ y in 𝓝 x,
            u x - (1 - δ) * quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2) x +
              ⟪p, y - x⟫ ≤
            u y - (1 - δ) * quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2) y) →
          (U - (1 - δ) • B).PosSemidef ∧
            (U - (1 - δ) • B).det ≤ (ε + δ) ^ n := by
  let v : E → ℝ := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)
  have hv := convexOn_quadraticAt Matrix.PosSemidef.one (0 : E) 0 (-1 / 2)
  have hMAv : ∀ G : Set E, IsOpen G → G ⊆ ball (0 : E) 1 →
      volume (subgradientImage v G) = volume G := by
    intro G hG _
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one, Matrix.det_one,
      ENNReal.ofReal_one, one_mul]
    exact hG.measurableSet
  filter_upwards [ae_det_residual_le_on_contact_of_alexandrov_density hn hu hv isOpen_ball
    hf hfpos hMAu hMAv hδ hδ1 hε hupper] with x hx
  obtain ⟨U, B, hU, hdU, hB, hdB, _g, _q, _hgu, _hqv, hc⟩ := hx
  exact ⟨U, B, hU, hdU, hB, hdB, hc⟩

/-- An actual literal-source client: no equation, quadratic expansion or Hessian
estimate for the moment witness is an input. The same normalized transporting
Holder witness is retained. The comparison reference remains given. -/
theorem source_ae_contact_determinant (hn : 0 < n)
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
      ∀ (v : E → ℝ), ConvexOn ℝ univ v → ∀ (Ω : Set E), IsOpen Ω →
        (∀ G : Set E, IsOpen G → G ⊆ Ω →
          volume (subgradientImage v G) = volume G) →
        ∀ (δ ε : ℝ), 0 < δ → δ < 1 → 0 ≤ ε →
          (∀ x ∈ Ω, Real.exp (-u x + W (gradient u x)) ≤ (1 + ε) ^ n) →
          ∀ᵐ x ∂(volume.restrict Ω), ∃ U B : Matrix (Fin n) (Fin n) ℝ,
            U.PosDef ∧ U.det = Real.exp (-u x + W (gradient u x)) ∧
            B.PosDef ∧ B.det = 1 ∧ ∀ p : E,
              (∀ᶠ y in 𝓝 x, u x - (1 - δ) * v x + ⟪p, y - x⟫ ≤ u y - (1 - δ) * v y) →
              (U - (1 - δ) • B).PosSemidef ∧
                (U - (1 - δ) • B).det ≤ (ε + δ) ^ n := by
  obtain ⟨u, L, hs, hl, hn', hm, hC1, he, hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  refine ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, ?_⟩
  intro v hv Ω hΩ hMAv δ ε hδ hδ1 hε hupper
  filter_upwards [ae_det_residual_le_on_contact_of_alexandrov_density hn hs.convexOn hv hΩ
    hf.continuousOn (fun x _ => Real.exp_pos _) (fun G hG _ => hMA G hG)
    hMAv hδ hδ1 hε hupper] with x hx
  obtain ⟨U, B, hU, hdU, hB, hdB, _g, _q, _hgu, _hqv, hc⟩ := hx
  exact ⟨U, B, hU, hdU, hB, hdB, hc⟩

/-- An actual singular residual at a supporting contact, constructed from two
quadratics. Residual PSD is obtained from the contact theorem, not supplied. -/
theorem singular_quadratic_contact (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef ∧
      (0 : Matrix (Fin n) (Fin n) ℝ).det ≤ δ ^ n := by
  let t : ℝ := 1 - δ
  have ht : 0 < t := by dsimp [t]; linarith
  let U : Matrix (Fin n) (Fin n) ℝ := t • 1
  let u : E → ℝ := quadraticAt U 0 0 0
  let v : E → ℝ := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0
  have hU : U.IsHermitian := Matrix.isHermitian_one.smul (IsSelfAdjoint.all t)
  have hu0 : u 0 = 0 := by simp [u, quadraticAt]
  have hv0 : v 0 = 0 := by simp [v, quadraticAt]
  have hu : ∀ η > 0, ∀ᶠ y in 𝓝 (0 : E),
      |u y - quadraticAt U 0 0 (u 0) y| ≤ η * ‖y - 0‖ ^ 2 := by
    intro η hη
    apply Eventually.of_forall
    intro y
    rw [hu0]
    change |u y - u y| ≤ _
    rw [sub_self, abs_zero]
    positivity
  have hv : ∀ η > 0, ∀ᶠ y in 𝓝 (0 : E),
      |v y - quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (v 0) y| ≤ η * ‖y - 0‖ ^ 2 := by
    intro η hη
    apply Eventually.of_forall
    intro y
    rw [hv0]
    change |v y - v y| ≤ _
    rw [sub_self, abs_zero]
    positivity
  have hscale (y : E) : u y = t * v y := by
    dsimp [u, v, U, quadraticAt]
    simp only [map_smul, LinearMap.smul_apply, real_inner_smul_right, inner_zero_left]
    ring
  have hsupport : ∀ᶠ y in 𝓝 (0 : E),
      u 0 - (1 - δ) * v 0 + ⟪(0 : E), y - 0⟫ ≤ u y - (1 - δ) * v y := by
    apply Eventually.of_forall
    intro y
    rw [hscale 0, hscale y]
    simp only [t, sub_self, inner_zero_left, add_zero, le_refl]
  have hdet : U.det ≤ (1 + (0 : ℝ)) ^ n := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, add_zero]
    exact pow_le_pow_left₀ ht.le (by dsimp [t]; linarith : t ≤ 1) n
  have hh := det_residual_le_of_contact_expansions hn hU Matrix.PosDef.one Matrix.det_one
    hu hv hδ hδ1 (by norm_num : (0 : ℝ) ≤ 0) hdet hsupport
  simpa only [U, t, sub_self, zero_add] using hh

end LetwinContactQuadraticAudit
#print axioms FunctionalInequalities.Analysis.posSemidef_of_contact_expansion
#print axioms FunctionalInequalities.Analysis.det_residual_le_of_contact_expansions
#print axioms FunctionalInequalities.Analysis.ae_det_residual_le_on_contact_of_alexandrov_density
#print axioms LetwinContactQuadraticAudit.quadratic_reference_ae_contact
#print axioms LetwinContactQuadraticAudit.source_ae_contact_determinant
#print axioms LetwinContactQuadraticAudit.singular_quadratic_contact
#check LetwinContactQuadraticAudit.singular_quadratic_contact (n := 1)
