import FunctionalInequalities.KLS.Klartag.LinearBounds
import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.Analysis.Convex.PointwiseCompactness
import FunctionalInequalities.Analysis.Convex.SecondOrder.Difference
import FunctionalInequalities.Analysis.Convex.Subgradient.Stability
import FunctionalInequalities.Analysis.Convex.Subgradient.Existence
import FunctionalInequalities.Probability.MomentMeasure.Gradient
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Limits of centered convex potentials and their moment measures

Klartag, *Logarithmically-concave moment measures I*, arXiv:1309.2767v1, Proposition 2.1
(continuity of the moment measure), for convex `L`-Lipschitz `C¹` potentials `ψ_l` on a
finite-dimensional real inner-product space with an additive Haar measure `m`.

* Direction (i) ⇒ (ii), with the uniform linear lower bound `α‖x‖ - β ≤ ψ_l(x)` (`α > 0`) as an
  input (in the paper it comes from Lemma 2.2): pointwise convergence `ψ_l → F` gives
  `∫ b(∇ψ_l) e^{-ψ_l} → ∫ b(∇F) e^{-F}` for bounded continuous `b`
  (`MomentMeasure.tendsto_integral_comp_gradient_mul_exp_neg`). Gradients converge wherever the
  limit is differentiable (Rockafellar, Theorem 24.5;
  `Analysis.tendsto_gradient_of_tendsto_of_convexOn`), hence almost everywhere by Rademacher.
* The compactness step of (ii) ⇒ (i): uniform two-sided linear bounds give a pointwise
  convergent subsequence with convex limit (`Analysis.exists_subseq_tendsto_of_linear_bounds`);
  with a uniform second-difference bound `C‖h‖²` and `μ_l → ν` weakly, the limit is a convex,
  `L`-Lipschitz, `C¹`, centered potential with `4C`-Lipschitz gradient whose moment measure is `ν`
  (`MomentMeasure.exists_limit_potential`).

For normalized potentials on `ℝⁿ`, the potential of an isotropic law whose gradient is bounded by
`R` satisfies Klartag's nondegeneracy (13) with `ε = 1/R`
(`MomentMeasure.inv_le_integral_abs_inner_gradient_of_isotropic`); translation and centering of
such potentials are in `Probability/MomentMeasure/Gradient.lean`.

Scope / not proved: the uniqueness step of (ii) ⇒ (i) (uniqueness of moment-measure potentials,
Cordero-Erausquin–Klartag) is not formalized, so the limit potential is produced, not identified
with a given potential, and convergence of the whole sequence is not asserted. The paper's
`Ω`-supported moment measures and continuous test functions on `Ω` are replaced by weak
convergence of probability measures and bounded continuous test functions; the potentials are
assumed `C¹`.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `e^{-(α‖x‖ - β)} ‖x‖^k` is integrable for an additive Haar measure and `α > 0`. -/
private theorem integrable_exp_neg_sub_mul_norm_pow (m : Measure E) [m.IsAddHaarMeasure]
    {α : ℝ} (hα : 0 < α) (β : ℝ) (k : ℕ) :
    Integrable (fun x : E => Real.exp (-(α * ‖x‖ - β)) * ‖x‖ ^ k) m := by
  refine ((integrable_norm_pow_mul_exp_neg_mul_norm m hα k).const_mul (Real.exp β)).congr
    (ae_of_all m fun x => ?_)
  simp only
  rw [show -(α * ‖x‖ - β) = β + -(α * ‖x‖) by ring, Real.exp_add]
  ring

/-- **Klartag arXiv:1309.2767v1, Proposition 2.1, (i) ⇒ (ii)**, with the uniform linear lower
bound as input: if convex Lipschitz `C¹` potentials `ψ l` converge pointwise to `F` and satisfy
`α‖x‖ - β ≤ ψ l x` with `α > 0`, then `∫ b(∇ψ_l) e^{-ψ_l} → ∫ b(∇F) e^{-F}` for every bounded
continuous `b`. -/
theorem tendsto_integral_comp_gradient_mul_exp_neg (m : Measure E) [m.IsAddHaarMeasure]
    {ψ : ℕ → E → ℝ} {F : E → ℝ} {L : NNReal} {α β : ℝ} (hα : 0 < α)
    (hψ : ∀ l, ConvexOn ℝ univ (ψ l)) (hC1 : ∀ l, ContDiff ℝ 1 (ψ l))
    (hLip : ∀ l, LipschitzWith L (ψ l))
    (hlow : ∀ l x, α * ‖x‖ - β ≤ ψ l x)
    (hlim : ∀ y, Tendsto (fun l => ψ l y) atTop (𝓝 (F y))) (b : BoundedContinuousFunction E ℝ) :
    Tendsto (fun l => ∫ x, b (gradient (ψ l) x) * Real.exp (-ψ l x) ∂m) atTop
      (𝓝 (∫ x, b (gradient F x) * Real.exp (-F x) ∂m)) := by
  have hLF : LipschitzWith L F := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    exact le_of_tendsto ((hlim x).dist (hlim y))
      (Eventually.of_forall fun l => (hLip l).dist_le_mul x y)
  have hdψ (l : ℕ) : Differentiable ℝ (ψ l) :=
    (hC1 l).differentiable (by norm_num)
  have hGψ (l : ℕ) : Continuous (gradient (ψ l)) :=
    Analysis.BakryEmery.continuous_gradient (hC1 l)
  let D : E → ℝ := fun x => Real.exp (-(α * ‖x‖ - β))
  have hD : Integrable D m := by
    simpa only [pow_zero, mul_one] using integrable_exp_neg_sub_mul_norm_pow m hα β 0
  have hdom (l : ℕ) (x : E) : Real.exp (-ψ l x) ≤ D x :=
    Real.exp_le_exp.mpr (neg_le_neg (hlow l x))
  apply tendsto_integral_of_dominated_convergence (fun x => ‖b‖ * D x)
  · intro l
    exact ((b.continuous.comp (hGψ l)).mul
      (Real.continuous_exp.comp (hLip l).continuous.neg)).aestronglyMeasurable
  · exact hD.const_mul ‖b‖
  · intro l
    exact ae_of_all m fun x => by
      change ‖b (gradient (ψ l) x) * Real.exp (-ψ l x)‖ ≤ ‖b‖ * D x
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      calc
        ‖b (gradient (ψ l) x)‖ * Real.exp (-ψ l x)
            ≤ ‖b‖ * Real.exp (-ψ l x) :=
          mul_le_mul_of_nonneg_right (b.norm_coe_le_norm _) (Real.exp_nonneg _)
        _ ≤ ‖b‖ * D x :=
          mul_le_mul_of_nonneg_left (hdom l x) (norm_nonneg b)
  · filter_upwards [hLF.ae_differentiableAt (μ := m)] with x hx
    have hg :
        Tendsto (fun l => gradient (ψ l) x) atTop (𝓝 (gradient F x)) :=
      Analysis.tendsto_gradient_of_tendsto_of_convexOn hψ hlim hx (fun l => hdψ l x)
    exact ((b.continuous.tendsto (gradient F x)).comp hg).mul
      ((Real.continuous_exp.tendsto (-F x)).comp (hlim x).neg)

/-- **The limit potential** (the compactness step of Klartag arXiv:1309.2767v1, Proposition 2.1,
(ii) ⇒ (i), without the uniqueness step). If `C¹` convex `L`-Lipschitz centered potentials of the
probability measures `μ l` have uniform two-sided linear bounds and uniform second-difference
bounds `C‖h‖²`, and `μ l → ν` weakly, then some convex `L`-Lipschitz `C¹` centered `F` with
`4C`-Lipschitz gradient and the same second-difference bound has moment measure `ν`. -/
theorem exists_limit_potential (m : Measure E) [m.IsAddHaarMeasure]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E} (hμν : Tendsto μ atTop (𝓝 ν))
    {ψ : ℕ → E → ℝ} {L : NNReal} {α β γ C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hψ : ∀ l, ConvexOn ℝ univ (ψ l)) (hC1 : ∀ l, ContDiff ℝ 1 (ψ l))
    (hLip : ∀ l, LipschitzWith L (ψ l))
    (hnorm : ∀ l, ∫ x, Real.exp (-ψ l x) ∂m = 1) (hbar : ∀ l, ∫ x, Real.exp (-ψ l x) • x ∂m = 0)
    (hmap : ∀ l, (m.tilted (-ψ l)).map (gradient (ψ l)) = (μ l : Measure E))
    (hb : ∀ l x, α * ‖x‖ - β ≤ ψ l x ∧ ψ l x ≤ (L : ℝ) * ‖x‖ + γ)
    (hsd : ∀ l x h, ψ l (x + h) + ψ l (x - h) - 2 * ψ l x ≤ C * ‖h‖ ^ 2) :
    ∃ F : E → ℝ, ConvexOn ℝ univ F ∧ LipschitzWith L F ∧ ContDiff ℝ 1 F ∧
      ∫ x, Real.exp (-F x) ∂m = 1 ∧ ∫ x, Real.exp (-F x) • x ∂m = 0 ∧
      (m.tilted (-F)).map (gradient F) = (ν : Measure E) ∧
      LipschitzWith (Real.toNNReal (4 * C)) (gradient F) ∧
      ∀ x h, F (x + h) + F (x - h) - 2 * F x ≤ C * ‖h‖ ^ 2 := by
  obtain ⟨s, F, hs, hconv, hlim⟩ :=
    Analysis.exists_subseq_tendsto_of_linear_bounds hψ hα.le hb
  have hLF : LipschitzWith L F := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    exact le_of_tendsto ((hlim x).dist (hlim y))
      (Eventually.of_forall fun j => (hLip (s j)).dist_le_mul x y)
  have hlo (x : E) : α * ‖x‖ - β ≤ F x :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (hlim x)
      (Eventually.of_forall fun j => (hb (s j) x).1)
  have hSF : ∀ x h, F (x + h) + F (x - h) - 2 * F x ≤ C * ‖h‖ ^ 2 := by
    intro x h
    exact le_of_tendsto
      (((hlim (x + h)).add (hlim (x - h))).sub ((hlim x).const_mul 2))
      (Eventually.of_forall fun j => hsd (s j) x h)
  have hdψ (l : ℕ) : Differentiable ℝ (ψ l) :=
    (hC1 l).differentiable (by norm_num)
  have hsupp (x : E) : ∃ p : E, ∀ y, F x + ⟪p, y - x⟫ ≤ F y :=
    (Analysis.exists_subgradient_slope_le_inner_add hconv x 0).imp fun _ h => h.1
  have hdF : Differentiable ℝ F :=
    fun x => Analysis.differentiableAt_of_second_difference_le hsupp hC hSF x
  have hGF := Analysis.lipschitzWith_gradient_of_second_difference_le hconv hdF hC hSF
  have hCF : ContDiff ℝ 1 F := by
    apply contDiff_one_iff_fderiv.2
    refine ⟨hdF, ?_⟩
    have he :
        fderiv ℝ F = fun x => (InnerProductSpace.toDual ℝ E) (gradient F x) := by
      funext x
      exact (hdF x).hasGradientAt.hasFDerivAt.fderiv
    rw [he]
    exact (InnerProductSpace.toDual ℝ E).continuous.comp hGF.continuous
  have hGψ (l : ℕ) :
      LipschitzWith (Real.toNNReal (4 * C)) (gradient (ψ l)) :=
    Analysis.lipschitzWith_gradient_of_second_difference_le (hψ l) (hdψ l) hC (hsd l)
  have hgrad (x : E) :
      Tendsto (fun j => gradient (ψ (s j)) x) atTop (𝓝 (gradient F x)) :=
    Analysis.tendsto_gradient_of_tendsto_of_convexOn
      (fun j => hψ (s j)) hlim (hdF x) (fun j => hdψ (s j) x)
  let D : E → ℝ := fun x => Real.exp (-(α * ‖x‖ - β))
  have hD : Integrable D m := by
    simpa only [pow_zero, mul_one] using integrable_exp_neg_sub_mul_norm_pow m hα β 0
  have hDx : Integrable (fun x => D x * ‖x‖) m := by
    simpa only [pow_one] using integrable_exp_neg_sub_mul_norm_pow m hα β 1
  have hdom (j : ℕ) (x : E) : Real.exp (-ψ (s j) x) ≤ D x :=
    Real.exp_le_exp.mpr (neg_le_neg (hb (s j) x).1)
  have hdomF (x : E) : Real.exp (-F x) ≤ D x :=
    Real.exp_le_exp.mpr (neg_le_neg (hlo x))
  have hIF : Integrable (fun x => Real.exp (-F x)) m := by
    apply hD.mono' (Real.continuous_exp.comp hLF.continuous.neg).aestronglyMeasurable
    exact ae_of_all m fun x => by
      change ‖Real.exp (-F x)‖ ≤ D x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      exact hdomF x
  have hsubψ := tendsto_integral_comp_gradient_mul_exp_neg m hα (fun j => hψ (s j))
    (fun j => hC1 (s j)) (fun j => hLip (s j)) (fun j x => (hb (s j) x).1) hlim
  have hnormlim := hsubψ (BoundedContinuousFunction.const E (1 : ℝ))
  simp only [BoundedContinuousFunction.const_apply, one_mul] at hnormlim
  have hnF : ∫ x, Real.exp (-F x) ∂m = 1 := by
    apply tendsto_nhds_unique hnormlim
    simpa only [hnorm] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hbarlim :
      Tendsto (fun j => ∫ x, Real.exp (-ψ (s j) x) • x ∂m) atTop
        (𝓝 (∫ x, Real.exp (-F x) • x ∂m)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => D x * ‖x‖)
    · intro j
      exact ((Real.continuous_exp.comp (hLip (s j)).continuous.neg).smul
        continuous_id).aestronglyMeasurable
    · exact hDx
    · intro j
      exact ae_of_all m fun x => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        exact mul_le_mul_of_nonneg_right (hdom j x) (norm_nonneg x)
    · exact ae_of_all m fun x =>
        ((Real.continuous_exp.tendsto (-F x)).comp (hlim x).neg).smul
          tendsto_const_nhds
  have hbF : ∫ x, Real.exp (-F x) • x ∂m = 0 := by
    apply tendsto_nhds_unique hbarlim
    simpa only [hbar] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 0))
  have : IsProbabilityMeasure (m.tilted (-F)) := isProbabilityMeasure_tilted (f := -F) hIF
  have : IsProbabilityMeasure ((m.tilted (-F)).map (gradient F)) :=
    Measure.isProbabilityMeasure_map hGF.continuous.aemeasurable
  let η : ProbabilityMeasure E := ⟨(m.tilted (-F)).map (gradient F), inferInstance⟩
  have hη : Tendsto (fun j => μ (s j)) atTop (𝓝 η) := by
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun b => ?_
    have hj (j : ℕ) :
        (∫ x, b x ∂(μ (s j) : Measure E)) =
          ∫ x, b (gradient (ψ (s j)) x) * Real.exp (-ψ (s j) x) ∂m := by
      rw [← hmap (s j), integral_map (hGψ (s j)).continuous.aemeasurable
        b.continuous.aestronglyMeasurable, integral_tilted]
      simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul, mul_comm]
    have hηint :
        (∫ x, b x ∂(η : Measure E)) = ∫ x, b (gradient F x) * Real.exp (-F x) ∂m := by
      change (∫ x, b x ∂(m.tilted (-F)).map (gradient F)) = _
      rw [integral_map hGF.continuous.aemeasurable b.continuous.aestronglyMeasurable,
        integral_tilted]
      simp only [Pi.neg_apply, hnF, div_one, smul_eq_mul, mul_comm]
    simpa only [hj, hηint] using hsubψ b
  have hην : η = ν :=
    tendsto_nhds_unique hη (hμν.comp hs.tendsto_atTop)
  have hmapF : (m.tilted (-F)).map (gradient F) = (ν : Measure E) :=
    congrArg (fun p : ProbabilityMeasure E => (p : Measure E)) hην
  exact ⟨F, hconv, hLF, hCF, hnF, hbF, hmapF, hGF, hSF⟩

section Euclidean

/-- **Klartag's nondegeneracy (13)** with `ε = 1/R` for the potential `u` of an isotropic law whose
gradient is bounded by `R` (`‖∇u‖ ≤ R`). -/
theorem inv_le_integral_abs_inner_gradient_of_isotropic {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u)
    (hnorm : (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hiso : FunctionalInequalities.KLS.Isotropic ν)
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (ν : Measure (EuclideanSpace ℝ (Fin n))))
    {R : ℝ} (hR : 0 < R) (hsupp : ∀ x, ‖gradient u x‖ ≤ R)
    {θ : EuclideanSpace ℝ (Fin n)} (hθ : ‖θ‖ = 1) :
    1 / R ≤ ∫ x, |⟪gradient u x, θ⟫| * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hg : Continuous (gradient u) := Analysis.BakryEmery.continuous_gradient hu
  have hball : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), ‖y‖ ≤ R := by
    have hc : IsClosed {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ R} :=
      isClosed_le continuous_norm continuous_const
    have hm : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ¬ ‖y‖ ≤ R} :=
      hc.measurableSet.compl
    rw [ae_iff, ← hmap, Measure.map_apply hg.measurable hm]
    have hempty :
        (gradient u) ⁻¹' {y | ¬ ‖y‖ ≤ R} = ∅ := by
      ext x
      simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_not_intro (hsupp x)
    rw [hempty, measure_empty]
  have habs :
      ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), |⟪θ, y⟫| ≤ R := by
    filter_upwards [hball] with y hy
    calc
      |⟪θ, y⟫| ≤ ‖θ‖ * ‖y‖ := abs_real_inner_le_norm _ _
      _ = ‖y‖ := by rw [hθ, one_mul]
      _ ≤ R := hy
  have hi : Integrable (fun y => |⟪θ, y⟫|)
      (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply (integrable_const R).mono'
      (continuous_const.inner continuous_id).abs.aestronglyMeasurable
    filter_upwards [habs] with y hy
    simpa only [Real.norm_eq_abs, abs_abs] using hy
  have hpoint :
      ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))),
        ⟪θ, y⟫ ^ 2 ≤ R * |⟪θ, y⟫| := by
    filter_upwards [habs] with y hy
    calc
      ⟪θ, y⟫ ^ 2 = |⟪θ, y⟫| * |⟪θ, y⟫| := by
        rw [← pow_two, sq_abs]
      _ ≤ R * |⟪θ, y⟫| :=
        mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  have hsq : Integrable (fun y => ⟪θ, y⟫ ^ 2)
      (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply (hi.const_mul R).mono'
      ((continuous_const.inner continuous_id).pow 2).aestronglyMeasurable
    filter_upwards [hpoint] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (⟪θ, y⟫ : ℝ))]
    exact hy
  have hsecond :
      (∫ y, ⟪θ, y⟫ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) = 1 := by
    simpa [pow_two, real_inner_self_eq_norm_sq, hθ] using
      hiso.integral_inner_mul_inner θ θ
  have hineq :
      1 ≤ R * ∫ y, |⟪θ, y⟫| ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      1 = ∫ y, ⟪θ, y⟫ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) :=
        hsecond.symm
      _ ≤ ∫ y, R * |⟪θ, y⟫| ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) :=
        integral_mono_ae hsq (hi.const_mul R) hpoint
      _ = R * ∫ y, |⟪θ, y⟫| ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
        rw [integral_const_mul]
  have hchange :
      (∫ y, |⟪θ, y⟫| ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, |⟪gradient u x, θ⟫| * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [← hmap, integral_map hg.measurable.aemeasurable
      (continuous_const.inner continuous_id).abs.aestronglyMeasurable, integral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul, mul_comm, real_inner_comm θ]
  rw [hchange] at hineq
  apply (div_le_iff₀ hR).2
  simpa only [mul_comm] using hineq

end Euclidean

end FunctionalInequalities.Probability.MomentMeasure
