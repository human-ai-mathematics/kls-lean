import FunctionalInequalities.Probability.Conditioning
import FunctionalInequalities.KLS.LogConcave.BallConditioning
import FunctionalInequalities.KLS.BKL.CompactReduction
import FunctionalInequalities.KLS.LogConcave.IsotropicReduction
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation

/-!
# Reduction of the compact Letwin bound to the regular class

`letwinCompactBound_of_regularClass`: if Letwin's quadratic-form bound holds for every isotropic law with density
`1_K e^{-W}` (K a compact convex body, W smooth and κ-strongly convex), it holds for every compactly supported isotropic
log-concave law, i.e. `LetwinCompactBound` (Letwin arXiv:2607.24164v1, Lemma A.1 approximation by Gaussian smoothing,
ball conditioning and whitening).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.KLS.LogConcave.Suspension

private lemma memLp_id_two_of_closedBall_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : ProbabilityMeasure E) {R : ℝ}
    (hs : (ν : Measure E) (closedBall (0 : E) R)ᶜ = 0) :
    MemLp id 2 (ν : Measure E) := by
  refine MemLp.of_bound continuous_id.aestronglyMeasurable R ?_
  filter_upwards [ae_iff.mpr hs] with x hx
  simpa only [id_eq, dist_zero_right] using mem_closedBall.mp hx

private lemma memLp_id_four_of_closedBall_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : ProbabilityMeasure E) {R : ℝ}
    (hs : (ν : Measure E) (closedBall (0 : E) R)ᶜ = 0) :
    MemLp id 4 (ν : Measure E) := by
  refine MemLp.of_bound continuous_id.aestronglyMeasurable R ?_
  filter_upwards [ae_iff.mpr hs] with x hx
  simpa only [id_eq, dist_zero_right] using mem_closedBall.mp hx

private lemma integrable_continuous_of_closedBall_support
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ν : ProbabilityMeasure E) {R : ℝ}
    (hs : (ν : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    {f : E → F} (hf : Continuous f) :
    Integrable f (ν : Measure E) := by
  have ha : ∀ᵐ x ∂(ν : Measure E), x ∈ closedBall (0 : E) R :=
    ae_iff.mpr hs
  have hi := hf.continuousOn.integrableOn_compact
    (μ := (ν : Measure E)) (isCompact_closedBall (0 : E) R)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hi

/-- **Reduction of the compact Letwin bound to Letwin's regular class** (Letwin arXiv:2607.24164v1, Lemma A.1): if every isotropic law `1_K e^{−W} dx` with `K` compact convex with nonempty interior and `W` smooth and
uniformly convex satisfies Letwin's quadratic bound, then so does every compactly supported isotropic log-concave law
in positive dimension (`LetwinCompactBound`). -/
theorem letwinCompactBound_of_regularClass
    (h : ∀ (n : ℕ), 0 < n → ∀ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ)
      (κ : ℝ), 0 < κ → IsCompact K → Convex ℝ K → (interior K).Nonempty → ContDiff ℝ ∞ W →
      ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) →
      ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        (μ : Measure (EuclideanSpace ℝ (Fin n))) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
            (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) →
        KLS.Isotropic μ → LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    LetwinCompactBound := by
  classical
  intro n hn μ hLC hiso hcompact
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨r, hr⟩ :=
    Bornology.IsBounded.subset_closedBall hcompact.isBounded (0 : E)
  let r₀ : ℝ := max r 0
  let R : ℝ := r₀ + 1
  have hr₀_nonneg : 0 ≤ r₀ := le_max_right r 0
  have hr₀ : (μ : Measure E) (closedBall (0 : E) r₀)ᶜ = 0 := by
    have hsub : (μ : Measure E).support ⊆ closedBall (0 : E) r₀ :=
      hr.trans (closedBall_subset_closedBall (le_max_left r 0))
    exact measure_mono_null (compl_subset_compl.mpr hsub)
      Measure.measure_compl_support
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hrR : r₀ < R := by
    dsimp [R]
    linarith
  have hμR : (μ : Measure E) (closedBall (0 : E) R)ᶜ = 0 :=
    measure_mono_null
      (compl_subset_compl.mpr (closedBall_subset_closedBall hrR.le)) hr₀
  obtain ⟨ρ, hρ⟩ :=
    KLS.LogConcave.exists_isBorellDensity_of_isotropic hLC hiso
  obtain ⟨k, _hk, _hkpos, _hkδ, hkV, _hkupper, hweak, _hmean, _hsecond, _hcov⟩ :=
    KLS.LogConcave.GaussianSmoothing.exists_regularSeq_limits hρ hiso.memLp_two
  let ν : ℕ → ProbabilityMeasure E :=
    fun j => KLS.LogConcave.GaussianSmoothing.regularSeq hρ j (k j)
  have hνV (j : ℕ) :
      KLS.RegularPotential
        (KLS.LogConcave.GaussianSmoothing.quadraticPotential ρ
          ((j : ℝ) + 1)
          (KLS.LogConcave.GaussianSmoothing.tiltRate (k j)))
        (KLS.LogConcave.GaussianSmoothing.tiltRate (k j))
        (2 * ((j : ℝ) + 1) +
          KLS.LogConcave.GaussianSmoothing.tiltRate (k j)) :=
    hkV j
  have hνeq (j : ℕ) : ν j = (hνV j).law := rfl
  have hweak' : Tendsto ν atTop (𝓝 μ) := hweak
  have hνball (j : ℕ) :
      0 < (ν j : Measure E) (closedBall (0 : E) R) := by
    rw [hνeq j]
    have hv :
        0 < (volume : Measure E) (closedBall (0 : E) R) :=
      Measure.measure_pos_of_mem_nhds volume
        (closedBall_mem_nhds (0 : E) hR)
    have hac :
        (volume : Measure E) ≪ ((hνV j).law : Measure E) :=
      MeasureTheory.absolutelyContinuous_tilted (hνV j).integrable_exp_neg
    by_contra hz
    have hz' : ((hνV j).law : Measure E) (closedBall (0 : E) R) = 0 :=
      nonpos_iff_eq_zero.mp (le_of_not_gt hz)
    exact (ne_of_gt hv) (hac hz')
  let lam : ℕ → ProbabilityMeasure E := fun j =>
    ⟨ProbabilityTheory.cond (ν j : Measure E) (closedBall (0 : E) R),
      ProbabilityTheory.cond_isProbabilityMeasure (ne_of_gt (hνball j))⟩
  have hlam (j : ℕ) :
      (lam j : Measure E) =
        ProbabilityTheory.cond (ν j : Measure E) (closedBall (0 : E) R) :=
    rfl
  have hlam_supp (j : ℕ) :
      (lam j : Measure E) (closedBall (0 : E) R)ᶜ = 0 := by
    rw [hlam j, ProbabilityTheory.cond_apply measurableSet_closedBall]
    simp
  have hlam_mom :
      ∀ d ≤ 4, ∀ v : Fin d → E,
        Tendsto
          (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam j : Measure E))
          atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by
    intro d _hd v
    exact FunctionalInequalities.KLS.tendsto_integral_cond_closedBall
      hweak' hrR hr₀ (by fun_prop)
  obtain ⟨L, c, hwhite, hwhmom⟩ :=
    FunctionalInequalities.KLS.exists_whitening_tendsto_moments
      hiso hlam_supp hμR hlam_mom
  let η : ℕ → ProbabilityMeasure E := fun j =>
    MeasureTheory.ProbabilityMeasure.map (lam j)
      (by fun_prop :
        AEMeasurable (fun x : E => L j (x - c j)) (lam j : Measure E))
  have hηsupp (j : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧
        (η j : Measure E) (closedBall (0 : E) C)ᶜ = 0 := by
    let f : E → E := fun x => L j (x - c j)
    have hf : Continuous f := by fun_prop
    obtain ⟨C₀, hC₀⟩ :=
      (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf.continuousOn
    let C : ℝ := max C₀ 0
    refine ⟨C, le_max_right _ _, ?_⟩
    change (Measure.map f (lam j : Measure E)) (closedBall (0 : E) C)ᶜ = 0
    rw [Measure.map_apply hf.measurable measurableSet_closedBall.compl]
    refine measure_mono_null (t := (closedBall (0 : E) R)ᶜ) ?_ (hlam_supp j)
    intro x hx hxR
    apply hx
    rw [mem_closedBall, dist_zero_right]
    exact (hC₀ x hxR).trans (le_max_left _ _)
  have hηmem2 (j : ℕ) : MemLp id 2 (η j : Measure E) := by
    obtain ⟨C, _hC, hs⟩ := hηsupp j
    exact memLp_id_two_of_closedBall_support (η j) hs
  have hηmem4 (j : ℕ) : MemLp id 4 (η j : Measure E) := by
    obtain ⟨C, _hC, hs⟩ := hηsupp j
    exact memLp_id_four_of_closedBall_support (η j) hs
  have hηintegral {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (j : ℕ) {f : E → F} (hf : Continuous f) :
      ∫ y, f y ∂(η j : Measure E) =
        ∫ x, f (L j (x - c j)) ∂(lam j : Measure E) := by
    let g : E → E := fun x => L j (x - c j)
    have hg : Continuous g := by fun_prop
    change (∫ y, f y ∂Measure.map g (lam j : Measure E)) =
      ∫ x, f (g x) ∂(lam j : Measure E)
    exact MeasureTheory.integral_map hg.aemeasurable hf.aestronglyMeasurable
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hwhite
  have hηiso (j : ℕ) (hj : j₀ ≤ j) : KLS.Isotropic (η j) := by
    have hwj := hj₀ j hj
    apply KLS.isotropic_of_moments (η j) (hηmem2 j)
    · exact (hηintegral j (f := fun x : E => x) continuous_id).trans hwj.1
    · intro u v
      exact (hηintegral j
        (f := fun x : E => ⟪u, x⟫ * ⟪v, x⟫) (by fun_prop)).trans (hwj.2 u v)
  have hηmom :
      ∀ d ≤ 4, ∀ v : Fin d → E,
        Tendsto
          (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(η j : Measure E))
          atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by
    intro d hd v
    apply (hwhmom d hd v).congr'
    filter_upwards [] with j
    exact (hηintegral j
      (f := fun x : E => ∏ i, ⟪v i, x⟫) (by fun_prop)).symm
  have hηgood (j : ℕ) (hj : j₀ ≤ j) :
      LetwinQuadraticBound (η j : Measure E) := by
    obtain ⟨K, W, κ, hκ, hK, hKconv, hKint, hW, hWconv, hmap⟩ :=
      FunctionalInequalities.KLS.exists_regularClass_of_cond_closedBall_map
        (hνV j) hR (L j) (c j)
    refine h n hn K W κ hκ hK hKconv hKint hW hWconv (η j) ?_ (hηiso j hj)
    change
      Measure.map (fun x : E => L j (x - c j))
          (ProbabilityTheory.cond (ν j : Measure E) (closedBall (0 : E) R)) =
        (volume : Measure E).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))
    rw [hνeq j]
    exact hmap
  let ζ : ℕ → ProbabilityMeasure E := fun j =>
    if j₀ ≤ j then η j else η j₀
  have hζmem (j : ℕ) : MemLp id 4 (ζ j : Measure E) := by
    by_cases hj : j₀ ≤ j
    · simpa [ζ, hj] using hηmem4 j
    · simpa [ζ, hj] using hηmem4 j₀
  have hζbound (j : ℕ) : LetwinQuadraticBound (ζ j : Measure E) := by
    by_cases hj : j₀ ≤ j
    · simpa [ζ, hj] using hηgood j hj
    · simpa [ζ, hj] using hηgood j₀ le_rfl
  have hζmom :
      ∀ d ≤ 4, ∀ v : Fin d → E,
        Tendsto
          (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(ζ j : Measure E))
          atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by
    intro d hd v
    apply (hηmom d hd v).congr'
    filter_upwards [eventually_ge_atTop j₀] with j hj
    simp [ζ, hj]
  have hμmem : MemLp id 4 (μ : Measure E) :=
    memLp_id_four_of_closedBall_support μ hμR
  exact
    FunctionalInequalities.Analysis.BakryEmery.letwinQuadraticBound_of_tendsto_moments
      (fun j => (ζ j : Measure E)) (μ : Measure E) hζmem hμmem hζmom hζbound

end FunctionalInequalities.KLS.LogConcave.Suspension
