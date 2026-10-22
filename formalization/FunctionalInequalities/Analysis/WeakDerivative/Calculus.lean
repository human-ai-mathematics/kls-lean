import FunctionalInequalities.Analysis.WeakDerivative.Approximation
import FunctionalInequalities.Analysis.Cutoff.SmoothBall
import FunctionalInequalities.Analysis.WeakDerivative.Basic
import FunctionalInequalities.Analysis.WeakDerivative.Mollification
import FunctionalInequalities.Analysis.Cutoff.Profile

/-!
# Weak products, chain rule and rough testing

Existing names and statements are preserved. The bounded cutoff power tests need nonnegativity only a.e. on the cutoff
support (`local_rpow_cutoff_weak_data`, `local_rpow_cutoff_weak_test`); the globally nonnegative versions are their
consumers. `exists_bounded_weak_log_extension` gives one bounded weak extension of `log (δ + max w 0)` that agrees with it
on every domain where `w ≥ 0`.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

section WeakProducts

open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology

namespace FunctionalInequalities.Analysis


private lemma tendsto_integral_mul_of_l2
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → ℝ} {u : ℕ → X → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hu : ∀ m, MemLp (u m) 2 μ)
    (hconv : Tendsto (fun m => eLpNorm (u m - b) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, a x * u m x ∂μ) atTop
      (𝓝 (∫ x, a x * b x ∂μ)) := by
  have hp {z : X → ℝ} (hz : MemLp z 2 μ) :
      inner ℝ (ha.toLp a) (hz.toLp z) = ∫ x, a x * z x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hz.coeFn_toLp] with x hx hz'
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, hz']
    exact mul_comm _ _
  have ht :
      Tendsto (fun m => (hu m).toLp (u m)) atTop (𝓝 (hb.toLp b)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu b hb).2 hconv
  have hi :
      Tendsto (fun m => inner ℝ (ha.toLp a) ((hu m).toLp (u m)))
        atTop (𝓝 (inner ℝ (ha.toLp a) (hb.toLp b))) :=
    tendsto_const_nhds.inner ht
  simpa only [hp] using hi

set_option maxHeartbeats 800000 in
/-- Scalar weak product rule: global L2 factors and directional derivatives
produce a locally integrable product and its actual weak derivative. -/
theorem HasWeakDerivAlong.mul_of_memLp_two {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : MemLp df 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg2 : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdg2 : MemLp dg 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v := by
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun m =>
    { rIn := (1 / ((m : ℝ) + 1)) / 2
      rOut := 1 / ((m : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hr : 0 < 1 / ((m : ℝ) + 1) := by positivity
        linarith }
  have hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    change Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let gm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  let dgm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] dg
  have hgm2 (m : ℕ) :
      MemLp (gm m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Mollification.memLp_convolution (φ m) hg2
  have hdgm2 (m : ℕ) :
      MemLp (dgm m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Mollification.memLp_convolution (φ m) hdg2
  have hgmconv :
      Tendsto (fun m => eLpNorm (gm m - g) 2 volume) atTop (𝓝 0) :=
    Mollification.tendsto_eLpNorm_convolution_sub hφ hg2
  have hdgmconv :
      Tendsto (fun m => eLpNorm (dgm m - dg) 2 volume) atTop (𝓝 0) :=
    Mollification.tendsto_eLpNorm_convolution_sub hφ hdg2
  have hgmC (m : ℕ) : ContDiff ℝ 1 (gm m) :=
    ((φ m).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((φ m).contDiff_normed (n := 1)) hg.1
  have hgmder (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (gm m) x v = dgm m x :=
    fderiv_convolution_eq_of_hasWeakDerivAlong hg (φ m) x
  refine ⟨(hf2.integrable_mul hg2).locallyIntegrable,
    ((hdf2.integrable_mul hg2).add (hf2.integrable_mul hdg2)).locallyIntegrable, ?_⟩
  intro ψ hψ hψc
  have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
    change HasCompactSupport ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) ∘
      fderiv ℝ ψ)
    exact (hψc.fderiv ℝ).comp_left (by simp)
  have hψtop : MemLp ψ (⊤ : ℝ≥0∞)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have hψdtop : MemLp (fun x => fderiv ℝ ψ x v) (⊤ : ℝ≥0∞)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψd.memLp_of_hasCompactSupport hψdc
  let a : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x * fderiv ℝ ψ x v
  let b : EuclideanSpace ℝ (Fin n) → ℝ := fun x => df x * ψ x
  let c : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x * ψ x
  have ha : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψdtop.mul' hf2
  have hb : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψtop.mul' hdf2
  have hc : MemLp c 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψtop.mul' hf2
  have hid (m : ℕ) :
      (∫ x, a x * gm m x) + (∫ x, c x * dgm m x) =
        -(∫ x, b x * gm m x) := by
    have hder (x : EuclideanSpace ℝ (Fin n)) :
        fderiv ℝ (fun y => ψ y * gm m y) x v =
          ψ x * dgm m x + gm m x * fderiv ℝ ψ x v := by
      change (fderiv ℝ (ψ * gm m) x) v = _
      rw [fderiv_mul
        ((hψ.differentiable one_ne_zero).differentiableAt)
        (((hgmC m).differentiable one_ne_zero).differentiableAt)]
      simp only [add_apply, smul_apply, smul_eq_mul, hgmder]
    have hw := hf.2.2 (fun x => ψ x * gm m x)
      (hψ.mul (hgmC m)) hψc.mul_right
    calc
      (∫ x, a x * gm m x) + (∫ x, c x * dgm m x) =
          ∫ x, a x * gm m x + c x * dgm m x :=
        (integral_add (ha.integrable_mul (hgm2 m))
          (hc.integrable_mul (hdgm2 m))).symm
      _ = ∫ x, f x * fderiv ℝ (fun y => ψ y * gm m y) x v := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change a x * gm m x + c x * dgm m x =
            f x * fderiv ℝ (fun y => ψ y * gm m y) x v
          rw [hder]
          dsimp only [a, c]
          ring
      _ = -(∫ x, df x * (ψ x * gm m x)) := hw
      _ = -(∫ x, b x * gm m x) := by
        apply congrArg Neg.neg
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only [b]
          ring
  have hA := tendsto_integral_mul_of_l2 ha hg2 hgm2 hgmconv
  have hB := tendsto_integral_mul_of_l2 hb hg2 hgm2 hgmconv
  have hC := tendsto_integral_mul_of_l2 hc hdg2 hdgm2 hdgmconv
  have hlim :
      (∫ x, a x * g x) + (∫ x, c x * dg x) =
        -(∫ x, b x * g x) :=
    tendsto_nhds_unique (hA.add hC)
      (Filter.Tendsto.congr (fun m => (hid m).symm) hB.neg)
  have hleft :
      (∫ x, (f x * g x) * fderiv ℝ ψ x v) = ∫ x, a x * g x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [a]
      ring
  have hright :
      (∫ x, (df x * g x + f x * dg x) * ψ x) =
        (∫ x, b x * g x) + (∫ x, c x * dg x) := by
    calc
      (∫ x, (df x * g x + f x * dg x) * ψ x) =
          ∫ x, b x * g x + c x * dg x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only [b, c]
          ring
      _ = (∫ x, b x * g x) + (∫ x, c x * dg x) :=
        integral_add (hb.integrable_mul hg2) (hc.integrable_mul hdg2)
  rw [hleft, hright]
  linarith



/-- A continuous compactly supported cutoff times a function that is L2 on every compact set is globally L2. -/
theorem memLp_mul_of_hasCompactSupport {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    MemLp (fun x => χ x * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hKm : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hind : MemLp ((tsupport χ).indicator f) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hKm).mpr (hf (tsupport χ) hχc)
  have hχlp : MemLp χ (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχ.memLp_of_hasCompactSupport hχc
  have hm : MemLp (fun x => χ x * ((tsupport χ).indicator f) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := hind.mul' hχlp
  convert hm using 1
  funext x
  by_cases hx : x ∈ tsupport χ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
      zero_mul, zero_mul]

/-- Bounded weak factors with compact-local L2 derivatives have the actual
weak product derivative, which is itself L2 on every compact set. -/
theorem HasWeakDerivAlong.mul_of_locally_memLp_two {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf_top : MemLp f (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg_top : MemLp g (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdg2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp dg 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => df x * g x + f x * dg x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  have hlocal :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => df x * g x + f x * dg x) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    have hfirst : MemLp (fun x => df x * g x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      simpa only [mul_comm] using (hdf2 S hS).mul' (hg_top.restrict S)
    exact hfirst.add ((hdg2 S hS).mul' (hf_top.restrict S))
  have hproduct : MemLp (fun x => f x * g x) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hg_top.mul' hf_top
  have hdensity : LocallyIntegrable (fun x => df x * g x + f x * dg x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hlocal S hS).integrable (by norm_num)
  refine ⟨⟨hproduct.locallyIntegrable le_top, hdensity, ?_⟩, hlocal⟩
  intro ψ hψ hψc
  obtain ⟨R, hR⟩ := hψc.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin n))
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    { rIn := max R 0 + 1
      rOut := max R 0 + 2
      rIn_pos := by
        have hnonneg := le_max_right R 0
        linarith
      rIn_lt_rOut := by linarith }
  have hχ : ContDiff ℝ 1 (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    χ.contDiff
  have hχc : HasCompactSupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    χ.hasCompactSupport
  have hχon (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport ψ) :
      χ x = 1 ∧ fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v = 0 := by
    have hradius : R ≤ χ.rIn := by
      change R ≤ max R 0 + 1
      have hle := le_max_left R 0
      linarith
    have he := χ.eventuallyEq_one_of_mem_ball
      ((ball_subset_ball hradius) (hR hx))
    refine ⟨he.eq_of_nhds, ?_⟩
    simp [he.fderiv_eq]
  have hχ2 : MemLp (χ : EuclideanSpace ℝ (Fin n) → ℝ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχ.continuous.memLp_of_hasCompactSupport hχc
  have hχd : Continuous
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hχdc : HasCompactSupport
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) :=
    hχc.fderiv_apply ℝ v
  have hχd2 : MemLp
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχd.memLp_of_hasCompactSupport hχdc
  have hχf2 : MemLp (fun x => χ x * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hf_top.mul' hχ2
  have hχg2 : MemLp (fun x => χ x * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hg_top.mul' hχ2
  have hχdf2 : MemLp
      (fun x => χ x * df x +
        fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_mul_of_hasCompactSupport hχ.continuous hχc hdf2).add (hf_top.mul' hχd2)
  have hχdg2 : MemLp
      (fun x => χ x * dg x +
        fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_mul_of_hasCompactSupport hχ.continuous hχc hdg2).add (hg_top.mul' hχd2)
  have hw := (hf.mul_contDiff hχ hχc).mul_of_memLp_two
    (hg.mul_contDiff hχ hχc) hχf2 hχdf2 hχg2 hχdg2
  have hleft :
      (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (f x * g x) * fderiv ℝ ψ x v =
        ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v
      by_cases hx : x ∈ tsupport ψ
      · rw [(hχon x hx).1]
        simp only [one_mul]
      · rw [fderiv_of_notMem_tsupport ℝ hx]
        simp only [zero_apply, mul_zero]
  have hright :
      (∫ x, ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x) =
        ∫ x, (df x * g x + f x * dg x) * ψ x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x =
        (df x * g x + f x * dg x) * ψ x
      by_cases hx : x ∈ tsupport ψ
      · obtain ⟨hone, hzero⟩ := hχon x hx
        rw [hone, hzero]
        simp only [one_mul, zero_mul, add_zero]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp only [mul_zero]
  calc
    (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := hleft
    _ = -(∫ x, ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x) :=
      hw.2.2 ψ hψ hψc
    _ = -(∫ x, (df x * g x + f x * dg x) * ψ x) :=
      congrArg Neg.neg hright


end FunctionalInequalities.Analysis

end WeakProducts


section WeakFinitePolynomials

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/-- Finite real linear combinations preserve the exact directional weak
derivative and its L2 membership on compact sets. -/
theorem hasWeakDerivAlong_finsetSum_mul {n : ℕ} {ι : Type*}
    (s : Finset ι) (c : ι → ℝ)
    {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasWeakDerivAlong (f i) (df i) v)
    (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => ∑ i ∈ s, c i * f i x)
      (fun x => ∑ i ∈ s, c i * df i x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ i ∈ s, c i * df i x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  have hcf : ∀ i ∈ s,
      LocallyIntegrable (fun x => c i * f i x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro i hi
    exact (hf i hi).1.smul (c i)
  have hcdf : ∀ i ∈ s,
      LocallyIntegrable (fun x => c i * df i x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro i hi
    exact (hf i hi).2.1.smul (c i)
  refine ⟨?_, ?_⟩
  · refine ⟨locallyIntegrable_finsetSum s hcf,
      locallyIntegrable_finsetSum s hcdf, ?_⟩
    intro ψ hψ hψc
    have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
      change HasCompactSupport
        ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
      exact (hψc.fderiv ℝ).comp_left (by simp)
    have iF : ∀ i ∈ s,
        Integrable (fun x => (c i * f i x) * fderiv ℝ ψ x v)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      intro i hi
      simpa only [smul_eq_mul, mul_comm] using
        (hcf i hi).integrable_smul_left_of_hasCompactSupport hψd hψdc
    have iG : ∀ i ∈ s,
        Integrable (fun x => (c i * df i x) * ψ x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      intro i hi
      simpa only [smul_eq_mul, mul_comm] using
        (hcdf i hi).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    calc
      (∫ x, (∑ i ∈ s, c i * f i x) * fderiv ℝ ψ x v
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ i ∈ s, ∫ x, (c i * f i x) * fderiv ℝ ψ x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        simp only [Finset.sum_mul]
        exact integral_finsetSum s iF
      _ = ∑ i ∈ s, -(∫ x, (c i * df i x) * ψ x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [mul_assoc, integral_const_mul,
          (hf i hi).2.2 ψ hψ hψc, mul_neg]
      _ = -(∫ x, (∑ i ∈ s, c i * df i x) * ψ x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        symm
        simp only [Finset.sum_mul]
        exact integral_finsetSum s iG
  · intro S hS
    exact memLp_finsetSum s (fun i hi => (hdf2 i hi S hS).const_mul (c i))


/-- Finite bounded weak factors with compact-local L2 directional derivatives
have the Leibniz weak derivative, including the empty product. -/
theorem hasWeakDerivAlong_finsetProd_of_locally_memLp_two {n : ℕ} {ι : Type*}
    [DecidableEq ι] (s : Finset ι)
    {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasWeakDerivAlong (f i) (df i) v)
    (hbound : ∀ i ∈ s, MemLp (f i) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => ∏ i ∈ s, f i x)
      (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  revert hf hbound hdf2
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _
      simp only [Finset.prod_empty, Finset.sum_empty]
      constructor
      · simpa using
          (hasWeakDerivAlong_of_contDiff
            (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
            contDiff_const v)
      · intro S _
        exact MemLp.zero
  | @insert i t hi ih =>
      intro hf hbound hdf2
      have hrest := ih
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hbound j (Finset.mem_insert_of_mem hj))
        (fun j hj => hdf2 j (Finset.mem_insert_of_mem hj))
      have hrest_top :
          MemLp (fun x => ∏ j ∈ t, f j x) (⊤ : ENNReal)
            (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        simpa only [ENNReal.inv_top, Finset.sum_const_zero, ENNReal.inv_zero] using
          (MemLp.prod' (p := fun _ : ι => (⊤ : ENNReal))
            (fun j hj => hbound j (Finset.mem_insert_of_mem hj)))
      have hbinary :=
        (hf i (Finset.mem_insert_self i t)).mul_of_locally_memLp_two
          hrest.1
          (hbound i (Finset.mem_insert_self i t))
          hrest_top
          (hdf2 i (Finset.mem_insert_self i t))
          hrest.2
      have hprod :
          (fun x => ∏ j ∈ insert i t, f j x) =
            (fun x => f i x * ∏ j ∈ t, f j x) := by
        funext x
        exact Finset.prod_insert hi
      have hsum :
          (fun x => ∑ j ∈ insert i t, df j x * ∏ k ∈ (insert i t).erase j, f k x) =
            (fun x => df i x * (∏ j ∈ t, f j x) +
              f i x * ∑ j ∈ t, df j x * ∏ k ∈ t.erase j, f k x) := by
        funext x
        rw [Finset.sum_insert hi, Finset.erase_insert hi, Finset.mul_sum]
        apply congrArg (fun r : ℝ => df i x * (∏ j ∈ t, f j x) + r)
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i ≠ j := by
          intro h
          subst j
          exact hi hj
        have hiErase : i ∉ t.erase j := by
          intro h
          exact hi (Finset.mem_of_mem_erase h)
        rw [Finset.erase_insert_of_ne hij, Finset.prod_insert hiErase]
        exact mul_left_comm _ _ _
      rw [hprod, hsum]
      exact hbinary


end FunctionalInequalities.Analysis

end WeakFinitePolynomials

universe u
section WeakNegativeExponential
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

section StructuredSpace

variable {E : Type*}
variable [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E]

private lemma weak_measurable_fderiv_apply
    [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (v : E) :
    Measurable (fun x => fderiv ℝ f x v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).measurable.comp (measurable_fderiv ℝ f)

private lemma weak_norm_fderiv_apply_le
    {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) (v x : E) :
    ‖fderiv ℝ f x v‖ ≤ (L : ℝ) * ‖v‖ :=
  (fderiv ℝ f x).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

private lemma weak_fderiv_apply_eq_zero_off_tsupport
    {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) (v : E) :
    fderiv ℝ f x v = 0 := by
  have hz : fderiv ℝ f x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hx ((tsupport_fderiv_subset ℝ) h))
  rw [hz]
  rfl

end NormedSpace

private lemma weak_exists_compact_contDiff_eq_one_near [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) :
    ∃ χ : E → ℝ, ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧
      ∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : E)
  let φ : ContDiffBump (0 : E) :=
    ⟨max r 0 + 1, max r 0 + 2, by positivity, by linarith⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_⟩
  intro x hx
  apply φ.eventuallyEq_one_of_mem_ball
  have h := hr hx
  change dist x 0 ≤ r at h
  change dist x 0 < max r 0 + 1
  linarith [le_max_left r 0]

end StructuredSpace

/-- A globally Lipschitz exponent has a local weak negative exponential
with its explicit chain density in L2 on compact sets. No bound on the
exponent or its exponential, and no C1 regularity of F, is assumed. -/
theorem hasWeakDerivAlong_exp_neg_of_lipschitz {E : Type u}
    [instNormedAddCommGroup : NormedAddCommGroup E]
    [instInnerProductSpace : InnerProductSpace ℝ E]
    [instFiniteDimensional : FiniteDimensional ℝ E]
    [instMeasurableSpace : MeasurableSpace E] [instBorelSpace : BorelSpace E]
    {F : E → ℝ} {L : NNReal} (hF : LipschitzWith L F) (v : E) :
    HasWeakDerivAlong (fun x => Real.exp (-F x))
      (fun x => -Real.exp (-F x) * fderiv ℝ F x v) v ∧
    ∀ S : Set E, IsCompact S →
      MemLp (fun x => -Real.exp (-F x) * fderiv ℝ F x v) 2
        ((volume : Measure E).restrict S) := by
  have hexp : Continuous (fun x => Real.exp (-F x)) :=
    Real.continuous_exp.comp hF.continuous.neg
  have hweakF := hasWeakDerivAlong_of_lipschitz hF v
  have hchain :
      ∀ᵐ x : E ∂(volume : Measure E),
        fderiv ℝ (fun y => Real.exp (-F y)) x v =
          -Real.exp (-F x) * fderiv ℝ F x v := by
    filter_upwards [hF.ae_differentiableAt] with x hx
    have hd :
        fderiv ℝ (fun y => Real.exp (-F y)) x =
          Real.exp (-F x) • (-fderiv ℝ F x) :=
      hx.hasFDerivAt.neg.exp.fderiv
    rw [hd]
    change Real.exp (-F x) * (-(fderiv ℝ F x v)) =
      -Real.exp (-F x) * fderiv ℝ F x v
    ring
  constructor
  · refine ⟨hexp.locallyIntegrable,
      LocallyIntegrable.continuous_mul hexp.neg hweakF.2.1, ?_⟩
    intro ψ hψ hψc
    obtain ⟨χ, hχ, hχc, hχone⟩ :=
      weak_exists_compact_contDiff_eq_one_near (hψc.isCompact.image hF.continuous)
    let q : ℝ → ℝ := fun t => χ t * Real.exp (-t)
    have hq : ContDiff ℝ 1 q :=
      hχ.mul (contDiff_id.neg.exp)
    have hqc : HasCompactSupport q := hχc.mul_right
    obtain ⟨C, hqLip⟩ :=
      ContDiff.lipschitzWith_of_hasCompactSupport hqc hq (by simp)
    have hweakq :
        HasWeakDerivAlong (fun x => q (F x))
          (fun x => fderiv ℝ (fun y => q (F y)) x v) v :=
      hasWeakDerivAlong_of_lipschitz (hqLip.comp hF) v
    have heq : ∀ x ∈ tsupport ψ,
        (fun y => q (F y)) =ᶠ[𝓝 x] (fun y => Real.exp (-F y)) := by
      intro x hx
      have hone :=
        (hχone (F x) ⟨x, hx, rfl⟩).comp_tendsto hF.continuous.continuousAt
      filter_upwards [hone] with y hy
      change χ (F y) = 1 at hy
      change χ (F y) * Real.exp (-F y) = Real.exp (-F y)
      rw [hy, one_mul]
    have hleft :
        (∫ x, Real.exp (-F x) * fderiv ℝ ψ x v ∂(volume : Measure E)) =
          ∫ x, q (F x) * fderiv ℝ ψ x v ∂(volume : Measure E) := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport ψ
      · rw [(heq x hx).eq_of_nhds]
      · rw [weak_fderiv_apply_eq_zero_off_tsupport hx v, mul_zero, mul_zero]
    have hright :
        (∫ x, fderiv ℝ (fun y => q (F y)) x v * ψ x ∂(volume : Measure E)) =
          ∫ x, (-Real.exp (-F x) * fderiv ℝ F x v) * ψ x
            ∂(volume : Measure E) := by
      apply integral_congr_ae
      filter_upwards [hchain] with x hxchain
      by_cases hx : x ∈ tsupport ψ
      · rw [(heq x hx).fderiv_eq, hxchain]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
    calc
      (∫ x, Real.exp (-F x) * fderiv ℝ ψ x v ∂(volume : Measure E)) =
          ∫ x, q (F x) * fderiv ℝ ψ x v ∂(volume : Measure E) := hleft
      _ = -(∫ x, fderiv ℝ (fun y => q (F y)) x v * ψ x
          ∂(volume : Measure E)) := hweakq.2.2 ψ hψ hψc
      _ = -(∫ x, (-Real.exp (-F x) * fderiv ℝ F x v) * ψ x
          ∂(volume : Measure E)) := congrArg Neg.neg hright
  · intro S hS
    let : IsFiniteMeasure ((volume : Measure E).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hexp.continuousOn
    apply MemLp.of_bound
      (hexp.neg.measurable.mul (weak_measurable_fderiv_apply F v)).aestronglyMeasurable
      (C * ((L : ℝ) * ‖v‖))
    filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
    calc
      ‖-Real.exp (-F x) * fderiv ℝ F x v‖ =
          ‖Real.exp (-F x)‖ * ‖fderiv ℝ F x v‖ := by
        rw [norm_mul, norm_neg]
      _ ≤ ‖Real.exp (-F x)‖ * ((L : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_left (weak_norm_fderiv_apply_le hF v x) (norm_nonneg _)
      _ ≤ C * ((L : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_right (hC x hx)
          (mul_nonneg L.coe_nonneg (norm_nonneg v))


end FunctionalInequalities.Analysis
end WeakNegativeExponential
section WeakLocalBoundedProducts
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

/-- Locally essentially bounded weak factors have their actual directional
product derivative, locally L2. No global bound or C1/C2 regularity is assumed. -/
theorem HasWeakDerivAlong.mul_of_locally_bounded {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf_top : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hg_top : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp g (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdg2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp dg 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => df x * g x + f x * dg x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  have hf2 :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hf_top S hS).mono_exponent le_top
  have hg2 :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hg_top S hS).mono_exponent le_top
  have hlocal :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => df x * g x + f x * dg x) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    have hfirst : MemLp (fun x => df x * g x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      simpa only [mul_comm] using (hdf2 S hS).mul' (hg_top S hS)
    exact hfirst.add ((hdg2 S hS).mul' (hf_top S hS))
  have hproduct : LocallyIntegrable (fun x => f x * g x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    have hp : MemLp (fun x => f x * g x) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      (hg_top S hS).mul' (hf_top S hS)
    exact hp.integrable le_top
  have hdensity : LocallyIntegrable (fun x => df x * g x + f x * dg x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hlocal S hS).integrable (by norm_num)
  refine ⟨⟨hproduct, hdensity, ?_⟩, hlocal⟩
  intro ψ hψ hψc
  obtain ⟨χ, hχ, hχc, hχnear⟩ := weak_exists_compact_contDiff_eq_one_near hψc
  have hχon (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport ψ) :
      χ x = 1 ∧ fderiv ℝ χ x v = 0 := by
    have he := hχnear x hx
    refine ⟨he.eq_of_nhds, ?_⟩
    rw [he.fderiv_eq]
    simp
  have hcut_top
      (a : EuclideanSpace ℝ (Fin n) → ℝ)
      (ha : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp a (⊤ : ENNReal)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
      MemLp (fun x => χ x * a x) (⊤ : ENNReal)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    classical
    have hKm : MeasurableSet (tsupport χ) :=
      (isClosed_tsupport χ).measurableSet
    have hind : MemLp ((tsupport χ).indicator a) (⊤ : ENNReal)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (memLp_indicator_iff_restrict hKm).mpr (ha (tsupport χ) hχc)
    have hχlp : MemLp χ (⊤ : ENNReal)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hχ.continuous.memLp_of_hasCompactSupport hχc
    have hm : MemLp (fun x => χ x * ((tsupport χ).indicator a) x)
        (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hind.mul' hχlp
    convert hm using 1
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
        zero_mul, zero_mul]
  have hχd : Continuous (fun x => fderiv ℝ χ x v) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hχdc : HasCompactSupport (fun x => fderiv ℝ χ x v) :=
    hχc.fderiv_apply ℝ v
  have hχdf2 : MemLp
      (fun x => χ x * df x + fderiv ℝ χ x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_mul_of_hasCompactSupport hχ.continuous hχc hdf2).add
      (memLp_mul_of_hasCompactSupport hχd hχdc hf2)
  have hχdg2 : MemLp
      (fun x => χ x * dg x + fderiv ℝ χ x v * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_mul_of_hasCompactSupport hχ.continuous hχc hdg2).add
      (memLp_mul_of_hasCompactSupport hχd hχdc hg2)
  have hw := (hf.mul_contDiff hχ hχc).mul_of_locally_memLp_two
    (hg.mul_contDiff hχ hχc) (hcut_top f hf_top) (hcut_top g hg_top)
    (fun S _ => hχdf2.restrict S) (fun S _ => hχdg2.restrict S)
  have hleft :
      (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (f x * g x) * fderiv ℝ ψ x v =
        ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v
      by_cases hx : x ∈ tsupport ψ
      · rw [(hχon x hx).1]
        simp only [one_mul]
      · rw [weak_fderiv_apply_eq_zero_off_tsupport hx v]
        simp only [mul_zero]
  have hright :
      (∫ x, ((χ x * df x + fderiv ℝ χ x v * f x) * (χ x * g x) +
        (χ x * f x) * (χ x * dg x + fderiv ℝ χ x v * g x)) * ψ x) =
        ∫ x, (df x * g x + f x * dg x) * ψ x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ((χ x * df x + fderiv ℝ χ x v * f x) * (χ x * g x) +
        (χ x * f x) * (χ x * dg x + fderiv ℝ χ x v * g x)) * ψ x =
        (df x * g x + f x * dg x) * ψ x
      by_cases hx : x ∈ tsupport ψ
      · obtain ⟨hone, hzero⟩ := hχon x hx
        rw [hone, hzero]
        simp only [one_mul, zero_mul, add_zero]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp only [mul_zero]
  calc
    (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := hleft
    _ = -(∫ x, ((χ x * df x + fderiv ℝ χ x v * f x) * (χ x * g x) +
        (χ x * f x) * (χ x * dg x + fderiv ℝ χ x v * g x)) * ψ x) :=
      hw.1.2.2 ψ hψ hψc
    _ = -(∫ x, (df x * g x + f x * dg x) * ψ x) :=
      congrArg Neg.neg hright
end FunctionalInequalities.Analysis
end WeakLocalBoundedProducts
section CompactWeakDerivativeTesting
noncomputable section
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

/-! Common-support smooth approximation and compact rough curl testing, used for
Letwin2607.24164v1 (2.6). These are scalar weak-calculus supports; they do not
establish the moment-law evolution, energy comparison, Theorem2.5 or compact8. -/

set_option maxHeartbeats 800000 in
/-- Compact rough H1 tests preserve the curl identity of two weak derivatives
of the same scalar function. Supporting interface for Letwin2607.24164v1 (2.6). -/
theorem integral_weakDeriv_mul_eq_swap {n : ℕ}
    {f p q η a b : EuclideanSpace ℝ (Fin n) → ℝ}
    {v w : EuclideanSpace ℝ (Fin n)}
    (hp : HasWeakDerivAlong f p v) (hq : HasWeakDerivAlong f q w)
    (hp2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp p 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hq2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp q 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hηv : HasWeakDerivAlong η a v) (hηw : HasWeakDerivAlong η b w)
    (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, p x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, q x * a x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  rcases exists_contDiff_compact_weak_deriv_approximation
      hηv hηw hηc hac hbc ha2 hb2 with
    ⟨S, hS, _hηS, haS, hbS, θ, hθ, hconvv, hconvw⟩

  have hpS : MemLp (S.indicator p) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hS.measurableSet).2 (hp2 S hS)

  have hqS : MemLp (S.indicator q) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hS.measurableSet).2 (hq2 S hS)

  have hθvS (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x v) ⊆ S :=
    (hθ m).2.2.2.1

  have hθwS (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x w) ⊆ S :=
    (hθ m).2.2.2.2.1

  have hu_v (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x v) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hθ m).2.2.2.2.2.1

  have hu_w (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x w) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hθ m).2.2.2.2.2.2

  have hsmooth :
      ∀ chi : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ ∞ chi → HasCompactSupport chi →
          (∫ x, p x * fderiv ℝ chi x w
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
            ∫ x, q x * fderiv ℝ chi x v
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro chi hchi hchic
    have hchi2 : ContDiff ℝ (2 : WithTop ℕ∞) chi :=
      hchi.of_le (WithTop.coe_le_coe.mpr le_top)
    have hfd : ContDiff ℝ 1 (fderiv ℝ chi) :=
      hchi2.fderiv_right (by norm_num)
    have hchi_v : ContDiff ℝ 1 (fun x => fderiv ℝ chi x v) :=
      hfd.clm_apply
        (contDiff_const : ContDiff ℝ 1
          (fun _ : EuclideanSpace ℝ (Fin n) => v))
    have hchi_w : ContDiff ℝ 1 (fun x => fderiv ℝ chi x w) :=
      hfd.clm_apply
        (contDiff_const : ContDiff ℝ 1
          (fun _ : EuclideanSpace ℝ (Fin n) => w))
    have hchi_vc : HasCompactSupport (fun x => fderiv ℝ chi x v) := by
      change HasCompactSupport
        ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) ∘ fderiv ℝ chi)
      exact (hchic.fderiv ℝ).comp_left (by simp)
    have hchi_wc : HasCompactSupport (fun x => fderiv ℝ chi x w) := by
      change HasCompactSupport
        ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L w) ∘ fderiv ℝ chi)
      exact (hchic.fderiv ℝ).comp_left (by simp)
    have hsymm (x : EuclideanSpace ℝ (Fin n)) :
        fderiv ℝ (fun y => fderiv ℝ chi y v) x w =
          fderiv ℝ (fun y => fderiv ℝ chi y w) x v := by
      have hfdx : DifferentiableAt ℝ (fderiv ℝ chi) x :=
        (hfd.differentiable (by simp)).differentiableAt
      have hcv :
          DifferentiableAt ℝ
            (fun _ : EuclideanSpace ℝ (Fin n) => v) x :=
        (differentiable_const v : Differentiable ℝ
          (fun _ : EuclideanSpace ℝ (Fin n) => v)).differentiableAt
      have hcw :
          DifferentiableAt ℝ
            (fun _ : EuclideanSpace ℝ (Fin n) => w) x :=
        (differentiable_const w : Differentiable ℝ
          (fun _ : EuclideanSpace ℝ (Fin n) => w)).differentiableAt
      have hv := fderiv_clm_apply hfdx hcv
      have hw := fderiv_clm_apply hfdx hcw
      have hv' := congrArg
        (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L w) hv
      have hw' := congrArg
        (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) hw
      simp at hv' hw'
      have hs :=
        second_derivative_symmetric
          (fun y => (hchi2.differentiable (by norm_num) y).hasFDerivAt)
          hfdx.hasFDerivAt w v
      calc
        fderiv ℝ (fun y => fderiv ℝ chi y v) x w =
            ((fderiv ℝ (fderiv ℝ chi) x) w) v := hv'
        _ = ((fderiv ℝ (fderiv ℝ chi) x) v) w := hs
        _ = fderiv ℝ (fun y => fderiv ℝ chi y w) x v := hw'.symm
    have ep := hp.2.2 (fun x => fderiv ℝ chi x w) hchi_w hchi_wc
    have eq := hq.2.2 (fun x => fderiv ℝ chi x v) hchi_v hchi_vc
    have hleft :
        (∫ x, f x * fderiv ℝ (fun y => fderiv ℝ chi y w) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, f x * fderiv ℝ (fun y => fderiv ℝ chi y v) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x =>
        congrArg (fun z : ℝ => f x * z) (hsymm x).symm)
    linarith [ep, eq, hleft]

  have hpair (m : ℕ) :
      (∫ x, S.indicator p x * fderiv ℝ (θ m) x w
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hpind :
        (∫ x, S.indicator p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ S
        · simp only [Set.indicator_of_mem hx]
        · have hd : fderiv ℝ (θ m) x w = 0 := by
            by_contra hd
            exact hx (hθwS m hd)
          simp only [Set.indicator_of_notMem hx, hd, mul_zero])
    have hqind :
        (∫ x, S.indicator q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ S
        · simp only [Set.indicator_of_mem hx]
        · have hd : fderiv ℝ (θ m) x v = 0 := by
            by_contra hd
            exact hx (hθvS m hd)
          simp only [Set.indicator_of_notMem hx, hd, mul_zero])
    calc
      (∫ x, S.indicator p x * fderiv ℝ (θ m) x w
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hpind
      _ = ∫ x, q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        hsmooth (θ m) (hθ m).1 (hθ m).2.1
      _ = ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hqind.symm

  have ht_p :
      Tendsto
          (fun m => ∫ x, S.indicator p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        atTop
        (𝓝 (∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :=
    tendsto_integral_mul_of_l2
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (a := S.indicator p) (b := b)
      (u := fun m x => fderiv ℝ (θ m) x w)
      hpS hb2 hu_w hconvw

  have ht_q :
      Tendsto
          (fun m => ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        atTop
        (𝓝 (∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :=
    tendsto_integral_mul_of_l2
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (a := S.indicator q) (b := a)
      (u := fun m x => fderiv ℝ (θ m) x v)
      hqS ha2 hu_v hconvv

  have hseq :
      (fun m => ∫ x, S.indicator p x * fderiv ℝ (θ m) x w
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        (fun m => ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    funext m
    exact hpair m

  have ht_q' :
      Tendsto
          (fun m => ∫ x, S.indicator p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        atTop
        (𝓝 (∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    rw [hseq]
    exact ht_q

  have hind :
      (∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    tendsto_nhds_unique ht_p ht_q'

  have hremove_b :
      (∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx]
      · have hbx : b x = 0 := by
          by_contra hbx
          exact hx (hbS hbx)
        simp only [Set.indicator_of_notMem hx, hbx, mul_zero])

  have hremove_a :
      (∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx]
      · have hax : a x = 0 := by
          by_contra hax
          exact hx (haS hax)
        simp only [Set.indicator_of_notMem hx, hax, mul_zero])

  calc
    (∫ x, p x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hremove_b.symm
    _ = ∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hind
    _ = ∫ x, q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hremove_a

end FunctionalInequalities.Analysis
end
end CompactWeakDerivativeTesting
section BoundedWeakDerivativeTesting
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace FunctionalInequalities.Analysis

/-! Bounded weak-test extension of compact-test divergence identities (accepted H2 generic part). -/

/-- A compact-local L1 density admits a common integrable bound for rough bounded tests. -/
theorem compact_bounded_test_domination {n : ℕ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {C : ℝ} (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hS : IsCompact S)
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hsupp : Function.support η ⊆ S) (hbound : ∀ x, ‖η x‖ ≤ C) :
    Integrable (S.indicator fun x => C * ‖F x‖)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ x, ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x) ∧
      Integrable (fun x => F x * η x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hb : Integrable (S.indicator fun x => C * ‖F x‖)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_indicator_iff hS.measurableSet).2
      ((hF.integrableOn_isCompact hS).norm.const_mul C)
  have hprod (x : EuclideanSpace ℝ (Fin n)) :
      ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, norm_mul]
      calc
        ‖F x‖ * ‖η x‖ ≤ ‖F x‖ * C :=
          mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)
        _ = C * ‖F x‖ := mul_comm _ _
    · have hzero : η x = 0 := by
        by_contra hne
        exact hx (hsupp hne)
      rw [Set.indicator_of_notMem hx, hzero, mul_zero, norm_zero]
  exact ⟨hb, hprod, hb.mono' (hF.aestronglyMeasurable.mul hη)
    (Filter.Eventually.of_forall hprod)⟩

/-- Dominated convergence for local L1 forcing and common compact uniformly bounded tests. -/
private theorem tendsto_integral_mul_compact_bounded_tests {n : ℕ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ}
    {θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {C : ℝ}
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hS : IsCompact S)
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hηsupp : Function.support η ⊆ S) (hηbound : ∀ x, ‖η x‖ ≤ C)
    (hθ : ∀ m, AEStronglyMeasurable (θ m)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hθsupp : ∀ m, Function.support (θ m) ⊆ S)
    (hθbound : ∀ m x, ‖θ m x‖ ≤ C)
    (hAE : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun m => θ m x) atTop (𝓝 (η x))) :
    (∀ m, Integrable (fun x => F x * θ m x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Tendsto (fun m => ∫ x, F x * θ m x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
  have hlim := compact_bounded_test_domination hF hS hη hηsupp hηbound
  have hseq (m : ℕ) :=
    compact_bounded_test_domination hF hS (hθ m) (hθsupp m) (hθbound m)
  refine ⟨fun m => (hseq m).2.2, hlim.2.2, ?_⟩
  refine tendsto_integral_of_dominated_convergence
    (S.indicator fun x => C * ‖F x‖)
    (fun m => hF.aestronglyMeasurable.mul (hθ m)) hlim.1
    (fun m => Filter.Eventually.of_forall (hseq m).2.1) ?_
  filter_upwards [hAE] with x hx
  exact tendsto_const_nhds.mul hx



/-- Local L2 fluxes can be paired with common compact global L2 test derivatives. -/
private theorem tendsto_integral_mul_of_compact_local_l2 {n : ℕ}
    {J b : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    (hJ : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MemLp J 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (hb : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hv : ∀ m, MemLp (v m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbS : Function.support b ⊆ S) (hvS : ∀ m, Function.support (v m) ⊆ S)
    (hconv : Tendsto (fun m => eLpNorm (v m - b) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0)) :
    Integrable (fun x => J x * b x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∀ m, Integrable (fun x => J x * v m x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Tendsto (fun m => ∫ x, J x * v m x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, J x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
  have hJS : MemLp (S.indicator J) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hS.measurableSet).2 (hJ S hS)
  have heqb : (fun x => S.indicator J x * b x) = (fun x => J x * b x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · have hz : b x = 0 := by
        by_contra hne
        exact hx (hbS hne)
      rw [Set.indicator_of_notMem hx, hz, mul_zero, mul_zero]
  have heqv (m : ℕ) : (fun x => S.indicator J x * v m x) =
      (fun x => J x * v m x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · have hz : v m x = 0 := by
        by_contra hne
        exact hx (hvS m hne)
      rw [Set.indicator_of_notMem hx, hz, mul_zero, mul_zero]
  have hJb : Integrable (fun x => J x * b x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [← heqb]
    exact hJS.integrable_mul hb
  have hJv (m : ℕ) : Integrable (fun x => J x * v m x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [← heqv m]
    exact hJS.integrable_mul (hv m)
  refine ⟨hJb, hJv, ?_⟩
  have ht := tendsto_integral_mul_of_l2 hJS hb hv hconv
  have hseq : (fun m => ∫ x, S.indicator J x * v m x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      (fun m => ∫ x, J x * v m x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    funext m
    rw [heqv m]
  rw [hseq, heqb] at ht
  exact ht


private theorem integral_flux_eq_neg_forcing_of_test_limits {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ}
    {θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : ℕ → Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {C : ℝ}
    (hS : IsCompact S)
    (hJ : ∀ i : Fin n, ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hηsupp : Function.support η ⊆ S) (hηbound : ∀ x, ‖η x‖ ≤ C)
    (hθ : ∀ m, AEStronglyMeasurable (θ m)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hθsupp : ∀ m, Function.support (θ m) ⊆ S)
    (hθbound : ∀ m x, ‖θ m x‖ ≤ C)
    (hAE : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun m => θ m x) atTop (𝓝 (η x)))
    (ha : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hasupp : ∀ i : Fin n, Function.support (a i) ⊆ S)
    (hv : ∀ m i, MemLp (v m i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hvsupp : ∀ m i, Function.support (v m i) ⊆ S)
    (hconv : ∀ i : Fin n, Tendsto (fun m => eLpNorm (v m i - a i) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0))
    (hId : ∀ m, (∫ x, ∑ i : Fin n, J i x * v m i x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * θ m x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    (∀ i : Fin n, Integrable (fun x => J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ i : Fin n, J i x * a i x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hforcing := tendsto_integral_mul_compact_bounded_tests
    hF hS hη hηsupp hηbound hθ hθsupp hθbound hAE
  have hflux (i : Fin n) := tendsto_integral_mul_of_compact_local_l2
    hS (hJ i) (ha i) (fun m => hv m i) (hasupp i) (fun m => hvsupp m i) (hconv i)
  refine ⟨fun i => (hflux i).1, hforcing.2.1, ?_⟩
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin n))
    (fun i _ => (hflux i).2.2)
  have hL : Tendsto (fun m => ∫ x, ∑ i : Fin n, J i x * v m i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, ∑ i : Fin n, J i x * a i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    have hseq (m : ℕ) := integral_finsetSum (Finset.univ : Finset (Fin n))
      (fun i _ => (hflux i).2.1 m)
    have hlim := integral_finsetSum (Finset.univ : Finset (Fin n))
      (fun i _ => (hflux i).1)
    simpa only [← hseq, ← hlim] using hsum
  have hR : Tendsto (fun m => ∫ x, ∑ i : Fin n, J i x * v m i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (-(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) := by
    simpa only [hId] using hforcing.2.2.neg
  exact tendsto_nhds_unique hL hR


/-- Bounded weak-test extension of a compact-test divergence identity: a compact-local L2 flux `J` and a
locally integrable forcing `F` satisfying `∫ Σᵢ Jᵢ ∂ᵢψ = -∫ F ψ` for every compactly supported C1 `ψ`
satisfy it for a bounded compactly supported locally integrable `η` whose coordinate weak derivatives are
compactly supported and globally L2, with both sides integrable. Every finite dimension, zero included. -/
theorem integral_flux_eq_neg_forcing_of_bounded_weak_test {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hJ : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, ∑ i : Fin n, J i x * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∀ i : Fin n, Integrable (fun x => J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ i : Fin n, J i x * a i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨S, hS, hηS, haS, θ, hθ, hconv, hAE⟩ :=
    exists_contDiff_compact_bounded_all_weak_deriv_approximation hη hbound hηc hweak hac ha2
  have hC : 0 ≤ C := (norm_nonneg (η 0)).trans (hbound 0)
  have hη3 (x : EuclideanSpace ℝ (Fin n)) : ‖η x‖ ≤ 3 * C :=
    (hbound x).trans (by linarith)
  exact integral_flux_eq_neg_forcing_of_test_limits hS hJ hF
    hη.aestronglyMeasurable hηS hη3
    (fun m => (hθ m).1.continuous.aestronglyMeasurable)
    (fun m => (hθ m).2.2.1) (fun m => (hθ m).2.2.2.1) hAE ha2 haS
    (fun m i => ((hθ m).2.2.2.2 i).2)
    (fun m i => ((hθ m).2.2.2.2 i).1) hconv
    (fun m => hId (θ m) ((hθ m).1.of_le (WithTop.coe_le_coe.mpr le_top)) (hθ m).2.1)

end FunctionalInequalities.Analysis
end BoundedWeakDerivativeTesting

section SharedCompactLocalTools

open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace Topology

namespace FunctionalInequalities.Analysis

/-- A continuous function is essentially bounded on every compact set. -/
theorem memLp_top_restrict_of_continuous {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.measurable.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC x hx

/-- The product of two functions that are L2 on every compact set is locally integrable. -/
theorem locallyIntegrable_mul_of_compact_L2 {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hg : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    LocallyIntegrable (fun x => f x * g x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  exact (hf S hS).integrable_mul (hg S hS)

/-- A function that is L2 on every compact set is locally integrable. -/
theorem locallyIntegrable_of_compact_local_memLp_two {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    LocallyIntegrable f (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact (hf S hS).integrable (by norm_num)

/-- Multiplying a weak derivative pair `(f, df)` along `v` by a compactly supported C1 function `ψ`, with `df` L2 and
`f` essentially bounded on compact sets, gives the weak derivative of `ψ f`, compact supports and a globally L2 derivative. -/
theorem HasWeakDerivAlong.compact_mul_data {n : ℕ}
    {f df : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (h : HasWeakDerivAlong f df v)
    (hdf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    HasWeakDerivAlong (fun x => ψ x * f x)
      (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) v ∧
    HasCompactSupport (fun x => ψ x * f x) ∧
    HasCompactSupport (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) ∧
    MemLp (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψc : HasCompactSupport (fun x => fderiv ℝ ψ x v) :=
    hψc.fderiv_apply ℝ v
  have hf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hf S hS).mono_exponent le_top
  refine ⟨h.mul_contDiff hψ hψc, hψc.mul_right, ?_, ?_⟩
  · exact hψc.mul_right.add hdψc.mul_right
  · exact (memLp_mul_of_hasCompactSupport hψ.continuous hψc hdf).add (memLp_mul_of_hasCompactSupport hdψ hdψc hf2)

end FunctionalInequalities.Analysis

end SharedCompactLocalTools

section CompactFluxGlobalBoundedWeakTest

open MeasureTheory Filter Set Metric
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- Integration by parts of a compactly supported compact-local L2 flux `J` with locally integrable forcing `F`
(tested identity against compact C1 tests) against a globally bounded locally integrable weak function `η` whose
coordinate weak derivatives are L2 on compact sets: both pairings are integrable and `∫ ∑ Jᵢ aᵢ = -∫ F η`. -/
theorem integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hJ : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hJc : ∀ i : Fin n, HasCompactSupport (J i)) (hFc : HasCompactSupport F)
    (hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, ∑ i : Fin n, J i x * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    (∀ i : Fin n, Integrable (fun x => J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ i : Fin n, J i x * a i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let S := tsupport F ∪ ⋃ i : Fin n, tsupport (J i)
  have hS : IsCompact S := hFc.union (isCompact_iUnion hJc)
  obtain ⟨R, hR, hRS⟩ := hS.isBounded.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨R, R + 1, hR, lt_add_one R⟩
  have hχ1 (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) : χ x = 1 :=
    χ.one_of_mem_closedBall (ball_subset_closedBall (hRS hx))
  have hχd (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) (i : Fin n) :
      fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) = 0 := by
    have he := (χ.eventuallyEq_one_of_mem_ball (hRS hx)).fderiv_eq (𝕜 := ℝ)
    simpa using congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) he
  let b := fun i x => χ x * a i x +
    fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) * η x
  have htop : MemLp η (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound hη.aestronglyMeasurable C (Filter.Eventually.of_forall hbound)
  have hdata (i : Fin n) := HasWeakDerivAlong.compact_mul_data
    (hweak i) (ha2 i) (fun T _ => htop.restrict T)
    (χ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) χ.hasCompactSupport
  have hηχ : LocallyIntegrable (fun x => χ x * η x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [mul_comm] using hη.continuous_mul χ.continuous
  have hbχ (x : EuclideanSpace ℝ (Fin n)) : ‖χ x * η x‖ ≤ C := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    exact (mul_le_mul_of_nonneg_right χ.le_one (norm_nonneg _)).trans
      (by simpa only [one_mul] using hbound x)
  obtain ⟨hprod, hforce, hEq⟩ := integral_flux_eq_neg_forcing_of_bounded_weak_test
    hJ hF hId hηχ hbχ χ.hasCompactSupport.mul_right
    (fun i => (hdata i).1) (fun i => (hdata i).2.2.1) (fun i => (hdata i).2.2.2)
  have hJeq (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
      J i x * b i x = J i x * a i x := by
    by_cases hx : J i x = 0
    · simp only [hx, zero_mul]
    · have hxS : x ∈ S := Or.inr (Set.mem_iUnion.mpr
        ⟨i, subset_tsupport (J i) hx⟩)
      dsimp only [b]
      rw [hχ1 x hxS, hχd x hxS i]
      ring
  have hFeq (x : EuclideanSpace ℝ (Fin n)) :
      F x * (χ x * η x) = F x * η x := by
    by_cases hx : F x = 0
    · simp only [hx, zero_mul]
    · have hxS : x ∈ S := Or.inl (subset_tsupport F hx)
      rw [hχ1 x hxS, one_mul]
  refine ⟨fun i => (hprod i).congr (Filter.Eventually.of_forall (hJeq i)),
    hforce.congr (Filter.Eventually.of_forall hFeq), ?_⟩
  calc
    _ = ∫ x, ∑ i : Fin n, J i x * b i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        Finset.sum_congr rfl fun i _ => (hJeq i x).symm
    _ = -(∫ x, F x * (χ x * η x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hEq
    _ = _ := congrArg Neg.neg (integral_congr_ae (Filter.Eventually.of_forall hFeq))

end FunctionalInequalities.Analysis

end CompactFluxGlobalBoundedWeakTest

section IntegrableWeakDivergence

open MeasureTheory Filter
open scoped ContDiff Topology
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

namespace FunctionalInequalities.Analysis

set_option maxHeartbeats 800000 in
/-- The integral of a globally integrable weak directional derivative is zero.
This is the cutoff lemma used for Letwin arXiv:2607.24164v1 (2.1)/Lemma2.7. -/
theorem integral_eq_zero_of_integrable_weak_derivative {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (hweak : HasWeakDerivAlong f g v)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x, g x ∂volume) = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  have hscaledNorm (R : ℝ) (x : E) : ‖scaled R x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (scaled_nonneg R x)]
    exact scaled_le_one R x
  have hevent (x : E) : ∀ᶠ k : ℕ in atTop, ‖x‖ < (k : ℝ) + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun k hk => ?_⟩
    exact lt_of_le_of_lt (hN.trans (Nat.cast_le.mpr hk)) (lt_add_one _)
  have hcutLim :
      Tendsto
        (fun k : ℕ => ∫ x, scaled ((k : ℝ) + 1) x * g x ∂volume)
        atTop (𝓝 (∫ x, g x ∂volume)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun k =>
        ((continuous_scaled ((k : ℝ) + 1)).aestronglyMeasurable.mul
          hg.aestronglyMeasurable))
      hg.norm
    · intro k
      filter_upwards [] with x
      change ‖scaled ((k : ℝ) + 1) x * g x‖ ≤ ‖g x‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hscaledNorm _ x)
    · filter_upwards [] with x
      have heq :
          (fun k : ℕ => scaled ((k : ℝ) + 1) x * g x) =ᶠ[atTop] fun _ => g x := by
        filter_upwards [hevent x] with k hk
        rw [scaled_eq_one (by positivity) hk.le, one_mul]
      exact tendsto_const_nhds.congr' heq.symm
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_bump (E := E)
  have hcof (k : ℕ) (x : E) :
      ‖fderiv ℝ (scaled ((k : ℝ) + 1)) x v‖ ≤ M * ‖v‖ := by
    have hR : 0 < (k : ℝ) + 1 := by positivity
    have hi : ((k : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by
        have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith)
    have hd : ‖fderiv ℝ (scaled ((k : ℝ) + 1)) x‖ ≤ M :=
      (norm_fderiv_scaled_le hR hM x).trans
        (mul_le_of_le_one_left hM0 hi)
    exact ((fderiv ℝ (scaled ((k : ℝ) + 1)) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg v))
  have hderivLim :
      Tendsto
        (fun k : ℕ =>
          ∫ x, fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x ∂volume)
        atTop (𝓝 0) := by
    have ht :
        Tendsto
          (fun k : ℕ =>
            ∫ x, fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x ∂volume)
          atTop
          (𝓝 (∫ _x : E, (0 : ℝ) ∂volume)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun x => (M * ‖v‖) * ‖f x‖)
        (fun k =>
          (((contDiff_scaled ((k : ℝ) + 1)).continuous_fderiv (by simp)).clm_apply
            continuous_const).aestronglyMeasurable.mul hf.aestronglyMeasurable)
        (hf.norm.const_mul (M * ‖v‖))
      · intro k
        filter_upwards [] with x
        change ‖fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x‖ ≤
          M * ‖v‖ * ‖f x‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hcof k x) (norm_nonneg _)
      · filter_upwards [] with x
        have heq :
            (fun k : ℕ =>
              fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x) =ᶠ[atTop] fun _ => (0 : ℝ) := by
          filter_upwards [hevent x] with k hk
          rw [fderiv_scaled_eq_zero (by positivity) hk]
          simp only [zero_apply, zero_mul]
        exact tendsto_const_nhds.congr' heq.symm
    simpa only [integral_zero] using ht
  have hidentity (k : ℕ) :
      (∫ x, scaled ((k : ℝ) + 1) x * g x ∂volume) =
        -(∫ x, fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x ∂volume) := by
    let R : ℝ := (k : ℝ) + 1
    have hR : 0 < R := by
      dsimp only [R]
      positivity
    have hχ : ContDiff ℝ 1 (scaled (E := E) R) :=
      (contDiff_scaled R).of_le (by simp)
    have hw := hweak.2.2 (scaled (E := E) R) hχ (hasCompactSupport_scaled hR)
    have hfd :
        (∫ x, f x * fderiv ℝ (scaled (E := E) R) x v ∂volume) =
          ∫ x, fderiv ℝ (scaled (E := E) R) x v * f x ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring
    have hgc :
        (∫ x, g x * scaled (E := E) R x ∂volume) =
          ∫ x, scaled (E := E) R x * g x ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring
    dsimp only [R] at hfd hgc hw ⊢
    linarith
  have hzero :
      Tendsto
        (fun k : ℕ => ∫ x, scaled ((k : ℝ) + 1) x * g x ∂volume)
        atTop (𝓝 0) := by
    have hneg :
        Tendsto
          (fun k : ℕ =>
            -(∫ x, fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x ∂volume))
          atTop (𝓝 (-0)) :=
      hderivLim.neg
    simpa only [neg_zero] using
      hneg.congr' (Filter.Eventually.of_forall fun k => (hidentity k).symm)
  exact tendsto_nhds_unique hcutLim hzero

end FunctionalInequalities.Analysis

end IntegrableWeakDivergence

section CompactBoundedWeakChain

open MeasureTheory Set
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-- A uniformly bounded, a.e. convergent multiplier sequence supported in a finite-measure set, paired with an `L²`-convergent
sequence, has convergent integrals. -/
private theorem tendsto_integral_bounded_mul_of_l2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {S : Set X} (hSm : MeasurableSet S) (hSμ : μ S ≠ ⊤)
    {g : ℕ → X → ℝ} {g₀ v₀ : X → ℝ} {w : ℕ → X → ℝ} {M : ℝ}
    (hg : ∀ m, AEStronglyMeasurable (g m) μ) (hgb : ∀ m x, ‖g m x‖ ≤ M)
    (hgS : ∀ m, Function.support (g m) ⊆ S)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun m => g m x) Filter.atTop (nhds (g₀ x)))
    (hv₀ : MemLp v₀ 2 μ) (hw : ∀ m, MemLp (w m) 2 μ)
    (hconv : Filter.Tendsto (fun m => eLpNorm (w m - v₀) 2 μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => ∫ x, g m x * w m x ∂μ) Filter.atTop (nhds (∫ x, g₀ x * v₀ x ∂μ)) := by
  classical
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSμ
  -- multipliers are L² with a uniform norm bound
  have hmem (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (hfb : ∀ x, ‖f x‖ ≤ M)
      (hfS : Function.support f ⊆ S) : MemLp f 2 μ ∧
        (eLpNorm f 2 μ).toReal ≤ ((μ.restrict S) Set.univ ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal M).toReal := by
    have hind : S.indicator f = f := Set.indicator_eq_self.mpr hfS
    have hr : MemLp f 2 (μ.restrict S) := MemLp.of_bound hf.restrict M (ae_of_all _ hfb)
    have hm : MemLp f 2 μ := by
      rw [← hind]; exact (memLp_indicator_iff_restrict hSm).2 hr
    refine ⟨hm, ?_⟩
    have he : eLpNorm f 2 μ = eLpNorm f 2 (μ.restrict S) := by
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hSm, hind]
    rw [he]
    refine ENNReal.toReal_mono ?_ (eLpNorm_le_of_ae_bound (ae_of_all _ hfb))
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_) ENNReal.ofReal_ne_top
    exact (measure_lt_top _ _).ne
  set B := ((μ.restrict S) Set.univ ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal M).toReal
  have hpair {f z : X → ℝ} (hf : MemLp f 2 μ) (hz : MemLp z 2 μ) :
      inner ℝ (hf.toLp f) (hz.toLp z) = ∫ x, f x * z x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hz.coeFn_toLp] with x hx hz'
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, hz']
    exact mul_comm _ _
  -- the L² error term tends to zero
  have herr : Filter.Tendsto (fun m => ∫ x, g m x * (w m - v₀) x ∂μ) Filter.atTop (nhds 0) := by
    have hbound (m : ℕ) : ‖∫ x, g m x * (w m - v₀) x ∂μ‖ ≤ B * (eLpNorm (w m - v₀) 2 μ).toReal := by
      obtain ⟨hgm, hgB⟩ := hmem (g m) (hg m) (hgb m) (hgS m)
      have hd : MemLp (w m - v₀) 2 μ := (hw m).sub hv₀
      rw [← hpair hgm hd, Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [Lp.norm_toLp, Lp.norm_toLp]
      exact mul_le_mul_of_nonneg_right hgB ENNReal.toReal_nonneg
    have ht : Filter.Tendsto (fun m => B * (eLpNorm (w m - v₀) 2 μ).toReal) Filter.atTop (nhds 0) := by
      have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
      simpa using h0.const_mul B
    exact squeeze_zero_norm hbound ht
  -- the fixed L² factor passes by dominated convergence
  have hv₀S : IntegrableOn v₀ S μ := (hv₀.restrict S).integrable one_le_two
  have hdom : Integrable (S.indicator fun x => M * ‖v₀ x‖) μ :=
    (integrable_indicator_iff hSm).2 (hv₀S.norm.const_mul M)
  have hle (f : X → ℝ) (hfb : ∀ x, ‖f x‖ ≤ M) (hfS : Function.support f ⊆ S) (x : X) :
      ‖f x * v₀ x‖ ≤ (S.indicator fun y => M * ‖v₀ y‖) x := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, norm_mul]
      exact mul_le_mul_of_nonneg_right (hfb x) (norm_nonneg _)
    · have hz : f x = 0 := by
        by_contra hne
        exact hx (hfS hne)
      rw [Set.indicator_of_notMem hx, hz, zero_mul, norm_zero]
  have hmain : Filter.Tendsto (fun m => ∫ x, g m x * v₀ x ∂μ) Filter.atTop (nhds (∫ x, g₀ x * v₀ x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (S.indicator fun x => M * ‖v₀ x‖)
      (fun m => (hg m).mul hv₀.1) hdom (fun m => ae_of_all _ (hle (g m) (hgb m) (hgS m))) ?_
    filter_upwards [hlim] with x hx
    exact hx.mul tendsto_const_nhds
  have hsplit (m : ℕ) : ∫ x, g m x * w m x ∂μ =
      ∫ x, g m x * (w m - v₀) x ∂μ + ∫ x, g m x * v₀ x ∂μ := by
    obtain ⟨hgm, -⟩ := hmem (g m) (hg m) (hgb m) (hgS m)
    have h1 : Integrable (fun x => g m x * (w m - v₀) x) μ := hgm.integrable_mul ((hw m).sub hv₀)
    have h2 : Integrable (fun x => g m x * v₀ x) μ := hgm.integrable_mul hv₀
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Pi.sub_apply]
    ring
  simp_rw [hsplit]
  simpa using herr.add hmain

/-- **Weak chain rule for bounded compactly supported weak data**: if `η` is bounded, compactly supported and locally
integrable with coordinate weak derivatives `aᵢ` that are compactly supported and globally L², and `Φ` is C1, Lipschitz with
`Φ 0 = 0`, then `Φ ∘ η` is compactly supported with weak derivatives `Φ'(η) aᵢ`, compactly supported and globally L².
Every finite dimension. -/
theorem hasWeakDerivAlong_comp_of_compact_bounded {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i)
      (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {Φ : ℝ → ℝ} {D : NNReal}
    (hΦ : ContDiff ℝ 1 Φ) (hΦLip : LipschitzWith D Φ) (hΦzero : Φ 0 = 0) :
    HasCompactSupport (fun x => Φ (η x)) ∧
      ∀ i : Fin n,
        HasWeakDerivAlong (fun x => Φ (η x)) (fun x => deriv Φ (η x) * a i x)
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∧
        HasCompactSupport (fun x => deriv Φ (η x) * a i x) ∧
        MemLp (fun x => deriv Φ (η x) * a i x) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hηm : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))) := hη.aestronglyMeasurable
  have hΦc : Continuous Φ := hΦ.continuous
  have hdΦc : Continuous (deriv Φ) := hΦ.continuous_deriv le_rfl
  have hdΦb (y : ℝ) : ‖deriv Φ y‖ ≤ D := norm_deriv_le_of_lipschitz hΦLip
  have hΦb (y : ℝ) : ‖Φ y‖ ≤ D * ‖y‖ := by
    have h := hΦLip.dist_le_mul y 0
    simpa only [hΦzero, dist_zero_right, Real.dist_eq, sub_zero] using h
  have hC : 0 ≤ C := (norm_nonneg (η 0)).trans (hbound 0)
  have hΦη_supp : Function.support (fun x => Φ (η x)) ⊆ Function.support η := by
    intro x hx
    by_contra h
    exact hx (by simp only [Function.notMem_support.mp h, hΦzero])
  have hcomp_c : HasCompactSupport (fun x => Φ (η x)) := hηc.comp_left hΦzero
  have hηint : Integrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) := (integrableOn_iff_integrable_of_support_subset (subset_tsupport η)).1 (hη.integrableOn_isCompact hηc.isCompact)
  have hΦηm : AEStronglyMeasurable (fun x => Φ (η x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hΦc.comp_aestronglyMeasurable hηm
  have hΦηint : Integrable (fun x => Φ (η x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hηint.norm.const_mul D).mono' hΦηm (ae_of_all _ fun x => hΦb (η x))
  have hdΦηm : AEStronglyMeasurable (fun x => deriv Φ (η x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hdΦc.comp_aestronglyMeasurable hηm
  have hdmem (i : Fin n) : MemLp (fun x => deriv Φ (η x) * a i x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (ha2 i).of_le_mul (hdΦηm.mul (ha2 i).1) (ae_of_all _ fun x => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hdΦb _) (norm_nonneg _))
  obtain ⟨S, hS, hηS, haS, θ, hθ, hconv, hAE⟩ :=
    exists_contDiff_compact_bounded_all_weak_deriv_approximation hη hbound hηc hweak hac ha2
  refine ⟨hcomp_c, fun i => ⟨⟨hΦηint.locallyIntegrable, (hdmem i).locallyIntegrable one_le_two, ?_⟩,
    (hac i).mul_left, hdmem i⟩⟩
  intro ψ hψ hψc
  beta_reduce
  set e := EuclideanSpace.basisFun (Fin n) ℝ i
  have hθ1 (m : ℕ) : ContDiff ℝ 1 (θ m) := (hθ m).1.of_le (WithTop.coe_le_coe.mpr le_top)
  -- classical chain rule identity for each smooth approximant
  have hderiv (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => Φ (θ m y)) x e = deriv Φ (θ m x) * fderiv ℝ (θ m) x e := by
    have h := ((hΦ.differentiable one_ne_zero (θ m x)).hasDerivAt.comp_hasFDerivAt x
      ((hθ1 m).differentiable one_ne_zero x).hasFDerivAt)
    rw [show (fun y => Φ (θ m y)) = Φ ∘ θ m from rfl, h.fderiv]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hid (m : ℕ) : (∫ x, Φ (θ m x) * fderiv ℝ ψ x e) =
      -∫ x, (deriv Φ (θ m x) * fderiv ℝ (θ m) x e) * ψ x := by
    have h := (hasWeakDerivAlong_of_contDiff (hΦ.comp (hθ1 m)) e).2.2 ψ hψ hψc
    simpa only [Function.comp_def, hderiv] using h
  obtain ⟨Cψ, hCψ⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hdψc : Continuous (fun x => fderiv ℝ ψ x e) := (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψmem : MemLp (fun x => fderiv ℝ ψ x e) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hdψc.memLp_of_hasCompactSupport (hψc.fderiv_apply ℝ e)
  have hSm := hS.measurableSet
  have hSμ : (volume : Measure (EuclideanSpace ℝ (Fin n))) S ≠ ⊤ := hS.measure_lt_top.ne
  -- left side
  have hleft : Filter.Tendsto (fun m => ∫ x, Φ (θ m x) * fderiv ℝ ψ x e) Filter.atTop
      (nhds (∫ x, Φ (η x) * fderiv ℝ ψ x e)) := by
    refine tendsto_integral_bounded_mul_of_l2 hSm hSμ (M := D * (3 * C))
      (fun m => (hΦc.comp (hθ m).1.continuous).aestronglyMeasurable)
      (fun m x => (hΦb _).trans (mul_le_mul_of_nonneg_left ((hθ m).2.2.2.1 x) D.2))
      (fun m => fun x hx => (hθ m).2.2.1 (fun h => hx (by simp only [h, hΦzero]))) ?_ hdψmem
      (fun _ => hdψmem) (by simp)
    filter_upwards [hAE] with x hx
    exact (hΦc.tendsto _).comp hx
  -- right side, with the multiplier cut off to `S`
  have hright : Filter.Tendsto (fun m => ∫ x, (deriv Φ (θ m x) * fderiv ℝ (θ m) x e) * ψ x) Filter.atTop
      (nhds (∫ x, (deriv Φ (η x) * a i x) * ψ x)) := by
    have hcut (m : ℕ) : (fun x => (deriv Φ (θ m x) * fderiv ℝ (θ m) x e) * ψ x) =
        fun x => S.indicator (fun y => deriv Φ (θ m y) * ψ y) x * fderiv ℝ (θ m) x e := by
      funext x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]; ring
      · have hz : fderiv ℝ (θ m) x e = 0 := by
          by_contra hne
          exact hx (((hθ m).2.2.2.2 i).1 hne)
        rw [hz]; simp
    have hcut₀ : (fun x => (deriv Φ (η x) * a i x) * ψ x) =
        fun x => S.indicator (fun y => deriv Φ (η y) * ψ y) x * a i x := by
      funext x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]; ring
      · have hz : a i x = 0 := by
          by_contra hne
          exact hx (haS i hne)
        rw [hz]; simp
    simp_rw [hcut, hcut₀]
    have hMb (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
        ‖S.indicator (fun y => deriv Φ (f y) * ψ y) x‖ ≤ D * Cψ := by
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, norm_mul]
        exact mul_le_mul (hdΦb _) (hCψ x) (norm_nonneg _) D.2
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact mul_nonneg D.2 ((norm_nonneg _).trans (hCψ x))
    refine tendsto_integral_bounded_mul_of_l2 hSm hSμ (M := D * Cψ)
      (fun m => (((hdΦc.comp (hθ m).1.continuous).mul hψ.continuous).aestronglyMeasurable).indicator hSm)
      (fun m x => hMb (θ m) x)
      (fun m => Set.support_indicator_subset) ?_ (ha2 i)
      (fun m => ((hθ m).2.2.2.2 i).2) (hconv i)
    filter_upwards [hAE] with x hx
    by_cases hxS : x ∈ S
    · simp only [Set.indicator_of_mem hxS]
      exact ((hdΦc.tendsto _).comp hx).mul tendsto_const_nhds
    · simp only [Set.indicator_of_notMem hxS]
      exact tendsto_const_nhds
  have hlim := hright.neg
  simp_rw [← hid] at hlim
  exact tendsto_nhds_unique hleft hlim

/-- **Weak shifted logarithm** of a bounded compactly supported weak test `η ≥ 0` a.e. (`δ > 0`):
`log(δ + η) - log δ` is compactly supported with weak derivatives `(δ + η)⁻¹ aᵢ`, compactly supported and globally L². -/
theorem hasWeakDerivAlong_log_shift_of_ae_nonneg_compact_bounded {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ η x) (hδ : 0 < δ) :
    HasCompactSupport (fun x => Real.log (δ + η x) - Real.log δ) ∧
      ∀ i : Fin n,
        HasWeakDerivAlong (fun x => Real.log (δ + η x) - Real.log δ)
          (fun x => (δ + η x)⁻¹ * a i x) (EuclideanSpace.basisFun (Fin n) ℝ i) ∧
        HasCompactSupport (fun x => (δ + η x)⁻¹ * a i x) ∧
        MemLp (fun x => (δ + η x)⁻¹ * a i x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨Φ,D,hΦ,-,hLip,hzero,he⟩ := exists_smooth_compact_log_shift_extension hδ (le_max_right C 0)
  have hchain := hasWeakDerivAlong_comp_of_compact_bounded (Φ := Φ) (D := D) hη hbound hηc hweak hac ha2
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top)) hLip hzero
  have hrange : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), η x ∈ Icc (0:ℝ) (max C 0) := by
    filter_upwards [hnonneg] with x hx
    refine ⟨hx,?_⟩
    exact (le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hbound x)).trans (le_max_left C 0)
  have hval : (fun x => Φ (η x)) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => Real.log (δ + η x) - Real.log δ) := by
    filter_upwards [hrange] with x hx
    exact (he (η x) hx).1
  refine ⟨hηc.comp_left (g := fun t : ℝ => Real.log (δ + t) - Real.log δ) (by simp),?_⟩
  intro i
  have hd : (fun x => deriv Φ (η x) * a i x) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => (δ + η x)⁻¹ * a i x) := by
    filter_upwards [hrange] with x hx
    rw [(he (η x) hx).2]
  exact ⟨(hchain.2 i).1.congr_ae hval hd, (hac i).mul_left, MemLp.ae_eq hd ((hchain.2 i).2.2)⟩

/-- **Weak shifted real power** of a bounded compactly supported weak test `η ≥ 0` a.e. (`δ > 0`, every real `q`):
`(δ + η)^q - δ^q` is compactly supported with weak derivatives `q (δ + η)^(q - 1) aᵢ`, compactly supported and
globally L². -/
theorem hasWeakDerivAlong_rpow_shift_of_ae_nonneg_compact_bounded {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ η x) (hδ : 0 < δ) (q : ℝ) :
    HasCompactSupport (fun x => (δ + η x) ^ q - δ ^ q) ∧
      ∀ i : Fin n,
        HasWeakDerivAlong (fun x => (δ + η x) ^ q - δ ^ q)
          (fun x => (q * (δ + η x) ^ (q - 1)) * a i x) (EuclideanSpace.basisFun (Fin n) ℝ i) ∧
        HasCompactSupport (fun x => (q * (δ + η x) ^ (q - 1)) * a i x) ∧
        MemLp (fun x => (q * (δ + η x) ^ (q - 1)) * a i x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨Φ,D,hΦ,-,hLip,hzero,he⟩ := exists_smooth_compact_rpow_shift_extension hδ (le_max_right C 0) q
  have hchain := hasWeakDerivAlong_comp_of_compact_bounded (Φ := Φ) (D := D) hη hbound hηc hweak hac ha2
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top)) hLip hzero
  have hrange : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), η x ∈ Icc (0:ℝ) (max C 0) := by
    filter_upwards [hnonneg] with x hx
    refine ⟨hx,?_⟩
    exact (le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hbound x)).trans (le_max_left C 0)
  have hval : (fun x => Φ (η x)) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => (δ + η x) ^ q - δ ^ q) := by
    filter_upwards [hrange] with x hx
    exact (he (η x) hx).1
  refine ⟨hηc.comp_left (g := fun t : ℝ => (δ + t) ^ q - δ ^ q) (by simp),?_⟩
  intro i
  have hd : (fun x => deriv Φ (η x) * a i x) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => (q * (δ + η x) ^ (q - 1)) * a i x) := by
    filter_upwards [hrange] with x hx
    rw [(he (η x) hx).2]
  exact ⟨(hchain.2 i).1.congr_ae hval hd, (hac i).mul_left, MemLp.ae_eq hd ((hchain.2 i).2.2)⟩

end FunctionalInequalities.Analysis

end CompactBoundedWeakChain

section BoundedNoncompactWeakChain

open MeasureTheory Set Filter
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-! Bounded weak `H¹_loc` data WITHOUT compact support: the chain rule for globally Lipschitz `C¹` profiles and the actual
shifted logarithm `log (δ + max w 0)`, the inputs of the logarithmic energy in Gilbarg–Trudinger (2001) (8.48)–(8.49). -/

/-- **Bounded noncompact weak chain rule.** For bounded `η` with coordinate weak derivatives `a i` in `L²_loc` (no compact
support, no global `L²`) and `Φ` of class `C¹` and `D`-Lipschitz (no `Φ 0 = 0`), `Φ ∘ η` is locally integrable, bounded by
`D C + |Φ 0|`, with exact weak derivatives `Φ′(η) a i` in `L²_loc`. Every dimension, zero included. Each test is handled by
an outer bump equal to one near its support, the compact chain rule for `Φ − Φ 0`, and the affine rule. -/
theorem hasWeakDerivAlong_comp_of_bounded {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {Φ : ℝ → ℝ} {D : NNReal} (hΦ : ContDiff ℝ 1 Φ) (hLip : LipschitzWith D Φ) :
    LocallyIntegrable (fun x => Φ (η x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖Φ (η x)‖ ≤ B) ∧
      ∀ i : Fin n, HasWeakDerivAlong (fun x => Φ (η x)) (fun x => deriv Φ (η x) * a i x)
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => deriv Φ (η x) * a i x) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  have hfm : AEStronglyMeasurable (fun x => Φ (η x)) volume :=
    hΦ.continuous.comp_aestronglyMeasurable hη.aestronglyMeasurable
  have hdfm : AEStronglyMeasurable (fun x => deriv Φ (η x)) volume :=
    (hΦ.continuous_deriv le_rfl).comp_aestronglyMeasurable hη.aestronglyMeasurable
  have hd (t : ℝ) : ‖deriv Φ t‖ ≤ D := norm_deriv_le_of_lipschitz hLip
  have hfb (x : EuclideanSpace ℝ (Fin n)) : ‖Φ (η x)‖ ≤ D * C + ‖Φ 0‖ := by
    have h : ‖Φ (η x) - Φ 0‖ ≤ D * ‖η x‖ := by
      simpa only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] using hLip.dist_le_mul (η x) 0
    calc
      ‖Φ (η x)‖ ≤ ‖Φ (η x) - Φ 0‖ + ‖Φ 0‖ := norm_le_norm_sub_add _ _
      _ ≤ D * C + ‖Φ 0‖ := by
        gcongr
        exact h.trans (mul_le_mul_of_nonneg_left (hbound x) D.2)
  have hfloc : LocallyIntegrable (fun x => Φ (η x)) volume := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (memLp_top_of_bound hfm.restrict (D * C + ‖Φ 0‖) (ae_of_all _ hfb)).integrable le_top
  have hdm (i : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => deriv Φ (η x) * a i x) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    (ha2 i S hS).of_le_mul (hdfm.restrict.mul (ha2 i S hS).1) (ae_of_all _ fun x => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hd _) (norm_nonneg _))
  refine ⟨hfloc, ⟨D * C + ‖Φ 0‖, by positivity, hfb⟩, fun i => ⟨?_, hdm i⟩⟩
  refine ⟨hfloc, ?_, ?_⟩
  · apply locallyIntegrable_iff.mpr
    intro S hS
    have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hdm i S hS).integrable one_le_two
  · intro ψ hψ hψc
    obtain ⟨r, hr⟩ := hψc.isCompact.isBounded.subset_closedBall 0
    let R := max r 0
    let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨R + 1, R + 2, by positivity, by linarith⟩
    have hχ : ContDiff ℝ 1 (fun x => χ x) := χ.contDiff
    have hone (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport ψ) : χ x = 1 ∧ fderiv ℝ χ x = 0 := by
      have hball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) χ.rIn := by
        have h := hr hx
        simp only [Metric.mem_closedBall, dist_zero_right] at h
        simp only [Metric.mem_ball, dist_zero_right]
        change ‖x‖ < R + 1
        linarith [le_max_left r 0]
      have he := χ.eventuallyEq_one_of_mem_ball hball
      refine ⟨he.eq_of_nhds, ?_⟩
      rw [he.fderiv_eq]
      exact fderiv_const_apply _
    have hzero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport ψ) : ψ x = 0 ∧ fderiv ℝ ψ x = 0 := by
      have he := notMem_tsupport_iff_eventuallyEq.mp hx
      refine ⟨he.eq_of_nhds, ?_⟩
      rw [he.fderiv_eq]
      exact fderiv_const_apply _
    have hηtop : MemLp η (⊤ : ENNReal) volume := memLp_top_of_bound hη.aestronglyMeasurable C (ae_of_all _ hbound)
    let b := fun x => χ x * η x
    let db := fun (k : Fin n) x => χ x * a k x + fderiv ℝ (fun y => χ y) x (EuclideanSpace.basisFun (Fin n) ℝ k) * η x
    have hb : LocallyIntegrable b volume := LocallyIntegrable.continuous_mul χ.continuous hη
    have hbb (x : EuclideanSpace ℝ (Fin n)) : ‖b x‖ ≤ C := by
      simp only [b, norm_mul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
      exact (mul_le_mul_of_nonneg_left (hbound x) χ.nonneg).trans
        (mul_le_of_le_one_left hC χ.le_one)
    have hdata (k : Fin n) := (hweak k).compact_mul_data (ha2 k) (fun S _ => hηtop.restrict S) hχ χ.hasCompactSupport
    let Θ := fun t : ℝ => Φ t - Φ 0
    have hΘ : ContDiff ℝ 1 Θ := hΦ.sub contDiff_const
    have hΘLip : LipschitzWith D Θ := LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [Θ, dist_sub_right] using hLip.dist_le_mul x y
    have hΘ0 : Θ 0 = 0 := sub_self _
    have hderiv (t : ℝ) : deriv Θ t = deriv Φ t := deriv_sub_const _
    have hchain := hasWeakDerivAlong_comp_of_compact_bounded hb hbb χ.hasCompactSupport.mul_right
      (fun k => (hdata k).1) (fun k => (hdata k).2.2.1) (fun k => (hdata k).2.2.2) hΘ hΘLip hΘ0
    have hΦb : HasWeakDerivAlong (fun x => Φ (b x)) (fun x => deriv Φ (b x) * db i x)
        (EuclideanSpace.basisFun (Fin n) ℝ i) :=
      ((hchain.2 i).1.const_add_mul (Φ 0) 1).congr_ae
        (ae_of_all _ fun x => by simp only [Θ, one_mul, add_sub_cancel])
        (ae_of_all _ fun x => by simp only [one_mul, hderiv, db])
    calc
      (∫ x, Φ (η x) * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)) =
          ∫ x, Φ (b x) * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ tsupport ψ
        · simp only [b, (hone x hx).1, one_mul]
        · simp only [(hzero x hx).2, _root_.zero_apply, mul_zero]
      _ = -(∫ x, (deriv Φ (b x) * db i x) * ψ x) := hΦb.2.2 ψ hψ hψc
      _ = -(∫ x, (deriv Φ (η x) * a i x) * ψ x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ tsupport ψ
        · simp only [b, db, (hone x hx).1, (hone x hx).2, one_mul, _root_.zero_apply, zero_mul, add_zero]
        · simp only [(hzero x hx).1, mul_zero]

/-- **Actual shifted logarithm.** For bounded `w ≥ 0` a.e. with coordinate weak derivatives `a i` in `L²_loc` (no compact
support) and `δ > 0`, `log (δ + max w 0)` is locally integrable and bounded, with exact weak derivatives
`(δ + max w 0)⁻¹ a i` in `L²_loc`. -/
theorem hasWeakDerivAlong_log_max_shift_of_ae_nonneg_bounded {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong w (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x) (hδ : 0 < δ) :
    LocallyIntegrable (fun x => Real.log (δ + max (w x) 0))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖Real.log (δ + max (w x) 0)‖ ≤ B) ∧
    ∀ i : Fin n, HasWeakDerivAlong (fun x => Real.log (δ + max (w x) 0))
      (fun x => (δ + max (w x) 0)⁻¹ * a i x) (EuclideanSpace.basisFun (Fin n) ℝ i) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => (δ + max (w x) 0)⁻¹ * a i x) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let wp := fun x => max (w x) 0
  have hae : w =ᵐ[volume] wp := by
    filter_upwards [hnonneg] with x hx
    exact (max_eq_left hx).symm
  have hwp := hw.congr hae
  have hwpb (x : EuclideanSpace ℝ (Fin n)) : ‖wp x‖ ≤ max C 0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans ((hbound x).trans (le_max_left _ _))) (le_max_right _ _)
  have hwpweak (i : Fin n) := (hweak i).congr_ae hae (Filter.EventuallyEq.rfl)
  obtain ⟨Φ,D,hΦ,-,hLip,-,he⟩ := exists_smooth_compact_log_shift_extension hδ (le_max_right C 0)
  have hchain := hasWeakDerivAlong_comp_of_bounded (Φ := Φ) (D := D) hwp hwpb hwpweak ha2
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top)) hLip
  have hrange (x : EuclideanSpace ℝ (Fin n)) : wp x ∈ Icc (0:ℝ) (max C 0) :=
    ⟨le_max_right _ _, (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hwpb x)⟩
  have hv (x : EuclideanSpace ℝ (Fin n)) : Real.log δ + Φ (wp x) = Real.log (δ + wp x) := by
    rw [(he (wp x) (hrange x)).1]
    ring
  have hd (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
      deriv Φ (wp x) * a i x = (δ + wp x)⁻¹ * a i x := by rw [(he (wp x) (hrange x)).2]
  obtain ⟨B,hB,hBb⟩ := hchain.2.1
  have hloc : LocallyIntegrable (fun x => Real.log (δ + wp x)) volume :=
    (locallyIntegrable_const (Real.log δ)).add hchain.1 |>.congr (ae_of_all _ hv)
  refine ⟨hloc, ⟨‖Real.log δ‖ + B, by positivity, fun x => ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · rw [← hv]
    exact (norm_add_le _ _).trans (by gcongr; exact hBb x)
  · exact ((hchain.2.2 i).1.const_add_mul (Real.log δ) 1).congr_ae
      (ae_of_all _ fun x => by simpa only [one_mul] using hv x)
      (ae_of_all _ fun x => by simpa only [one_mul] using hd i x)
  · intro S hS
    exact MemLp.ae_eq (ae_of_all _ (hd i)) ((hchain.2.2 i).2 S hS)

/-- **Bounded weak extension of the shifted logarithm.** For bounded `w` with coordinate weak derivatives `a k` in
`L²_loc` (no sign condition) and `δ > 0`, ONE bounded locally integrable `H` with weak derivatives `dH k` in `L²_loc` is
chosen before every domain: `H = log δ + Φ ∘ w` for the compact smooth log profile `Φ` on `[0, C]`, by the bounded
noncompact chain rule applied to `w` itself. On EVERY measurable `S` where `w ≥ 0` a.e., `H = log (δ + max w 0)` and
`dH k = (δ + max w 0)⁻¹ a k` a.e. for the restriction. No weak derivative of `log (δ + max w 0)` itself is asserted. -/
theorem exists_bounded_weak_log_extension {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hδ : 0 < δ) :
    ∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖H x‖ ≤ B) ∧
      (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S), 0 ≤ w x) →
        (H =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)]
          (fun x => Real.log (δ + max (w x) 0))) ∧
        ∀ k : Fin n, (dH k) =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)]
          (fun x => (δ + max (w x) 0)⁻¹ * a k x) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  -- one compact log profile on `[0, C]` and the bounded noncompact chain on the ORIGINAL `w`
  obtain ⟨Φ, D, hΦ, -, hLip, -, he⟩ := exists_smooth_compact_log_shift_extension hδ hC
  have hchain := hasWeakDerivAlong_comp_of_bounded (Φ := Φ) (D := D) hw hbound hweak ha2
    (hΦ.of_le (WithTop.coe_le_coe.mpr le_top)) hLip
  obtain ⟨B, hB, hBb⟩ := hchain.2.1
  refine ⟨fun x => Real.log δ + Φ (w x), fun k x => deriv Φ (w x) * a k x,
    (locallyIntegrable_const (Real.log δ)).add hchain.1,
    ⟨‖Real.log δ‖ + B, by positivity, fun x => (norm_add_le _ _).trans (by gcongr; exact hBb x)⟩,
    fun k => ⟨?_, (hchain.2.2 k).2⟩, ?_⟩
  · simpa only [one_mul] using (hchain.2.2 k).1.const_add_mul (Real.log δ) 1
  -- identification only on domains where `w ≥ 0` a.e.
  intro S _hS hS0
  have hrange : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
      0 ≤ w x ∧ w x ∈ Icc (0 : ℝ) C := by
    filter_upwards [hS0] with x hx
    exact ⟨hx, hx, (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound x)⟩
  refine ⟨?_, fun k => ?_⟩
  · filter_upwards [hrange] with x hx
    rw [max_eq_left hx.1, (he (w x) hx.2).1]
    ring
  · filter_upwards [hrange] with x hx
    rw [max_eq_left hx.1, (he (w x) hx.2).2]

end FunctionalInequalities.Analysis

end BoundedNoncompactWeakChain

section BoundedRpowCutoffTests

open MeasureTheory Set
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-! Shifted real powers of a bounded, a.e. nonnegative weak `H¹_loc` function under a compactly supported `C¹` cutoff:
the energy variables of a Moser-type iteration (Letwin arXiv:2607.24164v1 Lemma 2.2; GT (8.48)–(8.49)). -/

open Filter in
/-- **Linear cutoff energy variable, local nonnegativity.** For bounded `w` with coordinate weak derivatives `a k` in
`L²_loc`, nonnegative only a.e. on `tsupport χ` (`χ` of class `C¹` with compact support), `δ > 0` and every real `q`,
`χ (δ + max w 0)^q` is bounded, compactly supported in `tsupport χ` and nonnegative when `χ` is, with the exact weak
derivatives `∂χ · s^q + χ q s^(q-1) a k` (`s = δ + max w 0`), compactly supported in `tsupport χ` and globally `L²`.
The compact smooth power profile and the bounded noncompact chain rule are applied to `w` itself; the identification
with `max w 0` is used only on `tsupport χ`. Every dimension, zero included. -/
theorem local_rpow_cutoff_weak_data {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)), 0 ≤ w x)
    (hδ : 0 < δ) (q : ℝ) :
    let η := fun x => χ x * (δ + max (w x) 0) ^ q
    let dη := fun (k : Fin n) x =>
      fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * (δ + max (w x) 0) ^ q +
      χ x * (q * (δ + max (w x) 0) ^ (q - 1)) * a k x
    LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport η ∧ Function.support η ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖η x‖ ≤ Cη) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ η x) ∧
      ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  intro η dη
  classical
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  obtain ⟨Φ, D, hΦ, -, hLip, -, he⟩ := exists_smooth_compact_rpow_shift_extension hδ hC q
  have hc := hasWeakDerivAlong_comp_of_bounded hw hbound hweak ha2
    (hΦ.of_le (by exact_mod_cast le_top)) hLip
  obtain ⟨B, hB, hb⟩ := hc.2.1
  let P := fun x => δ ^ q + Φ (w x)
  let dP := fun (k : Fin n) x => deriv Φ (w x) * a k x
  have hp (k : Fin n) : HasWeakDerivAlong P (dP k) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    simpa only [P, dP, one_mul] using (hc.2.2 k).1.const_add_mul (δ ^ q) 1
  have hpb (x : EuclideanSpace ℝ (Fin n)) : ‖P x‖ ≤ ‖δ ^ q‖ + B :=
    (norm_add_le _ _).trans (add_le_add_right (hb x) _)
  have hpm : AEStronglyMeasurable P (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    aestronglyMeasurable_const.add hc.1.aestronglyMeasurable
  have hptop (S : Set (EuclideanSpace ℝ (Fin n))) (_hS : IsCompact S) :
      MemLp P (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    memLp_top_of_bound hpm.restrict _ (ae_of_all _ hpb)
  have hmain (k : Fin n) := (hp k).compact_mul_data (fun S _ => (hc.2.2 k).2 S ‹_›) hptop hχ hχc
  have hzero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport χ) : χ x = 0 ∧ fderiv ℝ χ x = 0 := by
    exact ⟨image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx⟩
  have hn := (ae_restrict_iff' (isClosed_tsupport χ).measurableSet).mp hnonneg
  have heP : (fun x => χ x * P x) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] η := by
    filter_upwards [hn] with x hx
    by_cases hxs : x ∈ tsupport χ
    · have h0 := hx hxs
      have hCw : w x ≤ C := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound x)
      simp only [P, η, max_eq_left h0, (he (w x) ⟨h0, hCw⟩).1]
      ring
    · simp only [η, (hzero x hxs).1, zero_mul]
  have hedP (k : Fin n) :
      (fun x => χ x * dP k x + fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * P x)
        =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] dη k := by
    filter_upwards [hn] with x hx
    by_cases hxs : x ∈ tsupport χ
    · have h0 := hx hxs
      have hCw : w x ≤ C := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound x)
      simp only [P, dP, dη, max_eq_left h0, (he (w x) ⟨h0, hCw⟩).1, (he (w x) ⟨h0, hCw⟩).2]
      ring
    · simp only [dη, (hzero x hxs).1, (hzero x hxs).2, _root_.zero_apply, zero_mul, add_zero]
  have hsupp : Function.support η ⊆ tsupport χ := by
    intro x hx
    exact by_contradiction fun h => hx (by simp only [η, (hzero x h).1, zero_mul])
  have hdsupp (k : Fin n) : Function.support (dη k) ⊆ tsupport χ := by
    intro x hx
    exact by_contradiction fun h => hx (by simp only [dη, (hzero x h).1, (hzero x h).2, _root_.zero_apply]; ring)
  obtain ⟨Bp, hBp⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) C)).exists_bound_of_continuousOn
    (f := fun t : ℝ => (δ + t) ^ q)
    (ContinuousOn.rpow_const (f := fun t : ℝ => δ + t) (by fun_prop)
      fun t ht => Or.inl (show δ + t ≠ 0 from ne_of_gt (by linarith [ht.1])))
  have hmax0 (x) : 0 ≤ max (w x) 0 := le_max_right _ _
  have hmaxC (x) : max (w x) 0 ≤ C := max_le
    ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound x)) hC
  have hpbound (x) : ‖(δ + max (w x) 0) ^ q‖ ≤ Bp := hBp _ ⟨hmax0 x,hmaxC x⟩
  obtain ⟨Cχ, hCχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hBp0 : 0 ≤ Bp := (norm_nonneg _).trans (hpbound 0)
  have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ 0)
  have hηb (x) : ‖η x‖ ≤ Cχ * Bp := by
    exact (norm_mul _ _).le.trans (mul_le_mul (hCχ x) (hpbound x) (norm_nonneg _) hCχ0)
  have hηm : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hχ.continuous.aestronglyMeasurable.mul hpm).congr heP
  have hloc : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (memLp_top_of_bound hηm.restrict _ (ae_of_all _ hηb)).integrable le_top
  refine ⟨hloc,hχc.mono' hsupp,hsupp,⟨Cχ*Bp,by positivity,hηb⟩,
    fun hχ0 x => mul_nonneg (hχ0 x) (Real.rpow_nonneg (by linarith [hmax0 x]) _),fun k => ?_⟩
  exact ⟨(hmain k).1.congr_ae heP (hedP k), hχc.mono' (hdsupp k), hdsupp k,
    MemLp.ae_eq (hedP k) (hmain k).2.2.2⟩

/-- **Linear cutoff energy variable.** For bounded `w ≥ 0` a.e. with coordinate weak derivatives `a k` in `L²_loc`, a
`C¹` compactly supported `χ`, `δ > 0` and every real `q`, the function `χ (δ + max w 0)^q` is bounded, compactly
supported in `tsupport χ` and nonnegative when `χ` is, with the exact coordinate weak derivatives
`∂χ · s^q + χ q s^(q-1) a k` (`s = δ + max w 0`), compactly supported in `tsupport χ` and globally `L²`. Every
dimension, zero included. -/
theorem bounded_rpow_cutoff_weak_data {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hδ : 0 < δ) (q : ℝ) :
    let η := fun x => χ x * (δ + max (w x) 0) ^ q
    let dη := fun (k : Fin n) x =>
      fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * (δ + max (w x) 0) ^ q +
      χ x * (q * (δ + max (w x) 0) ^ (q - 1)) * a k x
    LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport η ∧ Function.support η ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖η x‖ ≤ Cη) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ η x) ∧
      ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact local_rpow_cutoff_weak_data hw hbound hweak ha2 hχ hχc (ae_restrict_of_ae hnonneg) hδ q

open Filter in
/-- **Square cutoff test, local nonnegativity.** The pointwise nonnegative test `χ² (δ + max w 0)^q` with derivative
`2 χ ∂χ s^q + χ² q s^(q-1) a k`, from `local_rpow_cutoff_weak_data` at `χ²`; nonnegativity of `w` is needed only a.e.
on `tsupport χ`. -/
theorem local_rpow_cutoff_weak_test {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)), 0 ≤ w x)
    (hδ : 0 < δ) (q : ℝ) :
    let η := fun x => χ x ^ 2 * (δ + max (w x) 0) ^ q
    let dη := fun (k : Fin n) x =>
      2 * χ x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * (δ + max (w x) 0) ^ q +
      χ x ^ 2 * (q * (δ + max (w x) 0) ^ (q - 1)) * a k x
    LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport η ∧ Function.support η ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖η x‖ ≤ Cη) ∧ (∀ x, 0 ≤ η x) ∧
      ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  intro η dη
  have hsqc : HasCompactSupport (fun x => χ x ^ 2) := hχc.mono' fun x hx => subset_tsupport χ (fun h => hx (by
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]))
  have hts : tsupport (fun x => χ x ^ 2) ⊆ tsupport χ := closure_mono fun x hx => fun h => hx (by
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
  -- local nonnegativity on the smaller support of the square cutoff
  have hnonneg' : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport (fun x => χ x ^ 2))),
      0 ≤ w x := ae_restrict_of_ae_restrict_of_subset hts hnonneg
  obtain ⟨hl, hc, hs, hb, hpos, hd⟩ := local_rpow_cutoff_weak_data hw hbound hweak ha2
    (χ := fun x => χ x ^ 2) (hχ.pow 2) hsqc hnonneg' hδ q
  have hdsq (k : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => χ y ^ 2) x (EuclideanSpace.basisFun (Fin n) ℝ k) =
        2 * χ x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    rw [((hχ.differentiable one_ne_zero x).hasFDerivAt.pow 2).fderiv]
    simp only [_root_.smul_apply, smul_eq_mul]
    ring
  have hdη (k : Fin n) : (fun x => fderiv ℝ (fun y => χ y ^ 2) x (EuclideanSpace.basisFun (Fin n) ℝ k) *
      (δ + max (w x) 0) ^ q + χ x ^ 2 * (q * (δ + max (w x) 0) ^ (q - 1)) * a k x) = dη k := by
    funext x; rw [hdsq k x]
  -- pointwise nonnegativity of `χ² (δ + max w 0)^q` (not an a.e. statement)
  refine ⟨hl, hc, hs.trans hts, hb, hpos fun x => sq_nonneg _, fun k => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hd k
  rw [← hdη k]
  exact ⟨h1, h2, h3.trans hts, h4⟩

/-- **Square cutoff test.** The nonnegative test `χ² (δ + max w 0)^q` with derivative `2 χ ∂χ s^q + χ² q s^(q-1) a k`;
the linear cutoff energy variable at the cutoff `χ²`. -/
theorem bounded_rpow_cutoff_weak_test {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hδ : 0 < δ) (q : ℝ) :
    let η := fun x => χ x ^ 2 * (δ + max (w x) 0) ^ q
    let dη := fun (k : Fin n) x =>
      2 * χ x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * (δ + max (w x) 0) ^ q +
      χ x ^ 2 * (q * (δ + max (w x) 0) ^ (q - 1)) * a k x
    LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport η ∧ Function.support η ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖η x‖ ≤ Cη) ∧ (∀ x, 0 ≤ η x) ∧
      ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact local_rpow_cutoff_weak_test hw hbound hweak ha2 hχ hχc (ae_restrict_of_ae hnonneg) hδ q

end FunctionalInequalities.Analysis

end BoundedRpowCutoffTests
