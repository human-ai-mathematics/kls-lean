import FunctionalInequalities.Analysis.WeakDerivative.Approximation
import FunctionalInequalities.Analysis.Cutoff.SmoothBall
import FunctionalInequalities.Analysis.WeakDerivative.Basic
import FunctionalInequalities.Analysis.WeakDerivative.Mollification

/-!
# Weak products, chain rule and rough testing

Existing names, statements and proof payloads are preserved.
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

private lemma weak_measurable_fderiv_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (v : E) :
    Measurable (fun x => fderiv ℝ f x v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).measurable.comp (measurable_fderiv ℝ f)

private lemma weak_norm_fderiv_apply_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) (v x : E) :
    ‖fderiv ℝ f x v‖ ≤ (L : ℝ) * ‖v‖ :=
  (fderiv ℝ f x).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

private lemma weak_fderiv_apply_eq_zero_off_tsupport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) (v : E) :
    fderiv ℝ f x v = 0 := by
  have hz : fderiv ℝ f x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hx ((tsupport_fderiv_subset ℝ) h))
  rw [hz]
  rfl

private lemma weak_exists_compact_contDiff_eq_one_near {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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
private theorem compact_bounded_test_domination {n : ℕ}
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
