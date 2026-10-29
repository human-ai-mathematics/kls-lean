import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Riesz-potential representation on convex domains

For `u` of class `C¹` on an open convex `Ω ⊆ ℝⁿ` (`n > 0`), every measurable `S ⊆ Ω` and every `x ∈ Ω` with `S` within
distance `D` of `x`, the mass form `|S| · |u(x) − u_S| ≤ (D^n/n) ∫_Ω |z − x|^{1−n} |Du(z)| dz` holds; `|S| = 0` is included.
This is the smooth step of Gilbarg–Trudinger (2001), Lemma 7.16, with its coefficient `d^n/n` in mass form: the segment
fundamental theorem of calculus, the mean displacement, the homothety transport `y ↦ x + t(y − x)` (Jacobian `t^{-n}`,
support in `Ω ∩ B̄(x, tD)`) and the exact radial tail `(D^N/N) d^{1−N}`. It is not the `W^{1,1}` approximation step; the
bounded weak application is `WeakDerivative/Representation`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace FunctionalInequalities.Analysis

/-- Segment estimate `|u y − u x| ≤ ∫₀¹ ‖Du(x + t(y − x))‖ ‖y − x‖` on an open convex set. -/
private theorem enorm_sub_le_lintegral_segment_fderiv_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {u : E → ℝ} (hu : ContDiffOn ℝ 1 u Ω) (x : E) (hx : x ∈ Ω) (y : E) (hy : y ∈ Ω) :
    ENNReal.ofReal |u y - u x| ≤
      ∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖) := by
  let γ : ℝ → E := fun t => x + t • (y - x)
  have hγ : ContDiff ℝ 1 γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγΩ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω :=
    hΩc.add_smul_sub_mem hx hy ht
  have hdγ (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hcomp : ContDiffOn ℝ 1 (u ∘ γ) (Icc (0 : ℝ) 1) := hu.comp hγ.contDiffOn hγΩ
  have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hcomp zero_le_one
  have hγ1 : γ 1 = y := by dsimp [γ]; simp
  have hγ0 : γ 0 = x := by dsimp [γ]; simp
  rw [Function.comp_apply, Function.comp_apply, hγ1, hγ0] at h
  rw [← ofReal_norm, Real.norm_eq_abs] at h
  refine h.trans (lintegral_mono_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hd : HasDerivAt (fun t => u (γ t)) (fderiv ℝ u (γ t) (y - x)) t :=
    ((hu.contDiffAt (hΩo.mem_nhds (hγΩ t ht))).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt t (hdγ t)
  change ‖deriv (fun s => u (γ s)) t‖ₑ ≤ _
  rw [hd.deriv, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal ((fderiv ℝ u (γ t)).le_opNorm (y - x))

/-- Mass-form mean displacement `μ(X) |c − ⨍ f| ≤ ∫ |c − f|` on a finite measure (zero measure included). -/
private theorem measure_mul_enorm_sub_average_le_lintegral
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Integrable f μ) (c : ℝ) :
    μ univ * ENNReal.ofReal |c - ⨍ x, f x ∂μ| ≤
      ∫⁻ y, ENNReal.ofReal |c - f y| ∂μ := by
  have he : (∫ y, c - f y ∂μ) = μ.real univ * (c - ⨍ x, f x ∂μ) := by
    rw [integral_sub (integrable_const c) hf, ← integral_average μ f]
    simp only [integral_const, smul_eq_mul, mul_sub]
  have h := enorm_integral_le_lintegral_enorm (μ := μ) (fun y => c - f y)
  simpa only [he, ← ofReal_norm, Real.norm_eq_abs, abs_mul,
    measureReal_def, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

/-- **Convex ray transport.** For `0 < t ≤ 1`, the image of Lebesgue measure on `S ⊆ Ω` under
`y ↦ x + t (y − x)` is at most `t^{-n}` times Lebesgue measure on `Ω ∩ B̄(x, tD)` (`Ω` convex, `S` within distance `D` of `x`). -/
theorem map_restrict_convex_ray_le
    {n : ℕ} {Ω S : Set (EuclideanSpace ℝ (Fin n))}
    (hΩm : MeasurableSet Ω) (hSm : MeasurableSet S) (hΩ : Convex ℝ Ω)
    (hSΩ : S ⊆ Ω) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω)
    {D t : ℝ} (hD : 0 < D) (ht : 0 < t) (ht1 : t ≤ 1)
    (hdiam : ∀ y ∈ S, dist y x ≤ D) :
    Measure.map (fun y => x + t • (y - x))
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) ≤
      ENNReal.ofReal (t ^ (-(n : ℝ))) •
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Ω ∩ closedBall x (t * D))) := by
  -- The premises `hSm` and `hD` are not needed by the transport proof.
  have _hSm := hSm
  have _hD := hD
  let H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y => x + t • (y - x)
  let G := Ω ∩ closedBall x (t * D)
  let c := ENNReal.ofReal (t ^ (-(n : ℝ)))
  have hH : Measurable H := by fun_prop
  have hG : MeasurableSet G := hΩm.inter measurableSet_closedBall
  have hpre : S ⊆ H ⁻¹' G := by
    intro y hy
    refine ⟨hΩ.add_smul_sub_mem hx (hSΩ hy) ⟨ht.le,ht1⟩, ?_⟩
    change dist (x + t • (y - x)) x ≤ t * D
    rw [dist_eq_norm]
    have he : x + t • (y - x) - x = t • (y - x) := by abel
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hdiam y hy) ht.le
  have hfull : Measure.map H (volume : Measure (EuclideanSpace ℝ (Fin n))) =
      c • (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    let U : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y => y - x
    let V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y => t • y
    let W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y => x + y
    have hU : Measurable U := by fun_prop
    have hV : Measurable V := by fun_prop
    have hW : Measurable W := by fun_prop
    have hUmap : Measure.map U (volume : Measure (EuclideanSpace ℝ (Fin n))) = volume := by
      simpa only [U,sub_eq_add_neg] using map_add_right_eq_self
        (volume : Measure (EuclideanSpace ℝ (Fin n))) (-x)
    have hcoef : |(t ^ n)⁻¹| = t ^ (-(n : ℝ)) := by
      rw [abs_of_pos (inv_pos.mpr (pow_pos ht n)),Real.rpow_neg ht.le,Real.rpow_natCast]
    have hVmap : Measure.map V (volume : Measure (EuclideanSpace ℝ (Fin n))) = c • volume := by
      simpa only [V,c,finrank_euclideanSpace_fin,hcoef] using
        Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin n))) ht.ne'
    have hWmap : Measure.map W (volume : Measure (EuclideanSpace ℝ (Fin n))) = volume :=
      map_add_left_eq_self _ x
    have he : H = (W ∘ V) ∘ U := rfl
    rw [he, ← Measure.map_map (hW.comp hV) hU, ← Measure.map_map hW hV,
      hUmap,hVmap,Measure.map_smul,hWmap]
  change Measure.map H ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) ≤
    c • (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict G
  calc
    _ ≤ Measure.map H ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (H ⁻¹' G)) :=
      Measure.map_mono (Measure.restrict_mono hpre le_rfl) hH
    _ = (Measure.map H (volume : Measure (EuclideanSpace ℝ (Fin n)))).restrict G :=
      (Measure.restrict_map hH hG).symm
    _ = _ := by rw [hfull,Measure.restrict_smul]

/-- The exact radial tail `d ∫_{d/D}^∞ t^{−N−1} dt = (D^N/N) d^{1−N}`. -/
private theorem distance_mul_lintegral_ray_tail
    {N D d : ℝ} (hN : 0 < N) (hD : 0 < D) (hd : 0 < d) :
    ENNReal.ofReal d * (∫⁻ t in Ioi (d / D), ENNReal.ofReal (t ^ (-N - 1))) =
      ENNReal.ofReal (D ^ N / N * d ^ (1 - N)) := by
  have hT : 0 < d / D := div_pos hd hD
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -N - 1 < -1) hT
  have hnn : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioi (d / D))), 0 ≤ t ^ (-N - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hT.trans ht).le _
  have hreal : (∫ t in Ioi (d / D), t ^ (-N - 1)) = (d / D) ^ (-N) / N := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -N - 1 < -1) hT]
    have he : -N - 1 + 1 = -N := by ring
    rw [he, neg_div_neg_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn, hreal, ← ENNReal.ofReal_mul hd.le]
  apply congrArg ENNReal.ofReal
  rw [Real.div_rpow hd.le hD.le, Real.rpow_neg hd.le, Real.rpow_neg hD.le,
    Real.rpow_sub hd, Real.rpow_one]
  field_simp

/-- Layer integration of the closed radial cutoff gives the Riesz kernel `(D^N/N) r^{1−N}` (Tonelli). -/
private theorem lintegral_ray_layers_le_riesz_kernel
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {r : X → ℝ} (hr : Measurable r) (hr0 : ∀ z, 0 ≤ r z)
    {g : X → ℝ≥0∞} (hg : Measurable g) {N D : ℝ} (hN : 0 < N) (hD : 0 < D) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ z,
      (if r z ≤ t * D then ENNReal.ofReal (t ^ (-N - 1)) *
        (ENNReal.ofReal (r z) * g z) else 0) ∂μ) ≤
      ENNReal.ofReal (D ^ N / N) * (∫⁻ z, ENNReal.ofReal ((r z) ^ (1 - N)) * g z ∂μ) := by
  classical
  let F : ℝ → X → ℝ≥0∞ := fun t z => if r z ≤ t * D then
    ENNReal.ofReal (t ^ (-N - 1)) * (ENNReal.ofReal (r z) * g z) else 0
  have hF : Measurable (Function.uncurry F) := by
    apply Measurable.ite
      (measurableSet_le (hr.comp measurable_snd) (measurable_fst.mul_const D))
    · exact (measurable_fst.pow_const _).ennreal_ofReal.mul
        ((hr.comp measurable_snd).ennreal_ofReal.mul (hg.comp measurable_snd))
    · exact measurable_const
  change (∫⁻ t in Ioi (0 : ℝ), ∫⁻ z, F t z ∂μ) ≤ _
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (D ^ N / N) * (ENNReal.ofReal ((r z) ^ (1 - N)) * g z) ∂μ := by
      apply lintegral_mono
      intro z
      change (∫⁻ t in Ioi (0 : ℝ), F t z) ≤ ENNReal.ofReal (D ^ N / N) *
        (ENNReal.ofReal ((r z) ^ (1 - N)) * g z)
      by_cases hz : r z = 0
      · simp only [F,hz,ENNReal.ofReal_zero,zero_mul,mul_zero,ite_self,lintegral_zero]
        exact zero_le
      have hd : 0 < r z := lt_of_le_of_ne (hr0 z) (Ne.symm hz)
      have hT : 0 < r z / D := div_pos hd hD
      have heF : (fun t => F t z) = (Ici (r z / D)).indicator
          (fun t => ENNReal.ofReal (t ^ (-N - 1)) * (ENNReal.ofReal (r z) * g z)) := by
        funext t
        simp only [F,Set.indicator_apply,mem_Ici,div_le_iff₀ hD]
      have hinter : Ici (r z / D) ∩ Ioi (0 : ℝ) = Ici (r z / D) :=
        inter_eq_left.mpr fun t ht => hT.trans_le ht
      rw [heF,lintegral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici,
        hinter,← restrict_Ioi_eq_restrict_Ici]
      rw [lintegral_mul_const (ENNReal.ofReal (r z) * g z) (by fun_prop)]
      have he : (∫⁻ t in Ioi (r z / D), ENNReal.ofReal (t ^ (-N - 1))) *
          (ENNReal.ofReal (r z) * g z) =
          ENNReal.ofReal (r z) * (∫⁻ t in Ioi (r z / D), ENNReal.ofReal (t ^ (-N - 1))) * g z := by ring
      rw [he,distance_mul_lintegral_ray_tail hN hD hd,
        ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hD.le _) hN.le),mul_assoc]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Segment averaging over `S` gives the Riesz kernel with the coefficient `D^n/n`, for every measurable `g ≥ 0`. -/
private theorem lintegral_segment_average_le_riesz
    {n : ℕ} (hn : 0 < n) {Ω S : Set (EuclideanSpace ℝ (Fin n))}
    (hΩm : MeasurableSet Ω) (hSm : MeasurableSet S) (hΩ : Convex ℝ Ω)
    (hSΩ : S ⊆ Ω) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω)
    {D : ℝ} (hD : 0 < D) (hdiam : ∀ y ∈ S, dist y x ≤ D)
    {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in S,
      g (x + t • (y - x)) * ENNReal.ofReal ‖y - x‖) ≤
      ENNReal.ofReal (D ^ (n : ℝ) / (n : ℝ)) *
        (∫⁻ z in Ω, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ))) * g z) := by
  let J : ℝ → ℝ≥0∞ := fun t => ∫⁻ z in Ω,
    if ‖z - x‖ ≤ t * D then ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) *
      (ENNReal.ofReal ‖z - x‖ * g z) else 0
  have hdom (t : ℝ) : J t = ∫⁻ z in Ω ∩ closedBall x (t * D),
      ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) * (ENNReal.ofReal ‖z - x‖ * g z) := by
    dsimp only [J]
    have he : (fun z => if ‖z - x‖ ≤ t * D then ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) *
        (ENNReal.ofReal ‖z - x‖ * g z) else 0) =
        (closedBall x (t * D)).indicator
          (fun z => ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) * (ENNReal.ofReal ‖z - x‖ * g z)) := by
      funext z
      by_cases hz : ‖z - x‖ ≤ t * D
      · have hb : z ∈ closedBall x (t * D) := by simpa only [mem_closedBall,dist_eq_norm] using hz
        rw [if_pos hz,Set.indicator_of_mem hb]
      · have hb : z ∉ closedBall x (t * D) := by simpa only [mem_closedBall,dist_eq_norm] using hz
        rw [if_neg hz,Set.indicator_of_notMem hb]
    rw [he,lintegral_indicator measurableSet_closedBall,Measure.restrict_restrict measurableSet_closedBall,
      inter_comm]
  have hstep (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      (∫⁻ y in S, g (x + t • (y - x)) * ENNReal.ofReal ‖y - x‖) ≤ J t := by
    let H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y => x + t • (y - x)
    let f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun z => g z * ENNReal.ofReal (‖z - x‖ / t)
    have hH : Measurable H := by fun_prop
    have hf : Measurable f := hg.mul (((measurable_id.sub measurable_const).norm.div_const t).ennreal_ofReal)
    have hnorm (y : EuclideanSpace ℝ (Fin n)) : ‖H y - x‖ = t * ‖y - x‖ := by
      dsimp only [H]
      have he : x + t • (y - x) - x = t • (y - x) := by abel
      rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have hquot (y : EuclideanSpace ℝ (Fin n)) : ‖H y - x‖ / t = ‖y - x‖ := by
      rw [hnorm]
      field_simp
    have heinner : (∫⁻ y in S, g (H y) * ENNReal.ofReal ‖y - x‖) =
        ∫⁻ z, f z ∂Measure.map H ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      rw [lintegral_map hf hH]
      apply lintegral_congr
      intro y
      dsimp only [f]
      rw [hquot]
    have htransport := map_restrict_convex_ray_le hΩm hSm hΩ hSΩ hx hD ht ht1 hdiam
    have hfactor (z : EuclideanSpace ℝ (Fin n)) :
        ENNReal.ofReal (t ^ (-(n : ℝ))) * f z =
          ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) * (ENNReal.ofReal ‖z - x‖ * g z) := by
      dsimp only [f]
      have he : t ^ (-(n : ℝ)) * (‖z - x‖ / t) = t ^ (-(n : ℝ) - 1) * ‖z - x‖ := by
        rw [Real.rpow_sub ht,Real.rpow_one]
        ring
      calc
        _ = (ENNReal.ofReal (t ^ (-(n : ℝ))) * ENNReal.ofReal (‖z - x‖ / t)) * g z := by ring
        _ = ENNReal.ofReal (t ^ (-(n : ℝ)) * (‖z - x‖ / t)) * g z := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
        _ = _ := by rw [he,ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),mul_assoc]
    change (∫⁻ y in S, g (H y) * ENNReal.ofReal ‖y - x‖) ≤ _
    rw [heinner,hdom]
    calc
      _ ≤ ∫⁻ z, f z ∂(ENNReal.ofReal (t ^ (-(n : ℝ))) •
          (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Ω ∩ closedBall x (t * D))) :=
        lintegral_mono' htransport le_rfl
      _ = ∫⁻ z in Ω ∩ closedBall x (t * D), ENNReal.ofReal (t ^ (-(n : ℝ))) * f z := by
        rw [lintegral_smul_measure,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,smul_eq_mul]
      _ = _ := lintegral_congr hfactor
  rw [← restrict_Ioc_eq_restrict_Icc]
  calc
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, J t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hstep t ht.1 ht.2
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), J t :=
      lintegral_mono' (Measure.restrict_mono (fun _ ht => ht.1) le_rfl) le_rfl
    _ ≤ _ := lintegral_ray_layers_le_riesz_kernel ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω)
      (by fun_prop) (fun z => norm_nonneg (z - x)) hg (by exact_mod_cast hn) hD

/-- **Convex `C¹` Riesz representation** (GT 2001 Lemma 7.16, smooth step, mass form): for `u` of class `C¹`
on an open convex `Ω`, measurable `S ⊆ Ω`, `x ∈ Ω` and `dist y x ≤ D` on `S`,
`|S| · |u x − u_S| ≤ (D^n/n) ∫_Ω |z − x|^{1−n} ‖Du z‖`. -/
theorem measure_mul_abs_sub_average_le_riesz_of_contDiffOn
    {n : ℕ} (hn : 0 < n) {Ω S : Set (EuclideanSpace ℝ (Fin n))}
    (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω) (hSm : MeasurableSet S) (hSΩ : S ⊆ Ω)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u Ω)
    (huS : IntegrableOn u S (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    {D : ℝ} (hD : 0 < D) (hdiam : ∀ y ∈ S, dist y x ≤ D) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) S *
      ENNReal.ofReal |u x - ⨍ y in S, u y| ≤
      ENNReal.ofReal (D ^ (n : ℝ) / (n : ℝ)) *
        (∫⁻ z in Ω, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)) * ‖fderiv ℝ u z‖)) := by
  classical
  have hSball : S ⊆ closedBall x D := fun y hy => hdiam y hy
  have hSfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) S ≠ ∞ :=
    ((measure_mono hSball).trans_lt measure_closedBall_lt_top).ne
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hSfin
  let g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := Ω.indicator (fun z => ENNReal.ofReal ‖fderiv ℝ u z‖)
  have hgc : ContinuousOn (fun z => ENNReal.ofReal ‖fderiv ℝ u z‖) Ω :=
    ENNReal.continuous_ofReal.comp_continuousOn (hu.continuousOn_fderiv_of_isOpen hΩo le_rfl).norm
  have hgm : Measurable g := hgc.measurable_piecewise continuousOn_const hΩo.measurableSet
  let F : EuclideanSpace ℝ (Fin n) → ℝ → ℝ≥0∞ := fun y t =>
    g (x + t • (y - x)) * ENNReal.ofReal ‖y - x‖
  have hF : Measurable (Function.uncurry F) :=
    (hgm.comp (measurable_const.add (measurable_snd.smul (measurable_fst.sub measurable_const)))).mul
      (measurable_fst.sub measurable_const).norm.ennreal_ofReal
  have hinner (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ S) :
      ENNReal.ofReal |u x - u y| ≤ ∫⁻ t in Icc (0 : ℝ) 1, F y t := by
    rw [abs_sub_comm]
    refine (enorm_sub_le_lintegral_segment_fderiv_of_contDiffOn hΩo hΩ hu x hx y (hSΩ hy)).trans_eq ?_
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hp := hΩ.add_smul_sub_mem hx (hSΩ hy) ht
    dsimp only [F,g]
    rw [Set.indicator_of_mem hp,ENNReal.ofReal_mul (norm_nonneg _)]
  have havg := measure_mul_enorm_sub_average_le_lintegral
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) huS (u x)
  rw [Measure.restrict_apply_univ] at havg
  refine havg.trans ?_
  calc
    _ ≤ ∫⁻ y in S, ∫⁻ t in Icc (0 : ℝ) 1, F y t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hSm] with y hy
      exact hinner y hy
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in S, F y t :=
      lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ENNReal.ofReal (D ^ (n : ℝ) / (n : ℝ)) *
        (∫⁻ z in Ω, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ))) * g z) :=
      lintegral_segment_average_le_riesz hn hΩo.measurableSet hSm hΩ hSΩ hx hD hdiam hgm
    _ = _ := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hΩo.measurableSet] with z hz
      dsimp only [g]
      rw [Set.indicator_of_mem hz,ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]

end FunctionalInequalities.Analysis
