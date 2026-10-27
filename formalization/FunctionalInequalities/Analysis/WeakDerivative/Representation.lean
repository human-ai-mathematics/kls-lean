import FunctionalInequalities.Analysis.RieszPotential.Representation
import FunctionalInequalities.Analysis.RieszPotential.Critical
import FunctionalInequalities.Analysis.WeakDerivative.Approximation
import FunctionalInequalities.Analysis.WeakDerivative.Products
import FunctionalInequalities.L2.Components
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Riesz representation and John–Nirenberg for bounded weak `H¹_loc` data

For a bounded open convex `Ω ⊆ ℝⁿ` (`n ≥ 2`, diameter at most `D`), a measurable `S ⊆ Ω` and a GLOBALLY bounded weak
`H¹_loc` function `H` with coordinate weak derivatives `a` in `L²_loc`:
`|S| · |H x − H_S| ≤ (D^n/n) ∫_Ω |z − x|^{1−n} √(Σ aᵢ²)` for a.e. `x ∈ Ω`
(`measure_mul_abs_sub_average_le_riesz_of_bounded_weak_data`), by a cutoff, the smooth approximation of bounded compact
weak data and an `L¹`-controlled subsequence of potential errors. With the all-ball Morrey bound
`∫_{Ω ∩ B(x,r)} √(Σ aᵢ²) ≤ K r^{n−1}`, `exp((σ/K)|H − H_Ω|)` is integrable with `σ = [2(n−1)e]⁻¹ n |Ω|/D^n` and integral
at most `2 ω_n n/(n−1) (1 + 4(n−1)²) D^n` (`integrable_exp_abs_sub_average_of_bounded_weak_morrey`): the critical
John–Nirenberg estimate of Gilbarg–Trudinger (2001), Theorem 7.21, with its volume/diameter normalization.
This is the bounded global weak `H¹_loc` application class of Lemma 7.16, not the domain-only `W^{1,1}(Ω)` class; `n = 1`
is not covered.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

open FunctionalInequalities.L2 (memLp_sqrt_sum_sq gradient_density_l1_of_coordinate_l2)

/-- The operator norm of a scalar functional is the Euclidean norm of its coordinates. -/
private theorem norm_linearFunctional_eq_sqrt_sum_sq_basis {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖L‖ = Real.sqrt (∑ i : Fin n, (L (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) := by
  let v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L
  have hnorm : ‖v‖ = ‖L‖ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.norm_map L
  have hinner (i : Fin n) : inner ℝ v (EuclideanSpace.basisFun (Fin n) ℝ i) =
      L (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    have h := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).apply_symm_apply L)
    exact h
  have hsum : (∑ i : Fin n, (L (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) = ‖v‖ ^ 2 := by
    simpa only [hinner,Real.norm_eq_abs,sq_abs] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_norm_inner_left v
  rw [hsum,Real.sqrt_sq (norm_nonneg v)]
  exact hnorm.symm

/-- Vanishing `ℝ≥0∞` `L¹` mass with a.e. finite terms gives an a.e. vanishing subsequence. -/
private theorem exists_subsequence_tendsto_zero_of_lintegral_tendsto_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : ℕ → X → ℝ≥0∞}
    (hEm : ∀ m, AEMeasurable (E m) μ)
    (hEf : ∀ m, ∀ᵐ x ∂μ, E m x < ∞)
    (hE : Tendsto (fun m => ∫⁻ x, E m x ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => E (φ k) x) atTop (𝓝 0) := by
  have hm (m : ℕ) : AEStronglyMeasurable (fun x => (E m x).toReal) μ :=
    (hEm m).ennreal_toReal.aestronglyMeasurable
  have hbound (m : ℕ) : eLpNorm (fun x => (E m x).toReal) 1 μ ≤ ∫⁻ x, E m x ∂μ := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    apply lintegral_mono
    intro x
    change ‖(E m x).toReal‖ₑ ≤ E m x
    rw [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  have hnorm : Tendsto (fun m => eLpNorm (fun x => (E m x).toReal) 1 μ)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE
      (fun _ => zero_le) hbound
  have hmeasure : TendstoInMeasure μ (fun m x => (E m x).toReal) atTop (fun _ => (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero hm aestronglyMeasurable_const
    change Tendsto (fun m => eLpNorm (fun x => (E m x).toReal - 0) 1 μ) atTop (𝓝 0)
    simpa only [sub_zero] using hnorm
  obtain ⟨φ,hφ,hconv⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨φ,hφ,?_⟩
  filter_upwards [hconv,ae_all_iff.2 hEf] with x hx hfin
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx
  have hid : (fun k => ENNReal.ofReal ((E (φ k) x).toReal)) = fun k => E (φ k) x :=
    funext fun k => ENNReal.ofReal_toReal (hfin (φ k)).ne
  change Tendsto (fun k => ENNReal.ofReal ((E (φ k) x).toReal)) atTop (𝓝 (ENNReal.ofReal 0)) at h
  rw [hid] at h
  simpa only [ENNReal.ofReal_zero] using h

/-- Bounded a.e. convergence on a finite measure gives `L¹` and average convergence. -/
private theorem l1_average_tendsto_of_bounded_ae_tendsto
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {u : ℕ → X → ℝ} {f : X → ℝ} {C : ℝ}
    (hum : ∀ m, AEStronglyMeasurable (u m) μ) (hfm : AEStronglyMeasurable f μ)
    (huB : ∀ m x, ‖u m x‖ ≤ C) (hfB : ∀ x, ‖f x‖ ≤ C)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun m => u m x) atTop (𝓝 (f x))) :
    (∀ m, Integrable (u m) μ) ∧ Integrable f μ ∧
      Tendsto (fun m => ∫ x, |u m x - f x| ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun m => ⨍ x, u m x ∂μ) atTop (𝓝 (⨍ x, f x ∂μ)) := by
  have huI (m : ℕ) : Integrable (u m) μ :=
    (integrable_const C).mono' (hum m) (ae_of_all _ (huB m))
  have hfI : Integrable f μ :=
    (integrable_const C).mono' hfm (ae_of_all _ hfB)
  have hdM (m : ℕ) : AEStronglyMeasurable (fun x => |u m x - f x|) μ := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using ((hum m).sub hfm).norm
  have hdB (m : ℕ) : ∀ᵐ x ∂μ, ‖|u m x - f x|‖ ≤ 2 * C := by
    apply ae_of_all
    intro x
    simpa only [Real.norm_eq_abs,abs_abs] using
      (norm_sub_le (u m x) (f x)).trans (by linarith [huB m x,hfB x])
  have hdlim : ∀ᵐ x ∂μ, Tendsto (fun m => |u m x - f x|) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hconv] with x hx
    simpa only [sub_self,norm_zero,Real.norm_eq_abs] using (hx.sub_const (f x)).norm
  have hd := tendsto_integral_of_dominated_convergence (fun _ => 2 * C) hdM
    (integrable_const _) hdB hdlim
  have hi := tendsto_integral_of_dominated_convergence (fun _ => C) hum
    (integrable_const _) (fun m => ae_of_all _ (huB m)) hconv
  refine ⟨huI,hfI,?_,?_⟩
  · simpa only [integral_zero] using hd
  · simp_rw [average_eq]
    exact tendsto_const_nhds.smul hi

/-- The convex representation passes to `L¹` gradient-density limits of `C¹` approximations. -/
private theorem measure_mul_abs_sub_average_le_riesz_of_smooth_approximation
    {n : ℕ} (hn : 2 ≤ n) {Ω S : Set (EuclideanSpace ℝ (Fin n))}
    (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω) (hΩne : Ω.Nonempty)
    (hSm : MeasurableSet S) (hSΩ : S ⊆ Ω) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ y ∈ Ω, ∀ z ∈ Ω, dist y z ≤ D)
    {η ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hηS : IntegrableOn η S (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hρ : IntegrableOn ρ Ω (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hθ : ∀ m, ContDiffOn ℝ 1 (θ m) Ω)
    (hθS : ∀ m, IntegrableOn (θ m) S (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hθae : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω),
      Tendsto (fun m => θ m x) atTop (𝓝 (η x)))
    (havg : Tendsto (fun m => ⨍ y in S, θ m y) atTop (𝓝 (⨍ y in S, η y)))
    (herror : ∀ m, IntegrableOn (fun z => ‖fderiv ℝ (θ m) z‖ - ρ z) Ω
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (herrorconv : Tendsto (fun m => ∫ z in Ω, |‖fderiv ℝ (θ m) z‖ - ρ z|)
      atTop (𝓝 0)) :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω),
      (volume : Measure (EuclideanSpace ℝ (Fin n))) S *
        ENNReal.ofReal |η x - ⨍ y in S, η y| ≤
      ENNReal.ofReal (D ^ (n : ℝ) / (n : ℝ)) *
        (∫⁻ z in Ω, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)) * |ρ z|)) := by
  have _hηS := hηS
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω
  let P := fun x => ∫⁻ z in Ω, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)) * |ρ z|)
  let E := fun m x => ∫⁻ z in Ω,
    ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)) * |‖fderiv ℝ (θ m) z‖ - ρ z|)
  let c := ENNReal.ofReal (D ^ (n : ℝ) / (n : ℝ))
  let A := (volume : Measure (EuclideanSpace ℝ (Fin n))) S
  obtain ⟨x0,hx0⟩ := hΩne
  have hnonempty : Ω.Nonempty := ⟨x0,hx0⟩
  have hAfin : A ≠ ∞ :=
    ((measure_mono (show S ⊆ closedBall x0 D from fun y hy => hdiam y (hSΩ hy) x0 hx0)).trans_lt
      measure_closedBall_lt_top).ne
  have hPfinite : ∀ᵐ x ∂μ, P x < ∞ :=
    (lintegral_riesz_potential_le_diameter_mul_lintegral hn hΩo.measurableSet hnonempty hD hdiam hρ).2.1
  have hEb (m : ℕ) :=
    lintegral_riesz_potential_le_diameter_mul_lintegral hn hΩo.measurableSet hnonempty hD hdiam (herror m)
  have hEconv : Tendsto (fun m => ∫⁻ x, E m x ∂μ) atTop (𝓝 0) := by
    let K := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (n : ℝ) * D
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hh : Tendsto (fun m => ENNReal.ofReal K *
        ENNReal.ofReal (∫ z in Ω, |‖fderiv ℝ (θ m) z‖ - ρ z|)) atTop (𝓝 0) := by
      have H : Tendsto (fun m => ENNReal.ofReal (∫ z in Ω, |‖fderiv ℝ (θ m) z‖ - ρ z|))
          atTop (𝓝 (ENNReal.ofReal 0)) := ENNReal.continuous_ofReal.continuousAt.tendsto.comp herrorconv
      simpa only [ENNReal.ofReal_zero,mul_zero] using
        ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) H (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => zero_le)
    intro m
    simpa only [K,ENNReal.ofReal_mul hK] using (hEb m).2.2
  obtain ⟨φ,hφ,hEae⟩ := exists_subsequence_tendsto_zero_of_lintegral_tendsto_zero
    (E := E) (fun m => (hEb m).1) (fun m => (hEb m).2.1) hEconv
  have hρm : AEMeasurable (fun z => ENNReal.ofReal |ρ z|) μ := by
    simpa only [Real.norm_eq_abs] using hρ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
  have hineq (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
      A * ENNReal.ofReal |θ m x - ⨍ y in S, θ m y| ≤ c * (P x + E m x) := by
    refine (measure_mul_abs_sub_average_le_riesz_of_contDiffOn (by omega) hΩo hΩ hSm hSΩ
      (hθ m) (hθS m) x hx hD (fun y hy => hdiam y (hSΩ hy) x hx)).trans ?_
    apply mul_le_mul_of_nonneg_left _ zero_le
    calc
      _ ≤ ∫⁻ z in Ω, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)) *
          (|ρ z| + |‖fderiv ℝ (θ m) z‖ - ρ z|)) := by
        apply lintegral_mono
        intro z
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
        have H := le_abs_self (‖fderiv ℝ (θ m) z‖ - ρ z)
        linarith [le_abs_self (ρ z)]
      _ = P x + E m x := by
        have hk : AEMeasurable (fun z => ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) μ :=
          ((measurable_id.sub measurable_const).norm.pow_const _).ennreal_ofReal.aemeasurable
        have hleft := hk.mul hρm
        simp_rw [mul_add,ENNReal.ofReal_add
          (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (abs_nonneg _))
          (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (abs_nonneg _))]
        apply lintegral_add_left'
        convert hleft using 1
        funext z
        exact ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)
  filter_upwards [hθae,hEae,hPfinite,ae_restrict_mem hΩo.measurableSet] with x hx hEx hPx hxΩ
  have hleft : Tendsto (fun k => A * ENNReal.ofReal |θ (φ k) x - ⨍ y in S, θ (φ k) y|)
      atTop (𝓝 (A * ENNReal.ofReal |η x - ⨍ y in S, η y|)) := by
    have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((hx.comp hφ.tendsto_atTop).sub (havg.comp hφ.tendsto_atTop)).abs)
    exact ENNReal.Tendsto.const_mul H (Or.inr hAfin)
  have hright : Tendsto (fun k => c * (P x + E (φ k) x)) atTop (𝓝 (c * P x)) := by
    have H : Tendsto (fun k => P x + E (φ k) x) atTop (𝓝 (P x + 0)) :=
      tendsto_const_nhds.add hEx
    simpa only [add_zero] using ENNReal.Tendsto.const_mul (a := c) H (Or.inr ENNReal.ofReal_ne_top)
  exact le_of_tendsto_of_tendsto' hleft hright (fun k => hineq (φ k) x hxΩ)

/-- The representation for compactly supported bounded weak `H¹` data with global `L²` derivatives. -/
private theorem measure_mul_abs_sub_average_le_riesz_of_compact_bounded_weak_data
    {n : ℕ} (hn : 2 ≤ n) {Ω S : Set (EuclideanSpace ℝ (Fin n))}
    (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω) (hΩne : Ω.Nonempty)
    (hSm : MeasurableSet S) (hSΩ : S ⊆ Ω) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ y ∈ Ω, ∀ z ∈ Ω, dist y z ≤ D)
    {η : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {C : ℝ} (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hηK : Function.support η ⊆ K) (haK : ∀ i, Function.support (a i) ⊆ K)
    (hweak : ∀ i, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω),
      (volume : Measure (EuclideanSpace ℝ (Fin n))) S * ENNReal.ofReal |η x - ⨍ y in S, η y| ≤
      ENNReal.ofReal (D ^ (n : ℝ) / (n : ℝ)) *
        (∫⁻ z in Ω, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)) * Real.sqrt (∑ i : Fin n, (a i z)^2))) := by
  obtain ⟨T,_hT,_hTK,_hηT,_haT,θ,hθ,hconv,hae⟩ :=
    exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset
      hη hbound hK hηK haK (by norm_num : (0 : ℝ) < 1) hweak ha2
  obtain ⟨x0,hx0⟩ := hΩne
  have hnonempty : Ω.Nonempty := ⟨x0,hx0⟩
  have hΩball : Ω ⊆ closedBall x0 D := fun y hy => hdiam y hy x0 hx0
  have hΩfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) Ω ≠ ∞ :=
    ((measure_mono hΩball).trans_lt measure_closedBall_lt_top).ne
  have hSfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) S ≠ ∞ :=
    ((measure_mono (hSΩ.trans hΩball)).trans_lt measure_closedBall_lt_top).ne
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩfin
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hSfin
  have hC : 0 ≤ C := (norm_nonneg (η 0)).trans (hbound 0)
  have havgdata := l1_average_tendsto_of_bounded_ae_tendsto
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)
    (C := 3 * C) (fun m => (hθ m).1.continuous.aestronglyMeasurable.restrict)
    (hη.aestronglyMeasurable.restrict) (fun m => (hθ m).2.2.2.1)
    (fun x => (hbound x).trans (by linarith)) (ae_restrict_of_ae hae)
  let g := fun m (i : Fin n) x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i)
  let ρ := fun x => Real.sqrt (∑ i : Fin n, (a i x)^2)
  have hg (m : ℕ) (i : Fin n) : MemLp (g m i) 2 μ := ((hθ m).2.2.2.2 i).2.restrict Ω
  have ha (i : Fin n) : MemLp (a i) 2 μ := (ha2 i).restrict Ω
  have hc (i : Fin n) : Tendsto (fun m => eLpNorm (fun x => g m i x - a i x) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv i) (fun _ => zero_le)
    intro m
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  obtain ⟨hd1,hdconv⟩ := gradient_density_l1_of_coordinate_l2 hg ha hc
  have hρ : Integrable ρ μ := MemLp.integrable le_rfl ((memLp_sqrt_sum_sq ha).mono_exponent (by norm_num))
  have hid (m : ℕ) : (fun x => ‖fderiv ℝ (θ m) x‖ - ρ x) =
      fun x => Real.sqrt (∑ i : Fin n, (g m i x)^2) - Real.sqrt (∑ i : Fin n, (a i x)^2) := by
    funext x
    rw [norm_linearFunctional_eq_sqrt_sum_sq_basis]
  have heI (m : ℕ) : Integrable (fun x => ‖fderiv ℝ (θ m) x‖ - ρ x) μ := by
    rw [hid m]
    exact MemLp.integrable le_rfl (hd1 m)
  have herrconv : Tendsto (fun m => ∫ x in Ω, |‖fderiv ℝ (θ m) x‖ - ρ x|) atTop (𝓝 0) := by
    have H := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hdconv
    have heq (m : ℕ) :
        (eLpNorm (fun x => Real.sqrt (∑ i : Fin n, (g m i x)^2) -
          Real.sqrt (∑ i : Fin n, (a i x)^2)) 1 μ).toReal =
          ∫ x in Ω, |‖fderiv ℝ (θ m) x‖ - ρ x| := by
      rw [eLpNorm_one_eq_lintegral_enorm,← integral_norm_eq_lintegral_enorm (hd1 m).aestronglyMeasurable]
      apply integral_congr_ae
      apply ae_of_all
      intro x
      change ‖Real.sqrt (∑ i : Fin n, (g m i x)^2) - Real.sqrt (∑ i : Fin n, (a i x)^2)‖ =
        |‖fderiv ℝ (θ m) x‖ - ρ x|
      rw [← congrFun (hid m) x]
      exact Real.norm_eq_abs _
    simpa only [Function.comp_def,heq,ENNReal.toReal_zero] using H
  have result := measure_mul_abs_sub_average_le_riesz_of_smooth_approximation hn hΩo hΩ hnonempty
    hSm hSΩ hD hdiam havgdata.2.1 hρ
    (fun m => (hθ m).1.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffOn)
    havgdata.1 (ae_restrict_of_ae hae) havgdata.2.2.2 heI herrconv
  simpa only [ρ,abs_of_nonneg (Real.sqrt_nonneg _)] using result

/-- **Riesz representation for bounded weak `H¹_loc` data** (`n ≥ 2`): on a bounded open convex `Ω` of diameter at
most `D` and measurable `S ⊆ Ω`, `|S| · |H x − H_S| ≤ (D^n/n) ∫_Ω |z − x|^{1−n} √(Σ aᵢ²)` for a.e. `x ∈ Ω`. -/
theorem measure_mul_abs_sub_average_le_riesz_of_bounded_weak_data
    {n : ℕ} (hn : 2 ≤ n) {Ω S : Set (EuclideanSpace ℝ (Fin n))}
    (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω) (hΩne : Ω.Nonempty)
    (hSm : MeasurableSet S) (hSΩ : S ⊆ Ω) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ y ∈ Ω, ∀ z ∈ Ω, dist y z ≤ D)
    {H : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {C : ℝ} (hH : LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖H x‖ ≤ C)
    (hweak : ∀ i, HasWeakDerivAlong H (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i, ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K)) :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω),
      (volume : Measure (EuclideanSpace ℝ (Fin n))) S * ENNReal.ofReal |H x - ⨍ y in S, H y| ≤
      ENNReal.ofReal (D ^ (n : ℝ) / (n : ℝ)) *
        (∫⁻ z in Ω, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)) * Real.sqrt (∑ i : Fin n, (a i z)^2))) := by
  obtain ⟨x0,hx0⟩ := hΩne
  have hnonempty : Ω.Nonempty := ⟨x0,hx0⟩
  let ψ : ContDiffBump x0 := ⟨D + 1,D + 2,by linarith,by linarith⟩
  have hψon (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
      (ψ : EuclideanSpace ℝ (Fin n) → ℝ) =ᶠ[𝓝 x] (fun _ => 1) := by
    apply ψ.eventuallyEq_one_of_mem_ball
    change dist x x0 < D + 1
    linarith [hdiam x hx x0 hx0]
  have hψone (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) : ψ x = 1 :=
    (hψon x hx).eq_of_nhds
  have hψder (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
      fderiv ℝ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) x = 0 := by
    rw [(hψon x hx).fderiv_eq]
    simp only [fderiv_const_apply]
  let η := fun x => ψ x * H x
  let b := fun (i : Fin n) x => ψ x * a i x +
    fderiv ℝ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ i) * H x
  have hHtop (K : Set (EuclideanSpace ℝ (Fin n))) (_hK : IsCompact K) :
      MemLp H ∞ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) :=
    memLp_top_of_bound hH.aestronglyMeasurable.restrict C (ae_of_all _ hbound)
  have hprod (i : Fin n) := (hweak i).compact_mul_data (ha2 i) hHtop ψ.contDiff ψ.hasCompactSupport
  have hηbound (x : EuclideanSpace ℝ (Fin n)) : ‖η x‖ ≤ C := by
    calc
      _ = ‖ψ x‖ * ‖H x‖ := norm_mul _ _
      _ ≤ 1 * ‖H x‖ := mul_le_mul_of_nonneg_right
        (by rw [Real.norm_eq_abs,abs_of_nonneg (ψ.nonneg)]; exact ψ.le_one) (norm_nonneg _)
      _ = ‖H x‖ := one_mul _
      _ ≤ C := hbound x
  have hηK : Function.support η ⊆ tsupport (ψ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    (Function.support_mul_subset_left _ _).trans subset_closure
  have hbK (i : Fin n) : Function.support (b i) ⊆ tsupport (ψ : EuclideanSpace ℝ (Fin n) → ℝ) := by
    intro x hx
    by_contra hout
    apply hx
    have hz := image_eq_zero_of_notMem_tsupport hout
    have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hout
    dsimp only [b]
    rw [hz,hd]
    simp only [zero_mul,zero_apply,add_zero]
  have hηeq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) : η x = H x := by
    dsimp only [η]
    rw [hψone x hx,one_mul]
  have hbeq (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) : b i x = a i x := by
    dsimp only [b]
    rw [hψone x hx,hψder x hx]
    simp only [one_mul,zero_apply,zero_mul,add_zero]
  have hηaeS : η =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)] H :=
    (ae_restrict_mem hSm).mono fun x hx => hηeq x (hSΩ hx)
  have havg : (⨍ y in S, η y) = ⨍ y in S, H y := average_congr hηaeS
  have hpotential (x : EuclideanSpace ℝ (Fin n)) :
      (∫⁻ z in Ω, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)) * Real.sqrt (∑ i : Fin n, (b i z)^2))) =
      (∫⁻ z in Ω, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)) * Real.sqrt (∑ i : Fin n, (a i z)^2))) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hΩo.measurableSet] with z hz
    have heq : (fun i : Fin n => b i z) = fun i => a i z := funext fun i => hbeq i z hz
    simp_rw [show ∀ i : Fin n, b i z = a i z from fun i => congrFun heq i]
  have result := measure_mul_abs_sub_average_le_riesz_of_compact_bounded_weak_data (η := η) (a := b) hn hΩo hΩ hnonempty
    hSm hSΩ hD hdiam (hprod ⟨0,by omega⟩).1.1 hηbound ψ.hasCompactSupport hηK hbK
    (fun i => (hprod i).1) (fun i => (hprod i).2.2.2)
  filter_upwards [result,ae_restrict_mem hΩo.measurableSet] with x hx hxΩ
  rw [hηeq x hxΩ,havg,hpotential x] at hx
  exact hx

/-- **Critical John–Nirenberg for bounded weak `H¹_loc` data** (`n ≥ 2`, GT 7.21 normalization): with the all-ball Morrey
bound `K r^{n−1}` (`K > 0`), `σ = [2(n−1)e]⁻¹ n |Ω|/D^n > 0`, `exp((σ/K)|H − H_Ω|)` is integrable on `Ω` and its
integral is at most `2 ω_n n/(n−1) (1 + 4(n−1)²) D^n`. -/
theorem integrable_exp_abs_sub_average_of_bounded_weak_morrey
    {n : ℕ} (hn : 2 ≤ n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω) (hΩne : Ω.Nonempty)
    {D K : ℝ} (hD : 0 < D) (hK : 0 < K)
    (hdiam : ∀ y ∈ Ω, ∀ z ∈ Ω, dist y z ≤ D)
    {H : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {C : ℝ} (hH : LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖H x‖ ≤ C)
    (hweak : ∀ i, HasWeakDerivAlong H (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hmorrey : ∀ x : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
      (∫⁻ y in Ω ∩ ball x r, ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (a i y)^2))) ≤
        ENNReal.ofReal (K * r ^ ((n : ℝ) - 1))) :
    let σ := ((2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹) * (n : ℝ) *
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real Ω / D ^ (n : ℝ)
    0 < σ ∧
      Integrable (fun x => Real.exp ((σ / K) * |H x - ⨍ y in Ω, H y|))
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω) ∧
      (∫ x in Ω, Real.exp ((σ / K) * |H x - ⨍ y in Ω, H y|)) ≤
        2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) *
          (n : ℝ) / ((n : ℝ) - 1)) * (1 + 4 * ((n : ℝ) - 1)^2)) * D ^ (n : ℝ) := by
  intro σ
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω
  let ρ := fun y => Real.sqrt (∑ i : Fin n, (a i y)^2)
  let P := fun x => ∫⁻ y in Ω, ENNReal.ofReal (‖y - x‖ ^ (1 - (n : ℝ)) * |ρ y|)
  let τ := (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹
  let V := (volume : Measure (EuclideanSpace ℝ (Fin n))).real Ω
  have hN : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hNm1 : 0 < (n : ℝ) - 1 := by
    have hn2 : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpow : 0 < D ^ (n : ℝ) := Real.rpow_pos_of_pos hD _
  obtain ⟨x0,hx0⟩ := hΩne
  have hnonempty : Ω.Nonempty := ⟨x0,hx0⟩
  have hΩfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) Ω ≠ ∞ :=
    ((measure_mono (show Ω ⊆ closedBall x0 D from fun y hy => hdiam y hy x0 hx0)).trans_lt
      measure_closedBall_lt_top).ne
  have hV : 0 < V := ENNReal.toReal_pos (hΩo.measure_pos (μ := volume) hnonempty).ne' hΩfin
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩfin
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hσ : 0 < σ := by change 0 < τ * (n : ℝ) * V / D ^ (n : ℝ); positivity
  have hρm : AEStronglyMeasurable ρ μ := by
    apply Real.continuous_sqrt.comp_aestronglyMeasurable
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (((hweak i).2.1.aestronglyMeasurable.restrict).aemeasurable.pow_const (2 : ℕ)).aestronglyMeasurable
  have hm : ∀ x : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
      (∫⁻ y in Ω ∩ ball x r, ENNReal.ofReal |ρ y|) ≤ ENNReal.ofReal (K * r ^ ((n : ℝ) - 1)) := by
    simpa only [ρ,abs_of_nonneg (Real.sqrt_nonneg _)] using hmorrey
  obtain ⟨_,hPfin,hPi,hPle⟩ := integrable_exp_critical_morrey_potential hn hΩo.measurableSet hnonempty
    hρm hD hK hdiam hm
  have hrep := measure_mul_abs_sub_average_le_riesz_of_bounded_weak_data hn hΩo hΩ hnonempty
    hΩo.measurableSet (Subset.refl Ω) hD hdiam hH hbound hweak ha2
  have he : ∀ᵐ x ∂μ, Real.exp ((σ / K) * |H x - ⨍ y in Ω, H y|) ≤
      Real.exp ((τ / K) * (P x).toReal) := by
    filter_upwards [hrep,hPfin] with x hx hfin
    apply Real.exp_le_exp.mpr
    have hc0 : 0 ≤ D ^ (n : ℝ) / (n : ℝ) := by positivity
    have hrhsfin : ENNReal.ofReal (D ^ (n : ℝ) / (n : ℝ)) * P x ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
    have hrepr : (volume : Measure (EuclideanSpace ℝ (Fin n))) Ω *
        ENNReal.ofReal |H x - ⨍ y in Ω, H y| ≤ ENNReal.ofReal (D ^ (n : ℝ) / (n : ℝ)) * P x := by
      simpa only [P,ρ,abs_of_nonneg (Real.sqrt_nonneg _)] using hx
    have hreal := ENNReal.toReal_mono hrhsfin hrepr
    simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _),ENNReal.toReal_ofReal hc0] at hreal
    change V * |H x - ⨍ y in Ω, H y| ≤ (D ^ (n : ℝ) / (n : ℝ)) * (P x).toReal at hreal
    have hscaled := mul_le_mul_of_nonneg_left hreal
      (show 0 ≤ (τ / K) * ((n : ℝ) / D ^ (n : ℝ)) by positivity)
    have hscale : σ / K = ((τ / K) * ((n : ℝ) / D ^ (n : ℝ))) * V := by
      dsimp only [σ,τ,V]
      ring
    have hcancel : ((τ / K) * ((n : ℝ) / D ^ (n : ℝ))) * (D ^ (n : ℝ) / (n : ℝ)) = τ / K := by
      field_simp [hN.ne',hpow.ne',hK.ne']
    calc
      _ = ((τ / K) * ((n : ℝ) / D ^ (n : ℝ))) * (V * |H x - ⨍ y in Ω, H y|) := by rw [hscale]; ring
      _ ≤ ((τ / K) * ((n : ℝ) / D ^ (n : ℝ))) * ((D ^ (n : ℝ) / (n : ℝ)) * (P x).toReal) := hscaled
      _ = _ := by rw [← mul_assoc,hcancel]
  have hEm : AEStronglyMeasurable (fun x => Real.exp ((σ / K) * |H x - ⨍ y in Ω, H y|)) μ := by
    apply Real.continuous_exp.comp_aestronglyMeasurable
    have hd : AEStronglyMeasurable (fun x => H x - ⨍ y in Ω, H y) μ :=
      (show AEStronglyMeasurable H μ from hH.aestronglyMeasurable.restrict).sub aestronglyMeasurable_const
    simpa only [Real.norm_eq_abs] using hd.norm.const_mul (σ / K)
  have hEi : Integrable (fun x => Real.exp ((σ / K) * |H x - ⨍ y in Ω, H y|)) μ :=
    hPi.mono_nonneg hEm (ae_of_all _ fun x => (Real.exp_pos _).le) he
  exact ⟨hσ,hEi,(integral_mono_ae hEi hPi he).trans hPle⟩


/-! ## Dimension one

The one-dimensional case of Gilbarg–Trudinger (2001), Lemma 7.16, for bounded weak data: the kernel `|z − x|^{0} = 1`
gives `|S| |H(x) − H_S| ≤ D ∫_Ω |DH|` a.e. on an open convex `Ω` of diameter at most `D` (no Riesz potential), and a
density mass `∫_Ω |DH| ≤ K` with `t D K ≤ |Ω|` gives `t |H − H_Ω| ≤ 1` a.e. and `∫_Ω exp(t |H − H_Ω|) ≤ e |Ω|`. This is
the one-dimensional replacement for the John–Nirenberg step; the `n ≥ 2` exponent `(2(n−1)e)⁻¹` is not used. -/

section OneDimensional


/-- Dimension-one convex representation passes directly through the L1 density error, with kernel1 and constantD. -/
private theorem measure_mul_abs_sub_average_le_of_smooth_approximation_one
    {Ω S : Set (EuclideanSpace ℝ (Fin 1))}
    (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω) (hΩne : Ω.Nonempty)
    (hSm : MeasurableSet S) (hSΩ : S ⊆ Ω) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ y ∈ Ω, ∀ z ∈ Ω, dist y z ≤ D)
    {η ρ : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hρ : IntegrableOn ρ Ω (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    {θ : ℕ → EuclideanSpace ℝ (Fin 1) → ℝ}
    (hθ : ∀ m, ContDiffOn ℝ 1 (θ m) Ω)
    (hθS : ∀ m, IntegrableOn (θ m) S (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (hθae : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict Ω),
      Tendsto (fun m => θ m x) atTop (𝓝 (η x)))
    (havg : Tendsto (fun m => ⨍ y in S, θ m y) atTop (𝓝 (⨍ y in S, η y)))
    (herror : ∀ m, IntegrableOn (fun z => ‖fderiv ℝ (θ m) z‖ - ρ z) Ω
      (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (herrorconv : Tendsto (fun m => ∫ z in Ω, |‖fderiv ℝ (θ m) z‖ - ρ z|) atTop (𝓝 0)) :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict Ω),
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) S * ENNReal.ofReal |η x - ⨍ y in S, η y| ≤
        ENNReal.ofReal D * ENNReal.ofReal (∫ z in Ω, |ρ z|) := by
  obtain ⟨x0,hx0⟩ := hΩne
  let A := (volume : Measure (EuclideanSpace ℝ (Fin 1))) S
  have hAfin : A ≠ ∞ :=
    ((measure_mono (show S ⊆ closedBall x0 D from fun y hy => hdiam y (hSΩ hy) x0 hx0)).trans_lt
      measure_closedBall_lt_top).ne
  have hgI (m : ℕ) : IntegrableOn (fun z => ‖fderiv ℝ (θ m) z‖) Ω volume := by
    have H := (herror m).add hρ
    have heq : ((fun z => ‖fderiv ℝ (θ m) z‖-ρ z)+ρ) = fun z => ‖fderiv ℝ (θ m) z‖ := by
      funext z
      simp only [Pi.add_apply]
      ring
    rw [heq] at H
    exact H
  have hgrad (m : ℕ) : (∫ z in Ω, ‖fderiv ℝ (θ m) z‖) ≤
      (∫ z in Ω, |ρ z|) + (∫ z in Ω, |‖fderiv ℝ (θ m) z‖-ρ z|) := by
    rw [← integral_add hρ.abs (herror m).abs]
    apply integral_mono (hgI m) (hρ.abs.add (herror m).abs)
    intro z
    change ‖fderiv ℝ (θ m) z‖ ≤ |ρ z|+|‖fderiv ℝ (θ m) z‖-ρ z|
    linarith [le_abs_self (ρ z),le_abs_self (‖fderiv ℝ (θ m) z‖-ρ z)]
  have hineq (m : ℕ) (x : EuclideanSpace ℝ (Fin 1)) (hx : x ∈ Ω) :
      A * ENNReal.ofReal |θ m x-⨍ y in S,θ m y| ≤ ENNReal.ofReal D *
        ENNReal.ofReal ((∫ z in Ω,|ρ z|)+(∫ z in Ω,|‖fderiv ℝ (θ m) z‖-ρ z|)) := by
    have H := FunctionalInequalities.Analysis.measure_mul_abs_sub_average_le_riesz_of_contDiffOn
      (by norm_num : 0 < (1 : ℕ)) hΩo hΩ hSm hSΩ (hθ m) (hθS m) x hx hD
      (fun y hy => hdiam y (hSΩ hy) x hx)
    norm_num only [Nat.cast_one,sub_self,Real.rpow_zero,one_mul,Real.rpow_one,div_one] at H
    rw [← ofReal_integral_eq_lintegral_ofReal (hgI m) (ae_of_all _ fun _ => norm_nonneg _)] at H
    exact H.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hgrad m)) zero_le)
  filter_upwards [hθae,ae_restrict_mem hΩo.measurableSet] with x hx hxΩ
  have hleft : Tendsto (fun m => A*ENNReal.ofReal |θ m x-⨍ y in S,θ m y|) atTop
      (𝓝 (A*ENNReal.ofReal |η x-⨍ y in S,η y|)) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hx.sub havg).abs)) (Or.inr hAfin)
  have hright : Tendsto (fun m => ENNReal.ofReal D *
      ENNReal.ofReal ((∫ z in Ω,|ρ z|)+(∫ z in Ω,|‖fderiv ℝ (θ m) z‖-ρ z|))) atTop
      (𝓝 (ENNReal.ofReal D*ENNReal.ofReal (∫ z in Ω,|ρ z|))) := by
    have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := ∫ z in Ω,|ρ z|)).add herrorconv)
    simpa only [add_zero,Function.comp_def] using ENNReal.Tendsto.const_mul H (Or.inr ENNReal.ofReal_ne_top)
  exact le_of_tendsto_of_tendsto' hleft hright (fun m => hineq m x hxΩ)

private theorem measure_mul_abs_sub_average_le_of_compact_bounded_weak_data_one
    {Ω S : Set (EuclideanSpace ℝ (Fin 1))}
    (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω) (hΩne : Ω.Nonempty)
    (hSm : MeasurableSet S) (hSΩ : S ⊆ Ω) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ y ∈ Ω, ∀ z ∈ Ω, dist y z ≤ D)
    {η : EuclideanSpace ℝ (Fin 1) → ℝ} {a : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ}
    {C : ℝ} (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (hbound : ∀ x, ‖η x‖ ≤ C) {K : Set (EuclideanSpace ℝ (Fin 1))} (hK : IsCompact K)
    (hηK : Function.support η ⊆ K) (haK : ∀ i, Function.support (a i) ⊆ K)
    (hweak : ∀ i, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin 1) ℝ i))
    (ha2 : ∀ i, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1)))) :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict Ω),
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) S * ENNReal.ofReal |η x - ⨍ y in S, η y| ≤
      ENNReal.ofReal D * ENNReal.ofReal (∫ z in Ω, Real.sqrt (∑ i : Fin 1, (a i z)^2)) := by
  obtain ⟨T,_hT,_hTK,_hηT,_haT,θ,hθ,hconv,hae⟩ :=
    exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset
      hη hbound hK hηK haK (by norm_num : (0 : ℝ) < 1) hweak ha2
  obtain ⟨x0,hx0⟩ := hΩne
  have hnonempty : Ω.Nonempty := ⟨x0,hx0⟩
  have hΩball : Ω ⊆ closedBall x0 D := fun y hy => hdiam y hy x0 hx0
  have hΩfin : (volume : Measure (EuclideanSpace ℝ (Fin 1))) Ω ≠ ∞ :=
    ((measure_mono hΩball).trans_lt measure_closedBall_lt_top).ne
  have hSfin : (volume : Measure (EuclideanSpace ℝ (Fin 1))) S ≠ ∞ :=
    ((measure_mono (hSΩ.trans hΩball)).trans_lt measure_closedBall_lt_top).ne
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict Ω
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩfin
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict S) :=
    isFiniteMeasure_restrict.mpr hSfin
  have hC : 0 ≤ C := (norm_nonneg (η 0)).trans (hbound 0)
  have havgdata := l1_average_tendsto_of_bounded_ae_tendsto
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict S)
    (C := 3 * C) (fun m => (hθ m).1.continuous.aestronglyMeasurable.restrict)
    (hη.aestronglyMeasurable.restrict) (fun m => (hθ m).2.2.2.1)
    (fun x => (hbound x).trans (by linarith)) (ae_restrict_of_ae hae)
  let g := fun m (i : Fin 1) x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 1) ℝ i)
  let ρ := fun x => Real.sqrt (∑ i : Fin 1, (a i x)^2)
  have hg (m : ℕ) (i : Fin 1) : MemLp (g m i) 2 μ := ((hθ m).2.2.2.2 i).2.restrict Ω
  have ha (i : Fin 1) : MemLp (a i) 2 μ := (ha2 i).restrict Ω
  have hc (i : Fin 1) : Tendsto (fun m => eLpNorm (fun x => g m i x - a i x) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv i) (fun _ => zero_le)
    intro m
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  obtain ⟨hd1,hdconv⟩ := gradient_density_l1_of_coordinate_l2 hg ha hc
  have hρ : Integrable ρ μ := MemLp.integrable le_rfl ((memLp_sqrt_sum_sq ha).mono_exponent (by norm_num))
  have hid (m : ℕ) : (fun x => ‖fderiv ℝ (θ m) x‖ - ρ x) =
      fun x => Real.sqrt (∑ i : Fin 1, (g m i x)^2) - Real.sqrt (∑ i : Fin 1, (a i x)^2) := by
    funext x
    rw [norm_linearFunctional_eq_sqrt_sum_sq_basis]
  have heI (m : ℕ) : Integrable (fun x => ‖fderiv ℝ (θ m) x‖ - ρ x) μ := by
    rw [hid m]
    exact MemLp.integrable le_rfl (hd1 m)
  have herrconv : Tendsto (fun m => ∫ x in Ω, |‖fderiv ℝ (θ m) x‖ - ρ x|) atTop (𝓝 0) := by
    have H := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hdconv
    have heq (m : ℕ) :
        (eLpNorm (fun x => Real.sqrt (∑ i : Fin 1, (g m i x)^2) -
          Real.sqrt (∑ i : Fin 1, (a i x)^2)) 1 μ).toReal =
          ∫ x in Ω, |‖fderiv ℝ (θ m) x‖ - ρ x| := by
      rw [eLpNorm_one_eq_lintegral_enorm,← integral_norm_eq_lintegral_enorm (hd1 m).aestronglyMeasurable]
      apply integral_congr_ae
      apply ae_of_all
      intro x
      change ‖Real.sqrt (∑ i : Fin 1, (g m i x)^2) - Real.sqrt (∑ i : Fin 1, (a i x)^2)‖ =
        |‖fderiv ℝ (θ m) x‖ - ρ x|
      rw [← congrFun (hid m) x]
      exact Real.norm_eq_abs _
    simpa only [Function.comp_def,heq,ENNReal.toReal_zero] using H
  have result := measure_mul_abs_sub_average_le_of_smooth_approximation_one hΩo hΩ hnonempty
    hSm hSΩ hD hdiam hρ
    (fun m => (hθ m).1.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffOn)
    havgdata.1 (ae_restrict_of_ae hae) havgdata.2.2.2 heI herrconv
  simpa only [ρ,abs_of_nonneg (Real.sqrt_nonneg _)] using result

theorem measure_mul_abs_sub_average_le_of_bounded_weak_data_one
    {Ω S : Set (EuclideanSpace ℝ (Fin 1))}
    (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω) (hΩne : Ω.Nonempty)
    (hSm : MeasurableSet S) (hSΩ : S ⊆ Ω) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ y ∈ Ω, ∀ z ∈ Ω, dist y z ≤ D)
    {H : EuclideanSpace ℝ (Fin 1) → ℝ} {a : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ}
    {C : ℝ} (hH : LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (hbound : ∀ x, ‖H x‖ ≤ C)
    (hweak : ∀ i, HasWeakDerivAlong H (a i) (EuclideanSpace.basisFun (Fin 1) ℝ i))
    (ha2 : ∀ i, ∀ K : Set (EuclideanSpace ℝ (Fin 1)), IsCompact K →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict K)) :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict Ω),
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) S * ENNReal.ofReal |H x - ⨍ y in S, H y| ≤
      ENNReal.ofReal D * ENNReal.ofReal (∫ z in Ω, Real.sqrt (∑ i : Fin 1, (a i z)^2)) := by
  obtain ⟨x0,hx0⟩ := hΩne
  have hnonempty : Ω.Nonempty := ⟨x0,hx0⟩
  let ψ : ContDiffBump x0 := ⟨D + 1,D + 2,by linarith,by linarith⟩
  have hψon (x : EuclideanSpace ℝ (Fin 1)) (hx : x ∈ Ω) :
      (ψ : EuclideanSpace ℝ (Fin 1) → ℝ) =ᶠ[𝓝 x] (fun _ => 1) := by
    apply ψ.eventuallyEq_one_of_mem_ball
    change dist x x0 < D + 1
    linarith [hdiam x hx x0 hx0]
  have hψone (x : EuclideanSpace ℝ (Fin 1)) (hx : x ∈ Ω) : ψ x = 1 :=
    (hψon x hx).eq_of_nhds
  have hψder (x : EuclideanSpace ℝ (Fin 1)) (hx : x ∈ Ω) :
      fderiv ℝ (ψ : EuclideanSpace ℝ (Fin 1) → ℝ) x = 0 := by
    rw [(hψon x hx).fderiv_eq]
    simp only [fderiv_const_apply]
  let η := fun x => ψ x * H x
  let b := fun (i : Fin 1) x => ψ x * a i x +
    fderiv ℝ (ψ : EuclideanSpace ℝ (Fin 1) → ℝ) x (EuclideanSpace.basisFun (Fin 1) ℝ i) * H x
  have hHtop (K : Set (EuclideanSpace ℝ (Fin 1))) (_hK : IsCompact K) :
      MemLp H ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict K) :=
    memLp_top_of_bound hH.aestronglyMeasurable.restrict C (ae_of_all _ hbound)
  have hprod (i : Fin 1) := (hweak i).compact_mul_data (ha2 i) hHtop ψ.contDiff ψ.hasCompactSupport
  have hηbound (x : EuclideanSpace ℝ (Fin 1)) : ‖η x‖ ≤ C := by
    calc
      _ = ‖ψ x‖ * ‖H x‖ := norm_mul _ _
      _ ≤ 1 * ‖H x‖ := mul_le_mul_of_nonneg_right
        (by rw [Real.norm_eq_abs,abs_of_nonneg (ψ.nonneg)]; exact ψ.le_one) (norm_nonneg _)
      _ = ‖H x‖ := one_mul _
      _ ≤ C := hbound x
  have hηK : Function.support η ⊆ tsupport (ψ : EuclideanSpace ℝ (Fin 1) → ℝ) :=
    (Function.support_mul_subset_left _ _).trans subset_closure
  have hbK (i : Fin 1) : Function.support (b i) ⊆ tsupport (ψ : EuclideanSpace ℝ (Fin 1) → ℝ) := by
    intro x hx
    by_contra hout
    apply hx
    have hz := image_eq_zero_of_notMem_tsupport hout
    have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hout
    dsimp only [b]
    rw [hz,hd]
    simp only [zero_mul,zero_apply,add_zero]
  have hηeq (x : EuclideanSpace ℝ (Fin 1)) (hx : x ∈ Ω) : η x = H x := by
    dsimp only [η]
    rw [hψone x hx,one_mul]
  have hbeq (i : Fin 1) (x : EuclideanSpace ℝ (Fin 1)) (hx : x ∈ Ω) : b i x = a i x := by
    dsimp only [b]
    rw [hψone x hx,hψder x hx]
    simp only [one_mul,zero_apply,zero_mul,add_zero]
  have hηaeS : η =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict S)] H :=
    (ae_restrict_mem hSm).mono fun x hx => hηeq x (hSΩ hx)
  have havg : (⨍ y in S, η y) = ⨍ y in S, H y := average_congr hηaeS
  have hpotential : (∫ z in Ω, Real.sqrt (∑ i : Fin 1, (b i z)^2)) =
      (∫ z in Ω, Real.sqrt (∑ i : Fin 1, (a i z)^2)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩo.measurableSet] with z hz
    simp_rw [show ∀ i : Fin 1,b i z=a i z from fun i => hbeq i z hz]
  have result := measure_mul_abs_sub_average_le_of_compact_bounded_weak_data_one (η := η) (a := b) hΩo hΩ hnonempty
    hSm hSΩ hD hdiam (hprod ⟨0,by omega⟩).1.1 hηbound ψ.hasCompactSupport hηK hbK
    (fun i => (hprod i).1) (fun i => (hprod i).2.2.2)
  filter_upwards [result,ae_restrict_mem hΩo.measurableSet] with x hx hxΩ
  rw [hηeq x hxΩ,havg,hpotential] at hx
  exact hx

/-- The one-dimensional replacement for critical JohnNirenberg: density mass bounds the oscillation directly.
The exponent t is explicit and may be chosen uniformly before the application data. -/
theorem integrable_exp_abs_sub_average_one_of_density_mass
    {Ω : Set (EuclideanSpace ℝ (Fin 1))}
    (hΩo : IsOpen Ω) (hΩ : Convex ℝ Ω) (hΩne : Ω.Nonempty)
    {D K t : ℝ} (hD : 0 < D) (hK : 0 < K) (ht : 0 ≤ t)
    (hdiam : ∀ y ∈ Ω,∀ z ∈ Ω,dist y z ≤ D)
    {H : EuclideanSpace ℝ (Fin 1) → ℝ} {a : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ}
    {C : ℝ} (hH : LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (hbound : ∀ x,‖H x‖≤C)
    (hweak : ∀ i,FunctionalInequalities.Analysis.HasWeakDerivAlong H (a i) (EuclideanSpace.basisFun (Fin 1) ℝ i))
    (ha2 : ∀ i,∀ S : Set (EuclideanSpace ℝ (Fin 1)),IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict S))
    (hmass : (∫⁻ z in Ω,ENNReal.ofReal (Real.sqrt (∑ i : Fin 1,(a i z)^2))) ≤ ENNReal.ofReal K)
    (htK : t*D*K ≤ (volume : Measure (EuclideanSpace ℝ (Fin 1))).real Ω) :
    (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict Ω),
      t*|H x-⨍ y in Ω,H y|≤1) ∧
    Integrable (fun x => Real.exp (t*|H x-⨍ y in Ω,H y|))
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict Ω) ∧
    (∫ x in Ω,Real.exp (t*|H x-⨍ y in Ω,H y|)) ≤
      Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin 1))).real Ω := by
  obtain ⟨x0,hx0⟩ := hΩne
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict Ω
  let ρ := fun z => Real.sqrt (∑ i : Fin 1,(a i z)^2)
  let V := (volume : Measure (EuclideanSpace ℝ (Fin 1))).real Ω
  have hΩfin : (volume : Measure (EuclideanSpace ℝ (Fin 1))) Ω ≠ ∞ :=
    ((measure_mono (show Ω ⊆ closedBall x0 D from fun y hy => hdiam y hy x0 hx0)).trans_lt
      measure_closedBall_lt_top).ne
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩfin
  have hV : 0 < V := ENNReal.toReal_pos (hΩo.measure_pos (μ := volume) ⟨x0,hx0⟩).ne' hΩfin
  have hρm : AEStronglyMeasurable ρ μ := by
    apply Real.continuous_sqrt.comp_aestronglyMeasurable
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (((hweak i).2.1.aestronglyMeasurable.restrict).aemeasurable.pow_const (2 : ℕ)).aestronglyMeasurable
  have hρI : Integrable ρ μ := by
    refine ⟨hρm,(hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => Real.sqrt_nonneg _)).2 ?_⟩
    exact hmass.trans_lt ENNReal.ofReal_lt_top
  have hρreal : (∫ z in Ω,ρ z) ≤ K := by
    have hm := hmass
    rw [← ofReal_integral_eq_lintegral_ofReal hρI (ae_of_all _ fun _ => Real.sqrt_nonneg _)] at hm
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    have hInt0 : 0 ≤ ∫ z,ρ z ∂μ := integral_nonneg fun _ => Real.sqrt_nonneg _
    rw [ENNReal.toReal_ofReal hInt0,ENNReal.toReal_ofReal hK.le] at hr
    exact hr
  have hrep := measure_mul_abs_sub_average_le_of_bounded_weak_data_one hΩo hΩ ⟨x0,hx0⟩
    hΩo.measurableSet (Subset.refl Ω) hD hdiam hH hbound hweak ha2
  have hdev : ∀ᵐ x ∂μ,t*|H x-⨍ y in Ω,H y|≤1 := by
    filter_upwards [hrep] with x hx
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hx
    simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hD.le,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun _ => Real.sqrt_nonneg _)] at hr
    have hreal : V*|H x-⨍ y in Ω,H y| ≤ D*K :=
      hr.trans (mul_le_mul_of_nonneg_left hρreal hD.le)
    have hs := mul_le_mul_of_nonneg_left hreal ht
    have hs' : V*(t*|H x-⨍ y in Ω,H y|) ≤ V := by nlinarith [htK]
    nlinarith
  have hEm : AEStronglyMeasurable (fun x => Real.exp (t*|H x-⨍ y in Ω,H y|)) μ := by
    apply Real.continuous_exp.comp_aestronglyMeasurable
    have hd : AEStronglyMeasurable (fun x => H x-⨍ y in Ω,H y) μ :=
      (show AEStronglyMeasurable H μ from hH.aestronglyMeasurable.restrict).sub aestronglyMeasurable_const
    simpa only [Real.norm_eq_abs] using hd.norm.const_mul t
  have he : ∀ᵐ x ∂μ,Real.exp (t*|H x-⨍ y in Ω,H y|) ≤ Real.exp 1 :=
    hdev.mono fun _ hx => Real.exp_le_exp.mpr hx
  have hEi : Integrable (fun x => Real.exp (t*|H x-⨍ y in Ω,H y|)) μ :=
    (integrable_const (Real.exp 1)).mono_nonneg hEm (ae_of_all _ fun _ => (Real.exp_pos _).le) he
  refine ⟨hdev,hEi,(integral_mono_ae hEi (integrable_const _) he).trans_eq ?_⟩
  rw [integral_const]
  change ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict Ω univ).toReal * Real.exp 1 =
    Real.exp 1 * ((volume : Measure (EuclideanSpace ℝ (Fin 1))) Ω).toReal
  rw [Measure.restrict_apply_univ]
  ring

end OneDimensional

end FunctionalInequalities.Analysis
