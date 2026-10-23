import FunctionalInequalities.Analysis.Newtonian.PotentialC2
import FunctionalInequalities.Analysis.Newtonian.BoxFlux

/-!
# The boundary form of the Newtonian Hessian (GT (4.9)) and the full Lemma 4.2

The boundary representation (4.9) in Lemma 4.2 of Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), pp. 55–56: for every domain `Ω₀ ⊇ Ω`
"for which the divergence theorem holds",
`D_jD_iw(x) = ∫_{Ω₀} D_jD_iΓ(x - y)(F(y) - f(x)) dy - f(x) ∫_{∂Ω₀} D_iΓ(x - y) ν_j(y) ds_y`, `F = 1_Ω f`.

* `DivergenceAdmissible Ω₀ σ ν` encodes only the divergence theorem: `Ω₀` is open and bounded, and a
  finite family of finite boundary measures `σ_p` carried off `Ω₀`, with measurable normals
  `‖ν_p‖ ≤ 1`, satisfies `∫_{Ω₀} div V = ∑_p ∫ ⟪V, ν_p⟫ dσ_p` for every globally `C¹` field `V`. It
  contains no Hessian, PDE or flux value of `Γ`.
* `newtonianPotential_hessian_eq_boundary_formula`: (4.9) on every admissible `Ω₀ ⊇ Ω`, with integrable
  volume and boundary integrands.
* `divergenceAdmissible_euclideanOpenBox`, `exists_divergenceAdmissible_superset`: every coordinate box
  (faces with normals `±e_k`) is admissible, so an admissible `Ω₀` exists for every bounded `Ω`.
* `newtonianPotential_lemma_4_2`: Lemma 4.2 in full for `n ≥ 2`, a bounded open `Ω` and `f` bounded and
  locally `α`-Hölder in `Ω` (`0 < α ≤ 1`): `w ∈ C²(Ω)`, `Δw = f` in `Ω`, the compact-test representation,
  and (4.9) on every admissible `Ω₀`.

General `C^{1}` domains with surface measure are not treated; admissibility is the interface.
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal

namespace FunctionalInequalities.Analysis

/-- GT2001 (4.9) admissibility: `Ω₀` is open and bounded and the divergence theorem holds on `Ω₀` with the boundary measures
`σ_p` (finite, carried off `Ω₀`) and normals `ν_p` (measurable, `|ν_p| ≤ 1`), for every globally `C¹` vector field. -/
structure DivergenceAdmissible {n : ℕ} (Ω₀ : Set (EuclideanSpace ℝ (Fin n))) {ι : Type} [Fintype ι]
    (σ : ι → Measure (EuclideanSpace ℝ (Fin n)))
    (ν : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop where
  isOpen : IsOpen Ω₀
  isBounded : Bornology.IsBounded Ω₀
  finite : ∀ p, σ p univ < ⊤
  measurable_normal : ∀ p, Measurable (ν p)
  norm_normal_le : ∀ p y, ‖ν p y‖ ≤ 1
  boundary_null : ∀ p, σ p Ω₀ = 0
  divergence : ∀ V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), ContDiff ℝ 1 V →
    (∫ y in Ω₀, ∑ k : Fin n, fderiv ℝ (fun z => V z k) y (EuclideanSpace.basisFun (Fin n) ℝ k)) =
      ∑ p, ∫ y, ⟪V y, ν p y⟫ ∂(σ p)

section Helpers

variable {n : ℕ}

theorem abs_apply_le_norm_euclidean (v : EuclideanSpace ℝ (Fin n)) (k : Fin n) : |v k| ≤ ‖v‖ := by
  have h := abs_real_inner_le_norm v (EuclideanSpace.basisFun (Fin n) ℝ k)
  rwa [EuclideanSpace.inner_basisFun_real, show ‖EuclideanSpace.basisFun (Fin n) ℝ k‖ = 1 by simp, mul_one] at h

/-- The cut-off component is globally bounded: it vanishes on `|z| ≤ ε` and `|D_iΓ(z)| ≤ |z|^{1−n}/(nω_n)` elsewhere. -/
theorem abs_newtonianTruncatedGradientComponent_le_const (hn : 2 ≤ n) {eps : ℝ} (heps : 0 < eps) (i : Fin n)
    (z : EuclideanSpace ℝ (Fin n)) :
    |newtonianTruncatedGradientComponent n eps i z| ≤ (1 / ((n:ℝ) * euclideanUnitBallVolume n)) * eps ^ ((1:ℝ) - n) := by
  have hw := euclideanUnitBallVolume_pos n
  rcases le_or_gt ‖z‖ eps with hz | hz
  · rw [newtonianTruncatedGradientComponent_eq_zero heps i hz, abs_zero]; positivity
  · have hne : z ≠ 0 := norm_pos_iff.mp (heps.trans hz)
    refine (abs_newtonianTruncatedGradientComponent_le i z).trans ((abs_fderiv_newtonianKernel_basis_le hn z hne i).trans ?_)
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos heps hz.le ?_) (by positivity)
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith

end Helpers

section General

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ} {α : ℝ}
  {Ω₀ : Set (EuclideanSpace ℝ (Fin n))} {ι : Type} [Fintype ι] {σ : ι → Measure (EuclideanSpace ℝ (Fin n))}
  {ν : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}

/-- One-`ε` boundary identity and error: if `B(x,2ε) ⊆ Ω ⊆ Ω₀` (admissible) and `f` is `α`-Hölder at `x` on that ball, the
(4.9) integrands are integrable and `|D_j v_{ε,i}(x) − RHS(4.9)| ≤ (n/α + 2B) H (2ε)^α`. -/
theorem abs_newtonianGradientApprox_deriv_sub_boundary_le (hn : 2 ≤ n) (hΩo : IsOpen Ω)
    (hfi : IntegrableOn f Ω volume) (hA : DivergenceAdmissible Ω₀ σ ν) (hΩΩ₀ : Ω ⊆ Ω₀) (hα : 0 < α) (hαn : α < n)
    {eps H : ℝ} (heps : 0 < eps) (hH : 0 ≤ H) {x : EuclideanSpace ℝ (Fin n)} (hx : ball x (2 * eps) ⊆ Ω)
    (hHx : ∀ y ∈ ball x (2 * eps), |f y - f x| ≤ H * ‖y - x‖ ^ α) (i j : Fin n) :
    IntegrableOn (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
      (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (Ω.indicator f y - f x)) Ω₀ volume ∧
    (∀ p, Integrable (fun y => fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * ν p y j)
      (σ p)) ∧
    |(∫ y in Ω, fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ j) * f y) -
        ((∫ y in Ω₀, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
            (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (Ω.indicator f y - f x)) -
          f x * ∑ p, ∫ y, fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * ν p y j ∂(σ p))| ≤
      ((n:ℝ) / α + 2 * newtonianCutoffCap) * H * (2 * eps) ^ α := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  set G := newtonianTruncatedGradientComponent n eps i
  have hG : ContDiff ℝ 1 G :=
    (contDiff_newtonianTruncatedGradientComponent hn heps i).of_le (WithTop.coe_le_coe.mpr le_top)
  have hsub : Continuous (fun y : EuclideanSpace ℝ (Fin n) => x - y) := continuous_const.sub continuous_id
  set DG : EuclideanSpace ℝ (Fin n) → ℝ := fun y => fderiv ℝ G (x - y) (b j)
  have hDGc : Continuous DG := ((hG.continuous_fderiv one_ne_zero).comp hsub).clm_apply continuous_const
  set k0 : EuclideanSpace ℝ (Fin n) → ℝ := fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y) (b j) (b i)
  set F := Ω.indicator f
  have hΩm : MeasurableSet Ω := hΩo.measurableSet
  have hΩ₀m : MeasurableSet Ω₀ := hA.isOpen.measurableSet
  have hfin : volume Ω₀ < ⊤ := hA.isBounded.measure_lt_top
  -- the density `φ = 1_{Ω₀}(F − f(x))`
  set φ := Ω₀.indicator (fun y => F y - f x)
  have hFi : Integrable F volume := (integrable_indicator_iff hΩm).mpr hfi
  have hφi : Integrable φ volume :=
    (integrable_indicator_iff hΩ₀m).mpr (hFi.integrableOn.sub (integrableOn_const hfin.ne))
  have hφH : ∀ y ∈ ball x (2 * eps), |φ y| ≤ H * ‖y - x‖ ^ α := by
    intro y hy
    simp only [φ, F, Set.indicator_of_mem (hΩΩ₀ (hx hy)), Set.indicator_of_mem (hx hy)]
    exact hHx y hy
  obtain ⟨hk0, hDGφ, hnear⟩ := newtonianTruncatedGradient_near_error hn heps hα hαn hH x hφi hφH i j
  have hind (g : EuclideanSpace ℝ (Fin n) → ℝ) : (fun y => g y * φ y) = Ω₀.indicator (fun y => g y * (F y - f x)) := by
    funext y; by_cases hy : y ∈ Ω₀
    · simp only [φ, Set.indicator_of_mem hy]
    · simp only [φ, Set.indicator_of_notMem hy, mul_zero]
  have hk0Ω₀ : IntegrableOn (fun y => k0 y * (F y - f x)) Ω₀ volume := by
    have h := hk0; rw [hind k0, integrable_indicator_iff hΩ₀m] at h; exact h
  have hDGΩ₀ : IntegrableOn (fun y => DG y * (F y - f x)) Ω₀ volume := by
    have h := hDGφ; rw [hind DG, integrable_indicator_iff hΩ₀m] at h; exact h
  have hint1 : (∫ y, DG y * φ y) = ∫ y in Ω₀, DG y * (F y - f x) := by rw [hind DG, integral_indicator hΩ₀m]
  have hint2 : (∫ y, k0 y * φ y) = ∫ y in Ω₀, k0 y * (F y - f x) := by rw [hind k0, integral_indicator hΩ₀m]
  -- `DG` is bounded on the bounded `Ω₀`
  obtain ⟨C, hC⟩ := hA.isBounded.isCompact_closure.exists_bound_of_continuousOn hDGc.continuousOn
  have hDGb : IntegrableOn DG Ω₀ volume :=
    (integrableOn_const (C := C) hfin.ne).mono' hDGc.aestronglyMeasurable
      ((ae_restrict_mem hΩ₀m).mono fun y hy => hC y (subset_closure hy))
  -- `∫_Ω DG f = ∫_{Ω₀} DG (F − f(x)) + f(x) ∫_{Ω₀} DG`
  have hsplit : (∫ y in Ω, DG y * f y) = (∫ y in Ω₀, DG y * (F y - f x)) + f x * ∫ y in Ω₀, DG y := by
    have h1 : (∫ y in Ω, DG y * f y) = ∫ y in Ω₀, DG y * F y := by
      rw [← integral_indicator hΩm, ← integral_indicator hΩ₀m]
      congr 1; funext y
      by_cases hy : y ∈ Ω
      · simp only [F, Set.indicator_of_mem hy, Set.indicator_of_mem (hΩΩ₀ hy)]
      · by_cases hy0 : y ∈ Ω₀
        · simp only [F, Set.indicator_of_notMem hy, Set.indicator_of_mem hy0, mul_zero]
        · simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy0]
    rw [h1, ← integral_const_mul, ← integral_add hDGΩ₀ (hDGb.const_mul (f x))]
    congr 1; funext y; ring
  -- the divergence theorem for `V(y) = −G(x−y) e_j`
  have hσ (p : ι) : IsFiniteMeasure (σ p) := ⟨hA.finite p⟩
  set V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y => (-G (x - y)) • b j
  have hV : ContDiff ℝ 1 V := ((hG.comp (contDiff_const.sub contDiff_id)).neg).smul contDiff_const
  have hGd (y v : EuclideanSpace ℝ (Fin n)) : fderiv ℝ (fun z => G (x - z)) y v = -fderiv ℝ G (x - y) v := by
    have hs : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => x - z)
        (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y := (hasFDerivAt_id y).const_sub x
    have h : HasFDerivAt (fun z => G (x - z)) _ y := ((hG.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y hs
    rw [h.fderiv]; simp
  have hdivV : ∀ y, (∑ k : Fin n, fderiv ℝ (fun z => V z k) y (EuclideanSpace.basisFun (Fin n) ℝ k)) = DG y := by
    intro y
    have hk (k : Fin n) : fderiv ℝ (fun z => V z k) y (b k) = (b j) k * fderiv ℝ G (x - y) (b k) := by
      have he : (fun z => V z k) = fun z => (-(b j) k) * G (x - z) := by
        funext z; simp only [V, PiLp.smul_apply, smul_eq_mul]; ring
      have hd : DifferentiableAt ℝ (fun z => G (x - z)) y :=
        ((hG.differentiable one_ne_zero).comp (differentiable_id.const_sub x)) y
      rw [he, fderiv_const_mul hd, smul_apply, hGd, smul_eq_mul]; ring
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_eq_single j
      (fun k _ hkj => by simp [b, EuclideanSpace.basisFun_apply, hkj]) (by simp)]
    simp [DG, b, EuclideanSpace.basisFun_apply]
  have hdiv : (∫ y in Ω₀, DG y) = ∑ p, ∫ y, ⟪V y, ν p y⟫ ∂(σ p) := by
    rw [← hA.divergence V hV]
    exact setIntegral_congr_fun hΩ₀m fun y _ => (hdivV y).symm
  -- on every boundary piece `G(x − y) = D_iΓ(x − y)` almost everywhere, since `σ_p(B(x,2ε)) = 0`
  have hae (p : ι) : ∀ᵐ y ∂(σ p), ⟪V y, ν p y⟫ =
      -(fderiv ℝ (newtonianKernel n) (x - y) (b i) * ν p y j) := by
    have h0 : σ p (ball x (2 * eps)) = 0 := measure_mono_null (hx.trans hΩΩ₀) (hA.boundary_null p)
    filter_upwards [compl_mem_ae_iff.mpr h0] with y hy
    have hy' : 2 * eps ≤ ‖x - y‖ := by
      simpa only [mem_compl_iff, mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
    simp only [V, inner_smul_left, b, real_inner_comm, EuclideanSpace.inner_basisFun_real, RCLike.conj_to_real]
    rw [show G (x - y) = _ from newtonianTruncatedGradientComponent_eq_of_far heps i hy']
    ring
  have hνj (p : ι) : Measurable (fun y => ν p y j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp (hA.measurable_normal p)
  have hbdry (p : ι) : Integrable (fun y => fderiv ℝ (newtonianKernel n) (x - y) (b i) * ν p y j) (σ p) := by
    have hGi : Integrable (fun y => G (x - y) * ν p y j) (σ p) := by
      refine (integrable_const ((1 / ((n:ℝ) * euclideanUnitBallVolume n)) * eps ^ ((1:ℝ) - n))).mono'
        ((hG.continuous.comp hsub).measurable.mul (hνj p)).aestronglyMeasurable (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_newtonianTruncatedGradientComponent_le_const hn heps i (x - y)
      have h2 : |ν p y j| ≤ 1 := (abs_apply_le_norm_euclidean _ j).trans (hA.norm_normal_le p y)
      calc |G (x - y)| * |ν p y j| ≤ (1 / ((n:ℝ) * euclideanUnitBallVolume n)) * eps ^ ((1:ℝ) - n) * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
        _ = _ := mul_one _
    refine hGi.congr ?_
    have h0 : σ p (ball x (2 * eps)) = 0 := measure_mono_null (hx.trans hΩΩ₀) (hA.boundary_null p)
    filter_upwards [compl_mem_ae_iff.mpr h0] with y hy
    have hy' : 2 * eps ≤ ‖x - y‖ := by
      simpa only [mem_compl_iff, mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
    rw [show G (x - y) = _ from newtonianTruncatedGradientComponent_eq_of_far heps i hy']
  have hflux : (∫ y in Ω₀, DG y) =
      -∑ p, ∫ y, fderiv ℝ (newtonianKernel n) (x - y) (b i) * ν p y j ∂(σ p) := by
    rw [hdiv, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_congr_ae (hae p), integral_neg]
  refine ⟨hk0Ω₀, hbdry, ?_⟩
  rw [hsplit, hflux, ← hint1, ← hint2]
  convert hnear using 2
  ring

end General

section Limit

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **GT2001 (4.9) from the original inputs**, on every admissible `Ω₀ ⊇ Ω`: for `x ∈ Ω`,
`D_jD_iw(x) = ∫_{Ω₀} D_jD_iΓ(x−y)(F(y) − f(x))dy − f(x) Σ_p ∫ D_iΓ(x−y)ν_p(y)_j dσ_p(y)`, both integrands integrable. -/
theorem newtonianPotential_hessian_eq_boundary_formula (hn : 2 ≤ n) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfb : ∃ M, ∀ y ∈ Ω, |f y| ≤ M) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ∃ H : ℝ≥0, ball x r ⊆ Ω ∧ HolderOnWith H α f (ball x r))
    {Ω₀ : Set (EuclideanSpace ℝ (Fin n))} {ι : Type} [Fintype ι] {σ : ι → Measure (EuclideanSpace ℝ (Fin n))}
    {ν : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hA : DivergenceAdmissible Ω₀ σ ν) (hΩΩ₀ : Ω ⊆ Ω₀)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω) (i j : Fin n) :
    IntegrableOn (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
      (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (Ω.indicator f y - f x)) Ω₀ volume ∧
    (∀ p, Integrable (fun y => fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * ν p y j)
      (σ p)) ∧
    iteratedFDeriv ℝ 2 (newtonianPotential n Ω f) x
        ![EuclideanSpace.basisFun (Fin n) ℝ j, EuclideanSpace.basisFun (Fin n) ℝ i] =
      (∫ y in Ω₀, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
          (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (Ω.indicator f y - f x)) -
        f x * ∑ p, ∫ y, fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * ν p y j ∂(σ p) := by
  obtain ⟨-, -, hfi, hloc'⟩ := localHolder_regularity_of_holderOnWith hΩo hΩb hfb hα0 hloc
  obtain ⟨M, hM⟩ := hfb
  have hα : (0:ℝ) < α := hα0
  have hαn : (α:ℝ) < n := by
    have h1 : (α:ℝ) ≤ 1 := hα1
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨θ0, hθ0, hθ0c, U0, hU0, hΩU0, hθ01⟩ := exists_newtonian_test (n := n) hΩb
  have hθ0' : ContDiff ℝ 1 θ0 := hθ0.of_le (WithTop.coe_le_coe.mpr le_top)
  have hT1 := (newtonianPotential_hessian_local hn hΩo hΩb hfi hM hθ0' hθ0c hU0 hΩU0 hθ01 hα hαn hloc' hx i).2.2 j
  have hrep := ((newtonianPotential_contDiffOn_two_of_test hn hΩo hΩb hfi hM hθ0' hθ0c hU0 hΩU0 hθ01 hα hαn
    hloc').2.2 x hx i j).2.2
  obtain ⟨r, hr, H, hH, hball, hHol⟩ := hloc' x hx
  have hsub4 : ball x (2 * (r / 4)) ⊆ ball x r := ball_subset_ball (by linarith)
  obtain ⟨hI1, hI2, -⟩ := abs_newtonianGradientApprox_deriv_sub_boundary_le hn hΩo hfi hA hΩΩ₀ hα hαn
    (by positivity : 0 < r / 4) hH (hsub4.trans hball) (fun y hy => hHol y (hsub4 hy) x (mem_ball_self hr)) i j
  refine ⟨hI1, hI2, ?_⟩
  rw [hrep]
  refine tendsto_nhds_unique hT1 (tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall
    fun _ => norm_nonneg _) ?_ (by simpa only [mul_zero] using
      (tendsto_two_mul_inv_succ_rpow hα).const_mul (((n:ℝ) / α + 2 * newtonianCutoffCap) * H))))
  filter_upwards [eventually_two_mul_inv_succ_le hr] with k hk
  have hsub : ball x (2 * (1 / ((k:ℝ) + 1))) ⊆ ball x r := ball_subset_ball hk
  rw [Real.norm_eq_abs]
  exact (abs_newtonianGradientApprox_deriv_sub_boundary_le hn hΩo hfi hA hΩΩ₀ hα hαn (by positivity) hH
    (hsub.trans hball) (fun y hy => hHol y (hsub hy) x (mem_ball_self hr)) i j).2.2

end Limit

section Box

/-- The open coordinate box `{x | a_i < x_i < b_i}` in `ℝⁿ`. -/
def euclideanOpenBox {n : ℕ} (a b : Fin n → ℝ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, a i < x i ∧ x i < b i}

/-- Face measures of a box: face `(k, true)` is `{x_k = b_k}`, face `(k, false)` is `{x_k = a_k}`, each the push-forward of
Lebesgue measure on the complementary closed box under `y ↦ insertNth k c y`. -/
def euclideanBoxFaceMeasure {m : ℕ} (a b : Fin (m + 1) → ℝ) (p : Fin (m + 1) × Bool) :
    Measure (EuclideanSpace ℝ (Fin (m + 1))) :=
  Measure.map (fun y : Fin m → ℝ => WithLp.toLp 2 (p.1.insertNth (if p.2 then b p.1 else a p.1) y))
    (volume.restrict (Icc (a ∘ p.1.succAbove) (b ∘ p.1.succAbove)))

/-- Outward unit normals of the box faces: `+e_k` on `(k, true)`, `−e_k` on `(k, false)`. -/
def euclideanBoxFaceNormal {m : ℕ} (p : Fin (m + 1) × Bool) (_y : EuclideanSpace ℝ (Fin (m + 1))) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  (if p.2 then (1:ℝ) else -1) • EuclideanSpace.basisFun (Fin (m + 1)) ℝ p.1

theorem continuous_toLp_insertNth {m : ℕ} (k : Fin (m + 1)) (c : ℝ) :
    Continuous (fun y : Fin m → ℝ => WithLp.toLp 2 (k.insertNth (α := fun _ => ℝ) c y)) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_const.finInsertNth k continuous_id)

/-- **Admissible instance**: every coordinate box `a ≤ b` in `ℝ^{m+1}`, with its face measures and normals, satisfies
the divergence theorem in the sense of `DivergenceAdmissible` (via `integral_openBox_sum_fderiv_eq_faces` of `Analysis/Newtonian/BoxFlux.lean`). -/
theorem divergenceAdmissible_euclideanOpenBox {m : ℕ} {a b : Fin (m + 1) → ℝ} (hab : a ≤ b) :
    DivergenceAdmissible (euclideanOpenBox a b) (euclideanBoxFaceMeasure a b) euclideanBoxFaceNormal where
  isOpen := by
    have hc (i : Fin (m + 1)) : Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
    have he : euclideanOpenBox a b = ⋂ i, ({x | a i < x i} ∩ {x | x i < b i}) := by
      ext x; simp [euclideanOpenBox]
    rw [he]
    exact isOpen_iInter_of_finite fun i => (isOpen_lt continuous_const (hc i)).inter (isOpen_lt (hc i) continuous_const)
  isBounded := by
    refine ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).antilipschitz.isBounded_preimage
      (isCompact_Icc (a := a) (b := b)).isBounded).subset fun x hx => ?_
    show a ≤ x.ofLp ∧ x.ofLp ≤ b
    exact ⟨fun i => (hx i).1.le, fun i => (hx i).2.le⟩
  finite p := by
    rw [euclideanBoxFaceMeasure, Measure.map_apply (continuous_toLp_insertNth _ _).measurable MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top
  measurable_normal _ := measurable_const
  norm_normal_le p _ := by
    rcases p with ⟨k, _ | _⟩ <;> simp [euclideanBoxFaceNormal]
  boundary_null p := by
    have hpre : (fun y : Fin m → ℝ => WithLp.toLp 2 (p.1.insertNth (if p.2 then b p.1 else a p.1) y)) ⁻¹'
        euclideanOpenBox a b = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
      have h := hy p.1
      simp only [Fin.insertNth_apply_same] at h
      split_ifs at h <;> linarith [h.1, h.2]
    have hm : MeasurableSet (euclideanOpenBox a b) := by
      have hc (i : Fin (m + 1)) : Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x i) :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
      have he : euclideanOpenBox a b = ⋂ i, ({x | a i < x i} ∩ {x | x i < b i}) := by
        ext x; simp [euclideanOpenBox]
      rw [he]
      exact (isOpen_iInter_of_finite fun i =>
        (isOpen_lt continuous_const (hc i)).inter (isOpen_lt (hc i) continuous_const)).measurableSet
    rw [euclideanBoxFaceMeasure, Measure.map_apply (continuous_toLp_insertNth _ _).measurable hm, hpre, measure_empty]
  divergence V hV := by
    have h := integral_openBox_sum_fderiv_eq_faces a b hab (fun k z => V z k)
      (fun k => (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hV)
    refine h.trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_bool]
    have hVc : Continuous V := hV.continuous
    simp only [euclideanBoxFaceMeasure, euclideanBoxFaceNormal]
    rw [integral_map (continuous_toLp_insertNth _ _).aemeasurable
        ((hVc.inner continuous_const).aestronglyMeasurable),
      integral_map (continuous_toLp_insertNth _ _).aemeasurable
        ((hVc.inner continuous_const).aestronglyMeasurable)]
    simp [integral_neg, sub_eq_add_neg, EuclideanSpace.inner_single_right]

/-- Every bounded set of `ℝ^{m+1}` lies in a coordinate box. -/
theorem exists_euclideanOpenBox_superset {m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hΩb : Bornology.IsBounded Ω) : ∃ a b : Fin (m + 1) → ℝ, a ≤ b ∧ Ω ⊆ euclideanOpenBox a b := by
  obtain ⟨R, hR⟩ := hΩb.subset_ball 0
  set R' := max R 0
  refine ⟨fun _ => -R', fun _ => R', fun _ => by simp only [neg_le_self_iff]; exact le_max_right _ _, fun x hx i => ?_⟩
  have hx' : ‖x‖ < R' := by
    have := hR hx; rw [mem_ball, dist_zero_right] at this; exact this.trans_le (le_max_left _ _)
  exact abs_lt.mp ((abs_apply_le_norm_euclidean x i).trans_lt hx')

end Box

section Producer

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- An admissible `Ω₀ ⊇ Ω` exists for every bounded `Ω` (a coordinate box with its faces), in every dimension `n ≥ 1`. -/
theorem exists_divergenceAdmissible_superset (hn : 1 ≤ n) (hΩb : Bornology.IsBounded Ω) :
    ∃ (Ω₀ : Set (EuclideanSpace ℝ (Fin n))) (σ : Fin n × Bool → Measure (EuclideanSpace ℝ (Fin n)))
      (ν : Fin n × Bool → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      DivergenceAdmissible Ω₀ σ ν ∧ Ω ⊆ Ω₀ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨a, b, hab, hsub⟩ := exists_euclideanOpenBox_superset hΩb
  exact ⟨_, _, _, divergenceAdmissible_euclideanOpenBox hab, hsub⟩

/-- **GT2001 Lemma 4.2, complete statement from the original inputs.** For `n ≥ 2` (including `n = 2`), `Ω` bounded open,
`f` real, bounded on `Ω` and locally `α`-Hölder in `Ω`, `0 < α ≤ 1` (including `α = 1`), the Newtonian potential `w`:
(i) is `C²` in `Ω`; (ii) satisfies `Δw = f` in `Ω` (actual Mathlib Laplacian); (iii) has the integrable compact-test Hessian
representation for every `θ ∈ C¹_c` equal to `1` on an open `U ⊇ Ω`; (iv) satisfies (4.9) on EVERY divergence-admissible
`Ω₀ ⊇ Ω` with integrable volume and boundary integrands; (v) such an admissible `Ω₀` (a box) exists. -/
theorem newtonianPotential_lemma_4_2 (hn : 2 ≤ n) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfb : ∃ M, ∀ y ∈ Ω, |f y| ≤ M) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ∃ H : ℝ≥0, ball x r ⊆ Ω ∧ HolderOnWith H α f (ball x r)) :
    ContDiffOn ℝ 2 (newtonianPotential n Ω f) Ω ∧
    (∀ x ∈ Ω, Laplacian.laplacian (newtonianPotential n Ω f) x = f x) ∧
    (∀ θ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 θ → HasCompactSupport θ →
      ∀ U, IsOpen U → Ω ⊆ U → (∀ y ∈ U, θ y = 1) → ∀ x ∈ Ω, ∀ i j : Fin n,
        Integrable (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
          (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) *
            (Ω.indicator f y - f x * θ y)) volume ∧
        Integrable (fun y => fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ θ y (EuclideanSpace.basisFun (Fin n) ℝ j)) volume ∧
        iteratedFDeriv ℝ 2 (newtonianPotential n Ω f) x
            ![EuclideanSpace.basisFun (Fin n) ℝ j, EuclideanSpace.basisFun (Fin n) ℝ i] =
          (∫ y, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
              (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) *
                (Ω.indicator f y - f x * θ y)) +
            f x * ∫ y, fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
              fderiv ℝ θ y (EuclideanSpace.basisFun (Fin n) ℝ j)) ∧
    (∀ (Ω₀ : Set (EuclideanSpace ℝ (Fin n))) (ι : Type) [Fintype ι] (σ : ι → Measure (EuclideanSpace ℝ (Fin n)))
      (ν : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)), DivergenceAdmissible Ω₀ σ ν → Ω ⊆ Ω₀ →
      ∀ x ∈ Ω, ∀ i j : Fin n,
        IntegrableOn (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
          (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (Ω.indicator f y - f x)) Ω₀ volume ∧
        (∀ p, Integrable (fun y => fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * ν p y j)
          (σ p)) ∧
        iteratedFDeriv ℝ 2 (newtonianPotential n Ω f) x
            ![EuclideanSpace.basisFun (Fin n) ℝ j, EuclideanSpace.basisFun (Fin n) ℝ i] =
          (∫ y in Ω₀, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
              (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (Ω.indicator f y - f x)) -
            f x * ∑ p, ∫ y, fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * ν p y j ∂(σ p)) ∧
    (∃ (Ω₀ : Set (EuclideanSpace ℝ (Fin n))) (σ : Fin n × Bool → Measure (EuclideanSpace ℝ (Fin n)))
      (ν : Fin n × Bool → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      DivergenceAdmissible Ω₀ σ ν ∧ Ω ⊆ Ω₀) := by
  obtain ⟨h1, h2, h3, -⟩ := newtonianPotential_contDiffOn_two hn hΩo hΩb hfb hα0 hα1 hloc
  exact ⟨h1, h2, h3, fun Ω₀ ι _ σ ν hA hΩΩ₀ x hx i j =>
    newtonianPotential_hessian_eq_boundary_formula hn hΩo hΩb hfb hα0 hα1 hloc hA hΩΩ₀ hx i j,
    exists_divergenceAdmissible_superset (by omega) hΩb⟩

end Producer

end FunctionalInequalities.Analysis
