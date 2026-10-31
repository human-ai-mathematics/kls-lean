module

public import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
public import FunctionalInequalities.KLS.CEK.MomentRegularity.SmoothTrace
public import FunctionalInequalities.KLS.LogConcave.HessianStein
public import FunctionalInequalities.KLS.Letwin.MomentMap

/-!
# The smooth moment-map Stein kernel

Letwin, arXiv:2607.24164v1, Lemma 2.7 (Fathi's moment-map construction), first in the strong
regular class: smooth globally κ-uniformly convex W, compact convex K with nonempty interior,
normalized
isotropic law 1_K e^{-W}, every n > 0. The same smooth moment potential gives the kernel
τ = Hess u ∘ Ψ, where Ψ is a measurable everywhere left inverse, smooth on int K and a right
inverse there. The kernel is a symmetric Stein kernel, positive definite on int K (indeed at
every point of the chosen extension), with smooth entries there and the exact pointwise coupling
τ(∇u y) = Hess u y. The strengthened producer also gives the exact Theorem 2.5 source trace bounds
and
Hilbert–Schmidt L² bound at this same smooth potential.

`exists_smooth_moment_stein_kernel_of_bounded_open_convex` gives the same conclusions for the
paper's own source class of Lemma 2.2 (`K` bounded open convex nonempty, `V` smooth on an open
`U ⊇ closure K` and convex on `K`, isotropic `μ = 1_K e^{-V} dx`), at the potential produced in
`KLS/Letwin/MomentMap.lean`, together with Lemma 2.9: the `H^{-1}(μ)` norm of `⟪·, v⟫` is at
most `(∫ ‖τ v‖² dμ)^{1/2}` (`Probability.Stein.linear_dual_bound_of_ac`). The same holds at every
moment potential of `μ`: `exists_stein_kernel_of_moment_potential_of_bounded_open_convex` (any
convex `φ` with `∫ e^{-φ} = 1` and `(∇φ)_* e^{-φ} dx = μ`) and
`exists_stein_kernel_of_ofPotential_of_bounded_open_convex` (any convex essentially continuous
`ψ : ℝⁿ → ℝ ∪ {+∞}` with moment measure `μ`, the moment map of Letwin Lemma 2.1).
-/

@[expose] public section
noncomputable section
namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms
open Set Metric MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
open scoped NNReal ContDiff ENNReal Matrix.Norms.Frobenius
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
/-- Given-witness transport step: the sharp source trace bound is an explicit input; both
producers below supply it at the same smooth potential `u`. -/
private theorem sharp_smooth_stein_of_trace_bound (hn : 0 < n) {u W : E → ℝ}
    (hsm : ContDiff ℝ ∞ u) (hc : ConvexOn ℝ univ u)
    {L G : NNReal} (hl : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1)
    (μ : ProbabilityMeasure E)
    (hm : ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E))
    (hiso : KLS.Isotropic μ)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
    (hW : Continuous W)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hPD : ∀ x, (hessianMatrix u x).PosDef)
    (hT25 : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
      Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
        ((volume : Measure E).tilted (-u)) ∧
      (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
        ∂((volume : Measure E).tilted (-u))) ≤ 2 * (B * B).trace) :
    ∃ Ψ : E → E, Measurable Ψ ∧ Function.LeftInverse Ψ (gradient u) ∧
      (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ (interior K) ∧
      IsSteinKernel μ (hessianKernel u Ψ) ∧ SymmetricAE μ (hessianKernel u Ψ) ∧
      (∀ x, (hessianKernel u Ψ x).PosDef) ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun x => hessianKernel u Ψ x i j) (interior K)) ∧
      (∀ y, hessianKernel u Ψ (gradient u y) = hessianMatrix u y) ∧
      MemLp (fun x => hsNorm (hessianKernel u Ψ x)) 2 (μ : Measure E) ∧
      (∫ x, hsNorm (hessianKernel u Ψ x) ^ 2 ∂(μ : Measure E)) ≤ 2 * n ∧
      ∀ i j, (∫ x, hessianKernel u Ψ x i j ∂(μ : Measure E)) =
        (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  classical
  have hC1 : ContDiff ℝ 1 u := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hC2 : ContDiff ℝ 2 u := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨Ψ₀, _hleft₀, hright₀, hΨ₀⟩ :=
    Probability.MomentMeasure.exists_regular_inverse_of_map_gradient hn
      (k := ∞) (by simp) hl hc hnorm (by simpa using hsm) hPD
      hK hKc hKint hW (hm.trans hμ)
  obtain ⟨_hinj, Ψ, hΨ, hleft⟩ := measurable_inverse_gradient_of_map_gradient hn hl hc hnorm hC1
    hK hKc (hKint.mono interior_subset) hW (hm.trans hμ)
  have heqΨ : ∀ y ∈ interior K, Ψ y = Ψ₀ y := by
    intro y hy
    calc Ψ y = Ψ (gradient u (Ψ₀ y)) := congrArg Ψ (hright₀ y hy).symm
      _ = Ψ₀ y := hleft (Ψ₀ y)
  have hΨsm : ContDiffOn ℝ ∞ Ψ (interior K) := hΨ₀.congr heqΨ
  have hright : ∀ y ∈ interior K, gradient u (Ψ y) = y := by
    intro y hy
    rw [heqΨ y hy]
    exact hright₀ y hy
  let ρ : Measure E := volume.tilted (-u)
  have hexp : Integrable (fun y => Real.exp (-u y)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let ν : ProbabilityMeasure E := ⟨ρ, isProbabilityMeasure_tilted hexp⟩
  have hiAE : ∀ᵐ y ∂ρ, Ψ (gradient u y) = y := ae_of_all _ hleft
  have hEq : (fun y => hsNorm (hessianMatrix u y) ^ 2) =ᵐ[ρ]
      fun y => (hessianMatrix u y * hessianMatrix u y).trace := by
    exact ae_of_all _ fun y => hsNorm_sq_eq_trace_mul_self _
      (Matrix.isHermitian_iff_isSymm.mp (hPD y).isHermitian)
  have hTI := hT25 1 Matrix.isSymm_one
  have hInt : Integrable (fun y => hsNorm (hessianMatrix u y) ^ 2) ρ := by
    apply (show Integrable (fun y => (hessianMatrix u y * hessianMatrix u y).trace) ρ by
      simpa only [one_mul, mul_one] using hTI.1).congr hEq.symm
  have hHSρ : MemLp (fun y => hsNorm (hessianMatrix u y)) 2 ρ :=
    (memLp_hsNorm_iff_integrable_sq (fun i j => measurable_hessianMatrix_entry u i j)).2 hInt
  have hHS := memLp_hsNorm_hessianKernel_of_map hC1 ν μ hm hΨ hiAE hHSρ
  have hmeas (i j : Fin n) : Measurable (fun x => hessianKernel u Ψ x i j) :=
    (measurable_hessianMatrix_entry u i j).comp hΨ
  have hHSint : (∫ x, hsNorm (hessianKernel u Ψ x) ^ 2 ∂(μ : Measure E)) =
      ∫ y, hsNorm (hessianMatrix u y) ^ 2 ∂ρ := by
    rw [← hm, integral_map (continuous_gradient hC1).measurable.aemeasurable
      ((hsNorm_measurable hmeas).pow_const 2).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hiAE] with y hy
    simp only [hessianKernel, hy]
  refine ⟨Ψ, hΨ, hleft, hright, hΨsm,
    KLS.LogConcave.weak_hessianKernel_isSteinKernel hC1 hl hG hnorm μ hm hiso hΨ hiAE,
    hessianKernel_symmetricAE hC2 Ψ μ, fun x => hPD (Ψ x), ?_, ?_, hHS, ?_, ?_⟩
  · intro i j
    have hD2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) :=
      (hsm.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
    have hentry : ContDiff ℝ ∞ (fun x => hessianMatrix u x i j) :=
      (hD2.clm_apply contDiff_const).clm_apply contDiff_const
    exact hentry.comp_contDiffOn hΨsm
  · intro y
    change hessianMatrix u (Ψ (gradient u y)) = hessianMatrix u y
    rw [hleft y]
  · rw [hHSint, integral_congr_ae hEq]
    simpa only [one_mul, mul_one, Matrix.trace_one, Fintype.card_fin, Nat.cast_id] using hTI.2
  · exact KLS.LogConcave.integral_hessianKernel_eq_one u hsm hc hnorm ν μ rfl hm hiso Ψ hΨ hiAE

section RegularClass
variable (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
  {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
  (hW : ContDiff ℝ ∞ W) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- Letwin Lemma 2.7 at the actual smooth moment potential, strong class, every n > 0. -/
theorem exists_regular_smooth_moment_stein_kernel :
    ∃ (u : E → ℝ) (Ψ : E → E),
      ContDiff ℝ ∞ u ∧ ConvexOn ℝ univ u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      (∀ x, (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x)) ∧
      (∃ e : E ≃ₜ interior K, ∀ x, (e x : E) = gradient u x) ∧
      Measurable Ψ ∧ Function.LeftInverse Ψ (gradient u) ∧
      (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ (interior K) ∧
      IsSteinKernel μ (hessianKernel u Ψ) ∧ SymmetricAE μ (hessianKernel u Ψ) ∧
      (∀ x, (hessianKernel u Ψ x).PosDef) ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun x => hessianKernel u Ψ x i j) (interior K)) ∧
      ∀ y, hessianKernel u Ψ (gradient u y) = hessianMatrix u y := by
  obtain ⟨u, _L, _LF, _T, hconv, hl, hnorm, hmap, hC1, hG, _hF, _hd, _hT, hC2, _hHc,
      hEvery, _hLocal, he, _hΨ, hsm, _hall, Ψ₀, hleft₀, hright₀, hΨ₀⟩ :=
    exists_regular_moment_potential_smooth hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨_hinj, Ψ, hΨ, hleft⟩ := measurable_inverse_gradient_of_map_gradient hn hl hconv hnorm hC1
    hK hKc (hKint.mono interior_subset) hW.continuous (hmap.trans hμ)
  have heqΨ : ∀ y ∈ interior K, Ψ y = Ψ₀ y := by
    intro y hy
    calc Ψ y = Ψ (gradient u (Ψ₀ y)) := congrArg Ψ (hright₀ y hy).symm
      _ = Ψ₀ y := hleft (Ψ₀ y)
  have hΨsm : ContDiffOn ℝ ∞ Ψ (interior K) := hΨ₀.congr heqΨ
  have hright : ∀ y ∈ interior K, gradient u (Ψ y) = y := by
    intro y hy
    rw [heqΨ y hy]
    exact hright₀ y hy
  have hstein := KLS.LogConcave.weak_hessianKernel_isSteinKernel hC1 hl hG hnorm μ hmap hiso
    hΨ (Filter.Eventually.of_forall hleft)
  refine ⟨u, Ψ, hsm, hconv, hnorm, hmap, fun x => ⟨(hEvery x).1, (hEvery x).2.1⟩,
    he, hΨ, hleft, hright, hΨsm, hstein, hessianKernel_symmetricAE hC2 Ψ μ,
    fun x => (hEvery (Ψ x)).1, ?_, ?_⟩
  · intro i j
    have hD2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) :=
      (hsm.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
    have hentry : ContDiff ℝ ∞ (fun x => hessianMatrix u x i j) :=
      (hD2.clm_apply contDiff_const).clm_apply contDiff_const
    exact hentry.comp_contDiffOn hΨsm
  · intro y
    change hessianMatrix u (Ψ (gradient u y)) = hessianMatrix u y
    rw [hleft y]
/-- Letwin Theorem 2.5 and Lemma 2.7 at ONE smooth strong-class moment potential, every n > 0:
all symmetric source trace bounds with constant 2, the smooth positive definite Stein kernel,
exact coupling and its sharp Hilbert–Schmidt bound ∫||tau||² <= 2n, with mean Id. -/
theorem exists_regular_smooth_moment_stein_kernel_L2 :
    ∃ (u : E → ℝ) (Ψ : E → E),
      ContDiff ℝ ∞ u ∧ ConvexOn ℝ univ u ∧
      LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      (∀ x, (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x)) ∧
      (∃ e : E ≃ₜ interior K, ∀ x, (e x : E) = gradient u x) ∧
      Measurable Ψ ∧ Function.LeftInverse Ψ (gradient u) ∧
      (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ (interior K) ∧
      IsSteinKernel μ (hessianKernel u Ψ) ∧ SymmetricAE μ (hessianKernel u Ψ) ∧
      (∀ x, (hessianKernel u Ψ x).PosDef) ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun x => hessianKernel u Ψ x i j) (interior K)) ∧
      (∀ y, hessianKernel u Ψ (gradient u y) = hessianMatrix u y) ∧
      (∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure E).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure E).tilted (-u))) ≤ 2 * (B * B).trace) ∧
      MemLp (fun x => hsNorm (hessianKernel u Ψ x)) 2 (μ : Measure E) ∧
      (∫ x, hsNorm (hessianKernel u Ψ x) ^ 2 ∂(μ : Measure E)) ≤ 2 * n ∧
      ∀ i j, (∫ x, hessianKernel u Ψ x i j ∂(μ : Measure E)) =
        (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    obtain
      ⟨u, _L, _LF, _T, hconv, hl, hnorm, hmap, _hC1, hG, _hF, _hd, _hT, _hC2, _hHc,
        hEvery, _hLocal, he, _hΨ, hsm, _hall, _hΨsm, _hmean, htrace⟩ :=
      exists_regular_moment_potential_smooth_trace hn hκ hK hKc hKint hW hstrong μ hμ
        hiso
    obtain
      ⟨Ψ, hΨ, hleft, hright, hΨsm, hstein, hsym, hPD, hentries, hcoupling, hHS,
        hHSbound, hmean⟩ :=
      sharp_smooth_stein_of_trace_bound hn hsm hconv hl hG hnorm μ hmap hiso hK hKc
        hKint hW.continuous hμ (fun x => (hEvery x).1) htrace
    exact
      ⟨u, Ψ, hsm, hconv, hG, hnorm, hmap, fun x => ⟨(hEvery x).1, (hEvery x).2.1⟩, he,
        hΨ, hleft, hright, hΨsm, hstein, hsym, hPD, hentries, hcoupling, htrace, hHS,
        hHSbound, hmean⟩

end RegularClass
end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Probability.MomentMeasure

open Set MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
open scoped ContDiff
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

section BoundedOpenConvexSource

/-! The literal source class of Letwin Lemma 2.2: `K` bounded open convex nonempty, `V` smooth on
an open `U ⊇ closure K` and convex on `K`, and an isotropic `μ = 1_K e^{-V} dx`, `n > 0`. -/

-- `E` is a local notation over the section variable `n`; section variables spell the space out.
variable (hn : 0 < n) {K U : Set (EuclideanSpace ℝ (Fin n))}
  (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
  (hU : IsOpen U) (hKU : closure K ⊆ U) {V : EuclideanSpace ℝ (Fin n) → ℝ}
  (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V)
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
  (hiso : KLS.Isotropic μ)

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- Given-potential form of Letwin arXiv:2607.24164v1, Lemmas 2.7 and 2.9 with Theorem 2.5: a
smooth convex `L`-Lipschitz normalized moment potential `φ` of `μ` with `G`-Lipschitz gradient,
positive definite Hessian, `log det ∇²φ = -φ + V(∇φ)`, `range ∇φ ⊆ K` and `∇²φ ≤ C Id` gives the
Stein kernel conclusions of `exists_smooth_moment_stein_kernel_of_bounded_open_convex`. -/
private theorem stein_kernel_of_smooth_potential
    {φ : E → ℝ} {L G : NNReal} {C : ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hL : LipschitzWith L φ) (hG : LipschitzWith G (gradient φ))
    (hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1)
    (hmap : ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E))
    (hPD : ∀ x, (hessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x))
    (hrange : range (gradient φ) ⊆ K)
    (hC : ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef) :
    ∃ Ψ : E → E,
      Measurable Ψ ∧ Function.LeftInverse Ψ (gradient φ) ∧
      (∀ y ∈ K, gradient φ (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ K ∧
      IsSteinKernel μ (hessianKernel φ Ψ) ∧ SymmetricAE μ (hessianKernel φ Ψ) ∧
      (∀ x, (hessianKernel φ Ψ x).PosDef) ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun x => hessianKernel φ Ψ x i j) K) ∧
      (∀ y, hessianKernel φ Ψ (gradient φ y) = hessianMatrix φ y) ∧
      (∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix φ x * B * hessianMatrix φ x).trace)
          ((volume : Measure E).tilted (-φ)) ∧
        (∫ x, (B * hessianMatrix φ x * B * hessianMatrix φ x).trace
          ∂((volume : Measure E).tilted (-φ))) ≤ 2 * (B * B).trace) ∧
      MemLp (fun x => hsNorm (hessianKernel φ Ψ x)) 2 (μ : Measure E) ∧
      (∫ x, hsNorm (hessianKernel φ Ψ x) ^ 2 ∂(μ : Measure E)) ≤ 2 * n ∧
      (∀ i j, (∫ x, hessianKernel φ Ψ x i j ∂(μ : Measure E)) =
        (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      ∀ v : E, (∫ x, linearLp μ hiso.memLp_two v x ∂(μ : Measure E)) = 0 ∧
        Energy.Dual.dualNorm μ (linearLp μ hiso.memLp_two v) ≠ ⊤ ∧
        (Energy.Dual.dualNorm μ (linearLp μ hiso.memLp_two v)).toReal ^ 2 ≤
          ∫ x, ‖action (hessianKernel φ Ψ x) v‖ ^ 2 ∂(μ : Measure E) := by
    have htrace := fun B hB =>
      integral_trace_hessian_quadratic_le hKb hKo hU hKU hV hVc μ hiso hφ hnorm hmap
        hrange hPD hMA ⟨C, hC⟩ B
        hB
    -- Replace `1_K e^{-V}` by `1_{closure K} e^{-W}` with `W` globally smooth.

    obtain ⟨W, hW, hWV⟩ := Analysis.exists_contDiff_eqOn_closure hKb hU hKU hV
    have hμW :
      (μ : Measure E) =
        (volume : Measure E).withDensity
          ((closure K).indicator fun p => ENNReal.ofReal (Real.exp (-W p))) := by
      have hKW :
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))) =
          K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)) :=
        indicator_congr fun x hx => by rw [hWV (subset_closure hx)]
      rw [hμ, hKW]
      exact
        withDensity_congr_ae
          (indicator_ae_eq_of_ae_eq_set
            (closure_ae_eq_of_null_frontier (hKc.addHaar_frontier volume)).symm)
    have hi : interior (closure K) = K := by
      simpa only [hKo.interior_eq] using
        hKc.interior_closure_eq_interior_of_nonempty_interior
          (by simpa only [hKo.interior_eq] using hKne)
    obtain
      ⟨Ψ, hΨ, hleft, hright, hΨsm, hstein, hsym, hPDk, hentries, hcoupling, hHS,
        hHSbound, hmean⟩ :=
      Analysis.sharp_smooth_stein_of_trace_bound hn hφ hc hL hG hnorm μ hmap hiso
        hKb.isCompact_closure hKc.closure (by rw [hi]; exact hKne) hW.continuous hμW hPD
        htrace
    rw [hi] at hright hΨsm hentries
    have hac : (μ : Measure E) ≪ volume := hμ ▸ withDensity_absolutelyContinuous _ _
    refine
      ⟨Ψ, hΨ, hleft, hright, hΨsm, hstein, hsym, hPDk, hentries, hcoupling, htrace, hHS,
        hHSbound, hmean, fun v => ?_⟩
    obtain ⟨h0, hfin, -, hbound⟩ :=
      linear_dual_bound_of_ac μ (hessianKernel φ Ψ) hstein hac hiso.memLp_two hsym hHS v
    exact ⟨h0, hfin, hbound⟩

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Lemmas 2.7 and 2.9 with Theorem 2.5 at the produced potential.**
Under the hypotheses of Lemma 2.2 (`exists_smooth_moment_potential_of_bounded_open_convex`: `K`
bounded open convex nonempty, `V` smooth on an open `U ⊇ closure K` and convex on `K`, isotropic
`μ = 1_K e^{-V} dx`, `n > 0`), one smooth convex moment potential `φ` (normalized, transporting
`ν = e^{-φ} dx` to `μ`, positive definite Hessian, `log det ∇²φ = -φ + V(∇φ)`, `∇φ : ℝⁿ ≃ₜ K`)
and a measurable everywhere left inverse `Ψ` of `∇φ`, smooth on `K` and a right inverse there,
give the kernel `τ = ∇²φ ∘ Ψ` with:
* Lemma 2.7 (Fathi): `τ` is a symmetric Stein kernel of `μ`, positive definite everywhere, with
  smooth entries on `K` and the exact coupling `τ(∇φ y) = ∇²φ(y)`; moreover `E_μ τ = Id` and
  `∫ ‖τ‖²_HS dμ ≤ 2n`;
* Theorem 2.5: `E_ν tr(B ∇²φ B ∇²φ) ≤ 2 tr(B²)` for every real symmetric `B`, with integrability;
* Lemma 2.9: for every `v`, the linear function `⟪·, v⟫ ∈ L²(μ)` is centered, has finite
  `H^{-1}(μ)` norm, and `‖⟪·, v⟫‖²_{H^{-1}(μ)} ≤ ∫ ‖τ(x) v‖² dμ`.

The same conclusions hold for every moment potential of `μ`:
`exists_stein_kernel_of_moment_potential_of_bounded_open_convex` (finite convex normalized) and
`exists_stein_kernel_of_ofPotential_of_bounded_open_convex` (essentially continuous). -/
theorem exists_smooth_moment_stein_kernel_of_bounded_open_convex :
    ∃ (φ : E → ℝ) (Ψ : E → E),
      ContDiff ℝ ∞ φ ∧ ConvexOn ℝ univ φ ∧
      (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E) ∧
      (∀ x, (hessianMatrix φ x).PosDef ∧
        Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      Measurable Ψ ∧ Function.LeftInverse Ψ (gradient φ) ∧
      (∀ y ∈ K, gradient φ (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ K ∧
      IsSteinKernel μ (hessianKernel φ Ψ) ∧ SymmetricAE μ (hessianKernel φ Ψ) ∧
      (∀ x, (hessianKernel φ Ψ x).PosDef) ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun x => hessianKernel φ Ψ x i j) K) ∧
      (∀ y, hessianKernel φ Ψ (gradient φ y) = hessianMatrix φ y) ∧
      (∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix φ x * B * hessianMatrix φ x).trace)
          ((volume : Measure E).tilted (-φ)) ∧
        (∫ x, (B * hessianMatrix φ x * B * hessianMatrix φ x).trace
          ∂((volume : Measure E).tilted (-φ))) ≤ 2 * (B * B).trace) ∧
      MemLp (fun x => hsNorm (hessianKernel φ Ψ x)) 2 (μ : Measure E) ∧
      (∫ x, hsNorm (hessianKernel φ Ψ x) ^ 2 ∂(μ : Measure E)) ≤ 2 * n ∧
      (∀ i j, (∫ x, hessianKernel φ Ψ x i j ∂(μ : Measure E)) =
        (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      ∀ v : E, (∫ x, linearLp μ hiso.memLp_two v x ∂(μ : Measure E)) = 0 ∧
        Energy.Dual.dualNorm μ (linearLp μ hiso.memLp_two v) ≠ ⊤ ∧
        (Energy.Dual.dualNorm μ (linearLp μ hiso.memLp_two v)).toReal ^ 2 ≤
          ∫ x, ‖action (hessianKernel φ Ψ x) v‖ ^ 2 ∂(μ : Measure E) := by
  obtain ⟨φ, L, G, C, hφ, hc, hL, hG, hnorm, hmap, hPD, hMA, ⟨e, he⟩, -, hC, -⟩ :=
    exists_smooth_moment_calculus_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc μ hμ hiso
  have hrange : range (gradient φ) ⊆ K := by
    rintro _ ⟨x, rfl⟩
    rw [← he x]
    exact (e x).property
  obtain ⟨Ψ, hΨ⟩ := stein_kernel_of_smooth_potential hn hKb hKo hKc hKne hU hKU hV hVc μ hμ hiso hφ
    hc hL hG hnorm hmap hPD hMA hrange hC
  exact ⟨φ, Ψ, hφ, hc, hnorm, hmap, fun x => ⟨hPD x, hMA x⟩, ⟨e, he⟩, hΨ⟩

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Lemmas 2.7 and 2.9 with Theorem 2.5, for every finite moment
potential.** Under the hypotheses of Lemma 2.2, every convex `φ : ℝⁿ → ℝ` with `∫ e^{-φ} = 1` and
`(∇φ)_* e^{-φ} dx = μ` is smooth with positive definite Hessian, `log det ∇²φ = -φ + V(∇φ)` and
`∇φ : ℝⁿ ≃ₜ K`, and has a measurable left inverse `Ψ` of `∇φ` with all the Stein kernel, trace
and `H^{-1}` conclusions of `exists_smooth_moment_stein_kernel_of_bounded_open_convex`. -/
theorem exists_stein_kernel_of_moment_potential_of_bounded_open_convex
    {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    (hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1)
    (hmap : ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E)) :
    ContDiff ℝ ∞ φ ∧
      (∀ x, (hessianMatrix φ x).PosDef ∧
        Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      ∃ Ψ : E → E,
      Measurable Ψ ∧ Function.LeftInverse Ψ (gradient φ) ∧
      (∀ y ∈ K, gradient φ (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ K ∧
      IsSteinKernel μ (hessianKernel φ Ψ) ∧ SymmetricAE μ (hessianKernel φ Ψ) ∧
      (∀ x, (hessianKernel φ Ψ x).PosDef) ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun x => hessianKernel φ Ψ x i j) K) ∧
      (∀ y, hessianKernel φ Ψ (gradient φ y) = hessianMatrix φ y) ∧
      (∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix φ x * B * hessianMatrix φ x).trace)
          ((volume : Measure E).tilted (-φ)) ∧
        (∫ x, (B * hessianMatrix φ x * B * hessianMatrix φ x).trace
          ∂((volume : Measure E).tilted (-φ))) ≤ 2 * (B * B).trace) ∧
      MemLp (fun x => hsNorm (hessianKernel φ Ψ x)) 2 (μ : Measure E) ∧
      (∫ x, hsNorm (hessianKernel φ Ψ x) ^ 2 ∂(μ : Measure E)) ≤ 2 * n ∧
      (∀ i j, (∫ x, hessianKernel φ Ψ x i j ∂(μ : Measure E)) =
        (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      ∀ v : E, (∫ x, linearLp μ hiso.memLp_two v x ∂(μ : Measure E)) = 0 ∧
        Energy.Dual.dualNorm μ (linearLp μ hiso.memLp_two v) ≠ ⊤ ∧
        (Energy.Dual.dualNorm μ (linearLp μ hiso.memLp_two v)).toReal ^ 2 ≤
          ∫ x, ‖action (hessianKernel φ Ψ x) v‖ ^ 2 ∂(μ : Measure E) := by
  obtain ⟨hφ, hPD, hMA, ⟨e, he⟩, -, ⟨C, hC⟩, L, G, hL, hG, -⟩ :=
    smooth_moment_calculus_of_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV
      hVc μ hμ hiso hc hnorm hmap
  have hrange : range (gradient φ) ⊆ K := by
    rintro _ ⟨x, rfl⟩
    rw [← he x]
    exact (e x).property
  exact ⟨hφ, fun x => ⟨hPD x, hMA x⟩, ⟨e, he⟩,
    stein_kernel_of_smooth_potential hn hKb hKo hKc hKne hU hKU hV hVc μ hμ hiso hφ hc hL hG hnorm
      hmap hPD hMA hrange hC⟩

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Lemmas 2.7 and 2.9 with Theorem 2.5, for the moment map of
Lemma 2.1.** Under the hypotheses of Lemma 2.2, every convex, essentially continuous
`ψ : ℝⁿ → ℝ ∪ {+∞}` (CEK arXiv:1304.0630v1, Definition 2) with moment measure
`ofPotential volume ψ = μ` is a finite normalized convex potential `φ` with the conclusions of
`exists_stein_kernel_of_moment_potential_of_bounded_open_convex`. -/
theorem exists_stein_kernel_of_ofPotential_of_bounded_open_convex
    {ψ : E → EReal} (hψ : Analysis.ConvexPotential ψ)
    (hess : Analysis.EssentiallyContinuous ψ) (hψμ : ofPotential volume ψ = (μ : Measure E)) :
    ∃ φ : E → ℝ, (∀ x, ψ x = φ x) ∧ ConvexOn ℝ univ φ ∧
      (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E) ∧
      ContDiff ℝ ∞ φ ∧
      (∀ x, (hessianMatrix φ x).PosDef ∧
        Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      ∃ Ψ : E → E,
      Measurable Ψ ∧ Function.LeftInverse Ψ (gradient φ) ∧
      (∀ y ∈ K, gradient φ (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ K ∧
      IsSteinKernel μ (hessianKernel φ Ψ) ∧ SymmetricAE μ (hessianKernel φ Ψ) ∧
      (∀ x, (hessianKernel φ Ψ x).PosDef) ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun x => hessianKernel φ Ψ x i j) K) ∧
      (∀ y, hessianKernel φ Ψ (gradient φ y) = hessianMatrix φ y) ∧
      (∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix φ x * B * hessianMatrix φ x).trace)
          ((volume : Measure E).tilted (-φ)) ∧
        (∫ x, (B * hessianMatrix φ x * B * hessianMatrix φ x).trace
          ∂((volume : Measure E).tilted (-φ))) ≤ 2 * (B * B).trace) ∧
      MemLp (fun x => hsNorm (hessianKernel φ Ψ x)) 2 (μ : Measure E) ∧
      (∫ x, hsNorm (hessianKernel φ Ψ x) ^ 2 ∂(μ : Measure E)) ≤ 2 * n ∧
      (∀ i j, (∫ x, hessianKernel φ Ψ x i j ∂(μ : Measure E)) =
        (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      ∀ v : E, (∫ x, linearLp μ hiso.memLp_two v x ∂(μ : Measure E)) = 0 ∧
        Energy.Dual.dualNorm μ (linearLp μ hiso.memLp_two v) ≠ ⊤ ∧
        (Energy.Dual.dualNorm μ (linearLp μ hiso.memLp_two v)).toReal ^ 2 ≤
          ∫ x, ‖action (hessianKernel φ Ψ x) v‖ ^ 2 ∂(μ : Measure E) := by
  obtain ⟨φ, hcoe, hc, hnorm, hmap, -⟩ :=
    smooth_of_ofPotential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc μ hμ hiso hψ hess
      hψμ
  exact ⟨φ, hcoe, hc, hnorm, hmap,
    exists_stein_kernel_of_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc
      μ hμ hiso hc hnorm hmap⟩

end BoundedOpenConvexSource

end FunctionalInequalities.Probability.MomentMeasure
