import FunctionalInequalities.Analysis.BakryEmery.Bochner
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts

/-!
# The curvature condition `CD(ρ, ∞)` for a potential with Hessian bounded below

Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators* (2014), discussion before
Corollary 4.8.2: for `ℒ f = Δ f - ⟪∇U, ∇f⟫` and `Γ(f) = ‖∇f‖²`, the Bochner identity
`Γ₂(f) = ‖∇∇f‖² + ∇∇U(∇f, ∇f)` shows that `∇∇U ≥ ρ Id` implies `CD(ρ, ∞)`, that is
`Γ₂(f) ≥ ρ Γ(f)`.

This file proves that pointwise statement (`mul_gamma_le_gammaTwo`), that a Hessian bounded below
by `ρ ≥ 0` makes `U` convex, and the integrated form against `μ = m.tilted (-U)`:
`∫ Γ₂(f) dμ = ∫ (ℒf)² dμ` for compactly supported `C³` functions `f`, hence
`ρ ∫ Γ(f) dμ ≤ ∫ (ℒf)² dμ`, the inequality behind BGL Proposition 4.8.3. The Hessian bound is
`∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v`.
-/

noncomputable section

open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A `C²` potential whose Hessian is bounded below by `ρ ≥ 0` is convex. -/
theorem convexOn_of_hessian_ge {U : E → ℝ} (hU : ContDiff ℝ 2 U) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    ConvexOn ℝ Set.univ U := by
  have hline :
      ∀ (x v : E), ConvexOn ℝ Set.univ (fun t : ℝ => U (x + t • v)) := by
    intro x v
    let g : ℝ → ℝ := fun t => U (x + t • v)
    have hg : ContDiff ℝ 2 g := by
      dsimp [g]
      exact hU.comp (by fun_prop)
    have hg' : ContDiff ℝ (1 + 1) g := by
      norm_num
      exact hg
    have hgd : ContDiff ℝ 1 (deriv g) := by
      exact (contDiff_succ_iff_deriv.mp hg').2.2
    refine convexOn_of_deriv2_nonneg' convex_univ
      ((hg.differentiable (by norm_num)).differentiableOn)
      ((hgd.differentiable (by norm_num)).differentiableOn) ?_
    intro t ht
    have hshift :
        deriv (deriv (fun s : ℝ => g (s + t))) 0 =
          deriv (deriv g) t := by
      have h₁ :
          deriv (fun s : ℝ => g (s + t)) =
            (fun s => deriv g (s + t)) := by
        funext s
        rw [deriv_comp_add_const]
      rw [h₁, deriv_comp_add_const]
      simp
    have hline₂ :
        (fun s : ℝ => g (s + t)) =
          (fun s : ℝ => U ((x + t • v) + s • v)) := by
      funext s
      dsimp [g]
      congr 1
      module
    have hsecond :
        deriv (deriv g) t =
          bilinearIteratedFDerivTwo ℝ U (x + t • v) v v := by
      rw [← hshift, hline₂]
      exact deriv_deriv_line hU (x + t • v) v
    have hnonneg : 0 ≤ deriv (deriv g) t := by
      rw [hsecond]
      exact
        le_trans
          (mul_nonneg hρ (sq_nonneg ‖v‖))
          (hH (x + t • v) v)
    simpa [Function.iterate_succ_apply, Function.iterate_zero_apply, g] using hnonneg
  refine ⟨convex_univ, ?_⟩
  intro a ha b hb α β hα hβ hαβ
  have h := hline a (b - a)
  have h' :=
    h.2 (show (0 : ℝ) ∈ Set.univ by simp)
      (show (1 : ℝ) ∈ Set.univ by simp) hα hβ hαβ
  have hα' : α = 1 - β := by
    linarith
  have hab : α • a + β • b = a + β • (b - a) := by
    rw [hα']
    module
  rw [hab]
  simpa [hα', smul_eq_mul] using h'

/-- Pointwise `CD(ρ, ∞)`: if `∇∇U ≥ ρ`, then `ρ Γ(f) ≤ Γ₂(f)` for every `C³` function `f`. -/
theorem mul_gamma_le_gammaTwo {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 3 f) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) (x : E) :
    ρ * gamma f f x ≤ gammaTwo U f x := by
  rw [gammaTwo_eq_hessianSqStdBasis_add hU hf x, gamma_self]
  have hH' := hH x (gradient f x)
  have hnonneg := hessianSqStdBasis_nonneg f x
  linarith

variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]

omit [m.IsAddHaarMeasure] in
/-- `ℒ Γ(f)` is integrable against `m.tilted (-U)` for compactly supported `C³` functions `f`. -/
theorem integrable_weightedLaplacian_gamma {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    MeasureTheory.Integrable (fun x => weightedLaplacian U (fun y => gamma f f y) x)
      (m.tilted (-U)) := by
  have hgamma : ContDiff ℝ 2 (gamma f f) := by
    exact contDiff_gamma (n := 2) hf hf (by norm_num) (by norm_num)
  have hcont :
      Continuous (fun x => weightedLaplacian U (fun y => gamma f f y) x) := by
    simpa using
      (continuous_weightedLaplacian (U := U) (f := gamma f f)
        (hU.of_le (by norm_num)) hgamma)
  have hcompact :
      HasCompactSupport
        (fun x => weightedLaplacian U (fun y => gamma f f y) x) := by
    simpa using
      (hasCompactSupport_weightedLaplacian U
        (hasCompactSupport_gamma_left f hfc))
  exact hcont.integrable_of_hasCompactSupport hcompact

omit [m.IsAddHaarMeasure] in
/-- `Γ(f, ℒf)` is integrable against `m.tilted (-U)` for compactly supported `C³` functions `f`. -/
theorem integrable_gamma_weightedLaplacian {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    MeasureTheory.Integrable (fun x => gamma f (weightedLaplacian U f) x) (m.tilted (-U)) := by
  have hL : ContDiff ℝ 1 (weightedLaplacian U f) := by
    exact contDiff_weightedLaplacian (n := 1) hU hf
      (by norm_num) (by norm_num)
  have hgamma : ContDiff ℝ 0 (gamma f (weightedLaplacian U f)) := by
    exact contDiff_gamma (n := 0) hf hL
      (by norm_num) (by norm_num)
  have hcont :
      Continuous (fun x => gamma f (weightedLaplacian U f) x) := by
    simpa using hgamma.continuous
  have hcompact :
      HasCompactSupport (fun x => gamma f (weightedLaplacian U f) x) := by
    simpa using
      (hasCompactSupport_gamma_left (weightedLaplacian U f) hfc)
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- The invariance `∫ ℒ Γ(f) dμ = 0` for `μ = m.tilted (-U)`. -/
theorem integral_weightedLaplacian_gamma_eq_zero {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    ∫ x, weightedLaplacian U (fun y => gamma f f y) x ∂(m.tilted (-U)) = 0 := by
  have h :=
    integral_inner_gradient_tilted m
      (U := U) (f := fun y => gamma f f y) (g := fun _ : E => (1 : ℝ))
      (hU.of_le (by norm_num))
      (contDiff_gamma (n := 2) hf hf (by norm_num) (by norm_num))
      (hasCompactSupport_gamma_left f hfc)
      (contDiff_const (c := (1 : ℝ)))
  simp only [gradient_fun_const, inner_zero_right, integral_zero, mul_one, integral_neg] at h
  exact neg_eq_zero.mp h.symm

/-- Integration by parts: `∫ Γ(f, ℒf) dμ = -∫ (ℒf)² dμ` for `μ = m.tilted (-U)`. -/
theorem integral_gamma_weightedLaplacian_eq {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    ∫ x, gamma f (weightedLaplacian U f) x ∂(m.tilted (-U)) =
      -∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by
  have hL : ContDiff ℝ 1 (weightedLaplacian U f) := by
    exact contDiff_weightedLaplacian (n := 1) hU hf
      (by norm_num) (by norm_num)
  have h :=
    integral_inner_gradient_tilted m
      (U := U) (f := f) (g := weightedLaplacian U f)
      (hU.of_le (by norm_num))
      (hf.of_le (by norm_num))
      hfc hL
  calc
    ∫ x, gamma f (weightedLaplacian U f) x ∂(m.tilted (-U)) =
        ∫ x, ⟪gradient f x, gradient (weightedLaplacian U f) x⟫
          ∂(m.tilted (-U)) := by
            simp only [gamma_apply]
    _ = ∫ x, -weightedLaplacian U f x * weightedLaplacian U f x
          ∂(m.tilted (-U)) := h
    _ = ∫ x, -(weightedLaplacian U f x ^ 2) ∂(m.tilted (-U)) := by
          congr 1
          funext x
          ring
    _ = -∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by
          rw [integral_neg]

/-- The integrated Bochner identity: for `μ = m.tilted (-U)` with `C²` potential `U` and a compactly
supported `C³` function `f`, `∫ Γ₂(f) dμ = ∫ (ℒf)² dμ`. -/
theorem integral_gammaTwo_eq {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) :
    ∫ x, gammaTwo U f x ∂(m.tilted (-U)) = ∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by
  simp only [gammaTwo_apply]
  rw [integral_sub
    ((integrable_weightedLaplacian_gamma m hU hf hfc).div_const 2)
    (integrable_gamma_weightedLaplacian m hU hf hfc),
    integral_div,
    integral_weightedLaplacian_gamma_eq_zero m hU hf hfc,
    integral_gamma_weightedLaplacian_eq m hU hf hfc]
  ring

/-- Integrated `CD(ρ, ∞)`: if `∇∇U ≥ ρ`, then `ρ ∫ Γ(f) dμ ≤ ∫ (ℒf)² dμ` for every compactly
supported `C³` function `f`. -/
theorem mul_integral_gamma_le {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    ρ * ∫ x, gamma f f x ∂(m.tilted (-U)) ≤ ∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by
  let μ := m.tilted (-U)

  have hgamma : ContDiff ℝ 2 (gamma f f) := by
    exact contDiff_gamma (n := 2) hf hf (by norm_num) (by norm_num)

  have hgamma_cont : Continuous (fun x => gamma f f x) := by
    simpa using hgamma.continuous

  have hgamma_compact : HasCompactSupport (fun x => gamma f f x) := by
    simpa using hasCompactSupport_gamma_left f hfc

  have hgamma_integrable : Integrable (fun x => gamma f f x) μ := by
    dsimp [μ]
    exact hgamma_cont.integrable_of_hasCompactSupport hgamma_compact

  have hscaled_integrable : Integrable (fun x => ρ * gamma f f x) μ := by
    exact hgamma_integrable.const_mul ρ

  have hgammaTwo_integrable : Integrable (fun x => gammaTwo U f x) μ := by
    have h₁ :
        Integrable
          ((fun x => weightedLaplacian U (fun y => gamma f f y) x / 2) -
            (fun x => gamma f (weightedLaplacian U f) x)) μ := by
      exact
        ((integrable_weightedLaplacian_gamma m hU hf hfc).div_const 2).sub
          (integrable_gamma_weightedLaplacian m hU hf hfc)
    convert h₁ using 1
    funext x
    rfl

  have hpoint :
      ∀ x, ρ * gamma f f x ≤ gammaTwo U f x := by
    intro x
    exact mul_gamma_le_gammaTwo hU hf hH x

  rw [← integral_const_mul]
  rw [← integral_gammaTwo_eq m hU hf hfc]
  exact integral_mono hscaled_integrable hgammaTwo_integrable hpoint

end FunctionalInequalities.Analysis.BakryEmery
