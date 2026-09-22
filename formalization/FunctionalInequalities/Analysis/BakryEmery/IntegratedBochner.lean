import FunctionalInequalities.Analysis.BakryEmery.Bochner
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts
import FunctionalInequalities.Analysis.BakryEmery.WeakGamma

/-!
# The integrated Bochner inequality on smooth compactly supported tests

`Bochner.lean` proves the **pointwise** inequality `0 ≤ Γ₂(f)` for a `C²` convex potential and a
`C³` function. A pointwise inequality is not a statement about the heat semigroup: to reach one,
`Γ₂` must be integrated against a test function and the Laplacian moved off `Γ(f, f)`. This
module performs exactly that step, and nothing more.

For `μ = m.tilted (-U)` the law of density `exp (-U)`, a `C²` convex `U`, a `C³` compactly
supported `f` and a `C²` compactly supported `φ ≥ 0`,

`0 ≤ (∫ (ℒφ) Γ(f, f) dμ) / 2 - ∫ φ Γ(f, ℒf) dμ`  (`integral_mul_gammaTwo_nonneg`),

which is `∫ φ Γ₂(f) dμ ≥ 0` after moving `ℒ` from `Γ(f, f)` to `φ` with
`integral_weightedLaplacian_mul_comm`. Every integrand here is continuous with compact support,
so all three integrals are finite for any finite measure; no `L²` membership of `Γ(f, f)` is
claimed or needed, and none is available in general.

## What this is not

`f` and `φ` are classical smooth compactly supported functions. Nothing here applies to
`P_t g`: the heat semigroup does not preserve compact support or smoothness, and passing to a
limit requires the convergence hypotheses of
`KLS/LogConcave/HeatSemigroup/Gamma.lean`. No gradient estimate, no time interpolation and no
Buser inequality follows from this module alone.
-/

noncomputable section

open MeasureTheory InnerProductSpace Filter Topology
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Integrated

variable (m : Measure E) [m.IsAddHaarMeasure] {μ : Measure E} [IsFiniteMeasure μ] {U : E → ℝ}

omit [CompleteSpace E] in
private theorem integrable_of_continuous_hasCompactSupport {h : E → ℝ} (hc : Continuous h)
    (hs : HasCompactSupport h) : Integrable h μ :=
  memLp_one_iff_integrable.mp (hc.memLp_of_hasCompactSupport hs)

/-- **The integrated Bochner inequality** (weak `Γ₂ ≥ 0` on smooth compactly supported tests).
For `μ = m.tilted (-U)` with a `C²` convex potential `U`, a `C³` compactly supported `f` and a
`C²` compactly supported `φ ≥ 0`,
`0 ≤ (∫ (ℒφ) Γ(f, f) dμ) / 2 - ∫ φ Γ(f, ℒf) dμ`. -/
theorem integral_mul_gammaTwo_nonneg (hμ : μ = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) {f φ : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ (∫ x, weightedLaplacian U φ x * gamma f f x ∂μ) / 2 -
      ∫ x, φ x * gamma f (weightedLaplacian U f) x ∂μ := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hΓ2 : ContDiff ℝ 2 (gamma f f) := contDiff_gamma hf hf (by norm_num) (by norm_num)
  have hΓc : HasCompactSupport (gamma f f) := hasCompactSupport_gamma_left f hfc
  have hLf1 : ContDiff ℝ 1 (weightedLaplacian U f) :=
    contDiff_weightedLaplacian hU hf (by norm_num) (by norm_num)
  have hA : Integrable (fun x => φ x * weightedLaplacian U (gamma f f) x) μ :=
    integrable_of_continuous_hasCompactSupport
      (hφ.continuous.mul (continuous_weightedLaplacian hU1 hΓ2)) hφc.mul_right
  have hB : Integrable (fun x => φ x * gamma f (weightedLaplacian U f) x) μ :=
    integrable_of_continuous_hasCompactSupport
      (hφ.continuous.mul (continuous_gamma hf1 hLf1)) hφc.mul_right
  have hsplit : ∫ x, φ x * gammaTwo U f x ∂μ =
      (∫ x, φ x * weightedLaplacian U (gamma f f) x ∂μ) / 2 -
        ∫ x, φ x * gamma f (weightedLaplacian U f) x ∂μ := by
    rw [← integral_div, ← integral_sub (hA.div_const 2) hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [gammaTwo_apply]
    ring
  have hsym : ∫ x, φ x * weightedLaplacian U (gamma f f) x ∂μ =
      ∫ x, weightedLaplacian U φ x * gamma f f x ∂μ := by
    rw [hμ]
    exact (integral_weightedLaplacian_mul_comm m hU1 hφ hφc hΓ2 hΓc).symm
  have hnn : 0 ≤ ∫ x, φ x * gammaTwo U f x ∂μ :=
    integral_nonneg fun x => mul_nonneg (hφ0 x) (gammaTwo_nonneg hU hconv hf x)
  rw [hsplit, hsym] at hnn
  exact hnn

/-- **The integrated Bochner inequality in weak form.** The two classical gradients are replaced
by arbitrary `L²` vector fields `u`, `w` representing `∇f` and `-∇(ℒf)`; in the
nonnegative-generator convention `A = -ℒ` the second field is `∇(Af)`, so the statement reads
`0 ≤ (∫ (ℒφ) Γ(u, u) dμ) / 2 + ∫ φ Γ(u, w) dμ`. The test function `φ` stays classical: its role
is to be a **bounded** multiplier, which an abstract `L²` datum is not. -/
theorem integral_mul_weakGamma_nonneg (hμ : μ = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) {f φ : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) {u w : Lp E 2 μ} (hu : (u : E → E) =ᵐ[μ] gradient f)
    (hw : (w : E → E) =ᵐ[μ] fun x => -gradient (weightedLaplacian U f) x) :
    0 ≤ (∫ x, weightedLaplacian U φ x * WeakGamma.apply u u x ∂μ) / 2 +
      ∫ x, φ x * WeakGamma.apply u w x ∂μ := by
  have e1 : (fun x => weightedLaplacian U φ x * WeakGamma.apply u u x)
      =ᵐ[μ] fun x => weightedLaplacian U φ x * gamma f f x := by
    filter_upwards [WeakGamma.ae_eq_of_ae_eq hu hu] with x hx
    rw [hx, gamma_apply]
  have e2 : (fun x => φ x * WeakGamma.apply u w x)
      =ᵐ[μ] fun x => -(φ x * gamma f (weightedLaplacian U f) x) := by
    filter_upwards [WeakGamma.ae_eq_of_ae_eq hu hw] with x hx
    rw [hx, gamma_apply, inner_neg_right]
    ring
  rw [integral_congr_ae e1, integral_congr_ae e2, integral_neg, ← sub_eq_add_neg]
  exact integral_mul_gammaTwo_nonneg m hμ hU hconv hf hfc hφ hφc hφ0

/-- **Transfer of the weak integrated Bochner inequality along `L²` convergence of the fields.**
Each term of `integral_mul_weakGamma_nonneg` is continuous for the `L²` topology of the fields,
because the test function and `ℒφ` are bounded with compact support: this is exactly
`WeakGamma.tendsto_integral_mul`. Consequently the inequality holds for any pair of `L²` limits
of smooth data. The hypotheses say precisely what an approximation argument must supply — `∇fₙ`
converging in `L²` to `u`, and `∇(Afₙ) = -∇(ℒfₙ)` converging in `L²` to `w`. Neither convergence
is provided by this module, and neither follows from `L²` convergence of `fₙ` alone. -/
theorem integral_mul_weakGamma_nonneg_of_tendsto (hμ : μ = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {f : ℕ → E → ℝ}
    (hf : ∀ n, ContDiff ℝ 3 (f n)) (hfc : ∀ n, HasCompactSupport (f n))
    {u w : ℕ → Lp E 2 μ} {u₀ w₀ : Lp E 2 μ}
    (hu : ∀ n, ((u n : E → E)) =ᵐ[μ] gradient (f n))
    (hw : ∀ n, ((w n : E → E)) =ᵐ[μ] fun x => -gradient (weightedLaplacian U (f n)) x)
    (hul : Tendsto (fun n => ‖u n - u₀‖) atTop (𝓝 0))
    (hwl : Tendsto (fun n => ‖w n - w₀‖) atTop (𝓝 0)) :
    0 ≤ (∫ x, weightedLaplacian U φ x * WeakGamma.apply u₀ u₀ x ∂μ) / 2 +
      ∫ x, φ x * WeakGamma.apply u₀ w₀ x ∂μ := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  obtain ⟨C₁, hC₁⟩ := (continuous_weightedLaplacian hU1 hφ).bounded_above_of_compact_support
    (hasCompactSupport_weightedLaplacian U hφc)
  obtain ⟨C₂, hC₂⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hC₁' : ∀ᵐ x ∂μ, |weightedLaplacian U φ x| ≤ C₁ :=
    Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC₁ x
  have hC₂' : ∀ᵐ x ∂μ, |φ x| ≤ C₂ := Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hC₂ x
  have h1 := WeakGamma.tendsto_integral_mul
    (continuous_weightedLaplacian hU1 hφ).aestronglyMeasurable
    (le_trans (norm_nonneg _) (hC₁ 0)) hC₁' hul hul
  have h2 := WeakGamma.tendsto_integral_mul hφ.continuous.aestronglyMeasurable
    (le_trans (norm_nonneg _) (hC₂ 0)) hC₂' hul hwl
  exact ge_of_tendsto' ((h1.div_const 2).add h2) fun n =>
    integral_mul_weakGamma_nonneg m hμ hU hconv (hf n) (hfc n) hφ hφc hφ0 (hu n) (hw n)

end Integrated

section GeneratorForm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]

/-- **Transfer of the generator form of the weak `Γ₂` inequality along `L²` convergence.**

The generator form replaces `∫ φ Γ(u, w) dμ`, whose second field `w` is a second-order object,
by the two terms `∫ φ a² dμ` and `∫ a Γ(u, β) dμ`, in which `a` is the generator image and `β`
is the (bounded) gradient field of the test function. Both are continuous for `L²` convergence
of the pair `(u, a)`: the first because `φ` is bounded, the second by
`WeakGamma.tendsto_integral_mul_of_bdd_right`. This lemma is measure-theoretic; it knows nothing
about potentials, convexity or semigroups, and it is stated so that the per-index inequality is
the only structural input. -/
theorem integral_mul_sq_nonneg_of_tendsto {ψ φ : α → ℝ} {C₁ C₂ N : ℝ} {β : Lp H 2 μ}
    (hψm : AEStronglyMeasurable ψ μ) (hC₁0 : 0 ≤ C₁) (hψb : ∀ᵐ x ∂μ, |ψ x| ≤ C₁)
    (hφm : AEStronglyMeasurable φ μ) (hC₂0 : 0 ≤ C₂) (hφb : ∀ᵐ x ∂μ, |φ x| ≤ C₂)
    (hN0 : 0 ≤ N) (hNb : ∀ᵐ x ∂μ, ‖β x‖ ≤ N)
    {u : ℕ → Lp H 2 μ} {a : ℕ → Lp ℝ 2 μ} {u₀ : Lp H 2 μ} {a₀ : Lp ℝ 2 μ}
    (hu : Filter.Tendsto (fun n => ‖u n - u₀‖) atTop (𝓝 0))
    (ha : Filter.Tendsto (fun n => ‖a n - a₀‖) atTop (𝓝 0))
    (hnn : ∀ n, 0 ≤ (∫ x, ψ x * WeakGamma.apply (u n) (u n) x ∂μ) / 2 +
      (∫ x, φ x * ((a n : α → ℝ) x) ^ 2 ∂μ) -
        ∫ x, (a n : α → ℝ) x * WeakGamma.apply (u n) β x ∂μ) :
    0 ≤ (∫ x, ψ x * WeakGamma.apply u₀ u₀ x ∂μ) / 2 +
      (∫ x, φ x * ((a₀ : α → ℝ) x) ^ 2 ∂μ) -
        ∫ x, (a₀ : α → ℝ) x * WeakGamma.apply u₀ β x ∂μ := by
  have hsq : ∀ v : Lp ℝ 2 μ, (fun x => φ x * WeakGamma.apply v v x)
      = fun x => φ x * ((v : α → ℝ) x) ^ 2 := fun v => by
    funext x
    rw [WeakGamma.apply_self_real]
  have h1 := WeakGamma.tendsto_integral_mul hψm hC₁0 hψb hu hu
  have h2 := WeakGamma.tendsto_integral_mul (H := ℝ) hφm hC₂0 hφb ha ha
  simp only [hsq] at h2
  have h3 := WeakGamma.tendsto_integral_mul_of_bdd_right hN0 hNb ha hu
  exact ge_of_tendsto' (((h1.div_const 2).add h2).sub h3) hnn

end GeneratorForm

end FunctionalInequalities.Analysis.BakryEmery
