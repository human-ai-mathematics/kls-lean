/-
The compact-indicator approximation below adapts Mathlib's
Analysis/Distribution/AEEqOfIntegralContDiff.lean, by Sébastien Gouëzel (Apache 2.0).
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Order detected by nonnegative smooth tests

On a finite-dimensional real space with a finite Borel measure, nonnegative integrals against
all nonnegative smooth compactly supported tests detect a.e. nonnegativity of integrable
functions. The proof approximates compact indicators and uses inner regularity.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Function Set TopologicalSpace
open scoped Topology ContDiff Manifold

namespace FunctionalInequalities.Analysis.TestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {f g : E → ℝ}

private theorem setIntegral_nonneg_of_tests (hf : LocallyIntegrable f μ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x, φ x * f x ∂μ)
    (s : Set E) (hs : IsCompact s) : 0 ≤ ∫ x in s, f x ∂μ := by
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ IsCompact (cthickening δ s) := hs.exists_isCompact_cthickening
  -- choose a sequence of smooth functions `gₙ` equal to `1` on `s` and vanishing outside of the
  -- `uₙ`-neighborhood of `s`, where `uₙ` tends to zero. Each integral `∫ gₙ f` is nonnegative,
  -- and by dominated convergence these integrals converge to `∫ x in s, f`.
  obtain ⟨u, -, u_pos, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), u n ∈ Ioo 0 δ)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' δpos
  let v : ℕ → Set E := fun n ↦ thickening (u n) s
  obtain ⟨K, K_compact, vK⟩ : ∃ K, IsCompact K ∧ ∀ n, v n ⊆ K :=
    ⟨_, hδ, fun n ↦ thickening_subset_cthickening_of_le (u_pos n).2.le _⟩
  have : ∀ n, ∃ (g : E → ℝ), support g = v n ∧ ContDiff ℝ ∞ g ∧ Set.range g ⊆ Set.Icc 0 1
          ∧ ∀ x ∈ s, g x = 1 := by
    intro n
    rcases exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, E) isOpen_thickening hs.isClosed
      (self_subset_thickening (u_pos n).1 s) with ⟨g, g_smooth, g_range, g_supp, hg⟩
    exact ⟨g, g_supp, g_smooth.contDiff, g_range, fun x hx ↦ (hg x).1 hx⟩
  choose g g_supp g_diff g_range hg using this
  -- main fact: the integral of `∫ gₙ f` tends to `∫ x in s, f`.
  have L : Tendsto (fun n ↦ ∫ x, g n x * f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
    rw [← integral_indicator hs.measurableSet]
    let bound : E → ℝ := K.indicator (fun x ↦ ‖f x‖)
    have A : ∀ n, AEStronglyMeasurable (fun x ↦ g n x * f x) μ :=
      fun n ↦ (g_diff n).continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable
    have B : Integrable bound μ := by
      rw [integrable_indicator_iff K_compact.measurableSet]
      exact (hf.integrableOn_isCompact K_compact).norm
    have C : ∀ n, ∀ᵐ x ∂μ, ‖g n x * f x‖ ≤ bound x := by
      intro n
      filter_upwards with x
      rw [norm_mul]
      refine le_indicator_apply (fun _ ↦ ?_) (fun hxK ↦ ?_)
      · have : ‖g n x‖ ≤ 1 := by
          have := g_range n (mem_range_self (f := g n) x)
          rw [Real.norm_of_nonneg this.1]
          exact this.2
        exact mul_le_of_le_one_left (norm_nonneg _) this
      · have : g n x = 0 := by rw [← notMem_support, g_supp]; contrapose hxK; exact vK n hxK
        simp [this]
    have D : ∀ᵐ x ∂μ, Tendsto (fun n => g n x * f x) atTop (𝓝 (s.indicator f x)) := by
      filter_upwards with x
      by_cases hxs : x ∈ s
      · have : ∀ n, g n x = 1 := fun n ↦ hg n x hxs
        simp [this, indicator_of_mem hxs f]
      · simp_rw [indicator_of_notMem hxs f]
        apply tendsto_const_nhds.congr'
        suffices H : ∀ᶠ n in atTop, g n x = 0 by
          filter_upwards [H] with n hn using by simp [hn]
        obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ x ∉ thickening ε s := by
          rw [← hs.isClosed.closure_eq, closure_eq_iInter_thickening s] at hxs
          simpa using hxs
        filter_upwards [(tendsto_order.1 u_lim).2 _ εpos] with n hn
        rw [← notMem_support, g_supp]
        contrapose hε
        exact thickening_mono hn.le s hε
    exact tendsto_integral_of_dominated_convergence bound A B C D
  apply ge_of_tendsto L
  filter_upwards with n
  apply h _ (g_diff n)
  · apply HasCompactSupport.of_support_subset_isCompact K_compact
    simpa [g_supp] using vK n
  · exact fun x => (g_range n (mem_range_self (f := g n) x)).1

/-- Nonnegative smooth compactly supported tests detect a.e. nonnegativity. -/
theorem ae_nonneg_of_integral_mul_nonneg [IsFiniteMeasure μ] (hf : Integrable f μ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x, φ x * f x ∂μ) : ∀ᵐ x ∂μ, 0 ≤ f x := by
  let F := hf.aestronglyMeasurable.mk f
  have hFmeas : Measurable F := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have heq : f =ᵐ[μ] F := hf.aestronglyMeasurable.ae_eq_mk
  have hFi : Integrable F μ := hf.congr heq
  have hcompact : ∀ K : Set E, IsCompact K → 0 ≤ ∫ x in K, F x ∂μ := by
    intro K hK
    rw [← setIntegral_congr_ae hK.measurableSet (heq.mono fun x hx _ => hx)]
    exact setIntegral_nonneg_of_tests hf.locallyIntegrable h K hK
  have hzero : μ {x | F x < 0} = 0 := by
    rw [(measurableSet_lt hFmeas measurable_const).measure_eq_iSup_isCompact μ]
    apply le_antisymm ?_ bot_le
    refine iSup_le fun K => iSup_le fun hKsub => iSup_le fun hK => ?_
    have hneg : ∀ᵐ x ∂μ.restrict K, F x ≤ 0 :=
      (ae_restrict_mem hK.measurableSet).mono fun x hx => (hKsub hx).le
    have hInt : ∫ x in K, F x ∂μ = 0 :=
      le_antisymm (integral_nonpos_of_ae hneg) (hcompact K hK)
    have hz : ∀ᵐ x ∂μ.restrict K, F x = 0 :=
      by
        have hz := (integral_eq_zero_iff_of_nonneg_ae
          (hneg.mono fun x hx => neg_nonneg.mpr hx) hFi.integrableOn.neg).mp
          (by rw [integral_neg, hInt, neg_zero])
        exact hz.mono fun x hx => neg_eq_zero.mp hx
    have : ∀ᵐ x ∂μ.restrict K, False := by
      filter_upwards [ae_restrict_mem hK.measurableSet, hz] with x hx hx0
      exact (ne_of_lt (hKsub hx)) hx0
    simpa using this
  have hn : ∀ᵐ x ∂μ, 0 ≤ F x := by
    simpa only [ae_iff, not_le] using hzero
  filter_upwards [heq, hn] with x hx hn using hx ▸ hn

/-- Comparison of integrable functions from their nonnegative smooth tests. -/
theorem ae_le_of_integral_mul_le [IsFiniteMeasure μ] (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → (∫ x, φ x * f x ∂μ) ≤ ∫ x, φ x * g x ∂μ) :
    ∀ᵐ x ∂μ, f x ≤ g x := by
  have hn := ae_nonneg_of_integral_mul_nonneg (hg.sub hf) (fun φ hφ hφc hφ0 => by
    simp only [Pi.sub_apply, mul_sub]
    rw [integral_sub
      (by simpa only [smul_eq_mul] using
        hg.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc)
      (by simpa only [smul_eq_mul] using
        hf.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc)]
    exact sub_nonneg.mpr (h φ hφ hφc hφ0))
  exact hn.mono fun x hx => sub_nonneg.mp hx

end FunctionalInequalities.Analysis.TestFunction
