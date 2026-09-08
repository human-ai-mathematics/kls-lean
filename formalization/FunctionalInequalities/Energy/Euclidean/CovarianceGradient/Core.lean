import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Operator
import FunctionalInequalities.Energy.Euclidean.WeakDerivative
import FunctionalInequalities.L2.MeanVariance
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Dense domain and smooth core of the weighted gradient operator

Source: Blueprint `lem:covariance-core-closure`, the statements "densely defined" and "its graph
closure equals the graph closure of the restrictions of `ℝ + C_c^∞(V)`". Read
`IsGradientTest.of_contDiff_hasCompactSupport`, `smoothCore`, `dense_smoothCore`,
`dense_domain_gradientOperator`, and `closure_domRestrict_smoothCore`.

Smooth compactly supported functions are globally Lipschitz `L²` functions with bounded weighted
gradient, hence tests; their classes form the submodule `smoothCore ν`, which Mathlib proves dense
in `L²(ν)` for every finite Borel measure on a finite-dimensional space. This gives the dense
domain without any hypothesis on `ν`. The certified approximation theorem
`lem:covariance-test-core-density` approximates every test in graph norm by smooth compactly
supported functions when `ν` is absolutely continuous with respect to a Haar measure, so the
restriction of a closable weighted gradient operator to the smooth core has the same closure;
by monotonicity the same holds for every intermediate core, in particular for the Blueprint's
`ℝ + C_c^∞(V)`.

Closability itself is proved in `Closable.lean`; nothing here asserts it.
-/

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff

namespace FunctionalInequalities.Energy.Euclidean

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

variable (ν : ProbabilityMeasure V) (B : V →L[ℝ] V)

/-- A smooth compactly supported function is globally Lipschitz. -/
theorem lipschitzWith_of_contDiff_hasCompactSupport {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) : ∃ K : NNReal, LipschitzWith K g := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_of_hasCompactSupport (hg.of_le (mod_cast le_top)) hs
  refine ⟨⟨M, hM0⟩, lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable (by simp)) fun x ↦ ?_⟩
  change ‖fderiv ℝ g x‖ ≤ M
  exact hM x

/-- The weighted gradient of a smooth compactly supported function has compact support. -/
theorem hasCompactSupport_weightedGradient {g : V → ℝ} (hs : HasCompactSupport g) :
    HasCompactSupport (weightedGradient B g) := by
  have h1 : HasCompactSupport (gradient g) := by
    change HasCompactSupport ((toDual ℝ V).symm ∘ fderiv ℝ g)
    exact (hs.fderiv ℝ).comp_left (map_zero _)
  exact h1.comp_left (map_zero B)

/-- Smooth compactly supported functions are weighted gradient tests for every law. -/
theorem IsGradientTest.of_contDiff_hasCompactSupport {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) : IsGradientTest ν B g := by
  refine ⟨lipschitzWith_of_contDiff_hasCompactSupport hg hs, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hs
    exact MemLp.of_bound hg.continuous.aestronglyMeasurable C (ae_of_all _ hC)
  · have hcont : Continuous (weightedGradient B g) :=
      B.continuous.comp (continuous_gradient_of_contDiff hg (by simp))
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hasCompactSupport_weightedGradient B hs)
    exact MemLp.of_bound hcont.aestronglyMeasurable C (ae_of_all _ hC)

/-- Smooth compactly supported functions are square integrable for every probability law. -/
theorem memLp_of_contDiff_hasCompactSupport {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) : MemLp g 2 (ν : Measure V) :=
  (IsGradientTest.of_contDiff_hasCompactSupport ν 0 hg hs).memLp_two

/-- The smooth core: classes of smooth compactly supported functions in `L²(ν)`. -/
def smoothCore : Submodule ℝ (Lp ℝ 2 (ν : Measure V)) where
  carrier := {f | ∃ (g : V → ℝ) (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g),
    f = (memLp_of_contDiff_hasCompactSupport ν hg hs).toLp g}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    exact (MemLp.toLp_zero _).symm
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, hs₁, rfl⟩ ⟨g₂, hg₂, hs₂, rfl⟩
    refine ⟨g₁ + g₂, hg₁.add hg₂, hs₁.add hs₂, ?_⟩
    exact (MemLp.toLp_add _ _).symm
  smul_mem' := by
    rintro c f ⟨g, hg, hs, hf⟩
    have hcs : HasCompactSupport (c • g) := by
      have heq : c • g = (fun _ ↦ c) * g := by
        funext x
        simp [smul_eq_mul]
      rw [heq]
      exact hs.mul_left
    refine ⟨c • g, hg.const_smul c, hcs, ?_⟩
    rw [hf]
    exact (MemLp.toLp_const_smul c _).symm

theorem mem_smoothCore_iff (f : Lp ℝ 2 (ν : Measure V)) :
    f ∈ smoothCore ν ↔ ∃ (g : V → ℝ) (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g),
      f = (memLp_of_contDiff_hasCompactSupport ν hg hs).toLp g :=
  Iff.rfl

/-- The smooth core is dense in `L²(ν)`. -/
theorem dense_smoothCore : Dense (smoothCore ν : Set (Lp ℝ 2 (ν : Measure V))) := by
  refine (Lp.dense_hasCompactSupport_contDiff (μ := (ν : Measure V)) (F := ℝ) (p := 2)
    (by simp)).mono ?_
  rintro f ⟨g, hfg, hs, hg⟩
  refine ⟨g, hg, hs, ?_⟩
  apply Lp.ext
  exact hfg.trans (memLp_of_contDiff_hasCompactSupport ν hg hs).coeFn_toLp.symm

/-- The Blueprint core `ℝ + C_c^∞(V)`: constants together with the smooth compactly supported
classes. -/
def constantSmoothCore : Submodule ℝ (Lp ℝ 2 (ν : Measure V)) :=
  smoothCore ν ⊔ Submodule.span ℝ {L2.const ν 1}

theorem smoothCore_le_constantSmoothCore : smoothCore ν ≤ constantSmoothCore ν :=
  le_sup_left

/-- The `L²` constant one is the class of the constant test one. -/
theorem L2_const_eq_toLp (c : ℝ) :
    L2.const ν c = (memLp_const c : MemLp (fun _ : V ↦ c) 2 (ν : Measure V)).toLp _ := by
  apply Lp.ext
  exact (L2.const_coeFn ν c).trans (MemLp.coeFn_toLp _).symm

variable {m : Measure V} [m.IsAddHaarMeasure]

/-- The smooth core lies in the domain of the weighted gradient operator. -/
theorem smoothCore_le_domain_gradientOperator (hac : (ν : Measure V) ≪ m) :
    smoothCore ν ≤ (gradientOperator ν B hac).domain := by
  rintro f ⟨g, hg, hs, rfl⟩
  exact (mem_domain_gradientOperator_iff ν B hac _).mpr
    ⟨g, IsGradientTest.of_contDiff_hasCompactSupport ν B hg hs, rfl⟩

/-- The Blueprint core `ℝ + C_c^∞(V)` lies in the domain of the weighted gradient operator. -/
theorem constantSmoothCore_le_domain_gradientOperator (hac : (ν : Measure V) ≪ m) :
    constantSmoothCore ν ≤ (gradientOperator ν B hac).domain := by
  refine sup_le (smoothCore_le_domain_gradientOperator ν B hac) ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  change L2.const ν 1 ∈ (gradientOperator ν B hac).domain
  rw [L2_const_eq_toLp]
  exact toLp_mem_domain_gradientOperator ν B hac (IsGradientTest.const 1)

/-- The weighted gradient operator is densely defined. -/
theorem dense_domain_gradientOperator (hac : (ν : Measure V) ≪ m) :
    Dense ((gradientOperator ν B hac).domain : Set (Lp ℝ 2 (ν : Measure V))) :=
  (dense_smoothCore ν).mono (smoothCore_le_domain_gradientOperator ν B hac)

/-- Every test is a graph-norm limit of smooth compactly supported functions: the certified
weighted approximation theorem in operator form. -/
theorem exists_smoothCore_tendsto (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (f : (gradientOperator ν B hac).domain) :
    ∃ s : ℕ → smoothCore ν,
      Tendsto (fun n ↦ ((s n : Lp ℝ 2 (ν : Measure V)),
        gradientOperator ν B hac ⟨s n, smoothCore_le_domain_gradientOperator ν B hac (s n).2⟩))
        atTop (𝓝 ((f : Lp ℝ 2 (ν : Measure V)), gradientOperator ν B hac f)) := by
  obtain ⟨g, h, hfg⟩ := (mem_domain_gradientOperator_iff ν B hac _).mp f.2
  obtain ⟨K, hK⟩ := h.1
  obtain ⟨gSeq, hprop, hconv, hconvB⟩ := LipschitzApproximation.exists_smooth_weighted_L2_approximation
    ν m hac B g hK.locallyLipschitz h.memLp_two h.memLp_weightedGradient
  have hmem : ∀ n, (memLp_of_contDiff_hasCompactSupport ν (hprop n).1 (hprop n).2.1).toLp (gSeq n) ∈
      smoothCore ν := fun n ↦ ⟨gSeq n, (hprop n).1, (hprop n).2.1, rfl⟩
  refine ⟨fun n ↦ ⟨_, hmem n⟩, ?_⟩
  have htest : ∀ n, IsGradientTest ν B (gSeq n) := fun n ↦
    IsGradientTest.of_contDiff_hasCompactSupport ν B (hprop n).1 (hprop n).2.1
  have hT : ∀ n, gradientOperator ν B hac
      ⟨(memLp_of_contDiff_hasCompactSupport ν (hprop n).1 (hprop n).2.1).toLp (gSeq n),
        smoothCore_le_domain_gradientOperator ν B hac (hmem n)⟩ =
      (htest n).memLp_weightedGradient.toLp (weightedGradient B (gSeq n)) := fun n ↦
    gradientOperator_apply ν B hac hfr (htest n) _ rfl
  have hTf : gradientOperator ν B hac f = h.memLp_weightedGradient.toLp (weightedGradient B g) :=
    gradientOperator_apply ν B hac hfr h f.2 hfg
  refine Tendsto.prodMk_nhds ?_ ?_
  · rw [hfg, tendsto_iff_norm_sub_tendsto_zero]
    have h1 : ∀ n, ‖(memLp_of_contDiff_hasCompactSupport ν (hprop n).1 (hprop n).2.1).toLp (gSeq n) -
        h.memLp_two.toLp g‖ = (eLpNorm (fun x ↦ gSeq n x - g x) 2 (ν : Measure V)).toReal := by
      intro n
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
      rfl
    simp_rw [h1]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
    simpa [Function.comp_def] using this
  · simp only [hT, hTf]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : ∀ n, ‖(htest n).memLp_weightedGradient.toLp (weightedGradient B (gSeq n)) -
        h.memLp_weightedGradient.toLp (weightedGradient B g)‖ =
        (eLpNorm (fun x ↦ B (gradient (gSeq n) x) - B (gradient g x)) 2 (ν : Measure V)).toReal := by
      intro n
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
      rfl
    simp_rw [h1]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconvB
    simpa [Function.comp_def] using this

/-- For a closable weighted gradient operator, restricting to the smooth core does not change
the closure. -/
theorem closure_domRestrict_smoothCore (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hT : (gradientOperator ν B hac).IsClosable) :
    ((gradientOperator ν B hac).domRestrict (smoothCore ν)).closure =
      (gradientOperator ν B hac).closure :=
  Energy.IsClosable.closure_domRestrict_eq hT (smoothCore_le_domain_gradientOperator ν B hac)
    (exists_smoothCore_tendsto ν B hac hfr)

/-- Every core between the smooth core and the full domain, such as `ℝ + C_c^∞`, has the same
closure. -/
theorem closure_domRestrict_eq_of_smoothCore_le (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hT : (gradientOperator ν B hac).IsClosable) {S : Submodule ℝ (Lp ℝ 2 (ν : Measure V))}
    (hS : smoothCore ν ≤ S) (hS' : S ≤ (gradientOperator ν B hac).domain) :
    ((gradientOperator ν B hac).domRestrict S).closure = (gradientOperator ν B hac).closure :=
  Energy.IsClosable.closure_domRestrict_eq_of_le hT hS hS'
    (closure_domRestrict_smoothCore ν B hac hfr hT)

end FunctionalInequalities.Energy.Euclidean
