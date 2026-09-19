import FunctionalInequalities.KLS.LogConcave.Density.AbsoluteContinuity
import FunctionalInequalities.KLS.LogConcave.Borel
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Borell representation on the affine support

Source: Blueprint `thm:borell-logconcave-density`, Borell (1974), *Convex measures on locally
convex spaces*, Theorem 1.1 and its finite-dimensional consequences; Bobkov (1999) for the
exponential tail. Read `IsBorellDensity`, then the representative properties, the moment
section, the construction, and finally the intrinsic theorems at the end.

The intrinsic law `ν` of a compact-set log-concave probability `μ` lives on the direction
space `V` of the affine support and is absolutely continuous with respect to every additive
Haar measure `m` on `V`; that part is proved in `KLS/LogConcave/Density/AbsoluteContinuity.lean`.
This module proves the remaining conclusions of the representation theorem:

1. `ν` has a density representative `ρ : V → ℝ` that is Borel, nonnegative, finite-valued,
   upper semicontinuous and log-concave, with `ν = ρ · m` (`IsBorellDensity`,
   `LogConcave.exists_isBorellDensity`);
2. every such representative is positive and continuous on the interior `Ω` of the support of
   `ν` and is bounded above and below by positive constants on every compact subset of `Ω`
   (`IsBorellDensity.pos_of_mem_interior_support`, `IsBorellDensity.continuousOn_interior_support`,
   `IsBorellDensity.exists_bounds_of_isCompact`);
3. `ν` has an exponential moment, hence finite moments of every order
   (`LogConcave.intrinsic_integrable_exp_norm`, `LogConcave.intrinsic_integrable_norm_pow`).

Proof routes. The representative is the upper semicontinuous envelope of the lower density
`liminf ν(B(x, rₙ)) / m(B(0, rₙ))` along `rₙ = 1/(n+1)`: the lower density is log-concave
because equal-radius ball masses are, it is bounded by the proved small-ball estimate, and it
equals the Radon--Nikodym derivative almost everywhere by the Besicovitch differentiation
theorem; the envelope changes it only on the Haar-null frontier of its convex positivity set.
Positivity and the compact bounds use that a convex set with empty interior is Haar-null and that
the logarithm of a log-concave function is concave, hence continuous, on the open interior of the
positivity set. The exponential moment is Borell's lemma applied through the proved Borel-set
formulation: once a ball of radius `R` carries mass `3/4`, the mass outside radius `k R` is at
most `3^{(1-k)/2}`, and the exponential is dominated by a geometric series.

Quantities: `Ω` is `interior ν.support`. The Blueprint writes `Ω` as the interior of the closed
convex hull of the topological support; the two descriptions coincide because the support of a
log-concave law is closed and convex, and `closure_convexHull_intrinsic_support` proves this.
`ν (Ωᶜ) = 0` is `intrinsic_interior_support_compl`.

Reference measures are arbitrary additive Haar measures, so the theorem includes the
zero-dimensional direction space, where every Haar measure is a positive multiple of the Dirac
mass and `ρ` is a positive constant. Nothing here assumes a positive dimension, a density, a
second moment or full-dimensional ambient support. Pointwise bounds on compact subsets are
stronger than the `L^∞_loc` phrasing of the Blueprint and imply it. No Poincaré, Cheeger,
Dirichlet or KLS statement is asserted here.
-/

noncomputable section
open MeasureTheory Set Topology Filter

namespace FunctionalInequalities

section Representative

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]

namespace KLS

/-- A Borell density representative of the measure `ν` relative to the reference measure `m`:
a Borel, nonnegative, real-valued, upper semicontinuous, log-concave function whose
`m`-density is `ν`. Log-concavity is the pointwise inequality with real powers, so zeros of `ρ`
are allowed and the set `{ρ > 0}` is convex. This is a definition of the representative;
it does not by itself assert existence, positivity or bounds. -/
structure IsBorellDensity (ν m : Measure V) (ρ : V → ℝ) : Prop where
  measurable : Measurable ρ
  nonneg : ∀ x, 0 ≤ ρ x
  upperSemicontinuous : UpperSemicontinuous ρ
  logConcave : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
    ρ x ^ t * ρ y ^ (1 - t) ≤ ρ (t • x + (1 - t) • y)
  withDensity_eq : m.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) = ν

end KLS

namespace KLS.IsBorellDensity

omit [BorelSpace V] in
/-- The positivity set of a Borell density representative is convex. -/
theorem convex_pos {ν m : Measure V} {ρ : V → ℝ} (h : IsBorellDensity ν m ρ) :
    Convex ℝ {y | 0 < ρ y} := by
  intro a ha b hb s u hs hu hsu
  have ha' : 0 < ρ a := ha
  have hb' : 0 < ρ b := hb
  rcases hs.eq_or_lt with rfl | hs'
  · have hu1 : u = 1 := by linarith
    subst hu1
    simpa using hb'
  rcases hu.eq_or_lt with rfl | hu'
  · have hs1 : s = 1 := by linarith
    subst hs1
    simpa using ha'
  have hu_eq : u = 1 - s := by linarith
  have hs1 : s < 1 := by linarith
  have key := h.logConcave a b s hs' hs1
  rw [← hu_eq] at key
  show 0 < ρ (s • a + u • b)
  exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos ha' s) (Real.rpow_pos_of_pos hb' u)) key

omit [BorelSpace V] in
/-- The logarithm of a Borell density representative is concave on the positivity set. -/
theorem concaveOn_log {ν m : Measure V} {ρ : V → ℝ} (h : IsBorellDensity ν m ρ) :
    ConcaveOn ℝ {y | 0 < ρ y} fun y ↦ Real.log (ρ y) := by
  refine ⟨h.convex_pos, ?_⟩
  intro a ha b hb s u hs hu hsu
  have ha' : 0 < ρ a := ha
  have hb' : 0 < ρ b := hb
  rcases hs.eq_or_lt with rfl | hs'
  · have hu1 : u = 1 := by linarith
    subst hu1
    simp
  rcases hu.eq_or_lt with rfl | hu'
  · have hs1 : s = 1 := by linarith
    subst hs1
    simp
  have hu_eq : u = 1 - s := by linarith
  have hs1 : s < 1 := by linarith
  have key := h.logConcave a b s hs' hs1
  rw [← hu_eq] at key
  simp only [smul_eq_mul]
  calc s * Real.log (ρ a) + u * Real.log (ρ b)
      = Real.log (ρ a ^ s * ρ b ^ u) := by
        rw [Real.log_mul (Real.rpow_pos_of_pos ha' s).ne' (Real.rpow_pos_of_pos hb' u).ne',
          Real.log_rpow ha', Real.log_rpow hb']
    _ ≤ Real.log (ρ (s • a + u • b)) :=
        Real.log_le_log (mul_pos (Real.rpow_pos_of_pos ha' s) (Real.rpow_pos_of_pos hb' u)) key

omit [BorelSpace V] in
/-- The measure of the complement of the positivity set vanishes. -/
theorem measure_compl_pos {ν m : Measure V} {ρ : V → ℝ}
    (h : IsBorellDensity ν m ρ) : ν {y | 0 < ρ y}ᶜ = 0 := by
  have hmeas : MeasurableSet {y | 0 < ρ y} := measurableSet_lt measurable_const h.measurable
  rw [← h.withDensity_eq, withDensity_apply _ hmeas.compl]
  rw [setLIntegral_congr_fun hmeas.compl (g := fun _ ↦ 0)]
  · simp
  · intro x hx
    have : ¬ 0 < ρ x := hx
    exact ENNReal.ofReal_eq_zero.mpr (not_lt.mp this)

end KLS.IsBorellDensity

variable [FiniteDimensional ℝ V]

namespace KLS.IsBorellDensity

/-- The interior of the support of a probability law with a Borell density representative lies
inside the interior of the positivity set of that representative. -/
theorem interior_support_subset {ν : ProbabilityMeasure V} {m : Measure V}
    [m.IsAddHaarMeasure] {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) :
    interior (ν : Measure V).support ⊆ interior {y | 0 < ρ y} := by
  set S : Set V := {y | 0 < ρ y} with hS
  have hSconv : Convex ℝ S := h.convex_pos
  have hmeas : MeasurableSet S := measurableSet_lt measurable_const h.measurable
  have hνSc : (ν : Measure V) Sᶜ = 0 := h.measure_compl_pos
  have hint : (interior S).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hspan : affineSpan ℝ S ≠ ⊤ := by
      intro htop
      have := hSconv.interior_nonempty_iff_affineSpan_eq_top.mpr htop
      rw [hemp] at this
      exact Set.not_nonempty_empty this
    have hmS : m (affineSpan ℝ S : Set V) = 0 := Measure.addHaar_affineSubspace m _ hspan
    have hνS : (ν : Measure V) S = 0 := by
      rw [← h.withDensity_eq, withDensity_apply _ hmeas]
      exact setLIntegral_measure_zero _ _ (measure_mono_null (subset_affineSpan ℝ S) hmS)
    have huniv : (ν : Measure V) Set.univ = 0 := by
      rw [← Set.union_compl_self S]
      exact measure_union_null hνS hνSc
    simp at huniv
  have hsupp : (ν : Measure V).support ⊆ closure S := by
    intro y hy
    by_contra hyc
    have hopen : IsOpen (closure S)ᶜ := isClosed_closure.isOpen_compl
    have hnull : (ν : Measure V) (closure S)ᶜ = 0 :=
      measure_mono_null (Set.compl_subset_compl.mpr subset_closure) hνSc
    exact (Measure.notMem_support_iff_exists.mpr ⟨(closure S)ᶜ, hopen.mem_nhds hyc, hnull⟩) hy
  rw [← hSconv.interior_closure_eq_interior_of_nonempty_interior hint]
  exact interior_mono hsupp

/-- A Borell density representative of a probability law is positive at every interior point of
the topological support. -/
theorem pos_of_mem_interior_support {ν : ProbabilityMeasure V} {m : Measure V}
    [m.IsAddHaarMeasure] {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) {x : V}
    (hx : x ∈ interior (ν : Measure V).support) : 0 < ρ x := by
  have hxS : x ∈ {y | 0 < ρ y} := interior_subset (h.interior_support_subset hx)
  exact hxS

omit [BorelSpace V] in
/-- A Borell density representative is continuous on the interior of its positivity set: the
logarithm is a finite concave function there, hence continuous, and `ρ = exp ∘ log ρ`. -/
theorem continuousOn_interior_pos {ν m : Measure V} {ρ : V → ℝ}
    (h : IsBorellDensity ν m ρ) : ContinuousOn ρ (interior {y | 0 < ρ y}) := by
  have hlog := h.concaveOn_log.continuousOn_interior
  refine (Real.continuous_exp.comp_continuousOn hlog).congr ?_
  intro y hy
  have hyS : y ∈ {y | 0 < ρ y} := interior_subset hy
  have hy' : 0 < ρ y := hyS
  simp [Function.comp, Real.exp_log hy']

/-- A Borell density representative of a probability law is continuous on the interior of the
support. This is the continuity used by the downstream covariance-core and relative-perimeter
arguments; it is not continuity on all of `V`, where `ρ` is only upper semicontinuous. -/
theorem continuousOn_interior_support {ν : ProbabilityMeasure V} {m : Measure V}
    [m.IsAddHaarMeasure] {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) :
    ContinuousOn ρ (interior (ν : Measure V).support) :=
  h.continuousOn_interior_pos.mono h.interior_support_subset

/-- On every compact subset of the interior of the support, a Borell density representative is
bounded above and bounded below by a positive constant. Upper semicontinuity gives the upper
bound; continuity of the concave logarithm on the open interior gives the lower bound. This is
the pointwise form of `ρ, ρ⁻¹ ∈ L^∞_loc(Ω)`. -/
theorem exists_bounds_of_isCompact {ν : ProbabilityMeasure V} {m : Measure V}
    [m.IsAddHaarMeasure] {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) {K : Set V}
    (hK : IsCompact K) (hKΩ : K ⊆ interior (ν : Measure V).support) :
    ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ K, a ≤ ρ x ∧ ρ x ≤ b := by
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · exact ⟨1, 0, one_pos, by simp [hK0]⟩
  obtain ⟨b, hb⟩ := (h.upperSemicontinuous.upperSemicontinuousOn K).bddAbove_of_isCompact hK
  obtain ⟨x₀, hx₀K, hmin⟩ :=
    hK.exists_isMinOn hKne (h.continuousOn_interior_support.mono hKΩ)
  refine ⟨ρ x₀, b, h.pos_of_mem_interior_support (hKΩ hx₀K), fun x hx ↦ ⟨?_, hb ⟨x, hx, rfl⟩⟩⟩
  exact (isMinOn_iff.mp hmin) x hx

end KLS.IsBorellDensity

end Representative

section Moments

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]

namespace KLS.BorelLogConcave

omit [FiniteDimensional ℝ V] in
/-- Borell's tail lemma in the form needed here: once a ball of radius `R` carries mass at
least `3/4`, the mass outside radius `k R` decays geometrically in `k`. The bound is stated
for every `k`, the cases `k = 0, 1` being trivial. -/
theorem measure_norm_ge_le {ν : ProbabilityMeasure V} (hν : BorelLogConcave ν)
    {R : ℝ} (hball : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R)) (k : ℕ) :
    (ν : Measure V) {v | (k : ℝ) * R ≤ ‖v‖} ≤ ENNReal.ofReal ((3 : ℝ) ^ ((1 - (k : ℝ)) / 2)) := by
  by_cases hk : k < 2
  · have hk' : (k : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hk
    calc (ν : Measure V) {v | (k : ℝ) * R ≤ ‖v‖} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ ((1 - (k : ℝ)) / 2)) :=
        ENNReal.one_le_ofReal.mpr (Real.one_le_rpow (by norm_num) (by linarith))
  push Not at hk
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set t : ℝ := 2 / ((k : ℝ) + 1) with ht_def
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have ht : 0 < t := by positivity
  have ht1 : t < 1 := by
    rw [ht_def, div_lt_one hk1]; linarith
  have ht_eq : t * ((k : ℝ) + 1) = 2 := by
    rw [ht_def]; field_simp
  set B₀ : Set V := {v | (k : ℝ) * R ≤ ‖v‖} with hB₀_def
  have hB₀ : MeasurableSet B₀ := (isClosed_le continuous_const continuous_norm).measurableSet
  have hB₁ : MeasurableSet (Metric.ball (0 : V) R) := measurableSet_ball
  have key := hν B₀ (Metric.ball 0 R) hB₀ hB₁ t ht ht1
  have hsub : {z | ∃ x ∈ B₀, ∃ y ∈ Metric.ball (0 : V) R, z = t • x + (1 - t) • y} ⊆
      (Metric.closedBall (0 : V) R)ᶜ := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    have hx' : (k : ℝ) * R ≤ ‖x‖ := hx
    have hy' : ‖y‖ < R := mem_ball_zero_iff.mp hy
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
    have h1 := norm_le_add_norm_add (t • x) ((1 - t) • y)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht,
      abs_of_pos (sub_pos.mpr ht1)] at h1
    have h2 : t * ((k : ℝ) * R) ≤ t * ‖x‖ := mul_le_mul_of_nonneg_left hx' ht.le
    have h3 : (1 - t) * ‖y‖ < (1 - t) * R := mul_lt_mul_of_pos_left hy' (sub_pos.mpr ht1)
    have h4 : t * ((k : ℝ) * R) - (1 - t) * R = R := by linear_combination R * ht_eq
    linarith
  have hinner : innerMeasure (ν : Measure V)
      {z | ∃ x ∈ B₀, ∃ y ∈ Metric.ball (0 : V) R, z = t • x + (1 - t) • y} ≤
        (ν : Measure V) (Metric.closedBall (0 : V) R)ᶜ :=
    (innerMeasure_mono _ hsub).trans (innerMeasure_le _ _)
  have hcompl : (ν : Measure V) (Metric.closedBall (0 : V) R)ᶜ ≤ ENNReal.ofReal (1 / 4) := by
    calc (ν : Measure V) (Metric.closedBall (0 : V) R)ᶜ
        ≤ (ν : Measure V) (Metric.ball (0 : V) R)ᶜ :=
          measure_mono (Set.compl_subset_compl.mpr Metric.ball_subset_closedBall)
      _ = 1 - (ν : Measure V) (Metric.ball (0 : V) R) := prob_compl_eq_one_sub hB₁
      _ ≤ 1 - ENNReal.ofReal (3 / 4) := tsub_le_tsub_left hball 1
      _ = ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
  have h34 : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R) ^ (1 - t) := by
    calc ENNReal.ofReal (3 / 4) = ENNReal.ofReal (3 / 4) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ ≤ ENNReal.ofReal (3 / 4) ^ (1 - t) :=
          ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.ofReal_le_one.mpr (by norm_num))
            (by linarith)
      _ ≤ (ν : Measure V) (Metric.ball (0 : V) R) ^ (1 - t) :=
          ENNReal.rpow_le_rpow hball (by linarith)
  have hmain : (ν : Measure V) B₀ ^ t * ENNReal.ofReal (3 / 4) ≤ ENNReal.ofReal (1 / 4) :=
    calc (ν : Measure V) B₀ ^ t * ENNReal.ofReal (3 / 4)
        ≤ (ν : Measure V) B₀ ^ t * (ν : Measure V) (Metric.ball (0 : V) R) ^ (1 - t) :=
          mul_le_mul' le_rfl h34
      _ ≤ _ := key
      _ ≤ _ := hinner
      _ ≤ _ := hcompl
  have hpow : (ν : Measure V) B₀ ^ t ≤ ENNReal.ofReal (1 / 3) := by
    have h34ne : ENNReal.ofReal (3 / 4) ≠ 0 := by simp
    have h34top : ENNReal.ofReal (3 / 4) ≠ ⊤ := ENNReal.ofReal_ne_top
    have := (ENNReal.le_div_iff_mul_le (Or.inl h34ne) (Or.inl h34top)).mpr hmain
    rwa [← ENNReal.ofReal_div_of_pos (by norm_num), show (1 / 4 : ℝ) / (3 / 4) = 1 / 3 by norm_num]
      at this
  have hroot : (ν : Measure V) B₀ ≤ ENNReal.ofReal (1 / 3) ^ (((k : ℝ) + 1) / 2) := by
    have h1t : 1 / t = ((k : ℝ) + 1) / 2 := by rw [ht_def, one_div_div]
    calc (ν : Measure V) B₀ = ((ν : Measure V) B₀ ^ t) ^ (1 / t) := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel ht.ne', ENNReal.rpow_one]
      _ ≤ ENNReal.ofReal (1 / 3) ^ (1 / t) := ENNReal.rpow_le_rpow hpow (by positivity)
      _ = _ := by rw [h1t]
  refine hroot.trans ?_
  rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hexp : ((1 : ℝ) / 3) ^ (((k : ℝ) + 1) / 2) = (3 : ℝ) ^ (-(((k : ℝ) + 1) / 2)) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  rw [hexp]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

omit [FiniteDimensional ℝ V] in
/-- A Borel log-concave probability law on a finite-dimensional space has an exponential
moment. The radius is chosen from the exhaustion by balls, the tail from Borell's lemma, and
the integral is dominated by a geometric series. -/
theorem exists_integrable_exp_norm {ν : ProbabilityMeasure V}
    (hν : BorelLogConcave ν) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun v ↦ Real.exp (t * ‖v‖)) (ν : Measure V) := by
  -- a ball of integer radius carrying mass at least 3/4
  have hmono : Monotone fun n : ℕ ↦ Metric.ball (0 : V) n := fun i j hij ↦
    Metric.ball_subset_ball (by exact_mod_cast hij)
  have htend := tendsto_measure_iUnion_atTop (μ := (ν : Measure V)) hmono
  rw [Metric.iUnion_ball_nat, measure_univ] at htend
  obtain ⟨n, hn1, hball⟩ :=
    ((eventually_ge_atTop 1).and
      (htend.eventually_const_le (ENNReal.ofReal_lt_one.mpr (by norm_num : (3 / 4 : ℝ) < 1)))).exists
  set R : ℝ := (n : ℝ) with hR_def
  have hR : 0 < R := by rw [hR_def]; exact Nat.cast_pos.mpr hn1
  have hball' : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R) := hball
  have tail := hν.measure_norm_ge_le hball'
  -- the rate and the dominating series
  set t₀ : ℝ := Real.log 3 / (4 * R) with ht₀_def
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ht₀ : 0 < t₀ := by positivity
  set c : ℕ → ℝ := fun k ↦ Real.exp (t₀ * ((k : ℝ) + 1) * R) with hc_def
  set b : ℕ → ℝ := fun k ↦ (3 : ℝ) ^ ((1 - (k : ℝ)) / 2) with hb_def
  set A : ℕ → Set V := fun k ↦ {v | (k : ℝ) * R ≤ ‖v‖} with hA_def
  have hA : ∀ k, MeasurableSet (A k) := fun k ↦
    (isClosed_le continuous_const continuous_norm).measurableSet
  set f : ℕ → V → ENNReal := fun k ↦ (A k).indicator fun _ ↦ ENNReal.ofReal (c k) with hf_def
  have hc_pos : ∀ k, 0 < c k := fun k ↦ Real.exp_pos _
  have hb_pos : ∀ k, 0 < b k := fun k ↦ Real.rpow_pos_of_pos (by norm_num) _
  -- pointwise domination
  have hpt : ∀ v : V, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ≤ ∑' k, f k v := by
    intro v
    set n := ⌊‖v‖ / R⌋₊ with hn_def
    have hn1 : (n : ℝ) ≤ ‖v‖ / R := Nat.floor_le (div_nonneg (norm_nonneg _) hR.le)
    have hn2 : ‖v‖ / R < n + 1 := Nat.lt_floor_add_one _
    have hmem : v ∈ A n := by
      show (n : ℝ) * R ≤ ‖v‖
      exact (le_div_iff₀ hR).mp hn1
    have hlt : ‖v‖ < ((n : ℝ) + 1) * R := (div_lt_iff₀ hR).mp hn2
    calc ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ≤ ENNReal.ofReal (c n) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hlt.le ht₀.le
      _ = f n v := by simp [hf_def, Set.indicator_of_mem hmem]
      _ ≤ ∑' k, f k v := ENNReal.le_tsum n
  -- the series
  have hcb : ∀ k, c k * b k = (3 : ℝ) ^ ((3 : ℝ) / 4) * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
    intro k
    have hc : c k = (3 : ℝ) ^ (((k : ℝ) + 1) / 4) := by
      rw [hc_def, Real.rpow_def_of_pos (by norm_num)]
      rw [ht₀_def]
      field_simp
    rw [hc, hb_def]
    simp only
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hq1 : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hq0 : 0 ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hsum : Summable fun k ↦ c k * b k :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _).congr fun k ↦ (hcb k).symm
  -- the integral bound
  have hbound : ∫⁻ v, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ∂(ν : Measure V) < ⊤ := by
    calc ∫⁻ v, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ∂(ν : Measure V)
        ≤ ∫⁻ v, ∑' k, f k v ∂(ν : Measure V) := lintegral_mono hpt
      _ = ∑' k, ∫⁻ v, f k v ∂(ν : Measure V) :=
          lintegral_tsum fun k ↦ (measurable_const.indicator (hA k)).aemeasurable
      _ = ∑' k, ENNReal.ofReal (c k) * (ν : Measure V) (A k) := by
          congr 1; ext k; exact lintegral_indicator_const (hA k) _
      _ ≤ ∑' k, ENNReal.ofReal (c k) * ENNReal.ofReal (b k) :=
          ENNReal.tsum_le_tsum fun k ↦ mul_le_mul' le_rfl (tail k)
      _ = ∑' k, ENNReal.ofReal (c k * b k) := by
          congr 1; ext k; rw [ENNReal.ofReal_mul (hc_pos k).le]
      _ = ENNReal.ofReal (∑' k, c k * b k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (mul_pos (hc_pos k) (hb_pos k)).le) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨t₀, ht₀, ?_, ?_⟩
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable
      |>.aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun v ↦ (Real.exp_pos _).le)]
    exact hbound

end KLS.BorelLogConcave

namespace Probability

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- An exponential moment gives finite moments of every order. -/
theorem integrable_norm_pow_of_integrable_exp_norm {ν : Measure V} [IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 < t) (hint : Integrable (fun v ↦ Real.exp (t * ‖v‖)) ν) (p : ℕ) :
    Integrable (fun v ↦ ‖v‖ ^ p) ν := by
  have hneg : Integrable (fun v ↦ Real.exp (-t * ‖v‖)) ν := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun v ↦ ?_)
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg v])
  have := ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul ht.ne' hint hneg p
  simpa [abs_norm] using this

end Probability

end Moments

section Construction

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V]

namespace KLS.BorellRepresentation

/-- The radii `1/(n+1)` along which ball ratios are read. -/
def radius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- The radii are positive. -/
theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

/-- The radii tend to zero from the right. -/
theorem tendsto_radius : Tendsto radius atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n ↦ Set.mem_Ioi.mpr (radius_pos n)⟩

/-- Some radius lies below any positive threshold. -/
theorem exists_radius_lt {ε : ℝ} (hε : 0 < ε) : ∃ n, radius n < ε := exists_nat_one_div_lt hε

/-- Halving a radius stays in the sequence: `radius (2n+1) = radius n / 2`. -/
theorem radius_two_mul_add_one (n : ℕ) : radius (2 * n + 1) = radius n / 2 := by
  unfold radius
  push_cast
  field_simp
  ring

variable (ν m : Measure V)

/-- Mass of the closed ball around `x` of radius `radius n` divided by the Haar mass of the
ball of the same radius. -/
def ballRatio (n : ℕ) (x : V) : ENNReal :=
  ν (Metric.closedBall x (radius n)) / m (Metric.closedBall (0 : V) (radius n))

/-- The lower density along the sequence of radii. It is log-concave and equals the
Radon--Nikodym derivative almost everywhere. -/
def lowerDensity (x : V) : ENNReal := liminf (fun n ↦ ballRatio ν m n x) atTop

/-- The upper semicontinuous envelope of the lower density. -/
def envelope (x : V) : ENNReal :=
  ⨅ n : ℕ, ⨆ y ∈ Metric.ball x (radius n), lowerDensity ν m y

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The mass of the closed ball of fixed radius depends measurably on the center. -/
theorem measurable_measure_closedBall [SFinite ν] (r : ℝ) :
    Measurable fun x : V ↦ ν (Metric.closedBall x r) := by
  have hs : MeasurableSet {p : V × V | dist p.2 p.1 ≤ r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  exact measurable_measure_prodMk_left hs

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Ball ratios are measurable in the center. -/
theorem measurable_ballRatio [SFinite ν] (n : ℕ) : Measurable (ballRatio ν m n) :=
  (measurable_measure_closedBall ν _).div_const _

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The lower density is measurable, as a countable `liminf` of measurable functions. -/
theorem measurable_lowerDensity [SFinite ν] : Measurable (lowerDensity ν m) :=
  Measurable.liminf (measurable_ballRatio ν m)

/-- Positive real powers commute with suprema in `ENNReal`. -/
private theorem rpow_iSup {I : Sort*} (f : I → ENNReal) {t : ℝ} (ht : 0 < t) :
    (⨆ i, f i) ^ t = ⨆ i, f i ^ t :=
  (ENNReal.orderIsoRpow t ht).map_iSup f

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- A uniform eventual small-ball bound bounds the lower density everywhere. -/
theorem lowerDensity_le (C : ENNReal)
    (hC : ∀ x, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ν (Metric.closedBall x r) ≤ C * m (Metric.closedBall (0 : V) r)) (x : V) :
    lowerDensity ν m x ≤ C := by
  refine liminf_le_of_frequently_le' ((tendsto_radius.eventually (hC x)).mono ?_).frequently
  intro n hn
  exact ENNReal.div_le_of_le_mul hn

/-- Besicovitch differentiation: the lower density is the Radon--Nikodym derivative almost
everywhere with respect to the Haar reference measure. -/
theorem lowerDensity_ae_eq [IsFiniteMeasure ν] [m.IsAddHaarMeasure] :
    lowerDensity ν m =ᵐ[m] ν.rnDeriv m := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv ν m] with x hx
  have hx' : Tendsto (fun n ↦ ballRatio ν m n x) atTop (𝓝 (ν.rnDeriv m x)) := by
    refine (hx.comp tendsto_radius).congr fun n ↦ ?_
    simp only [Function.comp, ballRatio, Measure.addHaar_closedBall_center m x]
  exact hx'.liminf_eq

omit [BorelSpace V] [SecondCountableTopology V] in
/-- Equal-radius ball ratios inherit the log-concavity inequality of the law. -/
theorem ballRatio_logConcave {ν : ProbabilityMeasure V} (hlc : LogConcave ν) [m.IsAddHaarMeasure]
    (n : ℕ) (x y : V) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ballRatio ν m n x ^ t * ballRatio ν m n y ^ (1 - t) ≤
      ballRatio ν m n (t • x + (1 - t) • y) := by
  set D := m (Metric.closedBall (0 : V) (radius n)) with hD_def
  have hD0 : D ≠ 0 := (Metric.measure_closedBall_pos m _ (radius_pos n)).ne'
  have hDt : D ≠ ⊤ := measure_closedBall_lt_top.ne
  have ht1' : 0 ≤ 1 - t := sub_nonneg.mpr ht1.le
  have key := hlc.closedBall_mul_le x y (radius n) t ht ht1
  have hDt0 : D ^ t ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hD0) hDt).ne'
  have hDt1 : D ^ (1 - t) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hD0) hDt).ne'
  have hDtt : D ^ t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht.le hDt
  have hDtt1 : D ^ (1 - t) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht1' hDt
  have hD : D ^ t * D ^ (1 - t) = D := by
    rw [← ENNReal.rpow_add _ _ hD0 hDt]; simp
  unfold ballRatio
  rw [ENNReal.div_rpow_of_nonneg _ _ ht.le, ENNReal.div_rpow_of_nonneg _ _ ht1']
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  calc (ν : Measure V) (Metric.closedBall x (radius n)) ^ t * (D ^ t)⁻¹ *
        ((ν : Measure V) (Metric.closedBall y (radius n)) ^ (1 - t) * (D ^ (1 - t))⁻¹)
      = ((ν : Measure V) (Metric.closedBall x (radius n)) ^ t *
          (ν : Measure V) (Metric.closedBall y (radius n)) ^ (1 - t)) *
          ((D ^ t)⁻¹ * (D ^ (1 - t))⁻¹) := by ring
    _ = ((ν : Measure V) (Metric.closedBall x (radius n)) ^ t *
          (ν : Measure V) (Metric.closedBall y (radius n)) ^ (1 - t)) *
          (D ^ t * D ^ (1 - t))⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl hDt0) (Or.inl hDtt)]
    _ = ((ν : Measure V) (Metric.closedBall x (radius n)) ^ t *
          (ν : Measure V) (Metric.closedBall y (radius n)) ^ (1 - t)) * D⁻¹ := by rw [hD]
    _ ≤ (ν : Measure V) (Metric.closedBall (t • x + (1 - t) • y) (radius n)) * D⁻¹ :=
        mul_le_mul' key le_rfl

omit [BorelSpace V] [SecondCountableTopology V] in
/-- The lower density of a log-concave law is log-concave. -/
theorem lowerDensity_logConcave {ν : ProbabilityMeasure V} (hlc : LogConcave ν)
    [m.IsAddHaarMeasure] (x y : V) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    lowerDensity ν m x ^ t * lowerDensity ν m y ^ (1 - t) ≤
      lowerDensity ν m (t • x + (1 - t) • y) := by
  have ht1' : 0 < 1 - t := sub_pos.mpr ht1
  unfold lowerDensity
  simp only [liminf_eq_iSup_iInf_of_nat]
  rw [rpow_iSup _ ht, rpow_iSup _ ht1', ENNReal.iSup_mul]
  refine iSup_le fun i ↦ ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j ↦ ?_
  refine le_iSup_of_le (max i j) ?_
  refine le_iInf₂ fun k hk ↦ ?_
  calc (⨅ l ≥ i, ballRatio ν m l x) ^ t * (⨅ l ≥ j, ballRatio ν m l y) ^ (1 - t)
      ≤ ballRatio ν m k x ^ t * ballRatio ν m k y ^ (1 - t) :=
        mul_le_mul'
          (ENNReal.rpow_le_rpow (iInf₂_le k (le_trans (le_max_left i j) hk)) ht.le)
          (ENNReal.rpow_le_rpow (iInf₂_le k (le_trans (le_max_right i j) hk)) ht1'.le)
    _ ≤ _ := ballRatio_logConcave m hlc k x y ht ht1

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- The envelope dominates the lower density. -/
theorem le_envelope (x : V) : lowerDensity ν m x ≤ envelope ν m x :=
  le_iInf fun n ↦ le_iSup₂ (f := fun y (_ : y ∈ Metric.ball x (radius n)) ↦ lowerDensity ν m y)
    x (Metric.mem_ball_self (radius_pos n))

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- A uniform bound on the lower density bounds the envelope. -/
theorem envelope_le {C : ENNReal} (h : ∀ y, lowerDensity ν m y ≤ C) (x : V) :
    envelope ν m x ≤ C :=
  (iInf_le _ 0).trans (iSup₂_le fun y _ ↦ h y)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- The envelope is upper semicontinuous. -/
theorem upperSemicontinuous_envelope : UpperSemicontinuous (envelope ν m) := by
  intro x c hc
  obtain ⟨n, hn⟩ := iInf_lt_iff.mp hc
  have hball : Metric.ball x (radius n / 2) ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (by have := radius_pos n; positivity)
  filter_upwards [hball] with x' hx'
  calc envelope ν m x' ≤ ⨆ y ∈ Metric.ball x' (radius (2 * n + 1)), lowerDensity ν m y :=
        iInf_le _ _
    _ ≤ ⨆ y ∈ Metric.ball x (radius n), lowerDensity ν m y := by
        refine iSup₂_le fun y hy ↦ le_iSup₂_of_le y ?_ le_rfl
        rw [radius_two_mul_add_one] at hy
        rw [Metric.mem_ball] at hy hx' ⊢
        calc dist y x ≤ dist y x' + dist x' x := dist_triangle _ _ _
          _ < radius n / 2 + radius n / 2 := add_lt_add hy hx'
          _ = radius n := by ring
    _ < c := hn

omit [FiniteDimensional ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- The envelope of a log-concave lower density is log-concave. -/
theorem envelope_logConcave
    (hψ : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      lowerDensity ν m x ^ t * lowerDensity ν m y ^ (1 - t) ≤
        lowerDensity ν m (t • x + (1 - t) • y))
    (x y : V) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    envelope ν m x ^ t * envelope ν m y ^ (1 - t) ≤ envelope ν m (t • x + (1 - t) • y) := by
  have ht1' : 0 < 1 - t := sub_pos.mpr ht1
  refine le_iInf fun n ↦ ?_
  calc envelope ν m x ^ t * envelope ν m y ^ (1 - t)
      ≤ (⨆ x' ∈ Metric.ball x (radius n), lowerDensity ν m x') ^ t *
          (⨆ y' ∈ Metric.ball y (radius n), lowerDensity ν m y') ^ (1 - t) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (iInf_le _ n) ht.le)
          (ENNReal.rpow_le_rpow (iInf_le _ n) ht1'.le)
    _ ≤ ⨆ z ∈ Metric.ball (t • x + (1 - t) • y) (radius n), lowerDensity ν m z := by
        rw [rpow_iSup _ ht, rpow_iSup _ ht1']
        simp only [rpow_iSup _ ht, rpow_iSup _ ht1', ENNReal.iSup_mul, ENNReal.mul_iSup]
        refine iSup₂_le fun y' hy' ↦ iSup₂_le fun x' hx' ↦ ?_
        refine le_iSup₂_of_le (t • x' + (1 - t) • y') ?_ (hψ x' y' t ht ht1)
        rw [Metric.mem_ball, dist_eq_norm] at hx' hy' ⊢
        have heq : t • x' + (1 - t) • y' - (t • x + (1 - t) • y) =
            t • (x' - x) + (1 - t) • (y' - y) := by simp only [smul_sub]; abel
        rw [heq]
        calc ‖t • (x' - x) + (1 - t) • (y' - y)‖
            ≤ ‖t • (x' - x)‖ + ‖(1 - t) • (y' - y)‖ := norm_add_le _ _
          _ = t * ‖x' - x‖ + (1 - t) * ‖y' - y‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht,
                abs_of_pos ht1']
          _ < t * radius n + (1 - t) * radius n :=
              add_lt_add (mul_lt_mul_of_pos_left hx' ht) (mul_lt_mul_of_pos_left hy' ht1')
          _ = radius n := by ring

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The positivity set of a finite log-concave `ENNReal` function is convex. -/
theorem convex_pos_of_logConcave {ψ : V → ENNReal} (hfin : ∀ x, ψ x ≠ ⊤)
    (hψ : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 → ψ x ^ t * ψ y ^ (1 - t) ≤ ψ (t • x + (1 - t) • y)) :
    Convex ℝ {x | 0 < ψ x} := by
  intro a ha b hb s u hs hu hsu
  have ha' : 0 < ψ a := ha
  have hb' : 0 < ψ b := hb
  rcases hs.eq_or_lt with rfl | hs'
  · have hu1 : u = 1 := by linarith
    subst hu1
    simpa using hb'
  rcases hu.eq_or_lt with rfl | hu'
  · have hs1 : s = 1 := by linarith
    subst hs1
    simpa using ha'
  have hu_eq : u = 1 - s := by linarith
  have hs1 : s < 1 := by linarith
  have key := hψ a b s hs' hs1
  rw [← hu_eq] at key
  show 0 < ψ (s • a + u • b)
  exact lt_of_lt_of_le
    (ENNReal.mul_pos (ENNReal.rpow_pos ha' (hfin a)).ne' (ENNReal.rpow_pos hb' (hfin b)).ne') key

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- On the positivity set, the logarithm of the real part of a finite log-concave `ENNReal`
function is concave. -/
theorem concaveOn_log_toReal_of_logConcave {ψ : V → ENNReal} (hfin : ∀ x, ψ x ≠ ⊤)
    (hψ : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 → ψ x ^ t * ψ y ^ (1 - t) ≤ ψ (t • x + (1 - t) • y)) :
    ConcaveOn ℝ {x | 0 < ψ x} fun x ↦ Real.log (ψ x).toReal := by
  refine ⟨convex_pos_of_logConcave hfin hψ, ?_⟩
  intro a ha b hb s u hs hu hsu
  have ha' : 0 < (ψ a).toReal := ENNReal.toReal_pos (ne_of_gt ha) (hfin a)
  have hb' : 0 < (ψ b).toReal := ENNReal.toReal_pos (ne_of_gt hb) (hfin b)
  rcases hs.eq_or_lt with rfl | hs'
  · have hu1 : u = 1 := by linarith
    subst hu1
    simp
  rcases hu.eq_or_lt with rfl | hu'
  · have hs1 : s = 1 := by linarith
    subst hs1
    simp
  have hu_eq : u = 1 - s := by linarith
  have hs1 : s < 1 := by linarith
  have key := hψ a b s hs' hs1
  rw [← hu_eq] at key
  have key' : (ψ a).toReal ^ s * (ψ b).toReal ^ u ≤ (ψ (s • a + u • b)).toReal := by
    have := ENNReal.toReal_mono (hfin _) key
    rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at this
  simp only [smul_eq_mul]
  calc s * Real.log (ψ a).toReal + u * Real.log (ψ b).toReal
      = Real.log ((ψ a).toReal ^ s * (ψ b).toReal ^ u) := by
        rw [Real.log_mul (Real.rpow_pos_of_pos ha' s).ne' (Real.rpow_pos_of_pos hb' u).ne',
          Real.log_rpow ha', Real.log_rpow hb']
    _ ≤ Real.log (ψ (s • a + u • b)).toReal :=
        Real.log_le_log (mul_pos (Real.rpow_pos_of_pos ha' s) (Real.rpow_pos_of_pos hb' u)) key'

omit [SecondCountableTopology V] in
/-- The envelope agrees with a bounded log-concave lower density off the Haar-null frontier of
the positivity set, hence almost everywhere. -/
theorem envelope_ae_eq [m.IsAddHaarMeasure] {C : ENNReal} (hC : C ≠ ⊤)
    (hle : ∀ x, lowerDensity ν m x ≤ C)
    (hψ : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      lowerDensity ν m x ^ t * lowerDensity ν m y ^ (1 - t) ≤
        lowerDensity ν m (t • x + (1 - t) • y)) :
    envelope ν m =ᵐ[m] lowerDensity ν m := by
  set ψ := lowerDensity ν m with hψ_def
  have hfin : ∀ x, ψ x ≠ ⊤ := fun x ↦ ((hle x).trans_lt hC.lt_top).ne
  set P : Set V := {x | 0 < ψ x} with hP_def
  have hPconv : Convex ℝ P := convex_pos_of_logConcave hfin hψ
  have hfront : m (frontier P) = 0 := hPconv.addHaar_frontier m
  -- continuity of the real part on the interior of `P`
  have hcont : ContinuousOn (fun x ↦ (ψ x).toReal) (interior P) := by
    have hlog := (concaveOn_log_toReal_of_logConcave hfin hψ).continuousOn_interior
    refine (Real.continuous_exp.comp_continuousOn hlog).congr ?_
    intro y hy
    have hyP : y ∈ P := interior_subset hy
    have hy' : 0 < ψ y := hyP
    simp [Function.comp, Real.exp_log (ENNReal.toReal_pos hy'.ne' (hfin y))]
  refine measure_mono_null ?_ hfront
  intro x hx
  by_contra hxf
  apply hx
  show envelope ν m x = ψ x
  by_cases hxc : x ∈ closure P
  · have hxi : x ∈ interior P := by
      by_contra hxi
      exact hxf ⟨hxc, hxi⟩
    refine le_antisymm ?_ (le_envelope ν m x)
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hcC : c < C := lt_of_lt_of_le hc2 (envelope_le ν m hle x)
    have hcfin : c ≠ ⊤ := (lt_of_lt_of_le hcC le_top).ne
    have hxcont : ContinuousAt (fun x ↦ (ψ x).toReal) x :=
      hcont.continuousAt (isOpen_interior.mem_nhds hxi)
    have hlt' : (ψ x).toReal < c.toReal := (ENNReal.toReal_lt_toReal (hfin x) hcfin).mpr hc1
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hxcont.eventually (gt_mem_nhds hlt'))
    obtain ⟨n, hn⟩ := exists_radius_lt hε
    have hS : (⨆ y ∈ Metric.ball x (radius n), ψ y) ≤ c := by
      refine iSup₂_le fun y hy ↦ ?_
      have hy' : dist y x < ε := lt_trans (Metric.mem_ball.mp hy) hn
      exact ((ENNReal.toReal_lt_toReal (hfin y) hcfin).mp (hball hy')).le
    exact absurd ((iInf_le _ n).trans hS) (not_le.mpr hc2)
  · have hopen : IsOpen (closure P)ᶜ := isClosed_closure.isOpen_compl
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hxc
    obtain ⟨n, hn⟩ := exists_radius_lt hε
    have hS : (⨆ y ∈ Metric.ball x (radius n), ψ y) = 0 := by
      refine le_antisymm (iSup₂_le fun y hy ↦ ?_) bot_le
      have hyc : y ∈ (closure P)ᶜ := hball (Metric.ball_subset_ball hn.le hy)
      have hyP : y ∉ P := fun h ↦ hyc (subset_closure h)
      exact not_lt.mp hyP
    have hx0 : ψ x = 0 :=
      le_antisymm (not_lt.mp fun h ↦ hxc (subset_closure h)) bot_le
    refine le_antisymm ?_ (le_envelope ν m x)
    rw [hx0]
    exact (iInf_le _ n).trans hS.le

end KLS.BorellRepresentation

namespace KLS.LogConcave

open BorellRepresentation in

/-- Existence of a Borell density representative for a compact-set log-concave probability law
with full-dimensional support, relative to any additive Haar measure. -/
theorem exists_isBorellDensity_of_interior_support_nonempty {ν : ProbabilityMeasure V}
    (hlc : LogConcave ν) (m : Measure V) [m.IsAddHaarMeasure]
    (hint : (interior (ν : Measure V).support).Nonempty) (hac : (ν : Measure V) ≪ m) :
    ∃ ρ : V → ℝ, IsBorellDensity (ν : Measure V) m ρ := by
  obtain ⟨C, hC⟩ := hlc.exists_eventually_closedBall_le m hint
  have hψC : ∀ x, lowerDensity (ν : Measure V) m x ≤ C := lowerDensity_le _ m C hC
  have hψlc : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      lowerDensity (ν : Measure V) m x ^ t * lowerDensity (ν : Measure V) m y ^ (1 - t) ≤
        lowerDensity (ν : Measure V) m (t • x + (1 - t) • y) :=
    fun x y t ht ht1 ↦ lowerDensity_logConcave m hlc x y ht ht1
  have hEC : ∀ x, envelope (ν : Measure V) m x ≤ C := envelope_le _ m hψC
  have hEfin : ∀ x, envelope (ν : Measure V) m x ≠ ⊤ :=
    fun x ↦ ((hEC x).trans_lt ENNReal.coe_lt_top).ne
  have hEusc : UpperSemicontinuous (envelope (ν : Measure V) m) := upperSemicontinuous_envelope _ m
  have hElc := envelope_logConcave (ν : Measure V) m hψlc
  have hEae : envelope (ν : Measure V) m =ᵐ[m] lowerDensity (ν : Measure V) m :=
    envelope_ae_eq _ m ENNReal.coe_ne_top hψC hψlc
  have hψae : lowerDensity (ν : Measure V) m =ᵐ[m] (ν : Measure V).rnDeriv m :=
    lowerDensity_ae_eq _ m
  refine ⟨fun x ↦ (envelope (ν : Measure V) m x).toReal, hEusc.measurable.ennreal_toReal,
    fun x ↦ ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · intro x c hc
    have hlt : envelope (ν : Measure V) m x < ENNReal.ofReal c :=
      (ENNReal.lt_ofReal_iff_toReal_lt (hEfin x)).mpr hc
    filter_upwards [hEusc x _ hlt] with y hy
    exact ENNReal.toReal_lt_of_lt_ofReal hy
  · intro x y t ht ht1
    have h := hElc x y ht ht1
    have := ENNReal.toReal_mono (hEfin _) h
    rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at this
  · calc m.withDensity (fun x ↦ ENNReal.ofReal (envelope (ν : Measure V) m x).toReal)
        = m.withDensity (envelope (ν : Measure V) m) := by
          congr 1; ext x; exact ENNReal.ofReal_toReal (hEfin x)
      _ = m.withDensity (lowerDensity (ν : Measure V) m) := withDensity_congr_ae hEae
      _ = m.withDensity ((ν : Measure V).rnDeriv m) := withDensity_congr_ae hψae
      _ = ν := Measure.withDensity_rnDeriv_eq _ _ hac

end KLS.LogConcave

end Construction

section Intrinsic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]

namespace KLS.LogConcave

omit [CompleteSpace F] in
/-- The support of the intrinsic law is already its own closed convex hull. Hence the interior
of the closed convex hull of the support, as written in the Blueprint, is `interior ν.support`. -/
theorem closure_convexHull_intrinsic_support {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) :
    closure (convexHull ℝ (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction).support) =
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction).support := by
  rw [hμ.intrinsicMeasure.convex_support.convexHull_eq, Measure.isClosed_support.closure_eq]

omit [CompleteSpace F] in
/-- The intrinsic law gives zero mass to the complement of the interior of its support. This is
the `ν(V ∖ Ω) = 0` clause; it follows from the proved null-frontier result. -/
theorem intrinsic_interior_support_compl {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) :
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)
      (interior (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction).support)ᶜ = 0 := by
  set ν : Measure (Probability.affineSupport μ).direction :=
    (Probability.intrinsicMeasure μ).toMeasure
  have hsub : (interior ν.support)ᶜ ⊆ ν.supportᶜ ∪ frontier ν.support := by
    intro x hx
    by_cases hS : x ∈ ν.support
    · exact Or.inr ⟨subset_closure hS, hx⟩
    · exact Or.inl hS
  exact measure_mono_null hsub
    (measure_union_null Measure.measure_compl_support hμ.intrinsic_frontier_support_eq_zero)

omit [CompleteSpace F] in
/-- Existence of a Borell density representative of the intrinsic law relative to any additive
Haar measure on the direction of the affine support. Absolute continuity is already proved; the
obligation is to choose an upper semicontinuous log-concave finite-valued version of the
Radon--Nikodym density. Includes dimension zero. -/
theorem exists_isBorellDensity {μ : ProbabilityMeasure F} (hμ : LogConcave μ)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure] :
    ∃ ρ : (Probability.affineSupport μ).direction → ℝ,
      IsBorellDensity (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction) m ρ :=
  hμ.intrinsicMeasure.exists_isBorellDensity_of_interior_support_nonempty m
    hμ.interior_intrinsic_support_nonempty (hμ.intrinsic_absolutelyContinuous m)

omit [CompleteSpace F] in
/-- The intrinsic law of a log-concave probability has an exponential moment: some positive
rate `t` makes `exp (t ‖v‖)` integrable. This is the tail estimate behind the moment
conclusion and is stated separately because it is the form proved in the literature. -/
theorem intrinsic_integrable_exp_norm {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun v ↦ Real.exp (t * ‖v‖))
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) :=
  ((borel_iff _).1 hμ.intrinsicMeasure).exists_integrable_exp_norm

omit [CompleteSpace F] in
/-- The intrinsic law of a log-concave probability has finite moments of every order.
It follows from the exponential moment and Mathlib's `IntegrableExpMul`. -/
theorem intrinsic_integrable_norm_pow {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) (p : ℕ) :
    Integrable (fun v ↦ ‖v‖ ^ p)
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) := by
  obtain ⟨t, ht, hint⟩ := hμ.intrinsic_integrable_exp_norm
  exact Probability.integrable_norm_pow_of_integrable_exp_norm ht hint p

end KLS.LogConcave

end Intrinsic

end FunctionalInequalities
