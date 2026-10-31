module

public import FunctionalInequalities.KLS.LogConcave.Line.Isoperimetry
public import FunctionalInequalities.KLS.LogConcave.Line.OfDensity
public import FunctionalInequalities.KLS.LogConcave.Line.Poincare
public import FunctionalInequalities.Poincare.SmoothTest.Linear
public import FunctionalInequalities.Poincare.SmoothTest.Transport

/-!
# A Buser comparison with constant twelve: `Ψ² ≤ 12 C_P` in dimension one

Read
`evariance_le_smoothTest_constant` (the linear test), `LineDensity.one_div_le_evariance` (a
bounded density has variance at least `1 / (12 M²)`), then the assembly
`LogConcave.inv_minkowskiConstant_sq_le` and its affine-support form
`LogConcave.inverseScale_sq_le_of_finrank_le_one`.

On the line the identity is a smooth test of unit gradient energy, so
`Var_ν(id) ≤ C_P^smooth(ν)`.  A log-concave law has a finite second moment
(`LogConcave.memLp_id_two`), so the extended and the real variance agree.  A law with a Borell
density has support with nonempty interior, hence a median `m`; Bobkov's variance bound
`1 / (12 ρ(m)²) ≤ Var` of `Line/Variance.lean` and the density bound `ρ(m) ≤ M` give
`LineDensity.one_div_le_evariance` without a separate rearrangement argument.  Combining
`2 ρ(m) ≤ h_M` (`Line/Isoperimetry.lean`) with
`1 / (12 ρ(m)²) ≤ Var ≤ C_P^smooth` gives
`h_M⁻² ≤ 1 / (4 ρ(m)²) ≤ 1 / ρ(m)² ≤ 12 C_P^smooth`; Dirac laws on the line have `h_M = ⊤` and a
vanishing left side.

For the affine-support form the intrinsic law lives on a direction space of dimension at most
one.  Dimension zero has `Isoperimetry.constant = ⊤` by convention, hence inverse scale `0`.  In
dimension one a linear isometry equivalence with `ℝ` transports log-concavity
(`LogConcave.of_affineIsometry_map`), the Minkowski Cheeger infimum
(`Isoperimetry.minkowskiConstant_map`, proved here) and the smooth-test constant
(`Poincare.SmoothTest.constant_map_linearIsometryEquiv`); the identifications
`Isoperimetry.constant = h_M(intrinsic)` and `C_P^smooth(intrinsic) = C_P^lit` close the chain.

The constant is `12`, not `π`: nothing here is the sharp Buser inequality, and nothing here says
anything in dimension two or more.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FunctionalInequalities.Probability.Line (cdf)
open scoped ENNReal NNReal

namespace FunctionalInequalities.KLS

/-! ### One-dimensional inner-product spaces -/

/-- A one-dimensional real inner-product space is linearly isometric to the line. -/
theorem nonempty_linearIsometryEquiv_real {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (h : Module.finrank ℝ V = 1) :
    Nonempty (V ≃ₗᵢ[ℝ] ℝ) := by
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  set v : V := ‖w‖⁻¹ • w with hvdef
  have hv : ‖v‖ = 1 := by
    rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn]
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv
    norm_num at hv
  let f : ℝ →ₗᵢ[ℝ] V :=
    ⟨LinearMap.toSpanSingleton ℝ V v, fun t ↦ by
      simp [LinearMap.toSpanSingleton_apply, norm_smul, hv]⟩
  have hspan : Submodule.span ℝ ({v} : Set V) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_singleton hvne, h])
  have hsurj : Function.Surjective (f : ℝ → V) := by
    intro y
    have hy : y ∈ Submodule.span ℝ ({v} : Set V) := by rw [hspan]; trivial
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨t, by simpa [f, LinearMap.toSpanSingleton_apply] using ht⟩
  exact ⟨(LinearIsometryEquiv.ofSurjective f hsurj).symm⟩

/-! ### Transport of the Minkowski Cheeger infimum -/

namespace Isoperimetry

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] [FiniteDimensional ℝ W]

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] [CompleteSpace W]
  [SecondCountableTopology W] [FiniteDimensional ℝ W] in
/-- The Minkowski Cheeger infimum is invariant under a linear isometry equivalence; the special
case of `minkowskiConstant_eq_of_isometryEquiv` for the push-forward law. -/
theorem minkowskiConstant_map (e : V ≃ₗᵢ[ℝ] W) (ν : ProbabilityMeasure V) :
    minkowskiConstant (ν.map e) = minkowskiConstant ν :=
  minkowskiConstant_eq_of_isometryEquiv e.toIsometryEquiv
    ⟨e.continuous.measurable, (ProbabilityMeasure.toMeasure_map _).symm⟩

end Isoperimetry

/-! ### The linear test -/

/-- The identity is a smooth test of unit gradient energy on the line, so
the variance is at most the smooth-test Poincaré constant. -/
theorem evariance_le_smoothTest_constant (ν : ProbabilityMeasure ℝ)
    (h : MemLp id 2 (ν : Measure ℝ)) :
    evariance id (ν : Measure ℝ) ≤ Poincare.SmoothTest.constant (ν : Measure ℝ) := by
  have hprob : IsProbabilityMeasure (ν : Measure ℝ) := inferInstance
  have hid : Poincare.SmoothTest.linear (1 : ℝ) = (id : ℝ → ℝ) := by
    funext x
    simp [Poincare.SmoothTest.linear]
  have hadm : Poincare.SmoothTest.Admissible (ν : Measure ℝ) id :=
    hid ▸ Poincare.SmoothTest.linear_admissible hprob h 1
  have henergy : Poincare.SmoothTest.energy (ν : Measure ℝ) (id : ℝ → ℝ) = 1 := by
    rw [← hid, Poincare.SmoothTest.energy_linear]
    norm_num
  have hray := Poincare.SmoothTest.rayleigh_le_constant hadm
  rwa [Poincare.SmoothTest.rayleigh, henergy, ENNReal.ofReal_one, div_one,
    ofReal_variance h] at hray

/-! ### A bounded density forces a lower bound on the variance -/

namespace LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ)

include d in
/-- A law with a Borell Lebesgue density on the line has support with nonempty interior: the
support is convex and carries the whole mass, while points are null. -/
theorem interior_support_nonempty : (interior (μ : Measure ℝ).support).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hconv : Convex ℝ (μ : Measure ℝ).support := d.logConcave.convex_support
  have hsub : ((μ : Measure ℝ).support).Subsingleton := by
    intro u hu v hv
    by_contra huv
    rcases lt_or_gt_of_ne huv with h | h
    · obtain ⟨z, hz⟩ := nonempty_Ioo.mpr h
      have hs : Ioo u v ⊆ (μ : Measure ℝ).support := fun w hw ↦
        hconv.ordConnected.out hu hv ⟨hw.1.le, hw.2.le⟩
      exact absurd (hempty ▸ (interior_maximal hs isOpen_Ioo hz)) (by simp)
    · obtain ⟨z, hz⟩ := nonempty_Ioo.mpr h
      have hs : Ioo v u ⊆ (μ : Measure ℝ).support := fun w hw ↦
        hconv.ordConnected.out hv hu ⟨hw.1.le, hw.2.le⟩
      exact absurd (hempty ▸ (interior_maximal hs isOpen_Ioo hz)) (by simp)
  have hfull : (μ : Measure ℝ) (μ : Measure ℝ).support = 1 := by
    have hc := Measure.measure_compl_support (μ := (μ : Measure ℝ))
    have hadd := measure_add_measure_compl (μ := (μ : Measure ℝ))
      (s := (μ : Measure ℝ).support) Measure.isClosed_support.measurableSet
    rw [hc, add_zero, measure_univ] at hadd
    exact hadd
  rcases hsub.eq_empty_or_singleton with he | ⟨a, ha⟩
  · rw [he] at hfull
    simp at hfull
  · rw [ha, d.measure_singleton] at hfull
    simp at hfull

/-- A law on the line whose density is bounded by `M` has extended
variance at least `1 / (12 M²)`. -/
theorem one_div_le_evariance {M : ℝ} (hM : 0 < M) (hbd : ∀ x, d.ρ x ≤ M) :
    ENNReal.ofReal (1 / (12 * M ^ 2)) ≤ evariance id (μ : Measure ℝ) := by
  have hμ : LogConcave μ := d.logConcave
  have hi := d.interior_support_nonempty
  obtain ⟨m, hm⟩ := d.exists_median
  have hmΩ := median_mem hμ hi hm
  have hc : 0 < d.ρ m := d.pos hmΩ
  obtain ⟨k, hk⟩ := d.exists_supergradient hμ hmΩ
  have hvar := d.one_div_le_variance hμ hi hm hk
  have hcmp : 1 / (12 * M ^ 2) ≤ 1 / (12 * d.ρ m ^ 2) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [hbd m]
  rw [← ofReal_variance hμ.memLp_id_two]
  exact ENNReal.ofReal_le_ofReal (hcmp.trans hvar)

end LineDensity

/-! ### The assembly -/

namespace LogConcave

variable {ν : ProbabilityMeasure ℝ}

/-- A log-concave law on the line whose support has empty interior is a Dirac law. -/
theorem exists_support_eq_singleton (hν : LogConcave ν)
    (hempty : interior (ν : Measure ℝ).support = ∅) :
    ∃ a : ℝ, (ν : Measure ℝ).support = {a} := by
  have hconv : Convex ℝ (ν : Measure ℝ).support := hν.convex_support
  have hsub : ((ν : Measure ℝ).support).Subsingleton := by
    intro u hu v hv
    by_contra huv
    rcases lt_or_gt_of_ne huv with h | h
    · obtain ⟨z, hz⟩ := nonempty_Ioo.mpr h
      have hs : Ioo u v ⊆ (ν : Measure ℝ).support := fun w hw ↦
        hconv.ordConnected.out hu hv ⟨hw.1.le, hw.2.le⟩
      exact absurd (hempty ▸ (interior_maximal hs isOpen_Ioo hz)) (by simp)
    · obtain ⟨z, hz⟩ := nonempty_Ioo.mpr h
      have hs : Ioo v u ⊆ (ν : Measure ℝ).support := fun w hw ↦
        hconv.ordConnected.out hv hu ⟨hw.1.le, hw.2.le⟩
      exact absurd (hempty ▸ (interior_maximal hs isOpen_Ioo hz)) (by simp)
  have hfull : (ν : Measure ℝ) (ν : Measure ℝ).support = 1 := by
    have hc := Measure.measure_compl_support (μ := (ν : Measure ℝ))
    have hadd := measure_add_measure_compl (μ := (ν : Measure ℝ))
      (s := (ν : Measure ℝ).support) Measure.isClosed_support.measurableSet
    rw [hc, add_zero, measure_univ] at hadd
    exact hadd
  rcases hsub.eq_empty_or_singleton with he | ⟨a, ha⟩
  · rw [he] at hfull
    simp at hfull
  · exact ⟨a, ha⟩

/-- A log-concave law on the line whose support has empty interior has infinite Minkowski Cheeger
infimum: no Borel set has intermediate mass. -/
theorem minkowskiConstant_eq_top_of_interior_empty (hν : LogConcave ν)
    (hempty : interior (ν : Measure ℝ).support = ∅) :
    Isoperimetry.minkowskiConstant ν = ⊤ := by
  obtain ⟨a, ha⟩ := hν.exists_support_eq_singleton hempty
  have hpt : (ν : Measure ℝ) {a} = 1 := by
    have hc := Measure.measure_compl_support (μ := (ν : Measure ℝ))
    have hadd := measure_add_measure_compl (μ := (ν : Measure ℝ))
      (s := (ν : Measure ℝ).support) Measure.isClosed_support.measurableSet
    rw [hc, add_zero, measure_univ, ha] at hadd
    exact hadd
  have hzero : (ν : Measure ℝ) ({a}ᶜ) = 0 := by
    have hc := Measure.measure_compl_support (μ := (ν : Measure ℝ))
    rwa [ha] at hc
  rw [Isoperimetry.minkowskiConstant]
  refine iInf_eq_top.mpr fun B ↦ ?_
  by_cases hB : MeasurableSet B
  · rw [iInf_pos hB]
    by_cases haB : a ∈ B
    · have hB1 : (ν : Measure ℝ) B = 1 :=
        le_antisymm prob_le_one (hpt ▸ measure_mono (Set.singleton_subset_iff.mpr haB))
      rw [iInf_pos (by rw [hB1]; norm_num : (0 : ℝ≥0∞) < (ν : Measure ℝ) B)]
      exact iInf_neg (by rw [hB1]; exact lt_irrefl 1)
    · have hB0 : (ν : Measure ℝ) B = 0 := by
        refine measure_mono_null (fun z hz ↦ ?_) hzero
        intro hz'
        rw [Set.mem_singleton_iff] at hz'
        exact haB (hz' ▸ hz)
      exact iInf_neg (by rw [hB0]; exact lt_irrefl 0)
  · exact iInf_neg hB

/-- On the line the squared inverse Cheeger scale is at most twelve times
the smooth-test Poincaré constant. -/
theorem inv_minkowskiConstant_sq_le (hν : LogConcave ν) :
    (Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2 ≤
      12 * Poincare.SmoothTest.constant (ν : Measure ℝ) := by
  rcases eq_empty_or_nonempty (interior (ν : Measure ℝ).support) with hempty | hi
  · rw [hν.minkowskiConstant_eq_top_of_interior_empty hempty]
    simp
  obtain ⟨d⟩ := hν.exists_lineDensity hi
  obtain ⟨m, hm⟩ := d.exists_median
  have hmΩ := LineDensity.median_mem hν hi hm
  have hc : 0 < d.ρ m := d.pos hmΩ
  obtain ⟨k, hk⟩ := d.exists_supergradient hν hmΩ
  have hQ1 := d.two_mul_le_minkowskiConstant hν hi hm
  have hvar := d.one_div_le_variance hν hi hm hk
  have hQ4 := evariance_le_smoothTest_constant ν hν.memLp_id_two
  have hB : ENNReal.ofReal (1 / (4 * d.ρ m ^ 2)) ≤
      12 * Poincare.SmoothTest.constant (ν : Measure ℝ) := by
    have h1 : ENNReal.ofReal (1 / (12 * d.ρ m ^ 2)) ≤ evariance id (ν : Measure ℝ) := by
      rw [← ofReal_variance hν.memLp_id_two]
      exact ENNReal.ofReal_le_ofReal hvar
    calc ENNReal.ofReal (1 / (4 * d.ρ m ^ 2))
        ≤ ENNReal.ofReal (12 * (1 / (12 * d.ρ m ^ 2))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show (12 : ℝ) * (1 / (12 * d.ρ m ^ 2)) = 1 / d.ρ m ^ 2 by field_simp]
          refine one_div_le_one_div_of_le (by positivity) ?_
          nlinarith
      _ = 12 * ENNReal.ofReal (1 / (12 * d.ρ m ^ 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ 12 * evariance id (ν : Measure ℝ) := by gcongr
      _ ≤ 12 * Poincare.SmoothTest.constant (ν : Measure ℝ) := by gcongr
  refine le_trans ?_ hB
  have hinveq : ENNReal.ofReal (1 / (2 * d.ρ m)) = (ENNReal.ofReal (2 * d.ρ m))⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by linarith : (0 : ℝ) < 2 * d.ρ m)]
  have hinv : (Isoperimetry.minkowskiConstant ν)⁻¹ ≤ ENNReal.ofReal (1 / (2 * d.ρ m)) := by
    rw [hinveq]
    exact ENNReal.inv_le_inv.mpr hQ1
  calc (Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2
      ≤ ENNReal.ofReal (1 / (2 * d.ρ m)) ^ 2 := by gcongr
    _ = ENNReal.ofReal ((1 / (2 * d.ρ m)) ^ 2) := (ENNReal.ofReal_pow (by positivity) 2).symm
    _ = ENNReal.ofReal (1 / (4 * d.ρ m ^ 2)) := by
        rw [show ((1 : ℝ) / (2 * d.ρ m)) ^ 2 = 1 / (4 * d.ρ m ^ 2) by field_simp; ring]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- A log-concave law whose affine support has dimension at most one
satisfies the Buser comparison with constant twelve.  Dirac laws have both sides zero on the
left. -/
theorem inverseScale_sq_le_of_finrank_le_one {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    (hdim : Module.finrank ℝ (Probability.affineSupport μ).direction ≤ 1) :
    Isoperimetry.inverseScale μ ^ 2 ≤ 12 * Poincare.LocalSlope.Intrinsic.constant μ := by
  rcases Nat.lt_or_ge (Module.finrank ℝ (Probability.affineSupport μ).direction) 1 with h0 | h1
  · have hz : Module.finrank ℝ (Probability.affineSupport μ).direction = 0 := Nat.lt_one_iff.mp h0
    have htop : Isoperimetry.constant μ = ⊤ := by
      unfold Isoperimetry.constant
      rw [ite_eq_left hz]
    rw [Isoperimetry.inverseScale, htop]
    simp
  have hdim1 : Module.finrank ℝ (Probability.affineSupport μ).direction = 1 :=
    le_antisymm hdim h1
  obtain ⟨e⟩ := nonempty_linearIsometryEquiv_real hdim1
  set ν' := Probability.intrinsicMeasure μ with hν'
  set ν := ν'.map e with hνdef
  have hcoe : (ν : Measure ℝ) =
      (ν' : Measure (Probability.affineSupport μ).direction).map e :=
    ProbabilityMeasure.toMeasure_map _
  have hlc' : LogConcave ν' := hμ.intrinsicMeasure
  have hlc : LogConcave ν := by
    refine hlc'.of_affineIsometry_map ν (e.symm.toLinearIsometry.toAffineIsometry) ?_
    rw [LinearIsometry.coe_toAffineIsometry, LinearIsometryEquiv.coe_toLinearIsometry, hcoe,
      Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
    simp
  have hmain := hlc.inv_minkowskiConstant_sq_le
  rw [Isoperimetry.minkowskiConstant_map] at hmain
  have hconst : Poincare.SmoothTest.constant (ν : Measure ℝ) =
      Poincare.SmoothTest.constant (ν' : Measure (Probability.affineSupport μ).direction) := by
    rw [hcoe]
    exact Poincare.SmoothTest.constant_map_linearIsometryEquiv e _
  rw [hconst, (hμ.smoothTest_constant_eq_intrinsic_and_localSlope).2] at hmain
  rw [Isoperimetry.inverseScale, Isoperimetry.constant_eq_minkowskiConstant_intrinsic]
  exact hmain

end LogConcave

end FunctionalInequalities.KLS
