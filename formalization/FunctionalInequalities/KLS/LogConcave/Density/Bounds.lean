import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation

/-! # Quantitative bounds for Borell density representatives -/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
namespace FunctionalInequalities.KLS
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
namespace IsBorellDensity

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- The positivity set of a Borell density of a probability law has nonempty interior. -/
private theorem nonempty_interior_pos {ν : ProbabilityMeasure V} {m : Measure V}
    [m.IsAddHaarMeasure] {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) :
    (interior {y : V | 0 < ρ y}).Nonempty := by
  set S : Set V := {y | 0 < ρ y} with hS
  have hSconv : Convex ℝ S := h.convex_pos
  have hmeas : MeasurableSet S := measurableSet_lt measurable_const h.measurable
  have hνSc : (ν : Measure V) Sᶜ = 0 := h.measure_compl_pos
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hspan : affineSpan ℝ S ≠ ⊤ := by
    intro htop
    have hne := hSconv.interior_nonempty_iff_affineSpan_eq_top.mpr htop
    rw [hemp] at hne
    exact Set.not_nonempty_empty hne
  have hmS : m (affineSpan ℝ S : Set V) = 0 := Measure.addHaar_affineSubspace m _ hspan
  have hνS : (ν : Measure V) S = 0 := by
    rw [← h.withDensity_eq, withDensity_apply _ hmeas]
    exact setLIntegral_measure_zero _ _ (measure_mono_null (subset_affineSpan ℝ S) hmS)
  have huniv : (ν : Measure V) Set.univ = 0 := by
    rw [← Set.union_compl_self S]
    exact measure_union_null hνS hνSc
  simp at huniv

omit [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- A law with a Borell density is absolutely continuous with respect to its reference measure. -/
theorem absolutelyContinuous {ν m : Measure V} {ρ : V → ℝ} (h : IsBorellDensity ν m ρ) :
    ν ≪ m := by
  rw [← h.withDensity_eq]
  exact withDensity_absolutelyContinuous m _

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- A Borell density of a probability law is bounded below by a positive constant on some ball.
The recovery construction needs the ball itself, not only the resulting global bound. -/
theorem exists_ball_le {ν : ProbabilityMeasure V} {m : Measure V} [m.IsAddHaarMeasure]
    {ρ : V → ℝ} (h : IsBorellDensity (ν : Measure V) m ρ) :
    ∃ (a : V) (r b₀ : ℝ), 0 < r ∧ 0 < b₀ ∧ ∀ z ∈ Metric.ball a r, b₀ ≤ ρ z := by
  obtain ⟨a, ha⟩ := h.nonempty_interior_pos
  have haS : a ∈ {y : V | 0 < ρ y} := interior_subset ha
  have hpos : 0 < ρ a := haS
  have hca : ContinuousAt ρ a :=
    h.continuousOn_interior_pos.continuousAt (isOpen_interior.mem_nhds ha)
  have hmem : ρ ⁻¹' Set.Ioi (ρ a / 2) ∈ 𝓝 a :=
    hca (Ioi_mem_nhds (by linarith))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  exact ⟨a, r, ρ a / 2, hr, by linarith, fun z hz ↦ (hsub hz).le⟩

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- A Borell density of a probability law is bounded: `M = sup ρ < ∞`.  On a ball where
`ρ ≥ b₀ > 0`, log-concavity gives `ρ ≥ √(b₀ ρ(x))` on a half-size ball, whose mass is at most
one. -/
theorem exists_le {ν : ProbabilityMeasure V} {m : Measure V} [m.IsAddHaarMeasure] {ρ : V → ℝ}
    (h : IsBorellDensity (ν : Measure V) m ρ) :
    ∃ M : ℝ, ∀ x, ρ x ≤ M := by
  obtain ⟨a, r, b₀, hr, hb₀, hball⟩ := h.exists_ball_le
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  set K₀ : ℝ≥0∞ := m (Metric.ball (0 : V) (r / 2)) with hK₀
  have hK₀pos : 0 < K₀ := Metric.measure_ball_pos m 0 hr2
  have hK₀top : K₀ ≠ ⊤ := measure_ball_lt_top.ne
  set K : ℝ := K₀.toReal with hK
  have hKpos : 0 < K := ENNReal.toReal_pos hK₀pos.ne' hK₀top
  refine ⟨1 / (K ^ 2 * b₀), fun x ↦ ?_⟩
  set c : V := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • a with hc
  have hsqrt : ∀ z ∈ Metric.ball c (r / 2), Real.sqrt (ρ x * b₀) ≤ ρ z := by
    intro z hz
    set b : V := (2 : ℝ) • z - x with hb
    have hbmem : b ∈ Metric.ball a r := by
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have hbe : b - a = (2 : ℝ) • (z - c) := by rw [hb, hc]; module
      rw [hbe, norm_smul]
      simp only [Real.norm_ofNat]
      linarith [hz]
    have hlc := h.logConcave x b (1 / 2) (by norm_num) (by norm_num)
    have hzeq : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • b = z := by rw [hb]; module
    rw [hzeq] at hlc
    have hb₀b : b₀ ≤ ρ b := hball b hbmem
    calc Real.sqrt (ρ x * b₀) = ρ x ^ (1 / 2 : ℝ) * b₀ ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, Real.mul_rpow (h.nonneg x) hb₀.le]
      _ ≤ ρ x ^ (1 / 2 : ℝ) * ρ b ^ (1 - 1 / 2 : ℝ) := by
          have hexp : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
          rw [hexp]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb₀.le hb₀b (by norm_num))
            (Real.rpow_nonneg (h.nonneg x) _)
      _ ≤ ρ z := hlc
  have hcball : m (Metric.ball c (r / 2)) = K₀ := Measure.addHaar_ball_center m c (r / 2)
  have hint : ENNReal.ofReal (Real.sqrt (ρ x * b₀)) * K₀
      ≤ (ν : Measure V) (Metric.ball c (r / 2)) := by
    rw [← h.withDensity_eq, withDensity_apply _ Metric.isOpen_ball.measurableSet]
    calc ENNReal.ofReal (Real.sqrt (ρ x * b₀)) * K₀
        = ∫⁻ _ in Metric.ball c (r / 2), ENNReal.ofReal (Real.sqrt (ρ x * b₀)) ∂m := by
          rw [setLIntegral_const, hcball]
      _ ≤ ∫⁻ z in Metric.ball c (r / 2), ENNReal.ofReal (ρ z) ∂m :=
          setLIntegral_mono h.measurable.ennreal_ofReal
            (fun z hz ↦ ENNReal.ofReal_le_ofReal (hsqrt z hz))
  have hle1 : ENNReal.ofReal (Real.sqrt (ρ x * b₀)) * K₀ ≤ 1 := hint.trans prob_le_one
  -- transfer to the reals
  have hreal : Real.sqrt (ρ x * b₀) * K ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hle1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_one]
      at this
  have hsq : Real.sqrt (ρ x * b₀) ≤ 1 / K := by
    rw [le_div_iff₀ hKpos]; linarith
  have hmul : ρ x * b₀ ≤ (1 / K) ^ 2 := by
    have := Real.sq_sqrt (mul_nonneg (h.nonneg x) hb₀.le)
    nlinarith [Real.sqrt_nonneg (ρ x * b₀), hsq]
  rw [le_div_iff₀ (by positivity)]
  have : (1 / K) ^ 2 = 1 / K ^ 2 := by rw [div_pow, one_pow]
  rw [this] at hmul
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  calc ρ x * (K ^ 2 * b₀) = (ρ x * b₀) * K ^ 2 := by ring
    _ ≤ (1 / K ^ 2) * K ^ 2 := by
        exact mul_le_mul_of_nonneg_right hmul hK2.le
    _ = 1 := by field_simp

omit [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The log-concave comparison of the Blueprint: if `y = s x + (1 - s) b` with `0 < s < 1`,
`b₀ ≤ ρ b`, `0 < b₀`, and `ρ ≤ M` everywhere, then `ρ x ≤ (M / b₀)^{(1-s)/s} ρ y`.  Applied with
`b` in the ball where `ρ ≥ b₀`, it lets the weight at `x` be paid by the weight at the nearby
point `y` of the undilated domain. -/
theorem le_rpow_mul_of_combination {ν m : Measure V} {ρ : V → ℝ} (h : IsBorellDensity ν m ρ)
    {M b₀ s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) (hb₀ : 0 < b₀) (hM : ∀ z, ρ z ≤ M)
    {x y b : V} (hb : b₀ ≤ ρ b) (hy : y = s • x + (1 - s) • b) :
    ρ x ≤ (M / b₀) ^ ((1 - s) / s) * ρ y := by
  have hρx := h.nonneg x
  have hρy := h.nonneg y
  have hs' : (0 : ℝ) < 1 - s := by linarith
  have hM0 : 0 ≤ M := le_trans hρy (hM y)
  have hexp : 0 ≤ (1 - s) / s := (div_pos hs' hs₀).le
  rcases eq_or_lt_of_le hρx with hx0 | hxpos
  · rw [← hx0]
    positivity
  have hlc := h.logConcave x b s hs₀ hs₁
  rw [← hy] at hlc
  have hb₁ : b₀ ^ (1 - s) ≤ ρ b ^ (1 - s) := Real.rpow_le_rpow hb₀.le hb hs'.le
  have key : ρ x ^ s * b₀ ^ (1 - s) ≤ ρ y :=
    le_trans (mul_le_mul_of_nonneg_left hb₁ (Real.rpow_nonneg hρx s)) hlc
  have hb₀p : (0 : ℝ) < b₀ ^ (1 - s) := Real.rpow_pos_of_pos hb₀ _
  have hxsp : (0 : ℝ) < ρ x ^ s := Real.rpow_pos_of_pos hxpos s
  have hypos : 0 < ρ y := lt_of_lt_of_le (mul_pos hxsp hb₀p) key
  have key2 : ρ x ^ s ≤ ρ y / b₀ ^ (1 - s) := (le_div_iff₀ hb₀p).mpr key
  have hid : (ρ x ^ s) ^ (1 / s) = ρ x := by
    rw [← Real.rpow_mul hρx, mul_one_div, div_self hs₀.ne', Real.rpow_one]
  have h1 : ρ x ≤ (ρ y / b₀ ^ (1 - s)) ^ (1 / s) := by
    rw [← hid]
    exact Real.rpow_le_rpow hxsp.le key2 (by positivity)
  have h2 : (ρ y / b₀ ^ (1 - s)) ^ (1 / s) = ρ y ^ (1 / s) / b₀ ^ ((1 - s) / s) := by
    rw [Real.div_rpow hρy hb₀p.le, ← Real.rpow_mul hb₀.le, mul_one_div]
  have hsum : (1 : ℝ) + (1 - s) / s = 1 / s := by field_simp; ring
  have h3 : ρ y ^ (1 / s) = ρ y * ρ y ^ ((1 - s) / s) := by
    rw [← hsum, Real.rpow_add hypos, Real.rpow_one]
  have h4 : ρ y ^ ((1 - s) / s) ≤ M ^ ((1 - s) / s) := Real.rpow_le_rpow hρy (hM y) hexp
  have h5 : (M / b₀) ^ ((1 - s) / s) = M ^ ((1 - s) / s) / b₀ ^ ((1 - s) / s) :=
    Real.div_rpow hM0 hb₀.le _
  calc ρ x ≤ ρ y ^ (1 / s) / b₀ ^ ((1 - s) / s) := h2 ▸ h1
    _ = ρ y * ρ y ^ ((1 - s) / s) / b₀ ^ ((1 - s) / s) := by rw [h3]
    _ ≤ ρ y * M ^ ((1 - s) / s) / b₀ ^ ((1 - s) / s) := by
        gcongr
    _ = (M / b₀) ^ ((1 - s) / s) * ρ y := by rw [h5]; ring

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The interior of the positivity set lies in the interior of the measure support.
Only positivity on an open set and positivity of Haar measure on neighbourhoods are needed. -/
theorem interior_pos_subset {ν m : Measure V} [m.IsAddHaarMeasure] {ρ : V → ℝ}
    (h : IsBorellDensity ν m ρ) :
    interior {x | 0 < ρ x} ⊆ interior ν.support := by
  apply interior_maximal _ isOpen_interior
  intro x hx
  rw [Measure.mem_support_iff_forall]
  intro N hN
  let O := interior N ∩ interior {x | 0 < ρ x}
  have hO : IsOpen O := isOpen_interior.inter isOpen_interior
  have hxO : x ∈ O := ⟨mem_interior_iff_mem_nhds.mpr hN, hx⟩
  have hpos : 0 < ν O := by
    rw [← h.withDensity_eq, withDensity_apply _ hO.measurableSet,
      setLIntegral_pos_iff h.measurable.ennreal_ofReal]
    have heq : Function.support (fun y => ENNReal.ofReal (ρ y)) ∩ O = O := by
      apply Set.inter_eq_right.mpr
      intro y hy
      have hypos : y ∈ {x : V | 0 < ρ x} := interior_subset hy.2
      exact (ENNReal.ofReal_pos.mpr hypos).ne'
    rw [heq]
    exact m.measure_pos_of_mem_nhds (hO.mem_nhds hxO)
  exact hpos.trans_le (measure_mono fun y hy => interior_subset hy.1)

end IsBorellDensity
end FunctionalInequalities.KLS
