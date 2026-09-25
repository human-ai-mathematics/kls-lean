import FunctionalInequalities.Analysis.WaveSplitting.Potential
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator
import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier
import FunctionalInequalities.Analysis.Semigroup.Resolvent.Basic
import FunctionalInequalities.Analysis.Semigroup.VonNeumann

/-!
# Density of the form range `(I + T̄†T̄) C_c^∞` in the form domain

Let `ν = m.tilted (-U)` be a full-dimensional log-concave probability law on a
finite-dimensional Euclidean space `V`, with a smooth potential `U` and unit weight. Let
`T̄ = hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi` be the closed gradient,
`A = T̄†T̄`, `J = I + A`, and let `E = D(T̄)` carry the graph norm
`‖x‖_E² = ‖x‖² + ‖T̄ x‖²` of `L²(ν) × L²(ν; V)`. This is not the subspace topology of
`L²(ν)`.

Three bridges connect the classical wave-splitting objects to these classes. Directions are an
orthonormal basis `e`, `b_j = D_(e_j) U`, `w = exp (-U)` and `Z = ∫ exp (-U) dm > 0`.

* **Norm** (`norm_sq_add_norm_closedWeightedOperator_sq_eq`): if `x ∈ E` is the class of some
  `f ∈ C_c^∞`, then `‖x‖_E² = FE_w(f) / Z`.
* **Operator** (`toLp_add_adjointComp_eq_formOperator`,
  `toLp_add_adjointComp_mem_closedWeightedOperator_domain`): for `q ∈ C_c^∞`, `[q] ∈ D(A)`,
  `J[q] = [formOperator e b q]`, and `J[q] ∈ E`.
* **Density** (`exists_toLp_add_adjointComp_graph_lt`, `dense_formRange_graphL2`): for every
  `z ∈ E` and `ε > 0` there is `q ∈ C_c^∞` with `‖J[q] - z‖_E < ε`.

The density proof combines the graph-norm smooth core of `T̄` (`exists_seq_smooth_tendsto_graph`),
the classical time-average approximation (`exists_timeAverage_error_lt`) and the norm bridge.
Only the model hypotheses are used. There is no hypothesis on density of the form range, an
operator core, surjectivity of `J`, or a Poincaré inequality. Zero dimension is included; there
`J = I`.

* **Two-field core** (`exists_seq_smooth_tendsto_two_fields`): every `F ∈ D(A)` with
  `AF ∈ D(T̄)` has `qₙ ∈ C_c^∞` with `[qₙ] → F`, `[∇qₙ] → T̄F`, `[-ℒqₙ] → AF` and
  `[∇(-ℒqₙ)] → T̄(AF)`. It applies the density to `JF` and the second-order graph-norm
  expansion `‖Je‖² + ‖T̄Je‖² = ‖e‖² + 3‖T̄e‖² + 3‖Ae‖² + ‖T̄Ae‖²`
  (`Analysis.Semigroup.norm_add_adjointComp_sq_add_norm_sq`) to `e = [qₙ] - F`.

The heat-test frontend that consumes the two-field core is in `TestClassExtension.lean`.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
  FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.WeightedGradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

private theorem norm_toLp_sq_eq_integral {α W : Type*} [MeasurableSpace α]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {μ : Measure α} {f : α → W}
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- Minkowski's inequality for the norm `√(‖·‖² + ‖·‖²)` on a product, through `WithLp 2`. -/
private theorem sqrt_sq_add_sq_sub_le {H₀ H₁ : Type*} [NormedAddCommGroup H₀]
    [NormedAddCommGroup H₁] (a b c : H₀) (a' b' c' : H₁) :
    √(‖a - c‖ ^ 2 + ‖a' - c'‖ ^ 2) ≤
      √(‖a - b‖ ^ 2 + ‖a' - b'‖ ^ 2) + √(‖b - c‖ ^ 2 + ‖b' - c'‖ ^ 2) := by
  have hn (p : H₀) (p' : H₁) : √(‖p‖ ^ 2 + ‖p'‖ ^ 2) = ‖WithLp.toLp 2 (p, p')‖ := by
    have h := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (p, p'))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd] at h
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  rw [hn, hn, hn]
  have hs : WithLp.toLp 2 (a - c, a' - c') =
      WithLp.toLp 2 (a - b, a' - b') + WithLp.toLp 2 (b - c, b' - c') := by
    rw [← WithLp.toLp_add, Prod.mk_add_mk, sub_add_sub_cancel, sub_add_sub_cancel]
  rw [hs]
  exact norm_add_le _ _

section Bridges

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U))

include hνU in
/-- **Norm bridge.** Let `x ∈ D(T̄)` be the class of a smooth compactly supported `f`. For an
orthonormal basis `e`, the graph norm of `x` is the weighted coordinate form energy divided by
the normalization: `‖x‖² + ‖T̄ x‖² = FE_w(f) / Z`, `w = exp (-U)`, `Z = ∫ exp (-U) dm`. -/
theorem norm_sq_add_norm_closedWeightedOperator_sq_eq {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ V)
    (x : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hx : (x : Lp ℝ 2 (ν : Measure V)) = (memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f) :
    ‖(x : Lp ℝ 2 (ν : Measure V))‖ ^ 2 +
        ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi x‖ ^ 2 =
      weightedFormEnergy m (fun y => Real.exp (-U y)) e f / ∫ y, Real.exp (-U y) ∂m := by
  have hxe : x = ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ := Subtype.ext hx
  have hZ := (integral_exp_neg_pos_of_tilted m hνU).ne'
  have hf2 := (memLp_of_contDiff_hasCompactSupport ν hf hfc).integrable_sq
  have hg := memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc
  have hg2 : Integrable (fun y => ‖gradient f y‖ ^ 2) (ν : Measure V) :=
    (memLp_two_iff_integrable_sq_norm hg.1).mp hg
  rw [hxe, hν.closedWeightedOperator_toLp_eq m hi hf hfc, norm_toLp_sq_eq_integral,
    norm_toLp_sq_eq_integral, weightedFormEnergy_eq_mul_integral m hνU e f,
    integral_add hf2 hg2]
  simp only [Real.norm_eq_abs, sq_abs]
  field_simp

variable {m hν hi}

include hνU in
/-- **Operator bridge.** For a smooth potential, an orthonormal basis `e` and `q ∈ C_c^∞`:
`[q] ∈ D(T̄†T̄)` and `J[q] = [q] + T̄†T̄[q]` is the class of the classical operator
`formOperator e b q = q - ℒq`, `b_j = D_(e_j) U`. -/
theorem toLp_add_adjointComp_eq_formOperator (hU : ContDiff ℝ ∞ U) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ V) {q : V → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q +
        adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide)) hq hqc⟩ =
      (memLp_of_contDiff_hasCompactSupport ν (contDiff_formOperator e hU hq)
        (hasCompactSupport_formOperator e U (hq.of_le (WithTop.coe_le_coe.mpr le_top)) hqc)).toLp
        (formOperator e (fun j x => fderiv ℝ U x (e j)) q) := by
  rw [hν.adjointComp_toLp_eq m hi hνU (hU.of_le (by decide)) hq hqc, ← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun y => ?_)
  rw [formOperator_eq_sub_weightedLaplacian e U (hq.of_le (WithTop.coe_le_coe.mpr le_top))]
  simp only [Pi.add_apply]
  ring

include hνU in
/-- **Operator bridge, form-domain clause.** For a smooth potential and `q ∈ C_c^∞`,
`J[q] = [q] + T̄†T̄[q]` lies in the form domain `D(T̄)`: it is the class of the smooth compactly
supported function `q - ℒq`. -/
theorem toLp_add_adjointComp_mem_closedWeightedOperator_domain (hU : ContDiff ℝ ∞ U)
    {q : V → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q +
        adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide)) hq hqc⟩ ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  rw [toLp_add_adjointComp_eq_formOperator hνU hU (stdOrthonormalBasis ℝ V) hq hqc]
  exact hν.toLp_mem_closedWeightedOperator_domain m hi (contDiff_formOperator _ hU hq)
    (hasCompactSupport_formOperator _ U (hq.of_le (WithTop.coe_le_coe.mpr le_top)) hqc)

end Bridges

section Density

variable {ν : ProbabilityMeasure V} {m : Measure V} [m.IsAddHaarMeasure] {hν : LogConcave ν}
  {hi : (interior (ν : Measure V).support).Nonempty} {U : V → ℝ}

/-- **Density of the form range in the form domain.** For the closed unit-weight gradient `T̄`
of `ν = m.tilted (-U)` with a smooth potential, `A = T̄†T̄` and `J = I + A`: for **every**
`z ∈ D(T̄)` and `ε > 0` there is `q ∈ C_c^∞(V)` with `[q] ∈ D(A)`, `J[q] ∈ D(T̄)` and
`‖J[q] - z‖_E < ε` in the graph norm `‖x‖_E = √(‖x‖² + ‖T̄ x‖²)`. -/
theorem exists_toLp_add_adjointComp_graph_lt (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (z : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : V → ℝ) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
      (hA : (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q ∈
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
      (hJ : (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q +
          adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨_, hA⟩ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      √(‖(memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q +
            adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨_, hA⟩ -
            (z : Lp ℝ 2 (ν : Measure V))‖ ^ 2 +
          ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hJ⟩ -
            hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi z‖ ^ 2) < ε := by
  revert z
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  intro z
  set e := stdOrthonormalBasis ℝ V
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  set Z := ∫ y, Real.exp (-U y) ∂m
  have hZ : 0 < Z := integral_exp_neg_pos_of_tilted m hνU
  -- A smooth compactly supported `h` with `‖[h] - z‖_E < ε / 2`, from the graph-norm core.
  obtain ⟨g, hg, hgc, hlim₁, hlim₂⟩ :=
    hν.exists_seq_smooth_tendsto_graph m (ContinuousLinearMap.id ℝ V) hi z
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hlim₁ _ hε4
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hlim₂ _ hε4
  set n := max N₁ N₂
  have hn₁ := hN₁ n (le_max_left _ _)
  have hn₂ := hN₂ n (le_max_right _ _)
  set h := g n
  have hdom : (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp h ∈ T.domain :=
    hν.toLp_mem_closedWeightedOperator_domain m hi (hg n) (hgc n)
  have hTh : T ⟨_, hdom⟩ = (IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V)
      (hg n) (hgc n)).memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) h) := by
    rw [hν.closedWeightedOperator_toLp_eq m hi (hg n) (hgc n)]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun y => by rw [apply_id])
  have hzh : √(‖(memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp h -
      (z : Lp ℝ 2 (ν : Measure V))‖ ^ 2 + ‖T ⟨_, hdom⟩ - T z‖ ^ 2) < ε / 2 := by
    rw [hTh, ← dist_eq_norm, ← dist_eq_norm]
    calc √(dist _ _ ^ 2 + dist _ _ ^ 2) < √((ε / 4) ^ 2 + (ε / 4) ^ 2) := by
          apply Real.sqrt_lt_sqrt (by positivity)
          have := dist_nonneg (x := (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp h)
            (y := (z : Lp ℝ 2 (ν : Measure V)))
          nlinarith [dist_nonneg (x := (IsTest.of_contDiff_hasCompactSupport ν
            (ContinuousLinearMap.id ℝ V) (hg n) (hgc n)).memLp_apply.toLp
              (apply (ContinuousLinearMap.id ℝ V) h)) (y := T z)]
      _ ≤ ε / 2 := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
  -- A time average `q` with `√FE_w(J_cl q - h) < (ε / 2) √Z`, from the classical density.
  obtain ⟨N, δ, -, hq, hqc, hlt⟩ :=
    exists_timeAverage_error_lt m (⇑e) hU (hg n) (hgc n) (ε := ε / 2 * √Z) (by positivity)
  set q := timeAverage (⇑e) (fun j x => fderiv ℝ U x (e j)) (List.finRange _) δ (initial h) N
  have hA := hν.toLp_mem_adjointComp_domain m hi hνU hU1 hq hqc
  have hJ := toLp_add_adjointComp_mem_closedWeightedOperator_domain (hν := hν) (hi := hi) hνU hU
    hq hqc
  refine ⟨q, hq, hqc, hA, hJ, ?_⟩
  -- The norm bridge for `J[q] - [h]`, the class of `J_cl q - h ∈ C_c^∞`.
  have hfq := contDiff_formOperator e hU hq
  have hfqc := hasCompactSupport_formOperator e U (hq.of_le (WithTop.coe_le_coe.mpr le_top)) hqc
  have hd : ContDiff ℝ ∞ (fun y => formOperator (⇑e) (fun j x => fderiv ℝ U x (e j)) q y - h y) :=
    hfq.sub (hg n)
  have hdc : HasCompactSupport
      (fun y => formOperator (⇑e) (fun j x => fderiv ℝ U x (e j)) q y - h y) :=
    hfqc.sub (hgc n)
  set x : T.domain := ⟨_, hJ⟩ - ⟨_, hdom⟩
  have hx : (x : Lp ℝ 2 (ν : Measure V)) =
      (memLp_of_contDiff_hasCompactSupport ν hd hdc).toLp _ := by
    simp only [x, Submodule.coe_sub]
    rw [toLp_add_adjointComp_eq_formOperator hνU hU e hq hqc, ← MemLp.toLp_sub]
    rfl
  have hbridge := norm_sq_add_norm_closedWeightedOperator_sq_eq m hν hi hνU e x hd hdc hx
  have hTx : T x = T ⟨_, hJ⟩ - T ⟨_, hdom⟩ := LinearPMap.map_sub _ _ _
  rw [hTx] at hbridge
  have hxJ : (x : Lp ℝ 2 (ν : Measure V)) =
      ((memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q + adjointComp T ⟨_, hA⟩) -
        (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp h := rfl
  rw [hxJ] at hbridge
  have hqh : √(‖(memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q + adjointComp T ⟨_, hA⟩ -
      (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp h‖ ^ 2 +
      ‖T ⟨_, hJ⟩ - T ⟨_, hdom⟩‖ ^ 2) < ε / 2 := by
    rw [hbridge, Real.sqrt_div' _ hZ.le, div_lt_iff₀ (Real.sqrt_pos.mpr hZ)]
    exact hlt
  calc _ ≤ _ := sqrt_sq_add_sq_sub_le _ ((memLp_of_contDiff_hasCompactSupport ν (hg n)
          (hgc n)).toLp h) _ _ (T ⟨_, hdom⟩) _
    _ < ε / 2 + ε / 2 := add_lt_add hqh hzh
    _ = ε := add_halves ε

/-- **Density in the Hilbert space of the graph.** In `graphL2 T̄ ⊆ L²(ν) × L²(ν; V)`, whose norm
is the graph norm of the form domain, the graph points `(J[q], T̄ J[q])`, `q ∈ C_c^∞(V)`, are
dense. -/
theorem dense_formRange_graphL2 (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U) :
    Dense {p : graphL2 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) |
      ∃ (q : V → ℝ) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
        (hA : (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q ∈
          (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
        (hJ : (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q +
            adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨_, hA⟩ ∈
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
        (p : WithLp 2 (Lp ℝ 2 (ν : Measure V) × Lp V 2 (ν : Measure V))) =
          WithLp.toLp 2 ((memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q +
            adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨_, hA⟩,
            hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hJ⟩)} := by
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  rw [Metric.dense_iff]
  rintro ⟨p, hp⟩ r hr
  have hp' : (p.fst, p.snd) ∈ T.graph := by
    simpa [graphL2] using hp
  obtain ⟨z, hz₁, hz₂⟩ := (T.mem_graph_iff).mp hp'
  simp only at hz₁ hz₂
  obtain ⟨q, hq, hqc, hA, hJ, hlt⟩ := exists_toLp_add_adjointComp_graph_lt hνU hU z hr
  refine ⟨⟨WithLp.toLp 2 (_, T ⟨_, hJ⟩), ?_⟩, ?_, q, hq, hqc, hA, hJ, rfl⟩
  · rw [graphL2, Submodule.mem_comap]
    exact T.mem_graph ⟨_, hJ⟩
  · rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
    have h := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 ((memLp_of_contDiff_hasCompactSupport ν
      hq hqc).toLp q + adjointComp T ⟨_, hA⟩, T ⟨_, hJ⟩) - p)
    rw [← Real.sqrt_sq (norm_nonneg _), h]
    simp only [WithLp.sub_fst, WithLp.sub_snd, WithLp.toLp_fst, WithLp.toLp_snd, ← hz₁, ← hz₂]
    exact hlt

/-- **Two-field smooth core.** For the closed unit-weight gradient `T̄` of `ν = m.tilted (-U)`
with a smooth potential and `A = T̄†T̄`: every `F ∈ D(A)` with `AF ∈ D(T̄)` is approximated by
`qₙ ∈ C_c^∞(V)` in all four fields,
`[qₙ] → F`, `[∇qₙ] → T̄F`, `[-ℒqₙ] → AF` and `[∇(-ℒqₙ)] → T̄(AF)` in `L²(ν)`.

The sequence comes from the form-range density `exists_toLp_add_adjointComp_graph_lt` applied to
`JF = F + AF ∈ D(T̄)`; the second-order graph-norm expansion
(`Analysis.Semigroup.tendsto_of_tendsto_add_adjointComp`) turns `J[qₙ] → JF` in the graph norm
into convergence of all four fields. No classical differentiation of `F` is used. -/
theorem exists_seq_smooth_tendsto_two_fields (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hF : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
      Lp ℝ 2 (ν : Measure V)) ∈ (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ∃ (q : ℕ → V → ℝ) (hq : ∀ n, ContDiff ℝ ∞ (q n)) (hqc : ∀ n, HasCompactSupport (q n)),
      Tendsto (fun n => (memLp_of_contDiff_hasCompactSupport ν (hq n) (hqc n)).toLp (q n)) atTop
        (𝓝 (F : Lp ℝ 2 (ν : Measure V))) ∧
      Tendsto (fun n => (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq n)
          (hqc n)).toLp (gradient (q n))) atTop
        (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, F.2.2⟩)) ∧
      Tendsto (fun n => (memLp_neg_weightedLaplacian (ν := ν) (hU.of_le (by decide)) (hq n)
          (hqc n)).toLp (fun x => -weightedLaplacian U (q n) x)) atTop
        (𝓝 (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) ∧
      Tendsto (fun n => (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν)
          (contDiff_weightedLaplacian hU (hq n) (by decide) (by decide)).neg
          (hasCompactSupport_weightedLaplacian U (hqc n)).neg).toLp
            (gradient (fun x => -weightedLaplacian U (q n) x))) atTop
        (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hF⟩)) := by
  revert F
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  intro F hF
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  have hzmem : (F : Lp ℝ 2 (ν : Measure V)) + adjointComp T F ∈ T.domain :=
    T.domain.add_mem F.2.2 hF
  set z : T.domain := ⟨_, hzmem⟩
  have hex (n : ℕ) := exists_toLp_add_adjointComp_graph_lt hνU hU z
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose q hq hqc hA hJ hlt using hex
  refine ⟨q, hq, hqc, ?_⟩
  set x : ℕ → (adjointComp T).domain := fun n => ⟨_, hA n⟩
  have hx (n : ℕ) : (adjointComp T (x n) : Lp ℝ 2 (ν : Measure V)) ∈ T.domain := by
    have h := T.domain.sub_mem (hJ n) (hA n).2
    simpa [x] using h
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsq₁ (a b : ℝ) : a ≤ √(a ^ 2 + b ^ 2) := by
    rcases le_or_gt a 0 with ha | ha
    · exact ha.trans (Real.sqrt_nonneg _)
    · calc a = √(a ^ 2) := (Real.sqrt_sq ha.le).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  have hsq₂ (a b : ℝ) : b ≤ √(a ^ 2 + b ^ 2) := by
    rw [add_comm]; exact hsq₁ b a
  have h₁ : Tendsto (fun n => (x n : Lp ℝ 2 (ν : Measure V)) + adjointComp T (x n)) atTop
      (𝓝 ((F : Lp ℝ 2 (ν : Measure V)) + adjointComp T F)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hε)
    exact ((hsq₁ _ _).trans_lt (hlt n)).le
  have hTJ (n : ℕ) : T ⟨(x n : Lp ℝ 2 (ν : Measure V)), (x n).2.2⟩ + T ⟨_, hx n⟩ =
      T ⟨_, hJ n⟩ := by
    rw [← LinearPMap.map_add]; rfl
  have hTz : T ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩ + T ⟨_, hF⟩ = T z := by
    rw [← LinearPMap.map_add]; rfl
  have h₂ : Tendsto (fun n => T ⟨(x n : Lp ℝ 2 (ν : Measure V)), (x n).2.2⟩ + T ⟨_, hx n⟩)
      atTop (𝓝 (T ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩ + T ⟨_, hF⟩)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hε)
    rw [hTJ, hTz]
    exact ((hsq₂ _ _).trans_lt (hlt n)).le
  obtain ⟨c₁, c₂, c₃, c₄⟩ := tendsto_of_tendsto_add_adjointComp
    (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) hx F hF h₁ h₂
  have hAx (n : ℕ) : adjointComp T (x n) =
      (memLp_neg_weightedLaplacian (ν := ν) hU1 (hq n) (hqc n)).toLp
        (fun y => -weightedLaplacian U (q n) y) :=
    hν.adjointComp_toLp_eq m hi hνU hU1 (hq n) (hqc n)
  have hL (n : ℕ) : ContDiff ℝ ∞ (fun y => -weightedLaplacian U (q n) y) :=
    (contDiff_weightedLaplacian hU (hq n) (by decide) (by decide)).neg
  have hLc (n : ℕ) : HasCompactSupport (fun y => -weightedLaplacian U (q n) y) :=
    (hasCompactSupport_weightedLaplacian U (hqc n)).neg
  refine ⟨c₁, ?_, ?_, ?_⟩
  · refine c₂.congr fun n => ?_
    exact hν.closedWeightedOperator_toLp_eq m hi (hq n) (hqc n)
  · exact c₃.congr hAx
  · refine c₄.congr fun n => ?_
    have hmem : (memLp_of_contDiff_hasCompactSupport ν (hL n) (hLc n)).toLp
        (fun y => -weightedLaplacian U (q n) y) ∈ T.domain :=
      hν.toLp_mem_closedWeightedOperator_domain m hi (hL n) (hLc n)
    have hc : (⟨_, hx n⟩ : T.domain) = ⟨_, hmem⟩ := by
      apply Subtype.ext
      simp only
      rw [hAx n]
    rw [hc]
    exact hν.closedWeightedOperator_toLp_eq m hi (hL n) (hLc n)

end Density

end FunctionalInequalities.KLS.LogConcave
