import FunctionalInequalities.Analysis.Hausdorff.SurfaceSlicing

/-!
# Strict audit client for the Eilenberg measurable majorant (obligation `L1`)

Independent client of `Analysis/Hausdorff/SurfaceSlicing.lean` and `Analysis/Hausdorff/Slicing.lean`.
`target` states the route's `L1` quantifier for quantifier — including its `∃ C : ℝ≥0, 0 < C` and
its `[Nontrivial V]` — and proves it; `target_of_trivial` proves the same conclusion with
`[Nontrivial V]` dropped, so the library statement is strictly stronger than `L1` asks.

The remaining declarations are consumers, not repetitions of the proof. `null_slicing` re-derives
`L2` from the majorant alone, without invoking the library's `L2`. `ae_ne_top` is a consequence
`L2` cannot give: on a set of finite volume, almost every slice has *finite* surface measure.
`constant_on_set` records that `K = 0` forces the majorant's integral to vanish even when
`volume S = ∞`, and `univ_without_finiteness` applies the bound with no finiteness hypothesis at
all. `eilenbergConstant_real` and `eilenbergConstant_euclidean_zero` compute the constant in two
dimensions, so it is an explicit number rather than an abstract existential.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal

namespace EilenbergMajorantAudit

/-! ### The obligation itself -/

-- The statement text of obligation `L1` of the weighted coarea route.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Nontrivial V], ∃ C : ℝ≥0, 0 < C ∧
    ∀ {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzOnWith K u S →
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, KLS.surfaceMeasure V (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ (C : ℝ≥0∞) * (K : ℝ≥0∞) * volume S)

/-- The route target, restated and proved. -/
theorem target : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Nontrivial V], ∃ C : ℝ≥0, 0 < C ∧
    ∀ {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzOnWith K u S →
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, KLS.surfaceMeasure V (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ (C : ℝ≥0∞) * (K : ℝ≥0∞) * volume S := by
  intro V _ _ _ _ _ _ _
  exact ⟨eilenbergConstant V, eilenbergConstant_pos V,
    fun hu => exists_measurable_majorant hu⟩

/-- The same conclusion without `[Nontrivial V]`: the library statement covers dimension zero,
where the natural-subtraction convention makes the fibre measure `ℋ⁰`, not the zero measure. -/
theorem target_of_trivial : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
    ∃ C : ℝ≥0, 0 < C ∧
    ∀ {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzOnWith K u S →
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, KLS.surfaceMeasure V (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ (C : ℝ≥0∞) * (K : ℝ≥0∞) * volume S := by
  intro V _ _ _ _ _ _
  exact ⟨eilenbergConstant V, eilenbergConstant_pos V,
    fun hu => exists_measurable_majorant hu⟩

/-! ### Consumers -/

section Consumers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- `L2` re-derived from the majorant alone: this proof does not use the library's
`ae_surfaceMeasure_inter_levelSet_eq_zero`, only `exists_measurable_majorant`.  Measurability of
the majorant — not of the slice function — is what makes `lintegral_eq_zero_iff` applicable. -/
theorem null_slicing {u : V → ℝ} {K : ℝ≥0} {N : Set V} (hu : LipschitzOnWith K u N)
    (hN : (volume : Measure V) N = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), surfaceMeasure V (N ∩ {x | u x = t}) = 0 := by
  obtain ⟨F, hFmeas, hFdom, hFint⟩ := exists_measurable_majorant hu
  rw [hN, mul_zero] at hFint
  filter_upwards [(lintegral_eq_zero_iff hFmeas).1 (le_antisymm hFint (by simp))] with t ht
  exact le_antisymm (by simpa [ht] using hFdom t) (by simp)

/-- A consequence the null-slicing statement cannot give: on a set of finite volume, almost every
slice has **finite** surface measure.  Only the integral bound of the majorant is used. -/
theorem ae_ne_top {u : V → ℝ} {K : ℝ≥0} {S : Set V} (hu : LipschitzOnWith K u S)
    (hS : (volume : Measure V) S ≠ ∞) :
    ∀ᵐ t ∂(volume : Measure ℝ), surfaceMeasure V (S ∩ {x | u x = t}) ≠ ∞ := by
  obtain ⟨F, hFmeas, hFdom, hFint⟩ := exists_measurable_majorant hu
  have hfin : ∫⁻ t, F t ∂(volume : Measure ℝ) ≠ ∞ :=
    ne_top_of_le_ne_top (by
      simp [ENNReal.mul_ne_top, hS, ENNReal.coe_ne_top]) hFint
  filter_upwards [ae_lt_top hFmeas hfin] with t ht
  exact ne_top_of_le_ne_top ht.ne ((hFdom t).trans le_rfl)

/-- `K = 0`: the bound forces the majorant's integral to vanish, even when `volume S = ∞`, because
the whole slice family is concentrated on the single level attained on `S`. -/
theorem constant_on_set (c : ℝ) {S : Set V} :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, surfaceMeasure V (S ∩ {x | (fun _ : V => c) x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) = 0 := by
  obtain ⟨F, hFmeas, hFdom, hFint⟩ :=
    exists_measurable_majorant (K := 0) (u := fun _ : V => c) (S := S)
      (LipschitzWith.const c).lipschitzOnWith
  refine ⟨F, hFmeas, hFdom, le_antisymm ?_ (by simp)⟩
  simpa using hFint

/-- No finiteness, boundedness or measurability hypothesis: the bound applies to `S = univ`. -/
theorem univ_without_finiteness {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, surfaceMeasure V (Set.univ ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ))
        ≤ (eilenbergConstant V : ℝ≥0∞) * (K : ℝ≥0∞) * volume (Set.univ : Set V) :=
  exists_measurable_majorant hu.lipschitzOnWith

end Consumers

/-! ### Null-slicing contracts, restated verbatim

Each null-slicing contract is restated verbatim
and discharged by the library declaration applied with **named** arguments, so a renamed binder or
a changed hypothesis order would fail to elaborate here. -/

theorem preserved_exists_cover_of_hausdorffMeasure_eq_zero :
    ∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
      {d : ℝ} {N : Set X}, μH[d] N = 0 → ∀ {r c : ℝ≥0∞}, 0 < r → 0 < c →
      ∃ T : ℕ → Set X, N ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ r) ∧
        ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d < c := by
  intro X _ _ _ d N hN r c hr hc
  exact Analysis.exists_cover_of_hausdorffMeasure_eq_zero (d := d) (N := N) (r := r) (c := c) hN hr hc

theorem preserved_exists_levelSlab :
    ∀ {X : Type*} [EMetricSpace X] {u : X → ℝ} {K : ℝ≥0} {N : Set X},
      LipschitzOnWith K u N → ∀ (T : ℕ → Set X), (∀ i, Metric.ediam (T i) ≠ ∞) →
      ∃ J : ℕ → Set ℝ, (∀ i, MeasurableSet (J i)) ∧
        (∀ i, volume (J i) ≤ 2 * (K : ℝ≥0∞) * Metric.ediam (T i)) ∧
        (∀ i, ∀ x ∈ T i ∩ N, u x ∈ J i) := by
  intro X _ u K N hu T hT
  exact Analysis.exists_levelSlab (u := u) (K := K) (N := N) hu T hT

theorem preserved_ae_hausdorffMeasure_inter_levelSet_eq_zero :
    ∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
      {u : X → ℝ} {K : ℝ≥0} {N : Set X} {d : ℝ}, 0 ≤ d → LipschitzOnWith K u N →
      μH[d + 1] N = 0 →
      ∀ᵐ t ∂(volume : Measure ℝ), μH[d] (N ∩ {x | u x = t}) = 0 := by
  intro X _ _ _ u K N d hd hu hN
  exact Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero
    (u := u) (K := K) (N := N) (d := d) hd hu hN

theorem preserved_ae_surfaceMeasure_inter_levelSet_eq_zero :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V] {u : V → ℝ} {K : ℝ≥0} {N : Set V},
      LipschitzOnWith K u N → (volume : Measure V) N = 0 →
      ∀ᵐ t ∂(volume : Measure ℝ), surfaceMeasure V (N ∩ {x | u x = t}) = 0 := by
  intro V _ _ _ _ _ u K N hu hN
  exact ae_surfaceMeasure_inter_levelSet_eq_zero (u := u) (K := K) (N := N) hu hN

/-! ### The constant is explicit -/

/-- On the line the constant is `4 ω₀ / ω₁ = 4 / 2 = 2`. -/
theorem eilenbergConstant_real : eilenbergConstant ℝ = 2 := by
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hω1 : unitBallVolume 1 = 2 := by
    rw [unitBallVolume, Nat.cast_one, pow_one, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    field_simp
  have hω0 : unitBallVolume 0 = 1 := by simp [unitBallVolume]
  have hn : Module.finrank ℝ ℝ = 1 := by simp
  rw [eilenbergConstant, hn]
  norm_num [hω0, hω1]

/-- In dimension zero the natural subtraction gives `4 ω₀ / ω₀ = 4`. -/
theorem eilenbergConstant_euclidean_zero :
    eilenbergConstant (EuclideanSpace ℝ (Fin 0)) = 4 := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) = 0 := by simp
  rw [eilenbergConstant, hn]
  norm_num [unitBallVolume]

/-! ### Axiom audit -/

#print axioms FunctionalInequalities.Analysis.exists_measurable_majorant_of_eqOn
#print axioms FunctionalInequalities.Analysis.exists_cover_cost_lt
#print axioms FunctionalInequalities.Analysis.exists_cover_of_hausdorffMeasure_eq_zero
#print axioms FunctionalInequalities.Analysis.exists_levelSlab
#print axioms FunctionalInequalities.Analysis.exists_measurable_majorant
#print axioms FunctionalInequalities.Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero
#print axioms FunctionalInequalities.KLS.eilenbergConstant
#print axioms FunctionalInequalities.KLS.coe_eilenbergConstant
#print axioms FunctionalInequalities.KLS.eilenbergConstant_pos
#print axioms FunctionalInequalities.KLS.exists_measurable_majorant
#print axioms FunctionalInequalities.KLS.ae_surfaceMeasure_inter_levelSet_eq_zero
#print axioms EilenbergMajorantAudit.target
#print axioms EilenbergMajorantAudit.target_of_trivial
#print axioms EilenbergMajorantAudit.null_slicing
#print axioms EilenbergMajorantAudit.ae_ne_top
#print axioms EilenbergMajorantAudit.constant_on_set
#print axioms EilenbergMajorantAudit.univ_without_finiteness
#print axioms EilenbergMajorantAudit.eilenbergConstant_real
#print axioms EilenbergMajorantAudit.eilenbergConstant_euclidean_zero
#print axioms EilenbergMajorantAudit.preserved_exists_cover_of_hausdorffMeasure_eq_zero
#print axioms EilenbergMajorantAudit.preserved_exists_levelSlab
#print axioms EilenbergMajorantAudit.preserved_ae_hausdorffMeasure_inter_levelSet_eq_zero
#print axioms EilenbergMajorantAudit.preserved_ae_surfaceMeasure_inter_levelSet_eq_zero

end EilenbergMajorantAudit
