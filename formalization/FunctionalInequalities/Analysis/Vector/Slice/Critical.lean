import FunctionalInequalities.Analysis.Vector.Slice.Measurable
import FunctionalInequalities.Analysis.Vector.Coarea.Regular
import Mathlib.MeasureTheory.Function.Jacobian

/-! # The vanishing-derivative part of a `C¹` map has null level slices

The codimension-`m` analogue of `KLS/Geometry/Slice/Critical.lean`, for the part of the critical set
where the derivative **vanishes**.

`KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero` proves that for a real-valued `C¹` function
almost every level meets `{x | fderiv ℝ u x = 0}` in an `ℋ^{n-1}`-null set.  Its proof is the first
consumer of the Eilenberg bound: on that set the derivative vanishes, so Mathlib's approximating
partition covers it by countably many disjoint measurable pieces on which `u` is `ε`-Lipschitz, and
the Eilenberg bound on each piece gives a majorant whose integral tends to `0` with `ε`.

**The same argument works verbatim in codimension `m`**, with the codimension-`m` Eilenberg bound of
`Analysis/Vector/Slice/Hausdorff.lean`: the constant becomes `volume (closedBall 0 1) · ε ^ m`, and
`ε ^ m → 0` because `m ≥ 1`.  The positivity of `m` is genuinely needed and is a hypothesis: with a
zero-dimensional target every derivative vanishes, the "critical" set is everything, and the slice
is the whole set.

**This is not the full critical set when `m ≥ 2`.**  For a map into an `m`-dimensional target the
coarea formula's critical set is `{x | fderiv ℝ u x` is not surjective`}`, that is, where the rank
drops below `m`; the vanishing-derivative set is strictly smaller as soon as `m ≥ 2`.  The argument
here **does not** extend to the rank-deficient part: it rests on `u` being `ε`-Lipschitz on the
pieces, which needs the derivative to vanish, not merely to be non-surjective.  The rank-deficient
part needs an iterated slicing along the surviving directions, and **nothing about it is proved
here**.  For `m = 1` the two sets coincide, and the audit recovers the scalar statement.

**No Sard theorem is claimed.**  Nothing is asserted about the measure of the set of critical
*values*, which for a merely `C¹` map may well be positive.
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.Analysis

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

section Critical

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] in
/-- The vanishing-derivative set of a `C¹` map is closed: the derivative is continuous. -/
theorem isClosed_zeroDeriv {u : V → W} (hu : ContDiff ℝ 1 u) :
    IsClosed {x : V | fderiv ℝ u x = 0} :=
  isClosed_eq (hu.continuous_fderiv one_ne_zero) continuous_const

omit [MeasurableSpace W] [BorelSpace W] in
/-- Countably many pairwise disjoint measurable pieces covering the vanishing-derivative set, on
each of which `u` is `ε`-Lipschitz.  The approximating linear maps of
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` are values of the derivative, which
vanishes on that set, so the linear part drops out and the approximation becomes a genuine Lipschitz
estimate.  **This is the step that fails for a merely rank-deficient derivative.** -/
theorem exists_lipschitzOnWith_zeroDeriv_cover {u : V → W} (hu : ContDiff ℝ 1 u) {ε : ℝ≥0}
    (hε : ε ≠ 0) :
    ∃ T : ℕ → Set V, Pairwise (Function.onFun Disjoint T) ∧ (∀ n, MeasurableSet (T n)) ∧
      {x : V | fderiv ℝ u x = 0} ⊆ ⋃ n, T n ∧
      ∀ n, LipschitzOnWith ε u ({x : V | fderiv ℝ u x = 0} ∩ T n) := by
  rcases Set.eq_empty_or_nonempty {x : V | fderiv ℝ u x = 0} with hC | hC
  · refine ⟨fun _ => ∅, fun i j _ => by simp, fun _ => MeasurableSet.empty, by simp [hC], ?_⟩
    intro n
    simp only [Set.inter_empty]
    exact LipschitzOnWith.of_dist_le_mul fun x hx => absurd hx (Set.notMem_empty x)
  obtain ⟨T, A, hdisj, hmeas, hcov, happrox, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u {x : V | fderiv ℝ u x = 0}
      (fderiv ℝ u) (fun x _ => ((hu.differentiable one_ne_zero) x).hasFDerivAt.hasFDerivWithinAt)
      (fun _ => ε) (fun _ => hε)
  refine ⟨T, hdisj, hmeas, hcov, fun n => ?_⟩
  obtain ⟨y, hy, hAy⟩ := hA hC n
  have hA0 : A n = 0 := by rw [hAy]; exact hy
  refine LipschitzOnWith.of_dist_le_mul fun x hx y' hy' => ?_
  have h := happrox n x hx y' hy'
  rw [hA0] at h
  simpa [dist_eq_norm] using h

/-- The vanishing-derivative slices inside a fixed ball are null at almost every level. -/
theorem ae_hausdorffMeasure_zeroDeriv_ball_eq_zero {u : V → W} (hu : ContDiff ℝ 1 u) {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hm : 0 < finrank ℝ W) (R : ℕ) :
    ∀ᵐ t ∂(volume : Measure W),
      μH[(k : ℝ)] ({x : V | fderiv ℝ u x = 0} ∩ Metric.closedBall 0 R ∩ {x | u x = t}) = 0 := by
  set m : ℕ := finrank ℝ W with hmdef
  set C : Set V := {x : V | fderiv ℝ u x = 0} with hC
  set B : Set V := Metric.closedBall (0 : V) R with hB
  set c : ℝ≥0∞ := (volume : Measure W) (Metric.closedBall (0 : W) 1) with hc
  have hctop : c ≠ (⊤ : ℝ≥0∞) := measure_closedBall_lt_top.ne
  have hCmeas : MeasurableSet C := (isClosed_zeroDeriv hu).measurableSet
  have hBmeas : MeasurableSet B := measurableSet_closedBall
  have hcast : ((k : ℝ) + (m : ℝ)) = ((finrank ℝ V : ℕ) : ℝ) := by
    rw [← hk]; push_cast; ring
  have hBtop : μH[((finrank ℝ V : ℕ) : ℝ)] B ≠ (⊤ : ℝ≥0∞) := by
    rw [hausdorffMeasure_finrank_eq_smul_volume V, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  -- A majorant at each scale `(j + 1)⁻¹`.
  have hscale : ∀ j : ℕ, ∃ G : W → ℝ≥0∞, Measurable G ∧
      (∀ t, μH[(k : ℝ)] (C ∩ B ∩ {x | u x = t}) ≤ G t) ∧
      (∫⁻ t, G t ∂(volume : Measure W))
        ≤ c * μH[((finrank ℝ V : ℕ) : ℝ)] B * (((j : ℝ≥0∞) + 1)⁻¹) ^ m := by
    intro j
    obtain ⟨T, hdisj, hTmeas, hcov, hlip⟩ :=
      exists_lipschitzOnWith_zeroDeriv_cover hu (ε := ((j : ℝ≥0) + 1)⁻¹) (by positivity)
    set D : ℕ → Set V := fun n => C ∩ B ∩ T n with hD
    have hDmeas : ∀ n, MeasurableSet (D n) := fun n => (hCmeas.inter hBmeas).inter (hTmeas n)
    have hDdisj : Pairwise (Function.onFun Disjoint D) := fun i j' hij =>
      ((hdisj hij).mono Set.inter_subset_right Set.inter_subset_right)
    have hDunion : ⋃ n, D n = C ∩ B := by
      refine Set.Subset.antisymm (Set.iUnion_subset fun n => Set.inter_subset_left) fun x hx => ?_
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hcov hx.1)
      exact Set.mem_iUnion.2 ⟨n, hx, hn⟩
    choose F hFmeas hFdom hFint using fun n =>
      exists_measurable_majorant_vector (u := u) (S := D n) (d := (k : ℝ)) (Nat.cast_nonneg k)
        ((hlip n).mono (fun x hx => ⟨hx.1.1, hx.2⟩))
    refine ⟨fun t => ∑' n, F n t, ?_, fun t => ?_, ?_⟩
    · simp only [ENNReal.tsum_eq_iSup_sum]
      exact Measurable.iSup fun s => Finset.measurable_sum s fun n _ => hFmeas n
    · calc μH[(k : ℝ)] (C ∩ B ∩ {x | u x = t})
          = μH[(k : ℝ)] (⋃ n, D n ∩ {x | u x = t}) := by
            rw [← Set.iUnion_inter, hDunion]
        _ ≤ ∑' n, μH[(k : ℝ)] (D n ∩ {x | u x = t}) := measure_iUnion_le _
        _ ≤ ∑' n, F n t := ENNReal.tsum_le_tsum fun n => hFdom n t
    · rw [lintegral_tsum fun n => (hFmeas n).aemeasurable]
      have hterm : ∀ n, (∫⁻ t, F n t ∂(volume : Measure W))
          ≤ c * (((j : ℝ≥0∞) + 1)⁻¹) ^ m * μH[((finrank ℝ V : ℕ) : ℝ)] (D n) := by
        intro n
        refine (hFint n).trans (le_of_eq ?_)
        rw [hcast]
        congr 2
        rw [ENNReal.coe_inv (by positivity)]
        push_cast
        ring
      calc ∑' n, ∫⁻ t, F n t ∂(volume : Measure W)
          ≤ ∑' n, c * (((j : ℝ≥0∞) + 1)⁻¹) ^ m * μH[((finrank ℝ V : ℕ) : ℝ)] (D n) :=
            ENNReal.tsum_le_tsum hterm
        _ = c * (((j : ℝ≥0∞) + 1)⁻¹) ^ m * μH[((finrank ℝ V : ℕ) : ℝ)] (C ∩ B) := by
            rw [ENNReal.tsum_mul_left, ← measure_iUnion hDdisj hDmeas, hDunion]
        _ ≤ c * μH[((finrank ℝ V : ℕ) : ℝ)] B * (((j : ℝ≥0∞) + 1)⁻¹) ^ m := by
            rw [mul_assoc, mul_assoc, mul_comm ((((j : ℝ≥0∞) + 1)⁻¹) ^ m)]
            gcongr
            exact Set.inter_subset_right
  choose G hGmeas hGdom hGint using hscale
  -- The pointwise infimum is a measurable majorant of integral zero.
  have hHzero : ∫⁻ t, ⨅ j : ℕ, G j t ∂(volume : Measure W) = 0 := by
    have hinv : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have h : (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) = fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
        funext j; norm_cast
      rw [h]
      exact ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hpow : Tendsto (fun j : ℕ => (((j : ℝ≥0∞) + 1)⁻¹) ^ m) atTop (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) ^ m = 0 := zero_pow (by omega)
      have := (ENNReal.continuous_pow m).continuousAt.tendsto.comp hinv
      rw [h0] at this
      simpa [Function.comp_def] using this
    have htend : Tendsto
        (fun j : ℕ => c * μH[((finrank ℝ V : ℕ) : ℝ)] B * (((j : ℝ≥0∞) + 1)⁻¹) ^ m)
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := c * μH[((finrank ℝ V : ℕ) : ℝ)] B) hpow
        (Or.inr (by simp [ENNReal.mul_eq_top, hctop, hBtop]))
      simpa using this
    refine le_antisymm (ge_of_tendsto' htend fun j => ?_) (by simp)
    exact (lintegral_mono fun t => iInf_le _ j).trans (hGint j)
  filter_upwards [(lintegral_eq_zero_iff (Measurable.iInf hGmeas)).1 hHzero] with t ht
  refine le_antisymm ?_ (by simp)
  simpa [ht] using le_iInf fun j => hGdom j t

/-- **The vanishing-derivative part of almost every level is null**, in codimension `m`.

Not Sard's theorem: nothing is claimed about the measure of the set of critical *values*.  And not
the full critical set when `m ≥ 2`: the rank-deficient part is not covered. -/
theorem ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero {u : V → W} (hu : ContDiff ℝ 1 u)
    {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) (hm : 0 < finrank ℝ W) :
    ∀ᵐ t ∂(volume : Measure W),
      μH[(k : ℝ)] ({x : V | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0 := by
  filter_upwards [(ae_all_iff (ι := ℕ)).2 fun R =>
    ae_hausdorffMeasure_zeroDeriv_ball_eq_zero hu hk hm R] with t ht
  have hsplit : {x : V | fderiv ℝ u x = 0} ∩ {x | u x = t}
      = ⋃ R : ℕ, ({x : V | fderiv ℝ u x = 0} ∩ Metric.closedBall 0 R ∩ {x | u x = t}) := by
    rw [← Set.iUnion_inter, ← Set.inter_iUnion, Metric.iUnion_closedBall_nat, Set.inter_univ]
  rw [hsplit]
  exact measure_iUnion_null ht

/-- The normalized form, which the codimension-`m` coarea layer consumes. -/
theorem ae_hausdorffNormalized_zeroDeriv_inter_levelSet_eq_zero {u : V → W} (hu : ContDiff ℝ 1 u)
    {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) (hm : 0 < finrank ℝ W) :
    ∀ᵐ t ∂(volume : Measure W),
      KLS.hausdorffNormalized V k ({x : V | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0 := by
  filter_upwards [ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero hu hk hm] with t ht
  exact (hausdorffNormalized_eq_zero_iff (V := V) k _).2 ht

omit [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W] in
/-- The regular set of a `C¹` map is open. -/
theorem isOpen_coareaJacobian_ne_zero {u : V → W} (hu : ContDiff ℝ 1 u) :
    IsOpen {x : V | coareaJacobian (fderiv ℝ u x) ≠ 0} :=
  isOpen_ne_fun (continuous_coareaJacobian.comp (hu.continuous_fderiv one_ne_zero))
    continuous_const

/-- **Codimension-`m` coarea when the derivative vanishes wherever it fails to be surjective.**
Under that hypothesis the critical set is exactly the vanishing-derivative set, whose slices are
null by the theorem above, so the regular-case formula extends to the whole space.

For `m = 1` the hypothesis is **automatic** — a real differential is surjective exactly when it is
nonzero — so this is the codimension-one C¹ coarea in that case.  For `m ≥ 2` it is a genuine
restriction: it excludes intermediate ranks, and the rank-deficient part is **not** covered by
anything proved here. -/
theorem coarea_of_contDiff_of_critical_eq_zeroDeriv {S : Set V} {u : V → W} {g : V → ℝ≥0∞}
    {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) (hm : 0 < finrank ℝ W) (hu : ContDiff ℝ 1 u)
    (hcrit : ∀ x : V, coareaJacobian (fderiv ℝ u x) ≠ 0 ∨ fderiv ℝ u x = 0)
    (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) ∧
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
          ∂(volume : Measure W)) := by
  set ν : Measure V := KLS.hausdorffNormalized V k with hν
  set R : Set V := {x : V | coareaJacobian (fderiv ℝ u x) ≠ 0} with hR
  have hRopen : IsOpen R := isOpen_coareaJacobian_ne_zero hu
  have hRmeas : MeasurableSet R := hRopen.measurableSet
  have hkdim : k = finrank ℝ V - finrank ℝ W := by omega
  -- measurability, with no regularity hypothesis
  have hmeas : AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x | u x = t}, g y ∂ν)
      (volume : Measure W) :=
    aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector hk isOpen_univ hu.contDiffOn hS
      (Set.subset_univ S) hg
  refine ⟨hmeas, ?_⟩
  -- the regular part
  obtain ⟨-, heqR⟩ := coarea_of_contDiffOn_of_coareaJacobian_ne_zero (O := R) (S := S ∩ R)
    hRopen hu.contDiffOn (fun _ hx => hx) (hS.inter hRmeas) Set.inter_subset_right hg
  rw [← hkdim] at heqR
  -- the ambient integral sees only the regular part
  have hleft : (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
        ∂(volume : Measure V))
      = ∫⁻ x in S ∩ R, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
        ∂(volume : Measure V) := by
    rw [← lintegral_inter_add_sdiff _ _ hRmeas]
    have hzero : (∫⁻ x in S \ R, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
        ∂(volume : Measure V)) = 0 := by
      refine setLIntegral_eq_zero (hS.diff hRmeas) fun x hx => ?_
      have h0 : coareaJacobian (fderiv ℝ u x) = 0 := by
        by_contra hne
        exact hx.2 hne
      simp [h0]
    rw [hzero, add_zero]
  -- the fibre integral sees only the regular part, at almost every level
  have hright : ∀ᵐ t ∂(volume : Measure W),
      (∫⁻ y in S ∩ {x | u x = t}, g y ∂ν) = ∫⁻ y in (S ∩ R) ∩ {x | u x = t}, g y ∂ν := by
    filter_upwards [ae_hausdorffNormalized_zeroDeriv_inter_levelSet_eq_zero hu hk hm] with t ht
    refine setLIntegral_congr ?_
    have hsub : (S ∩ {x | u x = t}) \ ((S ∩ R) ∩ {x | u x = t})
        ⊆ {x : V | fderiv ℝ u x = 0} ∩ {x | u x = t} := by
      rintro x ⟨⟨hxS, hxt⟩, hxn⟩
      refine ⟨?_, hxt⟩
      rcases hcrit x with hreg | hzero
      · exact absurd ⟨⟨hxS, hreg⟩, hxt⟩ hxn
      · exact hzero
    have hempty : ((S ∩ R) ∩ {x | u x = t}) \ (S ∩ {x | u x = t}) = ∅ := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      tauto
    exact MeasureTheory.ae_eq_set.2 ⟨measure_mono_null hsub ht, by rw [hempty]; simp⟩
  calc (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V))
      = ∫⁻ x in S ∩ R, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
          ∂(volume : Measure V) := hleft
    _ = ∫⁻ t, ∫⁻ y in (S ∩ R) ∩ {x | u x = t}, g y ∂ν ∂(volume : Measure W) := heqR
    _ = ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂ν ∂(volume : Measure W) :=
        lintegral_congr_ae (hright.mono fun t ht => ht.symm)

end Critical

end FunctionalInequalities.Analysis
