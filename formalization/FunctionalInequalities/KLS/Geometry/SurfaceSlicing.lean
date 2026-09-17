import FunctionalInequalities.Analysis.HausdorffSlicing
import FunctionalInequalities.Analysis.HausdorffContent
import FunctionalInequalities.KLS.Geometry.SmoothDomain

/-!
# Eilenberg slicing bound and compact-slice measurability in the normalized surface measure

Normalized wrapper of `Analysis.exists_measurable_majorant` and of
`Analysis.measurable_hausdorffMeasure_inter_levelSet` for the codimension-one
`KLS.surfaceMeasure` of `KLS/Geometry/SurfaceMeasure.lean`.  The measure and the conclusions are
unchanged: `surfaceMeasure V` stays `(ω_{n-1} / 2^{n-1}) • μH[n-1]` with the repository's
natural-subtraction convention, and the two statements are a genuine measurable majorant for the
slice function and a genuine almost-everywhere vanishing of the slice measure, not statements about
a substitute measure.

`exists_measurable_majorant` carries the explicit constant `eilenbergConstant V = 4 ω_{n-1} / ω_n`,
which is positive in every dimension (`eilenbergConstant_pos`); it is `2` in Mathlib's
diameter-gauge normalization, rescaled once for the fibre measure and once for the ambient measure.
Above dimension zero `Analysis.hausdorffMeasure_finrank_eq_smul_volume` turns the ambient
`μH[n] S` into `(2^n / ω_n) • volume S`, and `(n - 1 : ℕ) + 1 = n` in `ℝ` because `1 ≤ n`.  In
dimension zero the natural subtraction gives `surfaceMeasure V = hausdorffNormalized V 0`, the
space is a subsingleton, so `u` is constant on `S` and the one-point majorant of
`Analysis.exists_measurable_majorant_of_eqOn` applies with integral zero.  Dimension zero is
therefore not treated by declaring `ℋ⁰` to be the zero measure — it is the counting measure of a
one-point space — and no nondegeneracy of `V` is required.

`ae_surfaceMeasure_inter_levelSet_eq_zero` is the null case: a Lebesgue-null `S` makes the bound
vanish, and the majorant — unlike the slice function — is measurable, so `lintegral_eq_zero_iff`
applies.  `S` is not assumed measurable, bounded or nonempty, `u` is Lipschitz on `S` only, and
`K = 0` is allowed.  `CompleteSpace V` is not among the hypotheses because it is never used; a
caller that has it available applies the statements unchanged.

`measurable_surfaceMeasure_inter_levelSet` is the separate compact-slice statement: for `S`
**compact** and `u` merely continuous, the slice measure is a Borel measurable function of the
level.  It is not a consequence of the majorant bound — that bound says nothing about the slice
function's measurability — and it is proved in `Analysis/HausdorffContent.lean` through the
scalewise open-cover costs, whose scale limit is `μH[d]` and each of which is upper semicontinuous
in the level.  Only the positive normalizing scalar is added here, so no dimension split is
needed. The later declarations in this module prove the Borel-set bridge L4 and
measurable-weight version L5, with almost-everywhere measurability under a Lipschitz bound on
the set. `LevelSetMeasurable` exposes L5 at `S = Set.univ` under the original Analysis name.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities.KLS

universe u

section Constant

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The constant `4 ω_{n-1} / ω_n` of the normalized codimension-one slicing bound: Mathlib's
diameter-gauge constant `2`, rescaled by `ω_{n-1} / 2^{n-1}` for the fibre measure and by
`2^n / ω_n` for the ambient measure.  No sharpness is claimed. -/
def eilenbergConstant : ℝ≥0 :=
  Real.toNNReal (4 * unitBallVolume (Module.finrank ℝ V - 1) / unitBallVolume (Module.finrank ℝ V))

@[simp]
theorem coe_eilenbergConstant : (eilenbergConstant V : ℝ≥0∞)
    = ENNReal.ofReal (4 * unitBallVolume (Module.finrank ℝ V - 1)
        / unitBallVolume (Module.finrank ℝ V)) := rfl

theorem eilenbergConstant_pos : 0 < eilenbergConstant V := by
  rw [eilenbergConstant, Real.toNNReal_pos]
  unfold unitBallVolume
  positivity

end Constant

section Slicing

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **Eilenberg slicing bound for the surface measure.**  For `u` Lipschitz on `S`, the slice
function `t ↦ surfaceMeasure V (S ∩ {u = t})` is dominated by a measurable `F` with
`∫⁻ F ≤ eilenbergConstant V * K * volume S`.

The measurability of `F` is part of the conclusion and is not assumed of the slice function, which
is not known to be measurable at this point of the development.  `S` is not assumed measurable,
bounded or nonempty, `u` is Lipschitz on `S` only, `K = 0` is allowed, `volume S = ∞` is allowed,
and `V` may be zero-dimensional. -/
theorem exists_measurable_majorant {u : V → ℝ} {K : ℝ≥0} {S : Set V}
    (hu : LipschitzOnWith K u S) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, surfaceMeasure V (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ))
        ≤ (eilenbergConstant V : ℝ≥0∞) * (K : ℝ≥0∞) * volume S := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with hn | hn
  · -- Dimension zero: the space is a subsingleton, so `u` is constant on `S`.
    have : Subsingleton V := Module.finrank_zero_iff.1 hn
    obtain ⟨F, hFmeas, hFdom, hFint⟩ :=
      Analysis.exists_measurable_majorant_of_eqOn (μ := surfaceMeasure V) (u := u) (S := S)
        fun x _ y _ => by rw [Subsingleton.elim x y]
    exact ⟨F, hFmeas, hFdom, by rw [hFint]; simp⟩
  -- Positive dimension: rescale the raw Hausdorff bound on both sides.
  set m : ℕ := Module.finrank ℝ V - 1 with hm
  have hmn : Module.finrank ℝ V = m + 1 := by rw [hm]; omega
  have hd : ((m : ℝ)) + 1 = (Module.finrank ℝ V : ℝ) := by rw [hmn]; push_cast; ring
  have hωm : 0 < unitBallVolume m := by unfold unitBallVolume; positivity
  have hωn : 0 < unitBallVolume (Module.finrank ℝ V) := by unfold unitBallVolume; positivity
  obtain ⟨F, hFmeas, hFdom, hFint⟩ :=
    Analysis.exists_measurable_majorant (X := V) (d := (m : ℝ)) (Nat.cast_nonneg m) hu
  refine ⟨fun t => ENNReal.ofReal (unitBallVolume m / 2 ^ m) * F t,
    measurable_const.mul hFmeas, fun t => ?_, ?_⟩
  · dsimp only
    rw [surfaceMeasure, ← hm, hausdorffNormalized, Measure.smul_apply, smul_eq_mul]
    gcongr
    exact hFdom t
  · have hcoe : (eilenbergConstant V : ℝ≥0∞)
        = ENNReal.ofReal (unitBallVolume m / 2 ^ m) * 2
          * ENNReal.ofReal (2 ^ Module.finrank ℝ V / unitBallVolume (Module.finrank ℝ V)) := by
      rw [coe_eilenbergConstant, ← hm, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hmn, pow_succ]
      field_simp
      ring
    rw [lintegral_const_mul _ hFmeas, hcoe]
    have hvol : μH[(m : ℝ) + 1] S
        = ENNReal.ofReal (2 ^ Module.finrank ℝ V / unitBallVolume (Module.finrank ℝ V))
          * volume S := by
      rw [hd, Analysis.hausdorffMeasure_finrank_eq_smul_volume V, Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal (unitBallVolume m / 2 ^ m) * ∫⁻ t, F t ∂(volume : Measure ℝ)
        ≤ ENNReal.ofReal (unitBallVolume m / 2 ^ m) * (2 * (K : ℝ≥0∞) * μH[(m : ℝ) + 1] S) :=
          by gcongr
      _ = ENNReal.ofReal (unitBallVolume m / 2 ^ m) * 2
            * ENNReal.ofReal (2 ^ Module.finrank ℝ V / unitBallVolume (Module.finrank ℝ V))
            * (K : ℝ≥0∞) * volume S := by rw [hvol]; ring

/-- **Null slicing for the surface measure.**  A Lebesgue-null set has `surfaceMeasure`-null slices
along almost every level of a function that is Lipschitz on that set.

Rademacher's theorem does not give this: almost-everywhere differentiability is a statement about
a volume-null set of bad points, not about the codimension-one measure of individual level sets.
This is the null case of `exists_measurable_majorant`, whose majorant is measurable even though the
slice function is not known to be. -/
theorem ae_surfaceMeasure_inter_levelSet_eq_zero {u : V → ℝ} {K : ℝ≥0} {N : Set V}
    (hu : LipschitzOnWith K u N) (hN : (volume : Measure V) N = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), surfaceMeasure V (N ∩ {x | u x = t}) = 0 := by
  obtain ⟨F, hFmeas, hFdom, hFint⟩ := exists_measurable_majorant hu
  rw [hN, mul_zero] at hFint
  filter_upwards [(lintegral_eq_zero_iff hFmeas).1 (le_antisymm hFint (by simp))] with t ht
  exact le_antisymm (by simpa [ht] using hFdom t) (by simp)

omit [FiniteDimensional ℝ V] in
/-- **Compact slices are measurable in the surface measure.**  For `S` compact and `u` continuous,
`t ↦ surfaceMeasure V (S ∩ {u = t})` is Borel measurable.

No Lipschitz hypothesis on `u`, no finiteness of any measure of `S`, and no nondegeneracy of `V`:
the normalizing scalar of `surfaceMeasure` multiplies the raw statement of
`Analysis.measurable_hausdorffMeasure_inter_levelSet` in every dimension, natural subtraction
included.  `FiniteDimensional ℝ V` is not needed either, since `surfaceMeasure` only reads
`Module.finrank`.  This is a statement about compact `S` only. -/
theorem measurable_surfaceMeasure_inter_levelSet {u : V → ℝ} {S : Set V}
    (hu : Continuous u) (hS : IsCompact S) :
    Measurable fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t}) := by
  have hrw : (fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t}))
      = fun t : ℝ => ENNReal.ofReal (unitBallVolume (Module.finrank ℝ V - 1)
            / 2 ^ (Module.finrank ℝ V - 1))
          * μH[((Module.finrank ℝ V - 1 : ℕ) : ℝ)] (S ∩ {x | u x = t}) := by
    funext t
    rw [surfaceMeasure, hausdorffNormalized, Measure.smul_apply, smul_eq_mul]
  rw [hrw]
  exact measurable_const.mul
    (Analysis.measurable_hausdorffMeasure_inter_levelSet (Nat.cast_nonneg _) hS hu)


/-! ### Borel sets and measurable weights -/

/-- Inner regularity of Lebesgue measure: a measurable set carries a countable family of compact
subsets whose union misses only a Lebesgue-null part of it.  Infinite volume is handled by the
compact exhaustion of the space, so no finiteness hypothesis is needed. -/
theorem exists_isCompact_seq_volume_sdiff_eq_zero {S : Set V} (hS : MeasurableSet S) :
    ∃ C : ℕ → Set V, (∀ n, IsCompact (C n)) ∧ (∀ n, C n ⊆ S) ∧
      (volume : Measure V) (S \ ⋃ n, C n) = 0 := by
  have hmeas : ∀ m : ℕ, MeasurableSet (S ∩ compactCovering V m) := fun m =>
    hS.inter (isCompact_compactCovering V m).isClosed.measurableSet
  have hfin : ∀ m : ℕ, (volume : Measure V) (S ∩ compactCovering V m) ≠ ∞ := fun m =>
    ne_top_of_le_ne_top (isCompact_compactCovering V m).measure_lt_top.ne
      (measure_mono Set.inter_subset_right)
  choose C' hC'sub hC'compact _ hC'lt using fun m k : ℕ =>
    (hmeas m).exists_isCompact_isClosed_sdiff_lt (hfin m)
      (ε := ((k : ℝ≥0∞) + 1)⁻¹) (ENNReal.inv_pos.2 (by simp)).ne'
  set C : ℕ → Set V := fun n => C' n.unpair.1 n.unpair.2 with hC
  refine ⟨C, fun n => hC'compact _ _, fun n => (hC'sub _ _).trans Set.inter_subset_left, ?_⟩
  have hnull : ∀ m : ℕ, (volume : Measure V) ((S ∩ compactCovering V m) \ ⋃ n, C n) = 0 := by
    intro m
    have hle : ∀ k : ℕ,
        (volume : Measure V) ((S ∩ compactCovering V m) \ ⋃ n, C n) ≤ ((k : ℝ≥0∞) + 1)⁻¹ := by
      intro k
      refine le_trans (measure_mono (Set.sdiff_subset_sdiff_right ?_)) (hC'lt m k).le
      exact Set.subset_iUnion_of_subset (Nat.pair m k) (by simp [hC])
    by_contra hne
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hne
    exact absurd ((hle k).trans (ENNReal.inv_le_inv.2 (by simp))) (not_le.2 hk)
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hnull)
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (iUnion_compactCovering V ▸ Set.mem_univ x)
  exact Set.mem_iUnion.2 ⟨m, ⟨⟨hx.1, hm⟩, hx.2⟩⟩

/-- **Measurable sets have almost everywhere measurable slices.**  For `S` measurable and `u`
continuous and Lipschitz on `S`, the slice function is almost everywhere equal to an explicit
measurable function: the supremum of the slice measures of an increasing sequence of compact
subsets of `S`.

Both proved ingredients are used and neither suffices alone: the compact pieces are handled by
`measurable_surfaceMeasure_inter_levelSet` and the Lebesgue-null remainder by
`ae_surfaceMeasure_inter_levelSet_eq_zero`.  `S` is not assumed bounded, nonempty or of finite
volume, `u` is Lipschitz on `S` only, `K = 0` is allowed, and `V` may be zero-dimensional. -/
theorem aemeasurable_surfaceMeasure_inter_levelSet {u : V → ℝ} {K : ℝ≥0} {S : Set V}
    (hc : Continuous u) (hu : LipschitzOnWith K u S) (hS : MeasurableSet S) :
    AEMeasurable (fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t})) (volume : Measure ℝ) := by
  obtain ⟨C, hCcompact, hCsub, hCnull⟩ := exists_isCompact_seq_volume_sdiff_eq_zero hS
  have hAcompact : ∀ n, IsCompact (Set.accumulate C n) := fun n => by
    rw [Set.accumulate_def]
    exact (Set.finite_Iic n).isCompact_biUnion fun i _ => hCcompact i
  refine ⟨fun t => ⨆ n, surfaceMeasure V (Set.accumulate C n ∩ {x | u x = t}),
    Measurable.iSup fun n => measurable_surfaceMeasure_inter_levelSet hc (hAcompact n), ?_⟩
  filter_upwards [ae_surfaceMeasure_inter_levelSet_eq_zero
    (hu.mono Set.sdiff_subset) hCnull] with t ht
  have hWsub : (⋃ n, C n) ⊆ S := Set.iUnion_subset hCsub
  have hacc : ∀ n, Set.accumulate (fun i => C i ∩ {x | u x = t}) n
      = Set.accumulate C n ∩ {x | u x = t} := by
    intro n
    simp only [Set.accumulate_def, Set.iUnion_inter]
  have hW : surfaceMeasure V ((⋃ n, C n) ∩ {x | u x = t})
      = ⨆ n, surfaceMeasure V (Set.accumulate C n ∩ {x | u x = t}) := by
    rw [Set.iUnion_inter, measure_iUnion_eq_iSup_accumulate]
    exact iSup_congr fun n => by rw [hacc n]
  refine le_antisymm ?_ (hW ▸ measure_mono (Set.inter_subset_inter_left _ hWsub))
  calc surfaceMeasure V (S ∩ {x | u x = t})
      ≤ surfaceMeasure V ((S \ ⋃ n, C n) ∩ {x | u x = t})
          + surfaceMeasure V ((⋃ n, C n) ∩ {x | u x = t}) := by
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        rw [← Set.union_inter_distrib_right, Set.sdiff_union_of_subset hWsub]
    _ = ⨆ n, surfaceMeasure V (Set.accumulate C n ∩ {x | u x = t}) := by rw [ht, zero_add, hW]

/-- **Measurable weights, almost everywhere measurable slice integrals.**  The weighted form of
`aemeasurable_surfaceMeasure_inter_levelSet`, by increasing simple functions: each simple weight
turns the slice integral into a finite sum of slice measures of the measurable sets
`S ∩ s ⁻¹' {c}`, and two monotone limits recover the general weight.

No integrability, finiteness or boundedness of `g` is assumed, and `g = ∞` is allowed.  In
particular the inner measure `surfaceMeasure V` is never assumed `SFinite`, which it is not in
positive dimension, so no parametric-integral theorem is used. -/
theorem aemeasurable_setLIntegral_inter_levelSet {u : V → ℝ} {K : ℝ≥0} {S : Set V}
    {g : V → ℝ≥0∞} (hc : Continuous u) (hu : LipschitzOnWith K u S) (hS : MeasurableSet S)
    (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) := by
  have hstep : ∀ n : ℕ, AEMeasurable (fun t : ℝ =>
      (SimpleFunc.eapprox g n).lintegral
        ((surfaceMeasure V).restrict (S ∩ {x | u x = t}))) (volume : Measure ℝ) := by
    intro n
    have hrw : (fun t : ℝ => (SimpleFunc.eapprox g n).lintegral
          ((surfaceMeasure V).restrict (S ∩ {x | u x = t})))
        = ∑ c ∈ (SimpleFunc.eapprox g n).range, fun t : ℝ =>
            c * surfaceMeasure V ((S ∩ SimpleFunc.eapprox g n ⁻¹' {c}) ∩ {x | u x = t}) := by
      funext t
      rw [SimpleFunc.lintegral, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hset : (SimpleFunc.eapprox g n ⁻¹' {c}) ∩ (S ∩ {x | u x = t})
          = (S ∩ SimpleFunc.eapprox g n ⁻¹' {c}) ∩ {x | u x = t} := by
        ext x; simp only [Set.mem_inter_iff]; tauto
      rw [Measure.restrict_apply ((SimpleFunc.eapprox g n).measurableSet_preimage _), hset]
    rw [hrw]
    exact Finset.aemeasurable_sum _ fun c _ =>
      (aemeasurable_surfaceMeasure_inter_levelSet hc (hu.mono Set.inter_subset_left)
        (hS.inter ((SimpleFunc.eapprox g n).measurableSet_preimage {c}))).const_mul c
  have hsup : (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      = fun t : ℝ => ⨆ n : ℕ, (SimpleFunc.eapprox g n).lintegral
          ((surfaceMeasure V).restrict (S ∩ {x | u x = t})) := by
    funext t
    exact lintegral_eq_iSup_eapprox_lintegral hg
  rw [hsup]
  exact AEMeasurable.iSup hstep

end Slicing

end FunctionalInequalities.KLS
