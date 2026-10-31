module

public import FunctionalInequalities.KLS.Geometry.Cheeger.MinkowskiContent

/-!
# The Minkowski Cheeger infimum and its integrated coarea bound

Hole-free layer on top of `KLS/Geometry/Cheeger/MinkowskiContent.lean`.  It owns the Minkowski
Cheeger
infimum

`h_M = minkowskiConstant ν = ⨅_{0 < ν B < 1} ν⁺(B) / min {ν B, 1 - ν B}`

over Borel sets (`⊤` when no admissible set exists, in particular in dimension zero), and the
multiplied form of the Minkowski coarea inequality

`h_M · ∫₀¹ min {ν{u > t}, 1 - ν{u > t}} dt ≤ ∫ ‖∇u‖ dν`

for a `C¹` globally Lipschitz `[0,1]`-valued `u`.  The law is an arbitrary probability measure:
singular and atomic laws, zero dimension and `h_M = ⊤` are all included, and no density, absolute
continuity, nonatomicity or finiteness of `h_M` is assumed.

The two measure-theoretic ingredients are proved here as well:
`ae_measure_superlevel_lt_eq_le`, which says that the strict and the closed superlevel sets carry
the same mass for Lebesgue-almost every level because only countably many level sets are charged,
and `measurable_min_measure_superlevel`, the measurability of the superlevel balance, which follows
from antitonicity of the superlevel mass.

Nothing here depends on the weighted coarea formula, Sard, the smooth recovery sequence or the
relative perimeter: the only local import is the likewise hole-free
`MinkowskiContent`, whose own import closure is Mathlib.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace FunctionalInequalities.KLS.Isoperimetry

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-! ### The Minkowski Cheeger infimum -/

/-- The Minkowski Cheeger infimum `h_M` over Borel sets of intermediate mass; `⊤` if none. -/
def minkowskiConstant (ν : ProbabilityMeasure V) : ℝ≥0∞ :=
  ⨅ (B : Set V) (_ : MeasurableSet B) (_ : 0 < (ν : Measure V) B) (_ : (ν : Measure V) B < 1),
    minkowskiContent (ν : Measure V) B / min ((ν : Measure V) B) (1 - (ν : Measure V) B)

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Dimension zero: no Borel set has intermediate mass. -/
theorem minkowskiConstant_eq_top_of_subsingleton [Subsingleton V] (ν : ProbabilityMeasure V) :
    minkowskiConstant ν = ⊤ := by
  unfold minkowskiConstant
  refine iInf_eq_top.mpr fun B => ?_
  by_cases hB : MeasurableSet B
  · rw [iInf_pos hB]
    rcases Set.eq_empty_or_nonempty B with hBe | ⟨x, hx⟩
    · subst hBe
      simp only [measure_empty]
      exact iInf_neg (lt_irrefl 0)
    · have hBu : B = Set.univ := Set.eq_univ_of_forall fun y ↦ by rwa [Subsingleton.elim y x]
      subst hBu
      rw [measure_univ, iInf_pos (by norm_num : (0 : ℝ≥0∞) < 1)]
      exact iInf_neg (lt_irrefl 1)
  · exact iInf_neg hB

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The defining infimum in multiplied form: `h_M · m(ν B) ≤ ν⁺(B)` for every Borel set `B`,
including the degenerate masses `0` and `1`.  There the balance vanishes and the bound is the
`ENNReal` identity `⊤ * 0 = 0`, so no finiteness of `h_M` is needed and the infimum, which only
ranges over sets of intermediate mass, is not applied to an inadmissible set. -/
theorem minkowskiConstant_mul_min_le (ν : ProbabilityMeasure V) {B : Set V}
    (hB : MeasurableSet B) :
    minkowskiConstant ν * min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≤
      minkowskiContent (ν : Measure V) B := by
  rcases eq_or_ne (min ((ν : Measure V) B) (1 - (ν : Measure V) B)) 0 with h0 | h0
  · rw [h0, mul_zero]
    exact zero_le
  have hmtop : min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((min_le_left _ _).trans prob_le_one)
  have hBpos : 0 < (ν : Measure V) B := by
    refine pos_iff_ne_zero.mpr fun h ↦ h0 ?_
    simp [h]
  have hBlt : (ν : Measure V) B < 1 := by
    refine lt_of_le_of_ne prob_le_one fun h ↦ h0 ?_
    simp [h]
  have hiInf : minkowskiConstant ν ≤
      minkowskiContent (ν : Measure V) B / min ((ν : Measure V) B) (1 - (ν : Measure V) B) := by
    simp only [minkowskiConstant]
    refine le_trans (iInf_le _ B) ?_
    rw [iInf_pos hB, iInf_pos hBpos, iInf_pos hBlt]
  exact (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hmtop)).mp hiInf

/-! ### Superlevel masses -/

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Strict and closed superlevel sets carry the same mass for Lebesgue-almost every level: the
level sets `{u = t}` are pairwise disjoint, so an s-finite measure charges only countably many of
them, and a countable set of levels is Lebesgue null.  No density, no bounded range and no
continuity of `u` are involved. -/
theorem ae_measure_superlevel_lt_eq_le (μ : Measure V) [SFinite μ] {u : V → ℝ}
    (hu : Measurable u) :
    ∀ᵐ t ∂(volume : Measure ℝ), μ {x | t < u x} = μ {x | t ≤ u x} := by
  have hnull : (volume : Measure ℝ) {t : ℝ | 0 < μ {x : V | u x = t}} = 0 :=
    (Measure.countable_meas_level_set_pos hu).measure_zero _
  have hlevel : ∀ᵐ t ∂(volume : Measure ℝ), μ {x : V | u x = t} = 0 := by
    rw [ae_iff]
    exact measure_mono_null (fun t ht ↦ pos_iff_ne_zero.mpr ht) hnull
  filter_upwards [hlevel] with t ht
  refine le_antisymm (measure_mono ?_) ?_
  · intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact le_of_lt hx
  have hsub : {x : V | t ≤ u x} ⊆ {x : V | t < u x} ∪ {x : V | u x = t} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rcases lt_or_eq_of_le hx with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  calc μ {x : V | t ≤ u x} ≤ μ ({x : V | t < u x} ∪ {x : V | u x = t}) := measure_mono hsub
    _ ≤ μ {x : V | t < u x} + μ {x : V | u x = t} := measure_union_le _ _
    _ = μ {x : V | t < u x} := by rw [ht, add_zero]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The superlevel balance `t ↦ m(ν{u > t})` is measurable, for an arbitrary `u`: the superlevel
mass is antitone in the level, hence measurable, and `1 - ·` turns it into a monotone function. -/
theorem measurable_min_measure_superlevel (ν : ProbabilityMeasure V) (u : V → ℝ) :
    Measurable fun t : ℝ ↦
      min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) := by
  have hanti : Antitone fun t : ℝ ↦ (ν : Measure V) {x | t < u x} := fun t1 t2 ht12 ↦
    measure_mono fun x hx ↦ lt_of_le_of_lt ht12 hx
  have hmono : Monotone fun t : ℝ ↦ 1 - (ν : Measure V) {x | t < u x} := fun t1 t2 ht12 ↦
    tsub_le_tsub_left (hanti ht12) 1
  exact hanti.measurable.min hmono.measurable

/-! ### The integrated coarea bound -/

-- `hu01` is part of the original statement and fixes its mathematical scope; the proof needs only
-- the restriction of the level integral to `Ioo 0 1`, so the hypothesis stays in the signature and
-- the linter is silenced instead of the statement being narrowed.
set_option linter.unusedVariables false in
/-- Consequence for `h_M`: `h_M ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν` for a `C¹` Lipschitz
`[0,1]`-valued `u` (open and closed superlevel sets have the same mass for almost every `t`). -/
theorem minkowskiConstant_mul_lintegral_min_superlevel_le (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu01 : ∀ x, u x ∈ Set.Icc (0 : ℝ) 1) :
    minkowskiConstant ν *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) := by
  have humeas : Measurable u := hu.continuous.measurable
  have hpt : ∀ᵐ t ∂(volume : Measure ℝ),
      minkowskiConstant ν *
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) ≤
        minkowskiContent (ν : Measure V) {x | t ≤ u x} := by
    filter_upwards [ae_measure_superlevel_lt_eq_le (ν : Measure V) humeas] with t ht
    rw [ht]
    exact minkowskiConstant_mul_min_le ν (measurableSet_le measurable_const humeas)
  calc minkowskiConstant ν *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x})
      = ∫⁻ t in Set.Ioo (0 : ℝ) 1, minkowskiConstant ν *
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) :=
        (lintegral_const_mul _ (measurable_min_measure_superlevel ν u)).symm
    _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, minkowskiContent (ν : Measure V) {x | t ≤ u x} :=
        lintegral_mono_ae (ae_restrict_of_ae hpt)
    _ ≤ ∫⁻ t, minkowskiContent (ν : Measure V) {x | t ≤ u x} ∂(volume : Measure ℝ) :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) :=
        lintegral_minkowskiContent_superlevel_le (ν : Measure V) hu hK

end FunctionalInequalities.KLS.Isoperimetry
