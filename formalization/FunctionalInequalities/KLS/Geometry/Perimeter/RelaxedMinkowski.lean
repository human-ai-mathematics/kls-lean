import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski

/-!
# The relaxed lower Minkowski content as a set infimum

For a probability law `ν` on a normed additive group with Borel structure,
`relaxedMinkowskiContent ν B` is the infimum of `liminf (minkowskiContent ν (A n))` over
sequences of measurable sets `A n` converging to `B` in global indicator `L¹(ν)`
(`MinkowskiApproximatingSequence`; only measurability and convergence, `⊤` for an empty class).
The content is the existing outer Minkowski content `Isoperimetry.minkowskiContent`, a liminf
over radii (not the limsup-radius upper content).

It equals the metric BV perimeter for every set (`relaxedMinkowskiContent_eq_perimeter`): the
perimeter is at most every liminf by lower semicontinuity and `perimeter ≤ content`
(`perimeter_le_liminf_minkowskiContent`), and for finite perimeter the Minkowski recovery sets
are a member of the class whose contents converge to the perimeter (`exists_minkowskiRecovery`);
infinite perimeter needs no sequence. Consequences: the relaxed content is at most the content
of a measurable set (constant sequence) and is sequentially lower semicontinuous under
indicator `L¹` convergence. This is an equality of infima; the pointwise inequality
`perimeter ≤ minkowskiContent` can be strict, and neither Lemma 2.1 nor Theorem 3.6 of
Ambrosio--Di Marino--Gigli in general metric measure spaces is addressed.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

/-- Sequences of measurable sets converging to `B` in global indicator `L¹(ν)`. -/
def MinkowskiApproximatingSequence (ν : ProbabilityMeasure V) (B : Set V) : Type _ :=
  {A : ℕ → Set V // (∀ n, MeasurableSet (A n)) ∧
    Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V))
      atTop (𝓝 0)}

/-- The relaxed lower Minkowski content: the infimum of the liminf of the outer Minkowski
contents over measurable approximating sequences; `⊤` for an empty class. -/
def relaxedMinkowskiContent (ν : ProbabilityMeasure V) (B : Set V) : ENNReal :=
  ⨅ A : MinkowskiApproximatingSequence ν B,
    liminf (fun n => Isoperimetry.minkowskiContent ν (A.1 n)) atTop

omit [BorelSpace V] in
theorem relaxedMinkowskiContent_le_liminf (ν : ProbabilityMeasure V) (B : Set V)
    (A : MinkowskiApproximatingSequence ν B) :
    relaxedMinkowskiContent ν B ≤
      liminf (fun n => Isoperimetry.minkowskiContent ν (A.1 n)) atTop :=
  iInf_le _ A

omit [BorelSpace V] in
/-- An empty class gives `⊤`. -/
theorem relaxedMinkowskiContent_eq_top_of_isEmpty (ν : ProbabilityMeasure V) (B : Set V)
    [IsEmpty (MinkowskiApproximatingSequence ν B)] : relaxedMinkowskiContent ν B = ⊤ :=
  iInf_of_empty _

/-- The perimeter is at most every liminf of contents along the class, hence at most the
relaxed content (no measurability of `B` is needed). -/
theorem perimeter_le_relaxedMinkowskiContent (ν : ProbabilityMeasure V) (B : Set V) :
    perimeter (ν : Measure V) B ≤ relaxedMinkowskiContent ν B :=
  le_iInf fun A => perimeter_le_liminf_minkowskiContent ν A.2.1 A.2.2

/-- The relaxed content is at most the perimeter: for infinite perimeter by order, otherwise
through the Minkowski recovery sets, whose contents converge to the perimeter. -/
theorem relaxedMinkowskiContent_le_perimeter (ν : ProbabilityMeasure V) (B : Set V) :
    relaxedMinkowskiContent ν B ≤ perimeter (ν : Measure V) B := by
  rcases eq_or_ne (perimeter (ν : Measure V) B) ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  · have hB : perimeter (ν : Measure V) B < ⊤ := lt_top_iff_ne_top.2 hfin
    obtain ⟨A, hA, hconv, hlim⟩ := exists_minkowskiRecovery ν hB
    exact (relaxedMinkowskiContent_le_liminf ν B ⟨A, hA, hconv⟩).trans hlim.liminf_eq.le

/-- The relaxed lower Minkowski content is the metric BV perimeter, for every set and every
probability law on a normed additive group with Borel structure. -/
theorem relaxedMinkowskiContent_eq_perimeter (ν : ProbabilityMeasure V) (B : Set V) :
    relaxedMinkowskiContent ν B = perimeter (ν : Measure V) B :=
  le_antisymm (relaxedMinkowskiContent_le_perimeter ν B)
    (perimeter_le_relaxedMinkowskiContent ν B)

/-- The constant sequence of a measurable set. -/
def MinkowskiApproximatingSequence.const (ν : ProbabilityMeasure V) {B : Set V}
    (hB : MeasurableSet B) : MinkowskiApproximatingSequence ν B :=
  ⟨fun _ => B, fun _ => hB, by simp⟩

omit [BorelSpace V] in
/-- The relaxed content of a measurable set is at most its outer Minkowski content, through the
constant sequence; this recovers `perimeter ≤ minkowskiContent`. -/
theorem relaxedMinkowskiContent_le_minkowskiContent (ν : ProbabilityMeasure V) {B : Set V}
    (hB : MeasurableSet B) :
    relaxedMinkowskiContent ν B ≤ Isoperimetry.minkowskiContent ν B := by
  have h := relaxedMinkowskiContent_le_liminf ν B (MinkowskiApproximatingSequence.const ν hB)
  change relaxedMinkowskiContent ν B ≤
    liminf (fun _ : ℕ => Isoperimetry.minkowskiContent ν B) atTop at h
  rwa [liminf_const] at h

/-- Sequential lower semicontinuity of the relaxed content under indicator `L¹` convergence of
measurable sets, through the identity with the perimeter. -/
theorem relaxedMinkowskiContent_le_liminf_of_tendsto (ν : ProbabilityMeasure V) {B : Set V}
    {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) :
    relaxedMinkowskiContent ν B ≤ liminf (fun n => relaxedMinkowskiContent ν (A n)) atTop := by
  simp only [relaxedMinkowskiContent_eq_perimeter]
  exact perimeter_le_liminf_of_tendsto (ν : Measure V) hA hconv

end FunctionalInequalities.KLS.MetricBV
