import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski
import FunctionalInequalities.KLS.Geometry.Perimeter.UpperMinkowskiRecovery

/-!
# The relaxed lower Minkowski content as a set infimum

For a finite Borel measure `ν` on a metric space (2026-09-30: generic metric and finite-measure
scope; probability laws are instances; scaling by nonnegative real scalars and the zero measure
are in the last section),
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
`perimeter ≤ minkowskiContent` can be strict. The additive finite-target declarations also
identify both existing relaxation infima at Theorem 3.6's measurable finite-mass target scope
under Borel measures finite on bounded Borel sets. Recovery sets are bounded (open for the
upper recovery), with finite masses and finite contents. Infinite perimeter is included by
order and lower semicontinuity, without claiming a recovery sequence there. The actual
approximation class is unchanged and permits infinite-mass finite prefixes. No properness,
finite total mass, complement symmetry or infinite-mass target endpoint is inferred.

The last section defines the relaxed *upper* Minkowski content `relaxedUpperMinkowskiContent`
over the same class, with the genuine `Isoperimetry.upperMinkowskiContent` (a limsup over radii)
in place of the lower content, and proves `relaxedUpperMinkowskiContent_eq_perimeter` for every
set: the lower bound is the same lower semicontinuity combined with `perimeter ≤ minkowskiContent
≤ upperMinkowskiContent` (`perimeter_le_liminf_upperMinkowskiContent`), and for finite perimeter
the upper recovery sets `exists_upperMinkowskiRecovery` are a member of the class whose upper
contents converge to the perimeter.  Hence both relaxed contents coincide
(`relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent`), again as infima; the pointwise
upper content of a set is not identified with its perimeter.

ADMG Lemma 2.1's equality of the two relaxations also holds for every Borel measure at
measurable finite-mass targets (`relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent_of_measure_lt_top`),
through near-minimum selection (`exists_upperApproximation_lt`) and global-`L¹` lower
semicontinuity of the relaxed upper content (`relaxedUpperMinkowskiContent_le_liminf_of_tendsto`).
This equality of infima carries no perimeter identification beyond the scopes above.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]

/-- Sequences of measurable sets converging to `B` in global indicator `L¹(ν)`. -/
def MinkowskiApproximatingSequence (ν : Measure V) (B : Set V) : Type _ :=
  {A : ℕ → Set V // (∀ n, MeasurableSet (A n)) ∧
    Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V))
      atTop (𝓝 0)}

/-- The relaxed lower Minkowski content: the infimum of the liminf of the outer Minkowski
contents over measurable approximating sequences; `⊤` for an empty class. -/
def relaxedMinkowskiContent (ν : Measure V) (B : Set V) : ENNReal :=
  ⨅ A : MinkowskiApproximatingSequence ν B,
    liminf (fun n => Isoperimetry.minkowskiContent ν (A.1 n)) atTop

omit [BorelSpace V] in
theorem relaxedMinkowskiContent_le_liminf (ν : Measure V) [IsFiniteMeasure ν] (B : Set V)
    (A : MinkowskiApproximatingSequence ν B) :
    relaxedMinkowskiContent ν B ≤
      liminf (fun n => Isoperimetry.minkowskiContent ν (A.1 n)) atTop :=
  iInf_le _ A

omit [BorelSpace V] in
/-- An empty class gives `⊤`. -/
theorem relaxedMinkowskiContent_eq_top_of_isEmpty (ν : Measure V) [IsFiniteMeasure ν] (B : Set V)
    [IsEmpty (MinkowskiApproximatingSequence ν B)] : relaxedMinkowskiContent ν B = ⊤ :=
  iInf_of_empty _

/-- The perimeter is at most every liminf of contents along the class, hence at most the
relaxed content (no measurability of `B` is needed). -/
theorem perimeter_le_relaxedMinkowskiContent (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    perimeter (ν : Measure V) B ≤ relaxedMinkowskiContent ν B :=
  le_iInf fun A => perimeter_le_liminf_minkowskiContent ν A.2.1 A.2.2

/-- The relaxed content is at most the perimeter: for infinite perimeter by order, otherwise
through the Minkowski recovery sets, whose contents converge to the perimeter. -/
theorem relaxedMinkowskiContent_le_perimeter (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    relaxedMinkowskiContent ν B ≤ perimeter (ν : Measure V) B := by
  rcases eq_or_ne (perimeter (ν : Measure V) B) ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  · have hB : perimeter (ν : Measure V) B < ⊤ := lt_top_iff_ne_top.2 hfin
    obtain ⟨A, hA, hconv, hlim⟩ := exists_minkowskiRecovery ν hB
    exact (relaxedMinkowskiContent_le_liminf ν B ⟨A, hA, hconv⟩).trans hlim.liminf_eq.le

/-- The relaxed lower Minkowski content is the metric BV perimeter, for every set and every
probability law on a normed additive group with Borel structure. -/
theorem relaxedMinkowskiContent_eq_perimeter (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    relaxedMinkowskiContent ν B = perimeter (ν : Measure V) B :=
  le_antisymm (relaxedMinkowskiContent_le_perimeter ν B)
    (perimeter_le_relaxedMinkowskiContent ν B)

/-- At a measurable finite-mass target, the existing approximating-set infimum bounds
the perimeter for any Borel measure. No finite-mass condition is added to the class. -/
theorem perimeter_le_relaxedMinkowskiContent_of_measure_lt_top (ν : Measure V) {B : Set V}
    (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    perimeter ν B ≤ relaxedMinkowskiContent ν B :=
  le_iInf fun A => perimeter_le_liminf_minkowskiContent_of_measure_lt_top ν hB hνB A.2.1 A.2.2

/-- Actual lower recovery bounds the relaxed lower content by perimeter under finiteness
on bounded Borel sets. Infinite perimeter is included by order; recovery is asserted only
for finite perimeter. -/
theorem relaxedMinkowskiContent_le_perimeter_of_finite_on_bounded (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    relaxedMinkowskiContent ν B ≤ perimeter ν B := by
  rcases eq_or_ne (perimeter ν B) ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  · obtain ⟨A, hA, -, -, -, hconv, hlim⟩ :=
      exists_minkowskiRecovery_of_finite_on_bounded ν hν hB hνB hfin.lt_top
    exact (iInf_le _ (⟨A, hA, hconv⟩ : MinkowskiApproximatingSequence ν B)).trans hlim.liminf_eq.le

/-- Theorem 3.6's relaxed-lower-content identity at its published target/measure scope:
Borel measures finite on bounded Borel sets, measurable finite-mass targets, and actual
global indicator L1 convergence. No properness, finite total mass or complement symmetry.
This is an equality of relaxation infima, not pointwise equality with lower content. -/
theorem relaxedMinkowskiContent_eq_perimeter_of_finite_on_bounded (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    relaxedMinkowskiContent ν B = perimeter ν B :=
  le_antisymm (relaxedMinkowskiContent_le_perimeter_of_finite_on_bounded ν hν hB hνB)
    (perimeter_le_relaxedMinkowskiContent_of_measure_lt_top ν hB hνB)

/-- The constant sequence of a measurable set. -/
def MinkowskiApproximatingSequence.const (ν : Measure V) {B : Set V}
    (hB : MeasurableSet B) : MinkowskiApproximatingSequence ν B :=
  ⟨fun _ => B, fun _ => hB, by simp⟩

omit [BorelSpace V] in
/-- The relaxed content of a measurable set is at most its outer Minkowski content, through the
constant sequence; this recovers `perimeter ≤ minkowskiContent`. -/
theorem relaxedMinkowskiContent_le_minkowskiContent (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : MeasurableSet B) :
    relaxedMinkowskiContent ν B ≤ Isoperimetry.minkowskiContent ν B := by
  have h := relaxedMinkowskiContent_le_liminf ν B (MinkowskiApproximatingSequence.const ν hB)
  change relaxedMinkowskiContent ν B ≤
    liminf (fun _ : ℕ => Isoperimetry.minkowskiContent ν B) atTop at h
  rwa [liminf_const] at h

/-- Sequential lower semicontinuity of the relaxed content under indicator `L¹` convergence of
measurable sets, through the identity with the perimeter. -/
theorem relaxedMinkowskiContent_le_liminf_of_tendsto (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) :
    relaxedMinkowskiContent ν B ≤ liminf (fun n => relaxedMinkowskiContent ν (A n)) atTop := by
  simp only [relaxedMinkowskiContent_eq_perimeter]
  exact perimeter_le_liminf_of_tendsto (ν : Measure V) hA hconv

/-! ### The relaxed upper Minkowski content -/

section RelaxedUpper

/-- The relaxed upper Minkowski content: the infimum of the liminf of the upper Minkowski
contents over the same measurable approximating sequences; `⊤` for an empty class. -/
def relaxedUpperMinkowskiContent (ν : Measure V) (B : Set V) : ENNReal :=
  ⨅ A : MinkowskiApproximatingSequence ν B,
    liminf (fun n => Isoperimetry.upperMinkowskiContent ν (A.1 n)) atTop

omit [BorelSpace V] in
theorem relaxedUpperMinkowskiContent_le_liminf (ν : Measure V) [IsFiniteMeasure ν] (B : Set V)
    (A : MinkowskiApproximatingSequence ν B) :
    relaxedUpperMinkowskiContent ν B ≤
      liminf (fun n => Isoperimetry.upperMinkowskiContent ν (A.1 n)) atTop :=
  iInf_le _ A

omit [BorelSpace V] in
/-- An empty class gives `⊤`. -/
theorem relaxedUpperMinkowskiContent_eq_top_of_isEmpty (ν : Measure V) [IsFiniteMeasure ν] (B : Set V)
    [IsEmpty (MinkowskiApproximatingSequence ν B)] : relaxedUpperMinkowskiContent ν B = ⊤ :=
  iInf_of_empty _

omit [BorelSpace V] in
/-- Termwise, the lower content is at most the upper content, so the relaxed lower content is at
most the relaxed upper content. -/
theorem relaxedMinkowskiContent_le_relaxedUpperMinkowskiContent (ν : Measure V) [IsFiniteMeasure ν]
    (B : Set V) : relaxedMinkowskiContent ν B ≤ relaxedUpperMinkowskiContent ν B :=
  le_iInf fun A => (relaxedMinkowskiContent_le_liminf ν B A).trans
    (liminf_le_liminf (Eventually.of_forall fun n =>
      Isoperimetry.minkowskiContent_le_upperMinkowskiContent ν (A.1 n)))

/-- The perimeter is at most every liminf of upper contents along the class (BV lower
semicontinuity below the upper content), hence at most the relaxed upper content. -/
theorem perimeter_le_relaxedUpperMinkowskiContent (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    perimeter (ν : Measure V) B ≤ relaxedUpperMinkowskiContent ν B :=
  le_iInf fun A => perimeter_le_liminf_upperMinkowskiContent ν B A.2.1 A.2.2

/-- The relaxed upper content is at most the perimeter: for infinite perimeter by order,
otherwise through the upper recovery sets, whose upper contents converge to the perimeter. -/
theorem relaxedUpperMinkowskiContent_le_perimeter (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    relaxedUpperMinkowskiContent ν B ≤ perimeter (ν : Measure V) B := by
  rcases eq_or_ne (perimeter (ν : Measure V) B) ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  · have hB : perimeter (ν : Measure V) B < ⊤ := lt_top_iff_ne_top.2 hfin
    obtain ⟨U, hU, hconv, hlim⟩ := exists_upperMinkowskiRecovery ν hB
    exact (relaxedUpperMinkowskiContent_le_liminf ν B ⟨U, hU, hconv⟩).trans hlim.liminf_eq.le

/-- **The relaxed upper Minkowski content is the metric BV perimeter**, for every set and every
probability law on a normed additive group with Borel structure. -/
theorem relaxedUpperMinkowskiContent_eq_perimeter (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    relaxedUpperMinkowskiContent ν B = perimeter (ν : Measure V) B :=
  le_antisymm (relaxedUpperMinkowskiContent_le_perimeter ν B)
    (perimeter_le_relaxedUpperMinkowskiContent ν B)

/-- Both relaxed contents coincide (as infima). -/
theorem relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent (ν : Measure V) [IsFiniteMeasure ν]
    (B : Set V) : relaxedUpperMinkowskiContent ν B = relaxedMinkowskiContent ν B := by
  rw [relaxedUpperMinkowskiContent_eq_perimeter, relaxedMinkowskiContent_eq_perimeter]

/-- An empty approximating class forces infinite perimeter. -/
theorem perimeter_eq_top_of_isEmpty (ν : Measure V) [IsFiniteMeasure ν] (B : Set V)
    [IsEmpty (MinkowskiApproximatingSequence ν B)] : perimeter (ν : Measure V) B = ⊤ := by
  rw [← relaxedUpperMinkowskiContent_eq_perimeter, relaxedUpperMinkowskiContent_eq_top_of_isEmpty]

theorem relaxedUpperMinkowskiContent_eq_top_iff (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    relaxedUpperMinkowskiContent ν B = ⊤ ↔ perimeter (ν : Measure V) B = ⊤ := by
  rw [relaxedUpperMinkowskiContent_eq_perimeter]

theorem relaxedUpperMinkowskiContent_eq_zero_iff (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    relaxedUpperMinkowskiContent ν B = 0 ↔ perimeter (ν : Measure V) B = 0 := by
  rw [relaxedUpperMinkowskiContent_eq_perimeter]

omit [BorelSpace V] in
/-- The relaxed upper content of a measurable set is at most its upper Minkowski content, through
the constant sequence; this recovers `perimeter ≤ upperMinkowskiContent`. -/
theorem relaxedUpperMinkowskiContent_le_upperMinkowskiContent (ν : Measure V) [IsFiniteMeasure ν]
    {B : Set V} (hB : MeasurableSet B) :
    relaxedUpperMinkowskiContent ν B ≤ Isoperimetry.upperMinkowskiContent ν B := by
  have h := relaxedUpperMinkowskiContent_le_liminf ν B (MinkowskiApproximatingSequence.const ν hB)
  change relaxedUpperMinkowskiContent ν B ≤
    liminf (fun _ : ℕ => Isoperimetry.upperMinkowskiContent ν B) atTop at h
  rwa [liminf_const] at h

omit [BorelSpace V] in
/-- Any sequence of the class whose upper contents converge bounds the relaxed upper content, and
hence the perimeter, by the limit. -/
theorem relaxedUpperMinkowskiContent_le_of_tendsto (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) {c : ENNReal}
    (hlim : Tendsto (fun n => Isoperimetry.upperMinkowskiContent ν (A n)) atTop (𝓝 c)) :
    relaxedUpperMinkowskiContent ν B ≤ c :=
  (relaxedUpperMinkowskiContent_le_liminf ν B ⟨A, hA, hconv⟩).trans hlim.liminf_eq.le

/-- ADMG Lemma 2.1 at measurable finite-mass targets: the genuine relaxed upper
content is at most the lower content under any Borel measure. The finite-content
branch uses actual positive-radius recovery and original global indicator L1;
the infinite-content branch needs no recovery. -/
theorem relaxedUpperMinkowskiContent_le_minkowskiContent_of_measure_lt_top (ν : Measure V)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    relaxedUpperMinkowskiContent ν B ≤ Isoperimetry.minkowskiContent ν B := by
  rcases eq_or_ne (Isoperimetry.minkowskiContent ν B) ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  · obtain ⟨s, -, -, hA, -, hconv, hlim⟩ :=
      Isoperimetry.exists_upperRecovery_of_measure_lt_top ν hB hνB hfin.lt_top
    exact (iInf_le _ (⟨fun n => Metric.thickening (s n) B, hA, hconv⟩ :
      MinkowskiApproximatingSequence ν B)).trans (le_trans liminf_le_limsup hlim)

/-- The actual upper-content approximation infimum bounds perimeter at measurable
finite-mass targets under any Borel measure, allowing infinite-mass finite prefixes. -/
theorem perimeter_le_relaxedUpperMinkowskiContent_of_measure_lt_top (ν : Measure V)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    perimeter ν B ≤ relaxedUpperMinkowskiContent ν B :=
  le_iInf fun A => perimeter_le_liminf_upperMinkowskiContent_of_measure_lt_top ν hB hνB A.2.1 A.2.2

/-- Actual bounded open upper recovery proves the upper relaxation bound under finiteness
on bounded Borel sets; the infinite-perimeter branch follows by order. -/
theorem relaxedUpperMinkowskiContent_le_perimeter_of_finite_on_bounded (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    relaxedUpperMinkowskiContent ν B ≤ perimeter ν B := by
  rcases eq_or_ne (perimeter ν B) ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  · obtain ⟨A, -, hA, -, -, -, hconv, hlim⟩ :=
      exists_upperMinkowskiRecovery_of_finite_on_bounded ν hν hB hνB hfin.lt_top
    exact (iInf_le _ (⟨A, hA, hconv⟩ : MinkowskiApproximatingSequence ν B)).trans hlim.liminf_eq.le

/-- Theorem 3.6 at the published measure/target scope: the genuine relaxed upper content
equals metric BV perimeter for measurable finite-mass targets of a measure finite on
bounded Borel sets, with the unchanged global indicator L1 approximation class. -/
theorem relaxedUpperMinkowskiContent_eq_perimeter_of_finite_on_bounded (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    relaxedUpperMinkowskiContent ν B = perimeter ν B :=
  le_antisymm (relaxedUpperMinkowskiContent_le_perimeter_of_finite_on_bounded ν hν hB hνB)
    (perimeter_le_relaxedUpperMinkowskiContent_of_measure_lt_top ν hB hνB)

/-- Both genuine relaxed contents coincide at the published finite-mass Borel target
scope. This identifies infima over actual approximating sequences, not pointwise contents. -/
theorem relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent_of_finite_on_bounded (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    relaxedUpperMinkowskiContent ν B = relaxedMinkowskiContent ν B :=
  (relaxedUpperMinkowskiContent_eq_perimeter_of_finite_on_bounded ν hν hB hνB).trans
    (relaxedMinkowskiContent_eq_perimeter_of_finite_on_bounded ν hν hB hνB).symm

/-! ### Lemma 2.1 equality for arbitrary Borel measures

The following declarations need no finiteness of the measure. Near-minimum selection and the
lower semicontinuity of the relaxed upper content hold for every target; the equality of the
two relaxations holds at measurable finite-mass targets. They do not identify either
relaxation with the perimeter, which is proved above only for finite measures or for
measures finite on bounded Borel sets. -/

omit [BorelSpace V] in
/-- Near-minimum selection for the relaxed upper content: below any threshold above it there are
measurable sets arbitrarily close to the target in global indicator `L¹(ν)` whose upper content
is below the threshold. No finiteness of the measure, target mass or measurability is assumed. -/
theorem exists_upperApproximation_lt (ν : Measure V) (B : Set V) {a ε : ENNReal}
    (ha : relaxedUpperMinkowskiContent ν B < a) (hε : 0 < ε) :
    ∃ C : Set V, MeasurableSet C ∧
      (∫⁻ x, ‖C.indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν) < ε ∧
      Isoperimetry.upperMinkowskiContent ν C < a := by
  unfold relaxedUpperMinkowskiContent at ha
  obtain ⟨s, hs⟩ := iInf_lt_iff.mp ha
  have hfreq : ∃ᶠ n in atTop,
      Isoperimetry.upperMinkowskiContent ν (s.1 n) < a :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hs
  have hev : ∀ᶠ n in atTop,
      (∫⁻ x, ‖(s.1 n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν) < ε :=
    s.2.2.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := (hfreq.and_eventually hev).exists
  exact ⟨s.1 n, s.2.1 n, hn.2, hn.1⟩

omit [BorelSpace V] in
/-- Sequential lower semicontinuity of the relaxed upper content under global indicator `L¹(ν)`
convergence of measurable sets, for every measure: diagonal selection of near-minimal sets and
the indicator triangle inequality. The limit set need not be measurable or of finite mass. -/
theorem relaxedUpperMinkowskiContent_le_liminf_of_tendsto (ν : Measure V) {B : Set V}
    {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    relaxedUpperMinkowskiContent ν B ≤
      liminf (fun n => relaxedUpperMinkowskiContent ν (A n)) atTop := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  have hfreq : ∃ᶠ n in atTop, relaxedUpperMinkowskiContent ν (A n) < a :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) ha
  have hε0 : ∀ k : ℕ, 0 < (((k + 1 : ℕ) : ENNReal))⁻¹ := fun k =>
    ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
  have hεlim : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ENNReal))⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hidx : ∀ k : ℕ, ∃ n,
      relaxedUpperMinkowskiContent ν (A n) < a ∧
        (∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν) <
          (((k + 1 : ℕ) : ENNReal))⁻¹ := fun k =>
    (hfreq.and_eventually (hconv.eventually (gt_mem_nhds (hε0 k)))).exists
  choose m hm using hidx
  have htest : ∀ k : ℕ, ∃ C : Set V,
      MeasurableSet C ∧
        (∫⁻ x, ‖C.indicator (1 : V → ℝ) x - (A (m k)).indicator 1 x‖ₑ ∂ν) <
          (((k + 1 : ℕ) : ENNReal))⁻¹ ∧
        Isoperimetry.upperMinkowskiContent ν C < a := fun k =>
    exists_upperApproximation_lt ν (A (m k)) (hm k).1 (hε0 k)
  choose C hC using htest
  have hd : ∀ k, (∫⁻ x, ‖(C k).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν) ≤
      (((k + 1 : ℕ) : ENNReal))⁻¹ + (((k + 1 : ℕ) : ENNReal))⁻¹ := fun k =>
    (lintegral_enorm_indicator_sub_le_add ν (hC k).1 (hA (m k)) B).trans
      (add_le_add (hC k).2.1.le (hm k).2.le)
  have hlim : Tendsto
      (fun k : ℕ => (((k + 1 : ℕ) : ENNReal))⁻¹ + (((k + 1 : ℕ) : ENNReal))⁻¹)
      atTop (𝓝 0) := by
    simpa using hεlim.add hεlim
  let s : MinkowskiApproximatingSequence ν B :=
    ⟨C, fun k => (hC k).1,
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ => zero_le) hd⟩
  change (⨅ t : MinkowskiApproximatingSequence ν B,
      liminf (fun n => Isoperimetry.upperMinkowskiContent ν (t.1 n)) atTop) ≤ _
  calc
    (⨅ t : MinkowskiApproximatingSequence ν B,
        liminf (fun n => Isoperimetry.upperMinkowskiContent ν (t.1 n)) atTop) ≤
        liminf (fun k => Isoperimetry.upperMinkowskiContent ν (s.1 k)) atTop :=
      iInf_le _ s
    _ ≤ a := liminf_le_of_frequently_le' (Frequently.of_forall fun k => (hC k).2.2.le)

/-- ADMG Lemma 2.1, second clause, for every Borel measure at measurable finite-mass targets:
the relaxed upper and lower Minkowski contents coincide. Lower semicontinuity of the relaxed
upper content and the bound (2.2) at the eventually finite-mass approximating sets give
`≤`; termwise `liminf ≤ limsup` gives `≥`. Finite prefixes of infinite mass are allowed. No
finiteness of the measure on bounded sets is assumed, and no perimeter identity is claimed. -/
theorem relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent_of_measure_lt_top
    (ν : Measure V) {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    relaxedUpperMinkowskiContent ν B = relaxedMinkowskiContent ν B := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun A => ?_
    calc
      relaxedUpperMinkowskiContent ν B ≤
          liminf (fun n => relaxedUpperMinkowskiContent ν (A.1 n)) atTop :=
        relaxedUpperMinkowskiContent_le_liminf_of_tendsto ν A.2.1 A.2.2
      _ ≤ liminf (fun n => Isoperimetry.minkowskiContent ν (A.1 n)) atTop :=
        liminf_le_liminf <| by
          have hfin : ∀ᶠ n in atTop, ν (A.1 n) < ⊤ := by
            filter_upwards
              [A.2.2.eventually_lt_const (by norm_num : (0 : ℝ≥0∞) < 1)] with n hn
            exact
              (measure_le_add_lintegral_indicator_sub ν (A.2.1 n) hB).trans_lt
                (ENNReal.add_lt_top.2 ⟨hνB, hn.trans (by norm_num)⟩)
          exact hfin.mono fun n hn =>
            relaxedUpperMinkowskiContent_le_minkowskiContent_of_measure_lt_top
              ν (A.2.1 n) hn
  · refine le_iInf fun A => (iInf_le _ A).trans ?_
    exact
      liminf_le_liminf (Eventually.of_forall fun n => by
        unfold Isoperimetry.minkowskiContent Isoperimetry.upperMinkowskiContent
        exact liminf_le_limsup)

end RelaxedUpper

/-! ### Scaling and the zero measure -/

section Scaling

/-- A measurable approximating sequence for `ν` approximates for `c • ν` (any `c : ℝ≥0`). -/
def MinkowskiApproximatingSequence.smul (c : ℝ≥0) {ν : Measure V} {B : Set V}
    (A : MinkowskiApproximatingSequence ν B) : MinkowskiApproximatingSequence (c • ν) B :=
  ⟨A.1, A.2.1, by
    have h := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) A.2.2 (Or.inr ENNReal.coe_ne_top)
    simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, mul_zero] at h ⊢
    exact h⟩

/-- A measurable approximating sequence for `c • ν` with `c ≠ 0` approximates for `ν`. -/
def MinkowskiApproximatingSequence.smulInv {c : ℝ≥0} (hc : c ≠ 0) {ν : Measure V} {B : Set V}
    (A : MinkowskiApproximatingSequence (c • ν) B) : MinkowskiApproximatingSequence ν B :=
  ⟨A.1, A.2.1, by
    have hc' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
    have h := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)⁻¹) A.2.2
      (Or.inr (ENNReal.inv_ne_top.2 hc'))
    simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hc' ENNReal.coe_ne_top, one_mul, mul_zero] at h
    exact h⟩

omit [BorelSpace V] in
theorem relaxedMinkowskiContent_smul_le (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure V) (B : Set V) :
    relaxedMinkowskiContent (c • ν) B ≤ c * relaxedMinkowskiContent ν B := by
  unfold relaxedMinkowskiContent
  rw [ENNReal.mul_iInf' (fun h => absurd h ENNReal.coe_ne_top)
    (fun h => absurd (ENNReal.coe_eq_zero.1 h) hc)]
  refine le_iInf fun A => (iInf_le _ (A.smul c)).trans (le_of_eq ?_)
  simp only [MinkowskiApproximatingSequence.smul, Isoperimetry.minkowskiContent_smul]
  exact Isoperimetry.liminf_coe_mul c _

omit [BorelSpace V] in
/-- **Relaxed lower content scaling** for every nonzero `c : ℝ≥0`. -/
theorem relaxedMinkowskiContent_smul (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure V) (B : Set V) :
    relaxedMinkowskiContent (c • ν) B = c * relaxedMinkowskiContent ν B := by
  refine le_antisymm (relaxedMinkowskiContent_smul_le c hc ν B) ?_
  have hc' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  have h := relaxedMinkowskiContent_smul_le c⁻¹ (inv_ne_zero hc) (c • ν) B
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  calc (c : ℝ≥0∞) * relaxedMinkowskiContent ν B
      ≤ c * ((c⁻¹ : ℝ≥0) * relaxedMinkowskiContent (c • ν) B) := mul_le_mul' le_rfl h
    _ = relaxedMinkowskiContent (c • ν) B := by
        rw [← mul_assoc, ENNReal.coe_inv hc, ENNReal.mul_inv_cancel hc' ENNReal.coe_ne_top, one_mul]

omit [BorelSpace V] in
theorem relaxedUpperMinkowskiContent_smul_le (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure V) (B : Set V) :
    relaxedUpperMinkowskiContent (c • ν) B ≤ c * relaxedUpperMinkowskiContent ν B := by
  unfold relaxedUpperMinkowskiContent
  rw [ENNReal.mul_iInf' (fun h => absurd h ENNReal.coe_ne_top)
    (fun h => absurd (ENNReal.coe_eq_zero.1 h) hc)]
  refine le_iInf fun A => (iInf_le _ (A.smul c)).trans (le_of_eq ?_)
  simp only [MinkowskiApproximatingSequence.smul, Isoperimetry.upperMinkowskiContent_smul]
  exact Isoperimetry.liminf_coe_mul c _

omit [BorelSpace V] in
/-- **Relaxed upper content scaling** for every nonzero `c : ℝ≥0`. -/
theorem relaxedUpperMinkowskiContent_smul (c : ℝ≥0) (hc : c ≠ 0) (ν : Measure V) (B : Set V) :
    relaxedUpperMinkowskiContent (c • ν) B = c * relaxedUpperMinkowskiContent ν B := by
  refine le_antisymm (relaxedUpperMinkowskiContent_smul_le c hc ν B) ?_
  have hc' : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  have h := relaxedUpperMinkowskiContent_smul_le c⁻¹ (inv_ne_zero hc) (c • ν) B
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  calc (c : ℝ≥0∞) * relaxedUpperMinkowskiContent ν B
      ≤ c * ((c⁻¹ : ℝ≥0) * relaxedUpperMinkowskiContent (c • ν) B) := mul_le_mul' le_rfl h
    _ = relaxedUpperMinkowskiContent (c • ν) B := by
        rw [← mul_assoc, ENNReal.coe_inv hc, ENNReal.mul_inv_cancel hc' ENNReal.coe_ne_top, one_mul]

omit [BorelSpace V] in
/-- The zero measure: both relaxed contents vanish for every set (the constant empty sequence is
in the class and has zero content). -/
theorem relaxedMinkowskiContent_zero_measure (B : Set V) :
    relaxedMinkowskiContent (0 : Measure V) B = 0 := by
  refine le_antisymm ?_ bot_le
  have h := relaxedMinkowskiContent_le_liminf (0 : Measure V) B
    ⟨fun _ => ∅, fun _ => MeasurableSet.empty, by simp⟩
  simpa [Isoperimetry.minkowskiContent_zero_measure] using h

omit [BorelSpace V] in
theorem relaxedUpperMinkowskiContent_zero_measure (B : Set V) :
    relaxedUpperMinkowskiContent (0 : Measure V) B = 0 := by
  refine le_antisymm ?_ bot_le
  have h := relaxedUpperMinkowskiContent_le_liminf (0 : Measure V) B
    ⟨fun _ => ∅, fun _ => MeasurableSet.empty, by simp⟩
  simpa [Isoperimetry.upperMinkowskiContent_zero_measure] using h

end Scaling

end FunctionalInequalities.KLS.MetricBV
