import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBV.Transport
import FunctionalInequalities.KLS.Geometry.Perimeter.LocalLipschitzTests

/-!
# Relaxation infima over globally and locally Lipschitz approximants

Two relaxations of the integrated local slope, as actual sequence classes:
`lipschitzRelaxation ν B` is the infimum of `liminf ∫⁻ |∇f n| dν` over sequences of globally
Lipschitz real functions (values and supports unrestricted) converging to `1_B` in global
`L¹(ν)`, the class of Ambrosio--Di Marino--Gigli's Definition 3.3 with the one-point local
Lipschitz constant `Energy.LocalSlope.apply`; `locallyLipschitzRelaxation ν B` is the same
infimum over locally Lipschitz sequences (the variant of their Remark 3.5, with global `L¹`
convergence). Both are `⊤` for an empty class and are defined for every measure on a metric
Borel space.

Tests are globally Lipschitz and globally Lipschitz functions are locally Lipschitz, so
`locallyLipschitzRelaxation ≤ lipschitzRelaxation ≤ perimeter` always. For a finite measure the
globally Lipschitz bridge gives `lipschitzRelaxation_eq_perimeter` on every metric space, and on
a proper space the locally Lipschitz bridge gives `locallyLipschitzRelaxation_eq_perimeter`. The
closed support of a probability law on a proper space is proper, so both relaxations of the
closed-support law equal its perimeter (`locallyLipschitzRelaxation_closedSupportLaw`).
For a measurable finite-mass target the global-Lipschitz identity holds for every Borel measure,
without finite total mass or properness (`lipschitzRelaxation_eq_perimeter_of_measure_lt_top`),
by the target-tail cutoff estimates of ADMG Remark 3.4. This is a test-class relaxation identity,
not a Minkowski relaxation identity. On a proper space the same holds at measurable finite-mass
targets for every Borel measure for the locally Lipschitz class with global `L¹` convergence
(`locallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top`) and with convergence on every
compact set (`compactLocallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top`), the alternative
classes of ADMG Remark 3.5. Non-proper spaces for the locally Lipschitz classes are not addressed.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Globally Lipschitz approximating sequences of `1_B` in global `L¹(ν)`: each term is globally
Lipschitz, with unrestricted values and support. -/
def LipschitzApproximatingSequence (ν : Measure X) (B : Set X) : Type _ :=
  {f : ℕ → X → ℝ // (∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n)) ∧
    Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)}

/-- The relaxation of the slope integral over globally Lipschitz approximants; `⊤` for an empty
class. -/
def lipschitzRelaxation (ν : Measure X) (B : Set X) : ENNReal :=
  ⨅ f : LipschitzApproximatingSequence ν B,
    liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop

/-- Locally Lipschitz approximating sequences of `1_B` in global `L¹(ν)`. -/
def LocallyLipschitzApproximatingSequence (ν : Measure X) (B : Set X) : Type _ :=
  {f : ℕ → X → ℝ // (∀ n, LocallyLipschitz (f n)) ∧
    Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)}

/-- The relaxation of the slope integral over locally Lipschitz approximants; `⊤` for an empty
class. -/
def locallyLipschitzRelaxation (ν : Measure X) (B : Set X) : ENNReal :=
  ⨅ f : LocallyLipschitzApproximatingSequence ν B,
    liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop

omit [BorelSpace X] in
theorem lipschitzRelaxation_le_liminf (ν : Measure X) (B : Set X)
    (f : LipschitzApproximatingSequence ν B) :
    lipschitzRelaxation ν B ≤
      liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop :=
  iInf_le _ f

omit [BorelSpace X] in
theorem locallyLipschitzRelaxation_le_liminf (ν : Measure X) (B : Set X)
    (f : LocallyLipschitzApproximatingSequence ν B) :
    locallyLipschitzRelaxation ν B ≤
      liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop :=
  iInf_le _ f

/-- A test sequence is a globally Lipschitz sequence. -/
def ApproximatingSequence.toLipschitz {ν : Measure X} {B : Set X}
    (g : ApproximatingSequence ν B) : LipschitzApproximatingSequence ν B :=
  ⟨fun n => g.1 n, fun n => (g.1 n).lipschitz, g.2⟩

/-- A globally Lipschitz sequence is a locally Lipschitz sequence. -/
def LipschitzApproximatingSequence.toLocallyLipschitz {ν : Measure X} {B : Set X}
    (f : LipschitzApproximatingSequence ν B) : LocallyLipschitzApproximatingSequence ν B :=
  ⟨f.1, fun n => (f.2.1 n).choose_spec.locallyLipschitz, f.2.2⟩

/-- Tests are globally Lipschitz, so the Lipschitz relaxation is at most the perimeter. -/
theorem lipschitzRelaxation_le_perimeter (ν : Measure X) (B : Set X) :
    lipschitzRelaxation ν B ≤ perimeter ν B :=
  le_iInf fun g => lipschitzRelaxation_le_liminf ν B g.toLipschitz

omit [BorelSpace X] in
/-- Globally Lipschitz functions are locally Lipschitz, so the locally Lipschitz relaxation is
at most the Lipschitz one. -/
theorem locallyLipschitzRelaxation_le_lipschitzRelaxation (ν : Measure X) (B : Set X) :
    locallyLipschitzRelaxation ν B ≤ lipschitzRelaxation ν B :=
  le_iInf fun f => locallyLipschitzRelaxation_le_liminf ν B f.toLocallyLipschitz

theorem locallyLipschitzRelaxation_le_perimeter (ν : Measure X) (B : Set X) :
    locallyLipschitzRelaxation ν B ≤ perimeter ν B :=
  (locallyLipschitzRelaxation_le_lipschitzRelaxation ν B).trans
    (lipschitzRelaxation_le_perimeter ν B)

/-- For a finite measure the perimeter is at most the Lipschitz relaxation (the globally
Lipschitz bridge), on every metric space. -/
theorem perimeter_le_lipschitzRelaxation (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    perimeter ν B ≤ lipschitzRelaxation ν B :=
  le_iInf fun f => perimeter_le_liminf_of_lipschitz ν f.2.1 f.2.2

/-- The relaxation over globally Lipschitz approximants (Definition 3.3 class) is the perimeter,
for every finite Borel measure on a metric space. -/
theorem lipschitzRelaxation_eq_perimeter (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    lipschitzRelaxation ν B = perimeter ν B :=
  le_antisymm (lipschitzRelaxation_le_perimeter ν B) (perimeter_le_lipschitzRelaxation ν B)

/-- At a measurable finite-mass target, the globally Lipschitz bridge bounds the perimeter
without requiring finite total mass. -/
theorem perimeter_le_lipschitzRelaxation_of_measure_lt_top (ν : Measure X) {B : Set X}
    (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    perimeter ν B ≤ lipschitzRelaxation ν B :=
  le_iInf fun f => perimeter_le_liminf_of_lipschitz_of_measure_lt_top ν hB hνB f.2.1 f.2.2

/-- The global-L1, globally Lipschitz relaxation of ADMG Definition 3.3 equals the
bounded-support metric BV perimeter at every measurable finite-mass target, for every Borel
measure on a metric space. This bounded-support reduction does not assume finite total mass,
properness, or finiteness on bounded sets, and it does not identify a Minkowski relaxation. -/
theorem lipschitzRelaxation_eq_perimeter_of_measure_lt_top (ν : Measure X) {B : Set X}
    (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    lipschitzRelaxation ν B = perimeter ν B :=
  le_antisymm (lipschitzRelaxation_le_perimeter ν B)
    (perimeter_le_lipschitzRelaxation_of_measure_lt_top ν hB hνB)

/-- On a proper space with a finite measure the perimeter is at most the locally Lipschitz
relaxation (the locally Lipschitz bridge). -/
theorem perimeter_le_locallyLipschitzRelaxation [ProperSpace X] (ν : Measure X)
    [IsFiniteMeasure ν] (B : Set X) :
    perimeter ν B ≤ locallyLipschitzRelaxation ν B :=
  le_iInf fun f => perimeter_le_liminf_of_locallyLipschitz ν f.2.1 f.2.2

/-- The relaxation over locally Lipschitz approximants with global `L¹` convergence is the
perimeter, for every finite Borel measure on a proper metric space. -/
theorem locallyLipschitzRelaxation_eq_perimeter [ProperSpace X] (ν : Measure X)
    [IsFiniteMeasure ν] (B : Set X) :
    locallyLipschitzRelaxation ν B = perimeter ν B :=
  le_antisymm (locallyLipschitzRelaxation_le_perimeter ν B)
    (perimeter_le_locallyLipschitzRelaxation ν B)

/-- On a proper space with a finite measure the two relaxations agree. -/
theorem locallyLipschitzRelaxation_eq_lipschitzRelaxation [ProperSpace X] (ν : Measure X)
    [IsFiniteMeasure ν] (B : Set X) :
    locallyLipschitzRelaxation ν B = lipschitzRelaxation ν B :=
  (locallyLipschitzRelaxation_eq_perimeter ν B).trans (lipschitzRelaxation_eq_perimeter ν B).symm

section ClosedSupport

variable [SecondCountableTopology X]

omit [BorelSpace X] [SecondCountableTopology X] in
/-- The closed support of a measure on a proper space is proper. -/
theorem properSpace_support [ProperSpace X] (ν : Measure X) : ProperSpace ν.support :=
  ProperSpace.of_isClosed Measure.isClosed_support

/-- The Lipschitz relaxation of the closed-support law is its perimeter. -/
theorem lipschitzRelaxation_closedSupportLaw (ν : ProbabilityMeasure X)
    (B : Set (ν : Measure X).support) :
    lipschitzRelaxation (closedSupportLaw ν : Measure (ν : Measure X).support) B =
      perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) B :=
  lipschitzRelaxation_eq_perimeter _ B

/-- On a proper space, the locally Lipschitz relaxation of the closed-support law is its
perimeter. -/
theorem locallyLipschitzRelaxation_closedSupportLaw [ProperSpace X] (ν : ProbabilityMeasure X)
    (B : Set (ν : Measure X).support) :
    locallyLipschitzRelaxation (closedSupportLaw ν : Measure (ν : Measure X).support) B =
      perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) B :=
  haveI := properSpace_support (ν : Measure X)
  locallyLipschitzRelaxation_eq_perimeter _ B

end ClosedSupport

section CompactLocal

/-! ### Compact-set `L¹` convergence

The class below asks only for bare convergence of the indicator error on every compact set; no
local integrability of the approximants is imposed. Global `L¹` sequences belong to it, and on a
proper space with a finite measure its infimum is again the perimeter (phase-20 bridge). -/

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Locally Lipschitz approximating sequences of `1_B` in `L¹(ν)` on every compact set. -/
def CompactLocallyLipschitzApproximatingSequence (ν : Measure X) (B : Set X) : Type _ :=
  {f : ℕ → X → ℝ // (∀ n, LocallyLipschitz (f n)) ∧ ∀ K : Set X, IsCompact K →
    Tendsto (fun n => ∫⁻ x in K, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)}

/-- The relaxation over locally Lipschitz approximants converging on every compact set; `⊤` for
an empty class. -/
def compactLocallyLipschitzRelaxation (ν : Measure X) (B : Set X) : ENNReal :=
  ⨅ f : CompactLocallyLipschitzApproximatingSequence ν B,
    liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop

theorem compactLocallyLipschitzRelaxation_le_liminf (ν : Measure X) (B : Set X)
    (f : CompactLocallyLipschitzApproximatingSequence ν B) :
    compactLocallyLipschitzRelaxation ν B ≤
      liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop :=
  iInf_le _ f

/-- Global `L¹` convergence gives convergence on every compact set. -/
def LocallyLipschitzApproximatingSequence.toCompact {ν : Measure X} {B : Set X}
    (f : LocallyLipschitzApproximatingSequence ν B) :
    CompactLocallyLipschitzApproximatingSequence ν B :=
  ⟨f.1, f.2.1, fun K _ => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds f.2.2
    (fun _ => zero_le) fun _ => setLIntegral_le_lintegral K _⟩

theorem compactLocallyLipschitzRelaxation_le_locallyLipschitzRelaxation (ν : Measure X)
    (B : Set X) : compactLocallyLipschitzRelaxation ν B ≤ locallyLipschitzRelaxation ν B :=
  le_iInf fun f => compactLocallyLipschitzRelaxation_le_liminf ν B f.toCompact

/-- On a proper space, convergence on every compact set and on every closed ball are the same
premise (closed balls are compact; every compact set lies in a closed ball). -/
theorem forall_isCompact_iff_forall_closedBall [ProperSpace X] (ν : Measure X)
    (g : ℕ → X → ℝ≥0∞) :
    (∀ K : Set X, IsCompact K → Tendsto (fun n => ∫⁻ x in K, g n x ∂ν) atTop (𝓝 0)) ↔
      ∀ (x₀ : X) (r : ℝ), 0 < r →
        Tendsto (fun n => ∫⁻ x in Metric.closedBall x₀ r, g n x ∂ν) atTop (𝓝 0) :=
  ⟨fun h x₀ r _ => h _ (isCompact_closedBall x₀ r),
    fun h _ hK => tendsto_setLIntegral_of_isCompact ν h hK⟩

variable [BorelSpace X]

theorem compactLocallyLipschitzRelaxation_le_perimeter (ν : Measure X) (B : Set X) :
    compactLocallyLipschitzRelaxation ν B ≤ perimeter ν B :=
  (compactLocallyLipschitzRelaxation_le_locallyLipschitzRelaxation ν B).trans
    (locallyLipschitzRelaxation_le_perimeter ν B)

/-- On a proper space with a finite measure the perimeter is at most the compact-local
relaxation (phase-20 bridge). -/
theorem perimeter_le_compactLocallyLipschitzRelaxation [ProperSpace X] (ν : Measure X)
    [IsFiniteMeasure ν] (B : Set X) :
    perimeter ν B ≤ compactLocallyLipschitzRelaxation ν B :=
  le_iInf fun f => perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact ν f.2.1 f.2.2

/-- The relaxation over locally Lipschitz approximants converging on every compact set is the
perimeter, for every finite Borel measure on a proper metric space. -/
theorem compactLocallyLipschitzRelaxation_eq_perimeter [ProperSpace X] (ν : Measure X)
    [IsFiniteMeasure ν] (B : Set X) :
    compactLocallyLipschitzRelaxation ν B = perimeter ν B :=
  le_antisymm (compactLocallyLipschitzRelaxation_le_perimeter ν B)
    (perimeter_le_compactLocallyLipschitzRelaxation ν B)

/-- At a measurable finite-mass target, for every Borel measure on a proper space, the perimeter
is at most the compact-local relaxation (ADMG Remark 3.5 without finite total mass). -/
theorem perimeter_le_compactLocallyLipschitzRelaxation_of_measure_lt_top [ProperSpace X]
    (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    perimeter ν B ≤ compactLocallyLipschitzRelaxation ν B :=
  le_iInf fun f =>
    perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact_of_measure_lt_top ν hB hνB f.2.1 f.2.2

/-- The compact-local locally Lipschitz relaxation equals the bounded-support perimeter at every
measurable finite-mass target, for every Borel measure on a proper metric space. -/
theorem compactLocallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top [ProperSpace X]
    (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    compactLocallyLipschitzRelaxation ν B = perimeter ν B :=
  le_antisymm (compactLocallyLipschitzRelaxation_le_perimeter ν B)
    (perimeter_le_compactLocallyLipschitzRelaxation_of_measure_lt_top ν hB hνB)

/-- The locally Lipschitz relaxation with global `L¹` convergence equals the bounded-support
perimeter at every measurable finite-mass target, for every Borel measure on a proper metric
space. -/
theorem locallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top [ProperSpace X]
    (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    locallyLipschitzRelaxation ν B = perimeter ν B :=
  le_antisymm (locallyLipschitzRelaxation_le_perimeter ν B)
    ((perimeter_le_compactLocallyLipschitzRelaxation_of_measure_lt_top ν hB hνB).trans
      (compactLocallyLipschitzRelaxation_le_locallyLipschitzRelaxation ν B))

/-- On a proper space, the compact-local relaxation of the closed-support law is its perimeter. -/
theorem compactLocallyLipschitzRelaxation_closedSupportLaw [SecondCountableTopology X]
    [ProperSpace X] (ν : ProbabilityMeasure X) (B : Set (ν : Measure X).support) :
    compactLocallyLipschitzRelaxation (closedSupportLaw ν : Measure (ν : Measure X).support) B =
      perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) B :=
  haveI := properSpace_support (ν : Measure X)
  compactLocallyLipschitzRelaxation_eq_perimeter _ B

end CompactLocal

end FunctionalInequalities.KLS.MetricBV
