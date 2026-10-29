import FunctionalInequalities.KLS.Geometry.Cheeger.BVIdentification
import FunctionalInequalities.Energy.LocalSlope.Gradient
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Independent full-signature clients for the relaxation infima over globally and locally
Lipschitz approximants: the classes carry no perimeter or energy field; the Lipschitz relaxation
equals the perimeter for every finite Borel measure on a metric space, the locally Lipschitz one
on proper spaces. Both directions are used: a test sequence bounds the Lipschitz relaxation, and
the non-globally-Lipschitz sequence `x ↦ x²` bounds the locally Lipschitz relaxation of `{1}`
for the two-atom law by `1`, hence the perimeter. Edge cases through the infima: an empty class
gives `⊤`, infinite perimeter transfers, the zero measure and the empty carrier. Support
instances: the closed-support law of a proper law on `ℝ`, and the actual closed intrinsic support
of a finite-dimensional probability law. `L¹_loc` convergence and non-proper spaces for the
locally Lipschitz class are not claimed. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVTestClassAudit

open FunctionalInequalities
open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

section Generic

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem globalIdentity (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    lipschitzRelaxation ν B = perimeter ν B := by
  exact lipschitzRelaxation_eq_perimeter ν B

theorem localIdentity [ProperSpace X] (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    locallyLipschitzRelaxation ν B = perimeter ν B := by
  exact locallyLipschitzRelaxation_eq_perimeter ν B

theorem bothClassesAgree [ProperSpace X] (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    locallyLipschitzRelaxation ν B = lipschitzRelaxation ν B := by
  exact locallyLipschitzRelaxation_eq_lipschitzRelaxation ν B

/-- Inclusions hold for every measure, without finiteness or properness. -/
theorem inclusions (ν : Measure X) (B : Set X) :
    locallyLipschitzRelaxation ν B ≤ lipschitzRelaxation ν B ∧
      lipschitzRelaxation ν B ≤ perimeter ν B :=
  ⟨locallyLipschitzRelaxation_le_lipschitzRelaxation ν B, lipschitzRelaxation_le_perimeter ν B⟩

/-- Direction one, used: every actual test sequence bounds the Lipschitz relaxation. -/
theorem testSequenceBound (ν : Measure X) (B : Set X) (g : ApproximatingSequence ν B) :
    lipschitzRelaxation ν B ≤ liminf (fun n => cost ν (g.1 n)) atTop :=
  lipschitzRelaxation_le_liminf ν B g.toLipschitz

/-- Direction two, used: every globally Lipschitz sequence bounds the perimeter, through the
relaxation identity. -/
theorem lipschitzSequenceBound (ν : Measure X) [IsFiniteMeasure ν] (B : Set X)
    (f : LipschitzApproximatingSequence ν B) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop :=
  (lipschitzRelaxation_eq_perimeter ν B).symm.le.trans (lipschitzRelaxation_le_liminf ν B f)

/-- An empty class gives `⊤` directly through the infimum. -/
theorem emptyClassTop (ν : Measure X) (B : Set X)
    (h : IsEmpty (LocallyLipschitzApproximatingSequence ν B)) :
    locallyLipschitzRelaxation ν B = ⊤ ∧ lipschitzRelaxation ν B = ⊤ ∧ perimeter ν B = ⊤ := by
  have h1 : locallyLipschitzRelaxation ν B = ⊤ := by
    unfold locallyLipschitzRelaxation
    exact iInf_of_empty _
  have h2 : lipschitzRelaxation ν B = ⊤ :=
    top_le_iff.mp (h1 ▸ locallyLipschitzRelaxation_le_lipschitzRelaxation ν B)
  exact ⟨h1, h2, top_le_iff.mp (h2 ▸ lipschitzRelaxation_le_perimeter ν B)⟩

/-- Infinite perimeter transfers to both relaxations for a finite measure on a proper space. -/
theorem topTransfer [ProperSpace X] (ν : Measure X) [IsFiniteMeasure ν] {B : Set X}
    (htop : perimeter ν B = ⊤) :
    lipschitzRelaxation ν B = ⊤ ∧ locallyLipschitzRelaxation ν B = ⊤ := by
  rw [lipschitzRelaxation_eq_perimeter, locallyLipschitzRelaxation_eq_perimeter]
  exact ⟨htop, htop⟩

end Generic

/-- The zero measure on `ℝ`: both relaxations vanish. -/
theorem zeroMeasure (B : Set ℝ) :
    lipschitzRelaxation (0 : Measure ℝ) B = 0 ∧
      locallyLipschitzRelaxation (0 : Measure ℝ) B = 0 := by
  have hz : perimeter (0 : Measure ℝ) B = 0 := by
    have h := perimeter_le_liminf_of_lipschitz (0 : Measure ℝ) (B := B)
      (f := fun _ _ => (0 : ℝ)) (fun _ => ⟨0, LipschitzWith.const 0⟩) (by simp)
    simp only [lintegral_zero_measure, liminf_const] at h
    exact le_antisymm h bot_le
  rw [lipschitzRelaxation_eq_perimeter, locallyLipschitzRelaxation_eq_perimeter, hz]
  exact ⟨rfl, rfl⟩

/-- The empty carrier: both relaxations equal the perimeter for every measure and set. -/
theorem emptyCarrier (ν : Measure Empty) (B : Set Empty) :
    lipschitzRelaxation ν B = perimeter ν B ∧ locallyLipschitzRelaxation ν B = perimeter ν B := by
  have : IsFiniteMeasure ν := ⟨by simp [Measure.eq_zero_of_isEmpty ν]⟩
  exact ⟨lipschitzRelaxation_eq_perimeter ν B, locallyLipschitzRelaxation_eq_perimeter ν B⟩

/-- The two-atom law `(δ₀ + δ₁)/2` on `ℝ`. -/
def twoAtom : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1)

instance : IsFiniteMeasure twoAtom := by
  refine ⟨?_⟩
  simp only [twoAtom, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 two_pos) (by norm_num)

theorem twoAtom_lintegral (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂twoAtom = (2 : ℝ≥0∞)⁻¹ * (g 0 + g 1) := by
  simp [twoAtom, lintegral_smul_measure, lintegral_add_measure, lintegral_dirac, mul_add]

/-- The constant sequence `x ↦ x²` is a genuine locally Lipschitz approximating sequence of `{1}`
for the two-atom law. -/
def squareSequence : LocallyLipschitzApproximatingSequence twoAtom ({1} : Set ℝ) :=
  ⟨fun _ => fun x : ℝ => x ^ 2,
    fun _ => (by fun_prop : ContDiff ℝ 1 (fun x : ℝ => x ^ 2)).locallyLipschitz, by
      have h : ∫⁻ x, ‖(fun x : ℝ => x ^ 2) x - ({1} : Set ℝ).indicator (1 : ℝ → ℝ) x‖ₑ ∂twoAtom
          = 0 := by
        rw [twoAtom_lintegral]
        simp
      simp only [h]
      exact tendsto_const_nhds⟩

theorem square_slope_integral :
    ∫⁻ x, Energy.LocalSlope.apply (fun x : ℝ => x ^ 2) x ∂twoAtom = 1 := by
  have hslope : ∀ x : ℝ, Energy.LocalSlope.apply (fun x : ℝ => x ^ 2) x =
      ENNReal.ofReal |2 * x| := fun x => by
    rw [FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient _ _
      (by fun_prop : DifferentiableAt ℝ (fun x : ℝ => x ^ 2) x)]
    have hg : gradient (fun x : ℝ => x ^ 2) x = 2 * x := by
      simpa using (hasDerivAt_pow 2 x).hasGradientAt.gradient
    rw [hg, Real.norm_eq_abs]
  rw [twoAtom_lintegral]
  simp only [hslope]
  norm_num
  rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- A genuine use of the locally Lipschitz class: the relaxation of `{1}` is at most `1`, and by
the identity so is the perimeter (`x²` has no global Lipschitz constant). -/
theorem squareRelaxationBound :
    locallyLipschitzRelaxation twoAtom ({1} : Set ℝ) ≤ 1 ∧ perimeter twoAtom ({1} : Set ℝ) ≤ 1 := by
  have h := locallyLipschitzRelaxation_le_liminf twoAtom ({1} : Set ℝ) squareSequence
  simp only [squareSequence, liminf_const, square_slope_integral] at h
  exact ⟨h, (locallyLipschitzRelaxation_eq_perimeter twoAtom _).symm.le.trans h⟩

/-- The uniform law on `[0, 1]`, a proper law on `ℝ`: both relaxations of its closed-support law
equal its perimeter, for every subset of the support. -/
def uniformInterval : ProbabilityMeasure ℝ :=
  ⟨(volume : Measure ℝ).restrict (Set.Icc 0 1), ⟨by simp⟩⟩

theorem uniformSupportIdentity (B : Set (uniformInterval : Measure ℝ).support) :
    lipschitzRelaxation (closedSupportLaw uniformInterval : Measure _) B =
        perimeter (closedSupportLaw uniformInterval : Measure _) B ∧
      locallyLipschitzRelaxation (closedSupportLaw uniformInterval : Measure _) B =
        perimeter (closedSupportLaw uniformInterval : Measure _) B :=
  ⟨lipschitzRelaxation_closedSupportLaw _ B, locallyLipschitzRelaxation_closedSupportLaw _ B⟩

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The actual closed intrinsic support: both test classes give the perimeter, for every
finite-dimensional probability law, with no convexity or log-concavity. -/
theorem intrinsicIdentity (μ : ProbabilityMeasure E)
    (B : Set (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support) :
    lipschitzRelaxation (intrinsicClosedSupportLaw μ : Measure _) B =
        perimeter (intrinsicClosedSupportLaw μ : Measure _) B ∧
      locallyLipschitzRelaxation (intrinsicClosedSupportLaw μ : Measure _) B =
        perimeter (intrinsicClosedSupportLaw μ : Measure _) B :=
  ⟨lipschitzRelaxation_intrinsicClosedSupportLaw μ B,
    locallyLipschitzRelaxation_intrinsicClosedSupportLaw μ B⟩

end Intrinsic

/-- The intrinsic instance for an actual law on `ℝ`. -/
theorem intrinsicUniform (B : Set (Probability.intrinsicMeasure uniformInterval :
      Measure (Probability.affineSupport uniformInterval).direction).support) :
    locallyLipschitzRelaxation (intrinsicClosedSupportLaw uniformInterval : Measure _) B =
      perimeter (intrinsicClosedSupportLaw uniformInterval : Measure _) B :=
  locallyLipschitzRelaxation_intrinsicClosedSupportLaw uniformInterval B

#print axioms globalIdentity
#print axioms localIdentity
#print axioms bothClassesAgree
#print axioms inclusions
#print axioms testSequenceBound
#print axioms lipschitzSequenceBound
#print axioms emptyClassTop
#print axioms topTransfer
#print axioms zeroMeasure
#print axioms emptyCarrier
#print axioms squareSequence
#print axioms squareRelaxationBound
#print axioms uniformSupportIdentity
#print axioms intrinsicIdentity
#print axioms intrinsicUniform

end MetricBVTestClassAudit
