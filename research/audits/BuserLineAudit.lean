import FunctionalInequalities.KLS.LogConcave.Line.Buser
import Mathlib.Probability.Moments.Variance

/-!
# Scope audit for Stage 1 of the Buser route on the line

This client imports only the two new modules `KLS/LogConcave/Line/Isoperimetry.lean` and
`KLS/LogConcave/Line/Buser.lean` (through the second, which imports the first) and discharges
every Stage-1 obligation of the route file `research/audits/BuserRouteStatements.lean` from them.
The propositions `Q0`, `Q0'`, `Q1`, `Q1'`, `Q2`, `Q3`, `Q4`, `Q5` and the bookkeeping fact `D1`
are restated **verbatim** from that file as `route_Q0` … `route_D1`.

`B0`, the Buser half in every dimension with the constant `π`, is **not** an obligation of
Stage 1 and does not appear here: nothing in this round says anything about dimension two or
more, and the Stage-1 constant is `12`, not `π` (`route_D1`).

Two deviations from the route file's narrative, both in the proofs and not in the statements:

* `Q3` is stated for a `LineDensity`, which already carries a log-concave Borell density, so it is
  proved through the certified median bound `LineDensity.one_div_le_variance` of
  `Line/Variance.lean` together with `ρ(m) ≤ M`, rather than through a bathtub rearrangement.
  The statement is the route file's, unchanged.
* `Q1'` is proved for an arbitrary smooth domain without using discreteness of its frontier or an
  enumeration of its connected components: for an open set containing the median, the supremum of
  the complement to the left of the median and the infimum of the complement to its right are two
  frontier points that already carry `2 ρ(m) · ν(Wᶜ)`, and the three positions of the median
  relative to the domain (inside, on the frontier, outside the closure) are handled separately.

The boundary section records the zero-dimensional convention of `Q0'` (inverse scale `0`) and the
Dirac law on the line, where the Minkowski Cheeger infimum is `⊤` and the left side of `Q0`
vanishes.

The axiom reports at the end cover every public declaration of the two new modules and every
theorem of this client; each of them must list only `propext`, `Classical.choice` and
`Quot.sound`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set FunctionalInequalities
  FunctionalInequalities.KLS FunctionalInequalities.KLS.Isoperimetry
open FunctionalInequalities.Probability.Line (cdf)
open scoped ENNReal NNReal

namespace BuserLineAudit

/-! ### `Q5` — a log-concave law on the line has finite second moment -/

theorem route_Q5 : ∀ (ν : ProbabilityMeasure ℝ), LogConcave ν → MemLp id 2 (ν : Measure ℝ) :=
  fun _ hν ↦ hν.memLp_id_two

/-! ### `Q4` — the linear test: the variance is at most the smooth-test Poincaré constant -/

theorem route_Q4 : ∀ (ν : ProbabilityMeasure ℝ), MemLp id 2 (ν : Measure ℝ) →
    evariance id (ν : Measure ℝ) ≤ Poincare.SmoothTest.constant (ν : Measure ℝ) :=
  fun ν h ↦ evariance_le_smoothTest_constant ν h

/-! ### `Q3` — a bounded density has variance at least `1 / (12 M²)` -/

theorem route_Q3 : ∀ (ν : ProbabilityMeasure ℝ) (d : LineDensity ν) {M : ℝ}, 0 < M →
    (∀ x, d.ρ x ≤ M) → ENNReal.ofReal (1 / (12 * M ^ 2)) ≤ evariance id (ν : Measure ℝ) := by
  intro ν d M hM hbd
  exact d.one_div_le_evariance (M := M) hM hbd

/-! ### `Q2` — the density is at most twice its value at a median -/

theorem route_Q2 : ∀ {ν : ProbabilityMeasure ℝ}, LogConcave ν →
    ∀ (_hi : (interior (ν : Measure ℝ).support).Nonempty) (d : LineDensity ν) {m : ℝ},
    cdf ν m = 1 / 2 → ∀ x, d.ρ x ≤ 2 * d.ρ m := by
  intro ν hν hi d m hm x
  exact d.le_two_mul (hμ := hν) (hi := hi) (hm := hm) x

/-! ### `Q1'` — the smooth-domain form that `Q1` reduces to through `h_M = h_S` -/

theorem route_Q1' : ∀ {ν : ProbabilityMeasure ℝ}, LogConcave ν →
    ∀ (_hi : (interior (ν : Measure ℝ).support).Nonempty) (d : LineDensity ν) {m : ℝ},
    cdf ν m = 1 / 2 → ∀ (U : SmoothDomain ℝ),
    ENNReal.ofReal (2 * d.ρ m) * min ((ν : Measure ℝ) U.carrier) (1 - (ν : Measure ℝ) U.carrier) ≤
      relativePerimeter d.ρ (interior (ν : Measure ℝ).support) U := by
  intro ν hν hi d m hm U
  exact d.mul_min_le_relativePerimeter (hμ := hν) (hi := hi) (hm := hm) U

/-! ### `Q1` — one-dimensional isoperimetry: `2 ρ(m) ≤ h_M(ν)` -/

theorem route_Q1 : ∀ {ν : ProbabilityMeasure ℝ}, LogConcave ν →
    ∀ (_hi : (interior (ν : Measure ℝ).support).Nonempty) (d : LineDensity ν) {m : ℝ},
    cdf ν m = 1 / 2 → ENNReal.ofReal (2 * d.ρ m) ≤ minkowskiConstant ν := by
  intro ν hν hi d m hm
  exact d.two_mul_le_minkowskiConstant (hμ := hν) (hi := hi) (hm := hm)

/-! ### `Q0` — Stage 1 target on the line: `Ψ² ≤ 12 C_P^smooth` -/

theorem route_Q0 : ∀ (ν : ProbabilityMeasure ℝ), LogConcave ν →
    (minkowskiConstant ν)⁻¹ ^ 2 ≤ 12 * Poincare.SmoothTest.constant (ν : Measure ℝ) :=
  fun _ hν ↦ hν.inv_minkowskiConstant_sq_le

/-! ### `Q0'` — Stage 1 target in the Blueprint's variables -/

theorem route_Q0' : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E}, LogConcave μ →
    Module.finrank ℝ (Probability.affineSupport μ).direction ≤ 1 →
    Isoperimetry.inverseScale μ ^ 2 ≤ 12 * Poincare.LocalSlope.Intrinsic.constant μ := by
  intro E _ _ _ _ _ _ _ μ hμ hdim
  exact hμ.inverseScale_sq_le_of_finrank_le_one hdim

/-! ### `D1` — the sharpness bookkeeping: `12` is not `π` -/

theorem route_D1 : Real.pi < 12 := by
  have := Real.pi_le_four
  linarith

/-! ### Boundary cases -/

/-- Dimension zero in `Q0'`: the affine-support constant is `⊤` by convention, so the inverse
scale vanishes and the left side of `Q0'` is `0`. -/
theorem boundary_inverseScale_eq_zero_of_finrank_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E)
    (hdim : Module.finrank ℝ (Probability.affineSupport μ).direction = 0) :
    Isoperimetry.inverseScale μ = 0 := by
  have htop : Isoperimetry.constant μ = ⊤ := by
    unfold Isoperimetry.constant
    rw [if_pos hdim]
  rw [Isoperimetry.inverseScale, htop, ENNReal.inv_top]

/-- The Dirac law on the line: its support is a single point, no Borel set has intermediate mass,
the Minkowski Cheeger infimum is `⊤`, and the left side of `Q0` vanishes. -/
theorem boundary_minkowskiConstant_dirac (a : ℝ) :
    minkowskiConstant (Probability.ofMeasure (Measure.dirac a)) = ⊤ := by
  set ν : ProbabilityMeasure ℝ := Probability.ofMeasure (Measure.dirac a) with hν
  have hcoe : (ν : Measure ℝ) = Measure.dirac a := rfl
  have hsupp : (ν : Measure ℝ).support ⊆ {a} := by
    intro x hx
    by_contra hxa
    refine (Measure.notMem_support_iff_exists.mpr ⟨({a} : Set ℝ)ᶜ, ?_, ?_⟩) hx
    · exact (isClosed_singleton.isOpen_compl).mem_nhds hxa
    · rw [hcoe, Measure.dirac_apply' _ (measurableSet_singleton a).compl]
      simp
  have hempty : interior (ν : Measure ℝ).support = ∅ := by
    have := interior_mono hsupp
    rwa [interior_singleton, Set.subset_empty_iff] at this
  exact LogConcave.minkowskiConstant_eq_top_of_interior_empty (logConcave_dirac a) hempty

theorem boundary_inv_minkowskiConstant_dirac (a : ℝ) :
    (minkowskiConstant (Probability.ofMeasure (Measure.dirac a)))⁻¹ ^ 2 = 0 := by
  rw [boundary_minkowskiConstant_dirac a, ENNReal.inv_top]
  simp

end BuserLineAudit

/-! ### Axiom reports

Every public declaration of `KLS/LogConcave/Line/Isoperimetry.lean`, every public declaration of
`KLS/LogConcave/Line/Buser.lean`, and every theorem of this client. -/

#print axioms FunctionalInequalities.KLS.surfaceMeasure_real
#print axioms FunctionalInequalities.KLS.surfaceMeasure_real_singleton
#print axioms FunctionalInequalities.KLS.measure_Iic_eq_ofReal_cdf
#print axioms FunctionalInequalities.KLS.measure_eq_ofReal_measureReal
#print axioms FunctionalInequalities.KLS.LineDensity.ofReal_le_setLIntegral
#print axioms FunctionalInequalities.KLS.LineDensity.measure_singleton
#print axioms FunctionalInequalities.KLS.LineDensity.interior_pos_subset
#print axioms FunctionalInequalities.KLS.LineDensity.abs_le_two_mul
#print axioms FunctionalInequalities.KLS.LineDensity.le_two_mul
#print axioms FunctionalInequalities.KLS.LineDensity.mul_measure_Iio_diff_le
#print axioms FunctionalInequalities.KLS.LineDensity.mul_measure_Ioi_diff_le
#print axioms FunctionalInequalities.KLS.LineDensity.mul_measure_compl_le
#print axioms FunctionalInequalities.KLS.LineDensity.mul_min_le_relativePerimeter
#print axioms FunctionalInequalities.KLS.LineDensity.two_mul_le_minkowskiConstant

#print axioms FunctionalInequalities.KLS.nonempty_linearIsometryEquiv_real
#print axioms FunctionalInequalities.KLS.Isoperimetry.thickening_preimage_isometry
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_map
#print axioms FunctionalInequalities.KLS.evariance_le_smoothTest_constant
#print axioms FunctionalInequalities.KLS.LineDensity.interior_support_nonempty
#print axioms FunctionalInequalities.KLS.LineDensity.one_div_le_evariance
#print axioms FunctionalInequalities.KLS.LogConcave.exists_support_eq_singleton
#print axioms FunctionalInequalities.KLS.LogConcave.minkowskiConstant_eq_top_of_interior_empty
#print axioms FunctionalInequalities.KLS.LogConcave.inv_minkowskiConstant_sq_le
#print axioms FunctionalInequalities.KLS.LogConcave.inverseScale_sq_le_of_finrank_le_one

#print axioms BuserLineAudit.route_Q0
#print axioms BuserLineAudit.route_Q0'
#print axioms BuserLineAudit.route_Q1
#print axioms BuserLineAudit.route_Q1'
#print axioms BuserLineAudit.route_Q2
#print axioms BuserLineAudit.route_Q3
#print axioms BuserLineAudit.route_Q4
#print axioms BuserLineAudit.route_Q5
#print axioms BuserLineAudit.route_D1
#print axioms BuserLineAudit.boundary_inverseScale_eq_zero_of_finrank_zero
#print axioms BuserLineAudit.boundary_minkowskiConstant_dirac
#print axioms BuserLineAudit.boundary_inv_minkowskiConstant_dirac
