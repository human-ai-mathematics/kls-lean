import FunctionalInequalities.Probability.MomentMeasure.ConjugateMass

/-! Audit clients for exponential potential measures, the CEK functional and conjugate-mass semicontinuity
(`Probability/MomentMeasure/{Basic,ConjugateMass}.lean`; Cordero-Erausquin–Klartag, arXiv:1304.0630v1, Proposition 12
and Lemma 17, (56b)). Section `AcceptedClients` is verbatim from the accepted `ConjugateMassClients.lean` (16e578f1…):
zero conjugate mass, infinite conjugate mass, and a sequence with infinite initial dual mass and zero tail.
Section `ExtendedValueClients` is new in this candidate: the functional takes the values `⊥` and `⊤` at zero and
infinite dual mass, and an infinite-mass exponential measure is not finite. -/

noncomputable section

section AcceptedClients

open MeasureTheory Filter Set
open scoped ENNReal Topology
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.MomentMeasure

namespace CEKConjugateMassClients

/-- The actual Legendre transform of zero on the line is infinite away from zero. -/
theorem legendre_zero_top {y : ℝ} (hy : y ≠ 0) :
    legendre (fun _ : ℝ => (0 : EReal)) y = ⊤ := by
  by_contra ht
  have hb : legendre (fun _ : ℝ => (0 : EReal)) y ≠ ⊥ :=
    (legendre_ne_bot_iff _ y).mpr ⟨0, by simp⟩
  lift legendre (fun _ : ℝ => (0 : EReal)) y to ℝ using ⟨ht, hb⟩ with r hr
  have hh := le_iSup (fun x : ℝ => (inner ℝ x y : EReal) - (0 : EReal)) ((r + 1) / y)
  change (inner ℝ ((r + 1) / y) y : EReal) - 0 ≤ legendre (fun _ : ℝ => (0 : EReal)) y at hh
  rw [← hr, sub_zero] at hh
  have hinner : inner ℝ ((r + 1) / y) y = r + 1 := by
    rw [Real.inner_apply]
    exact div_mul_cancel₀ _ hy
  rw [hinner] at hh
  have hreal := EReal.coe_le_coe_iff.mp hh
  linarith

/-- Zero conjugate exponential mass is retained as an actual integral. -/
theorem zero_exponential_mass :
    mass volume (legendre (fun _ : ℝ => (0 : EReal))) = 0 := by
  change (∫⁻ y : ℝ, density (legendre (fun _ => (0 : EReal))) y) = 0
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with y hy
  simp only [density, legendre_zero_top hy, EReal.neg_top, EReal.exp_bot, Pi.zero_apply]

/-- A potential concentrated at the origin has the actual zero conjugate,
therefore infinite exponential mass in positive-dimensional Lebesgue space. -/
def originPotential (x : ℝ) : EReal := if x = 0 then 0 else ⊤

theorem legendre_originPotential (y : ℝ) : legendre originPotential y = 0 := by
  apply le_antisymm
  · apply iSup_le
    intro x
    by_cases hx : x = 0
    · subst x
      simp [originPotential]
    · simp [originPotential, hx]
  · have h0 : originPotential 0 = 0 := by simp [originPotential]
    have h := le_iSup (fun x : ℝ => (inner ℝ x y : EReal) - originPotential x) 0
    change (inner ℝ (0 : ℝ) y : EReal) - originPotential 0 ≤ legendre originPotential y at h
    simpa only [h0, inner_zero_left, EReal.coe_zero, sub_zero] using h

theorem infinite_origin_conjugate_mass : mass volume (legendre originPotential) = ⊤ := by
  simp [mass, density, legendre_originPotential]

/-- The semicontinuity support accepts a genuinely infinite initial dual mass
and then zero masses; the finite tail domination is derived from convergence. -/
theorem infinite_initial_mass_zero_tail :
    let φ : ℕ → ℝ → EReal := fun j x => if j = 0 then originPotential x else 0
    mass volume (legendre (φ 0)) = ⊤ ∧
      mass volume (legendre (fun _ : ℝ => (0 : EReal))) = 0 ∧
      limsup (fun j => mass volume (legendre (φ j))) atTop ≤ 0 := by
  dsimp only
  let φ : ℕ → ℝ → EReal := fun j x => if j = 0 then originPotential x else 0
  have hlim : ∀ x ∈ (univ : Set ℝ), Tendsto (fun j => φ j x) atTop (𝓝 (0 : EReal)) := by
    intro x _
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with j hj
    simp only [φ, if_neg (ne_of_gt hj)]
  have h := limsup_mass_legendre_le (volume : Measure ℝ) φ (fun _ => (0 : EReal))
    isOpen_univ convex_univ (mem_univ 0) (fun _ _ => by simp) hlim
    (fun _ => tendsto_const_nhds) (by simp)
  refine ⟨?_, zero_exponential_mass, ?_⟩
  · simpa [φ] using infinite_origin_conjugate_mass
  · simpa only [zero_exponential_mass] using h.2

end CEKConjugateMassClients

end AcceptedClients

section ExtendedValueClients

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.MomentMeasure

namespace CEKConjugateMassClients

/-- Zero dual mass: the extended logarithm gives `I_μ(0) = ⊥` for the Dirac mass at `0` on the line. -/
theorem variationalFunctional_zero_mass :
    variationalFunctional volume (Measure.dirac (0 : ℝ)) (fun _ => (0 : EReal)) = ⊥ := by
  simp [variationalFunctional, zero_exponential_mass]

/-- Infinite dual mass: `I_μ = ⊤` for the potential concentrated at the origin, which is finite on the support. -/
theorem variationalFunctional_infinite_mass :
    variationalFunctional volume (Measure.dirac (0 : ℝ)) originPotential = ⊤ := by
  simp [variationalFunctional, infinite_origin_conjugate_mass, originPotential]

/-- The total mass of the exponential measure is `mass`. -/
theorem weightedMeasure_univ (φ : ℝ → EReal) :
    weightedMeasure volume φ Set.univ = mass volume φ := by
  simp [weightedMeasure, mass]

/-- The exponential measure of the conjugate of the origin potential is not a finite measure. -/
theorem not_isFiniteMeasure_weightedMeasure_origin :
    ¬ IsFiniteMeasure (weightedMeasure volume (legendre originPotential)) := by
  intro h
  have hlt := measure_lt_top (weightedMeasure volume (legendre originPotential)) Set.univ
  rw [weightedMeasure_univ, infinite_origin_conjugate_mass] at hlt
  exact lt_irrefl _ hlt

end CEKConjugateMassClients

end ExtendedValueClients

#print axioms CEKConjugateMassClients.legendre_zero_top
#print axioms CEKConjugateMassClients.zero_exponential_mass
#print axioms CEKConjugateMassClients.legendre_originPotential
#print axioms CEKConjugateMassClients.infinite_origin_conjugate_mass
#print axioms CEKConjugateMassClients.infinite_initial_mass_zero_tail
#print axioms CEKConjugateMassClients.variationalFunctional_zero_mass
#print axioms CEKConjugateMassClients.variationalFunctional_infinite_mass
#print axioms CEKConjugateMassClients.weightedMeasure_univ
#print axioms CEKConjugateMassClients.not_isFiniteMeasure_weightedMeasure_origin
#print axioms FunctionalInequalities.Probability.MomentMeasure.mass_legendre_mono
#print axioms FunctionalInequalities.Probability.MomentMeasure.measurable_density_legendre
#print axioms FunctionalInequalities.Probability.integrable_exp_sub_norm
#print axioms FunctionalInequalities.Probability.MomentMeasure.limsup_density_legendre_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exponential_domination
#print axioms FunctionalInequalities.Probability.MomentMeasure.limsup_mass_legendre_le
