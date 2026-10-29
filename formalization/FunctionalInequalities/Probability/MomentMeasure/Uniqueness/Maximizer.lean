import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.ExtendedMidpointEquality

/-!
# Uniqueness of the maximizers of the CEK functional up to translation

Let `μ` be a probability measure on a finite-dimensional real inner-product space and let
`I_μ(f) = log ∫ e^{-f*} − ∫ f dμ` be the functional of Cordero-Erausquin–Klartag, *Moment measures*
(arXiv:1304.0630v1), Proposition 12 (`variationalFunctional`). If `φ₀` and `φ₁` both maximize
`I_μ` among `μ`-integrable potentials and are normalized by `∫ e^{-φᵢ*} = 1`, then their
conjugates are translates of each other: `φ₁*(y) = φ₀*(y − y₀)` for all `y`
(`exists_eq_translate_legendre_of_maximizer`).

This is the uniqueness argument of CEK, proof of Theorem 2 ((36)–(37) and the equality case of
Prékopa's inequality), applied to two maximizers: the midpoint competitor `(φ₀ + φ₁)/2` has
`I_μ((φ₀ + φ₁)/2) ≤ I_μ(φᵢ)`, which forces `∫ e^{-((φ₀ + φ₁)/2)*} ≤ 1`, while
`((φ₀ + φ₁)/2)*((x + y)/2) ≤ (φ₀*(x) + φ₁*(y))/2`; the equality case
`exists_eq_translate_of_midpoint_le_of_lintegral_le_one` concludes. Every maximizer's conjugate
has moment measure `μ` (`ofPotential_legendre_eq_of_maximizer`), so the moment potential produced
by the variational method is unique up to translation among conjugates of maximizers; that every
essentially continuous moment potential arises this way is CEK Theorem 8
(`Probability.MomentMeasure.variationalFunctional_le_legendre`, module
`Probability.MomentMeasure.Maximality.EssentiallyContinuous`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The midpoint `(φ₀ + φ₁)/2` of two extended-real potentials, `+∞` where either one is. -/
private def midPotential (φ₀ φ₁ : E → EReal) (p : E) : EReal :=
  if φ₀ p = ⊤ ∨ φ₁ p = ⊤ then ⊤ else ((((φ₀ p).toReal + (φ₁ p).toReal) / 2 : ℝ) : EReal)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `((φ₀ + φ₁)/2)*((x + y)/2) ≤ (φ₀*(x) + φ₁*(y))/2`, in density form. -/
private theorem density_legendre_midPotential {φ₀ φ₁ : E → EReal} (hφ₀ : ProperPotential φ₀)
    (hφ₁ : ProperPotential φ₁) (x y : E) :
    density (legendre φ₀) x ^ (1 / 2 : ℝ) * density (legendre φ₁) y ^ (1 - 1 / 2 : ℝ) ≤
      density (legendre (midPotential φ₀ φ₁)) ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) := by
  by_cases hx : legendre φ₀ x = ⊤
  · have h0 : density (legendre φ₀) x = 0 := by rw [density, hx, EReal.neg_top, EReal.exp_bot]
    rw [h0, ENNReal.zero_rpow_of_pos (by norm_num), zero_mul]
    exact bot_le
  by_cases hy : legendre φ₁ y = ⊤
  · have h0 : density (legendre φ₁) y = 0 := by rw [density, hy, EReal.neg_top, EReal.exp_bot]
    rw [h0, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]
    exact bot_le
  have hbx := legendre_ne_bot φ₀ hφ₀ x
  have hby := legendre_ne_bot φ₁ hφ₁ y
  set a := (legendre φ₀ x).toReal with ha
  set b := (legendre φ₁ y).toReal with hb
  have hax : legendre φ₀ x = (a : EReal) := (EReal.coe_toReal hx hbx).symm
  have hby' : legendre φ₁ y = (b : EReal) := (EReal.coe_toReal hy hby).symm
  have hle : legendre (midPotential φ₀ φ₁) ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) ≤
      (((a + b) / 2 : ℝ) : EReal) := by
    refine iSup_le fun p => ?_
    by_cases hp : φ₀ p = ⊤ ∨ φ₁ p = ⊤
    · simp only [midPotential, hp, if_true, EReal.sub_top, bot_le]
    · simp only [midPotential, hp, if_false]
      push Not at hp
      have h₀ : ((⟪p, x⟫ - (φ₀ p).toReal : ℝ) : EReal) ≤ (a : EReal) := by
        rw [← hax, EReal.coe_sub, EReal.coe_toReal hp.1 (hφ₀.1 p)]
        exact le_iSup (fun z : E => (⟪z, x⟫ : EReal) - φ₀ z) p
      have h₁ : ((⟪p, y⟫ - (φ₁ p).toReal : ℝ) : EReal) ≤ (b : EReal) := by
        rw [← hby', EReal.coe_sub, EReal.coe_toReal hp.2 (hφ₁.1 p)]
        exact le_iSup (fun z : E => (⟪z, y⟫ : EReal) - φ₁ z) p
      have h₀' := EReal.coe_le_coe_iff.mp h₀
      have h₁' := EReal.coe_le_coe_iff.mp h₁
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff, inner_add_right, real_inner_smul_right,
        real_inner_smul_right]
      linarith
  have hdens : density (legendre (midPotential φ₀ φ₁)) ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) ≥
      ENNReal.ofReal (Real.exp (-((a + b) / 2))) := by
    rw [density, ← EReal.exp_coe, EReal.coe_neg]
    exact EReal.exp_monotone (EReal.neg_le_neg_iff.mpr hle)
  refine le_trans (le_of_eq ?_) hdens
  rw [density, density, hax, hby', ← EReal.coe_neg, ← EReal.coe_neg, EReal.exp_coe,
    EReal.exp_coe, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 2
  ring

/-- **Maximizers of the CEK functional are unique up to translation** (Cordero-Erausquin–Klartag
arXiv:1304.0630v1, proof of Theorem 2, uniqueness, (36)–(37), applied to maximizers of
Proposition 12). Let `μ` be a probability measure on a finite-dimensional real inner-product space
and let `φ₀, φ₁` be `μ`-integrable potentials with `∫ e^{-φᵢ*} dx = 1`, each maximizing
`I_μ(f) = log ∫ e^{-f*} − ∫ f dμ` among `μ`-integrable `f`. Then `φ₁*(y) = φ₀*(y − y₀)` for all
`y`, for some `y₀`. -/
theorem exists_eq_translate_legendre_of_maximizer {μ : Measure E} [IsProbabilityMeasure μ]
    {φ₀ φ₁ : E → EReal} (hφ₀ : PotentialIntegrable φ₀ μ) (hφ₁ : PotentialIntegrable φ₁ μ)
    (hm₀ : mass volume (legendre φ₀) = 1) (hm₁ : mass volume (legendre φ₁) = 1)
    (hmax₀ : ∀ f : E → EReal, PotentialIntegrable f μ →
      variationalFunctional volume μ f ≤ variationalFunctional volume μ φ₀)
    (hmax₁ : ∀ f : E → EReal, PotentialIntegrable f μ →
      variationalFunctional volume μ f ≤ variationalFunctional volume μ φ₁) :
    ∃ y₀ : E, ∀ y, legendre φ₁ y = legendre φ₀ (y - y₀) := by
  -- properness from a.e. finiteness
  have hprop : ∀ {φ : E → EReal}, PotentialIntegrable φ μ → ProperPotential φ := by
    intro φ hφ
    refine ⟨hφ.1, ?_⟩
    obtain ⟨p, hp⟩ := hφ.2.1.exists
    exact ⟨p, hp⟩
  have hp₀ := hprop hφ₀
  have hp₁ := hprop hφ₁
  set φh := midPotential φ₀ φ₁ with hφh
  -- the midpoint competitor is integrable, with integral the average
  have hae : ∀ᵐ p ∂μ, (φh p).toReal = ((φ₀ p).toReal + (φ₁ p).toReal) / 2 := by
    filter_upwards [hφ₀.2.1, hφ₁.2.1] with p h₀ h₁
    have hn : ¬(φ₀ p = ⊤ ∨ φ₁ p = ⊤) := by tauto
    simp only [hφh, midPotential, hn, if_false, EReal.toReal_coe]
  have hint : Integrable (fun p => (φh p).toReal) μ :=
    ((hφ₀.2.2.add hφ₁.2.2).div_const 2).congr (hae.mono fun p hp => hp.symm)
  have hφhI : PotentialIntegrable φh μ := by
    refine ⟨fun p => ?_, ?_, hint⟩
    · simp only [hφh, midPotential]
      split_ifs
      · exact top_ne_bot
      · exact EReal.coe_ne_bot _
    · filter_upwards [hφ₀.2.1, hφ₁.2.1] with p h₀ h₁
      have hn : ¬(φ₀ p = ⊤ ∨ φ₁ p = ⊤) := by tauto
      simp only [hφh, midPotential, hn, if_false]
      exact EReal.coe_ne_top _
  have hav : ∫ p, (φh p).toReal ∂μ =
      ((∫ p, (φ₀ p).toReal ∂μ) + ∫ p, (φ₁ p).toReal ∂μ) / 2 := by
    rw [integral_congr_ae hae, integral_div, integral_add hφ₀.2.2 hφ₁.2.2]
  -- maximality bounds the mass of the midpoint conjugate by `1`
  set c₀ := ∫ p, (φ₀ p).toReal ∂μ
  set c₁ := ∫ p, (φ₁ p).toReal ∂μ
  set ch := ∫ p, (φh p).toReal ∂μ
  have hbound : ∀ {c : ℝ}, (variationalFunctional volume μ φh ≤ ((-c : ℝ) : EReal)) →
      ENNReal.log (mass volume (legendre φh)) ≤ ((ch - c : ℝ) : EReal) := by
    intro c h
    simp only [variationalFunctional] at h
    have h' := EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
      |>.mp h
    rwa [← EReal.coe_add, show -c + ch = ch - c by ring] at h'
  have hv₀ : variationalFunctional volume μ φ₀ = ((-c₀ : ℝ) : EReal) := by
    rw [variationalFunctional, hm₀, ENNReal.log_one, zero_sub, ← EReal.coe_neg]
  have hv₁ : variationalFunctional volume μ φ₁ = ((-c₁ : ℝ) : EReal) := by
    rw [variationalFunctional, hm₁, ENNReal.log_one, zero_sub, ← EReal.coe_neg]
  have hb₀ := hbound ((hmax₀ φh hφhI).trans_eq hv₀)
  have hb₁ := hbound ((hmax₁ φh hφhI).trans_eq hv₁)
  have hmass : mass volume (legendre φh) ≤ 1 := by
    rw [← ENNReal.log_le_zero_iff]
    rcases le_total c₀ c₁ with h | h
    · refine hb₁.trans ?_
      rw [← EReal.coe_zero, EReal.coe_le_coe_iff, hav]
      linarith
    · refine hb₀.trans ?_
      rw [← EReal.coe_zero, EReal.coe_le_coe_iff, hav]
      linarith
  -- the equality case of Prékopa–Leindler
  exact exists_eq_translate_of_midpoint_le_of_lintegral_le_one
    (convexPotential_legendre _ hp₀.2) (convexPotential_legendre _ hp₁.2)
    (lowerSemicontinuous_legendre _) (lowerSemicontinuous_legendre _) hm₀ hm₁
    (measurable_density_legendre φh) (density_legendre_midPotential hp₀ hp₁) hmass

end FunctionalInequalities.Probability.MomentMeasure
