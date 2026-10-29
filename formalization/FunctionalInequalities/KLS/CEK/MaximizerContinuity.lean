import FunctionalInequalities.Analysis.Convex.Legendre.Affine
import FunctionalInequalities.Analysis.Convex.EssentialContinuity
import FunctionalInequalities.Analysis.Convex.FrontierGraph
import FunctionalInequalities.Probability.MomentMeasure.FirstVariation
import Mathlib.MeasureTheory.Function.L2Space

/-!
# CEK Proposition 10: the conjugate of a maximizer is essentially continuous

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Proposition 10, in the form used
in the existence part of Theorem 2: let `μ` be a finite measure with finite first moment, `φ` a
convex `μ`-integrable potential with `∫ exp(-φ*) dx = 1` maximizing `I_μ(f) = log ∫ e^{-f*} - ∫ f dμ`
among convex `μ`-integrable competitors (CEK (22)/(39)). Then `ψ = φ*` is essentially continuous
(`essentiallyContinuous_legendre_of_maximizer`).

The proof is the source's. Near a point `x₀` of `{ψ < ∞} \ int {ψ < ∞}` the boundary is a Lipschitz
graph with outer direction `θ` (`exists_convex_frontier_chart`, CEK (23)–(24)). The competitor
`φ_ε = max {φ, φ + ε⟨·, θ⟩ − 1}` (CEK (25)) has `∫ (φ_ε − φ) dμ = o(ε)` (CEK (28)–(29)), while
`ψ_ε = φ_ε* ≤ min {ψ, ψ(· − εθ) + 1}` (CEK (30)) is at most `k + 1` on the segments
`x + (0, ε]θ` above `A_k = {x ∈ U ; ψ(x) ≤ k}`, which lie outside `{ψ < ∞}` (CEK (31), (33)); their
volume is at least `c ε H^{n−1}(A_k)` (CEK (32)), so `log ∫ e^{-ψ_ε} ≥ c' ε H^{n−1}(A_k)`
(CEK (34)) and the maximality forces `H^{n−1}(A_k) = 0`.

In the source, `μ` is the moment measure of `ψ`; that hypothesis enters the proof only through the
finite first moment `∫ |y| dμ < ∞` (CEK Lemma 4) and the `μ`-integrability of `φ` (CEK
Proposition 7), and both are hypotheses here.
-/

noncomputable section

namespace FunctionalInequalities.KLS.CEK

open MeasureTheory Set Metric Filter Module
open scoped ENNReal NNReal Topology RealInnerProductSpace
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The competitor (25) of CEK arXiv:1304.0630v1, Proposition 10:
`φ_ε(y) = max {φ(y), φ(y) + ε⟪θ, y⟫ − 1}`. -/
private def competitor (φ : E → EReal) (θ : E) (ε : ℝ) (y : E) : EReal :=
  max (φ y) (affineSubtract φ (-(ε • θ)) 1 y)

/-- The gain `max {ε⟪θ, y⟫ − 1, 0}` of the competitor over `φ`. -/
private def gain (θ : E) (ε : ℝ) (y : E) : ℝ := max (ε * ⟪θ, y⟫ - 1) 0

private theorem competitor_ne_bot {φ : E → EReal} (hφ : ∀ y, φ y ≠ ⊥) (θ : E) (ε : ℝ) (y : E) :
    competitor φ θ ε y ≠ ⊥ := fun h =>
  hφ y (le_bot_iff.mp (h ▸ le_max_left (φ y) (affineSubtract φ (-(ε • θ)) 1 y)))

private theorem convexPotential_competitor {φ : E → EReal} (hφ : ConvexPotential φ) (θ : E)
    (ε : ℝ) : ConvexPotential (competitor φ θ ε) := by
  refine ⟨competitor_ne_bot hφ.1 θ ε, ?_⟩
  have hset : {p : E × ℝ | competitor φ θ ε p.1 ≤ (p.2 : EReal)} =
      {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} ∩
        {p : E × ℝ | affineSubtract φ (-(ε • θ)) 1 p.1 ≤ (p.2 : EReal)} := by
    ext p
    change competitor φ θ ε p.1 ≤ (p.2 : EReal) ↔
      φ p.1 ≤ (p.2 : EReal) ∧ affineSubtract φ (-(ε • θ)) 1 p.1 ≤ (p.2 : EReal)
    exact max_le_iff
  rw [hset]
  exact hφ.2.inter (convex_epigraph_affineSubtract φ _ 1 hφ.2)

/-- CEK (30), first half: `ψ_ε ≤ ψ`. -/
private theorem legendre_competitor_le (φ : E → EReal) (θ : E) (ε : ℝ) (z : E) :
    legendre (competitor φ θ ε) z ≤ legendre φ z :=
  legendre_antitone (fun _ => le_max_left _ _) z

/-- CEK (30), second half: `ψ_ε(z) ≤ ψ(z − εθ) + 1`. -/
private theorem legendre_competitor_le_shift (φ : E → EReal) (θ : E) (ε : ℝ) (z : E) :
    legendre (competitor φ θ ε) z ≤ legendre φ (z - ε • θ) + ((1 : ℝ) : EReal) := by
  refine (legendre_antitone (fun _ => le_max_right _ _) z).trans_eq ?_
  rw [legendre_affineSubtract, sub_eq_add_neg]

private theorem competitor_eq_coe {φ : E → EReal} (θ : E) (ε : ℝ) {y : E} (htop : φ y ≠ ⊤)
    (hbot : φ y ≠ ⊥) :
    competitor φ θ ε y = (((φ y).toReal + gain θ ε y : ℝ) : EReal) := by
  have hφy : φ y = ((φ y).toReal : EReal) := (EReal.coe_toReal htop hbot).symm
  unfold competitor affineSubtract gain
  rw [hφy, EReal.toReal_coe, ← EReal.coe_sub, ← EReal.coe_strictMono.monotone.map_max]
  congr 1
  rw [inner_neg_left, real_inner_smul_left, ← max_add_add_left, max_comm]
  congr 1 <;> ring

private theorem competitor_toReal {φ : E → EReal} (hφ : ∀ y, φ y ≠ ⊥) (θ : E) (ε : ℝ) {y : E}
    (htop : φ y ≠ ⊤) :
    (competitor φ θ ε y).toReal = (φ y).toReal + gain θ ε y := by
  rw [competitor_eq_coe θ ε htop (hφ y), EReal.toReal_coe]

section Measure

variable [MeasurableSpace E]

private theorem integrable_gain {μ : Measure E} [IsFiniteMeasure μ]
    (hfirst : Integrable (fun y : E => y) μ) (θ : E) (ε : ℝ) : Integrable (gain θ ε) μ :=
  (((hfirst.const_inner θ).const_mul ε).sub (integrable_const 1)).pos_part

private theorem potentialIntegrable_competitor {μ : Measure E} [IsFiniteMeasure μ]
    (hfirst : Integrable (fun y : E => y) μ) {φ : E → EReal} (hpot : PotentialIntegrable φ μ)
    (θ : E) (ε : ℝ) :
    PotentialIntegrable (competitor φ θ ε) μ ∧
      ∫ y, (competitor φ θ ε y).toReal ∂μ = ∫ y, (φ y).toReal ∂μ + ∫ y, gain θ ε y ∂μ := by
  have hae : (fun y => (competitor φ θ ε y).toReal) =ᵐ[μ]
      fun y => (φ y).toReal + gain θ ε y := by
    filter_upwards [hpot.2.1] with y hy
    exact competitor_toReal hpot.1 θ ε hy
  have hint : Integrable (fun y => (φ y).toReal + gain θ ε y) μ :=
    hpot.2.2.add (integrable_gain hfirst θ ε)
  refine ⟨⟨competitor_ne_bot hpot.1 θ ε, ?_, hint.congr hae.symm⟩, ?_⟩
  · filter_upwards [hpot.2.1] with y hy
    rw [competitor_eq_coe θ ε hy (hpot.1 y)]
    exact EReal.coe_ne_top _
  · rw [integral_congr_ae hae, integral_add hpot.2.2 (integrable_gain hfirst θ ε)]

/-- CEK (28)–(29): `∫ max {⟪θ, y⟫ − R, 0} dμ → 0` as `R → ∞`, so `∫ (φ_ε − φ) dμ = o(ε)`. -/
private theorem tendsto_integral_tail {μ : Measure E} [IsFiniteMeasure μ] (hfirst : Integrable (fun y : E => y) μ)
    {θ : E} (hθ : ‖θ‖ = 1) :
    Tendsto (fun R : ℝ => ∫ y, max (⟪θ, y⟫ - R) 0 ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun (R : ℝ) (y : E) => max (⟪θ, y⟫ - R) 0) (f := fun _ => (0 : ℝ)) (fun y => ‖y‖) ?_ ?_
    hfirst.norm ?_
  · simpa only [integral_zero] using h
  · refine Eventually.of_forall fun R => ?_
    exact (((hfirst.const_inner θ).sub (integrable_const R)).pos_part).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (norm_nonneg y)
    have h := real_inner_le_norm θ y
    rw [hθ, one_mul] at h
    linarith
  · refine Eventually.of_forall fun y => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⟪θ, y⟫] with R hR
    exact (max_eq_right (by linarith)).symm

end Measure

/-- The final comparison of CEK (34) with (29): `log(1 + αε) ≤ ε G(1/ε)` for all `ε ∈ (0, 1]`
with `α > 0` is impossible when `G(R) → 0`. -/
private theorem false_of_log_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {G : ℝ → ℝ}
    (hG : Tendsto G atTop (𝓝 0))
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → Real.log (1 + α * ε) ≤ ε * G ε⁻¹) : False := by
  obtain ⟨R, hRG, hR1⟩ := ((hG.eventually (gt_mem_nhds (half_pos hα))).and
    (eventually_ge_atTop 1)).exists
  have hR0 : 0 < R := by linarith
  have hε : 0 < R⁻¹ := inv_pos.mpr hR0
  have hε1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hlog := h R⁻¹ hε hε1
  rw [inv_inv] at hlog
  set x := α * R⁻¹ with hx
  have hx0 : 0 < x := mul_pos hα hε
  have hx1 : x ≤ 1 := by
    calc x = α * R⁻¹ := rfl
      _ ≤ 1 * 1 := mul_le_mul hα1 hε1 hε.le zero_le_one
      _ = 1 := one_mul 1
  have hlow : x / 2 ≤ Real.log (1 + x) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + x)
    have h2 : x / 2 ≤ 1 - (1 + x)⁻¹ := by
      rw [show 1 - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring]
      exact div_le_div_of_nonneg_left hx0.le (by linarith) (by linarith)
    linarith
  have hle : α / 2 * R⁻¹ ≤ R⁻¹ * G R := by
    calc α / 2 * R⁻¹ = x / 2 := by rw [hx]; ring
      _ ≤ R⁻¹ * G R := hlow.trans hlog
  have hlt := mul_lt_mul_of_pos_left hRG hε
  linarith

/-- The mass gain behind CEK (33)–(34): if `ψ' ≤ ψ` and a measurable `T` lies where `ψ = ⊤` and
`ψ' ≤ c`, then `∫ e^{-ψ} + e^{-c} dx(T) ≤ ∫ e^{-ψ'}`. -/
private theorem mass_add_le {F : Type*} [MeasurableSpace F] (dx : Measure F) {ψ ψ' : F → EReal} (hle : ∀ z, ψ' z ≤ ψ z)
    {T : Set F} (hT : MeasurableSet T) {c : ℝ} (hTc : ∀ z ∈ T, ψ z = ⊤ ∧ ψ' z ≤ (c : EReal)) :
    mass dx ψ + ENNReal.ofReal (Real.exp (-c)) * dx T ≤ mass dx ψ' := by
  unfold mass
  rw [← lintegral_indicator_const hT, ← lintegral_add_right _ (measurable_const.indicator hT)]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ T
  · rw [indicator_of_mem hz, density, (hTc z hz).1, EReal.neg_top, EReal.exp_bot, zero_add,
      density, ← EReal.exp_coe, EReal.coe_neg]
    exact EReal.exp_monotone (EReal.neg_le_neg_iff.mpr (hTc z hz).2)
  · rw [indicator_of_notMem hz, add_zero]
    exact EReal.exp_monotone (EReal.neg_le_neg_iff.mpr (hle z))

section Main

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The local step of CEK arXiv:1304.0630v1, Proposition 10: around every point `x₀` outside the
interior of `K = {ψ < ∞}`, `ψ = φ*`, there is a neighbourhood `U` with
`H^{n−1}(U ∩ (K \ int K) ∩ {ψ ≤ k}) = 0` for every `k`. -/
private theorem exists_nhds_hausdorffMeasure_eq_zero (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsFiniteMeasure μ] (hfirst : Integrable (fun y : E => y) μ) {φ : E → EReal}
    (hφ : ConvexPotential φ) (hpot : PotentialIntegrable φ μ) (hmass : mass dx (legendre φ) = 1)
    (hmax : ∀ f : E → EReal, ConvexPotential f → PotentialIntegrable f μ →
      variationalFunctional dx μ f ≤ variationalFunctional dx μ φ)
    (hconv : Convex ℝ {x | legendre φ x ≠ ⊤}) (hint : (interior {x | legendre φ x ≠ ⊤}).Nonempty)
    {x₀ : E} (hx₀ : x₀ ∉ interior {x | legendre φ x ≠ ⊤}) :
    ∃ U ∈ 𝓝 x₀, ∀ k : ℕ, μH[(finrank ℝ E : ℝ) - 1]
      (U ∩ ({x | legendre φ x ≠ ⊤} \ interior {x | legendre φ x ≠ ⊤}) ∩
        {x | legendre φ x ≤ ((k : ℝ) : EReal)}) = 0 := by
  set ψ := legendre φ with hψ
  set K := {x | ψ x ≠ ⊤} with hK
  obtain ⟨θ, hθ, U, hU, M, hM, hout, hvol⟩ := exists_convex_frontier_chart dx hconv hint hx₀
  refine ⟨U, hU, fun k => ?_⟩
  set B := U ∩ (K \ interior K) ∩ {x | ψ x ≤ ((k : ℝ) : EReal)} with hB
  by_contra hB0
  set c' : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((k : ℝ) + 1))) with hc'
  have hc'0 : c' ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  -- the set gained by the competitor
  let T : ℝ → Set E := fun ε =>
    {z | ψ z = ⊤ ∧ legendre (competitor φ θ ε) z ≤ (((k : ℝ) + 1 : ℝ) : EReal)}
  have hTm : ∀ ε, MeasurableSet (T ε) := fun ε =>
    ((lowerSemicontinuous_legendre φ).measurable (measurableSet_singleton ⊤)).inter
      ((lowerSemicontinuous_legendre _).measurable measurableSet_Iic)
  -- CEK (31), (33): the segments above `B` lie in `T ε`
  have hseg : ∀ ε : ℝ, 0 < ε → ∀ x ∈ B, ∀ t ∈ Ioc (0 : ℝ) ε, x + t • θ ∈ T ε := by
    intro ε hε x hx t ht
    refine ⟨?_, ?_⟩
    · by_contra hne
      exact hout x hx.1.1 hx.1.2.2 t ht.1 hne
    · have hxk : ψ x ≤ ((k : ℝ) : EReal) := hx.2
      have hp1 : legendre (competitor φ θ ε) x ≤ (((k : ℝ) + 1 : ℝ) : EReal) :=
        (legendre_competitor_le φ θ ε x).trans
          (hxk.trans (EReal.coe_le_coe_iff.mpr (by linarith)))
      have hp2 : legendre (competitor φ θ ε) (x + ε • θ) ≤ (((k : ℝ) + 1 : ℝ) : EReal) := by
        refine (legendre_competitor_le_shift φ θ ε _).trans ?_
        rw [add_sub_cancel_right, EReal.coe_add]
        exact add_le_add hxk le_rfl
      have hab : (1 - t / ε) + t / ε = 1 := by ring
      have hcomb := convex_epigraph_legendre (competitor φ θ ε)
        (show (x, (k : ℝ) + 1) ∈ {p : E × ℝ | legendre (competitor φ θ ε) p.1 ≤ (p.2 : EReal)}
          from hp1)
        (show (x + ε • θ, (k : ℝ) + 1) ∈
            {p : E × ℝ | legendre (competitor φ θ ε) p.1 ≤ (p.2 : EReal)} from hp2)
        (by rw [sub_nonneg, div_le_one hε]; exact ht.2) (div_nonneg ht.1.le hε.le) hab
      have hpt : (1 - t / ε) • ((x, (k : ℝ) + 1) : E × ℝ) + (t / ε) • (x + ε • θ, (k : ℝ) + 1) =
          (x + t • θ, (k : ℝ) + 1) := by
        ext
        · simp only [Prod.fst_add, Prod.smul_fst]
          rw [smul_add, smul_smul, div_mul_cancel₀ t hε.ne', ← add_assoc, ← add_smul, hab, one_smul]
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          linear_combination ((k : ℝ) + 1) * hab
      rw [hpt] at hcomb
      exact hcomb
  -- CEK (32): volume of the gained set
  have hvolT : ∀ ε : ℝ, 0 < ε →
      μH[(finrank ℝ E : ℝ) - 1] B * ENNReal.ofReal ε ≤ M * dx (T ε) := fun ε hε =>
    hvol B inter_subset_left ε hε (T ε) (hTm ε) (hseg ε hε)
  have hM0 : M ≠ 0 := by
    intro h0
    have h := hvolT 1 one_pos
    rw [h0, zero_mul, ENNReal.ofReal_one, mul_one, nonpos_iff_eq_zero] at h
    exact hB0 h
  -- a real lower rate `α`
  have hX : 0 < c' * μH[(finrank ℝ E : ℝ) - 1] B / M :=
    ENNReal.div_pos (mul_ne_zero hc'0 hB0) hM
  obtain ⟨r, hr0, hrX⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hX
  set α : ℝ := min (r : ℝ) 1 with hαdef
  have hα : 0 < α := lt_min (by exact_mod_cast hr0) one_pos
  have hα1 : α ≤ 1 := min_le_right _ _
  have hαM : ENNReal.ofReal α * M ≤ c' * μH[(finrank ℝ E : ℝ) - 1] B := by
    have h1 : ENNReal.ofReal α ≤ c' * μH[(finrank ℝ E : ℝ) - 1] B / M := by
      refine le_trans ?_ hrX.le
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
    calc ENNReal.ofReal α * M ≤ c' * μH[(finrank ℝ E : ℝ) - 1] B / M * M := by gcongr
      _ = c' * μH[(finrank ℝ E : ℝ) - 1] B := ENNReal.div_mul_cancel hM0 hM
  have hgain : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal (α * ε) ≤ c' * dx (T ε) := by
    intro ε hε
    rw [← ENNReal.mul_le_mul_iff_left hM0 hM]
    calc ENNReal.ofReal (α * ε) * M = ENNReal.ofReal α * M * ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_mul hα.le]; ring
      _ ≤ c' * μH[(finrank ℝ E : ℝ) - 1] B * ENNReal.ofReal ε := by gcongr
      _ = c' * (μH[(finrank ℝ E : ℝ) - 1] B * ENNReal.ofReal ε) := by ring
      _ ≤ c' * (M * dx (T ε)) := by gcongr c' * ?_; exact hvolT ε hε
      _ = c' * dx (T ε) * M := by ring
  -- CEK (26) with (29) and (34)
  refine false_of_log_le hα hα1 (tendsto_integral_tail hfirst hθ) fun ε hε _ => ?_
  obtain ⟨hcpot, hcint⟩ := potentialIntegrable_competitor hfirst hpot θ ε
  have hv := hmax _ (convexPotential_competitor hφ θ ε) hcpot
  unfold variationalFunctional at hv
  rw [hmass, ENNReal.log_one, hcint] at hv
  have hmassε : ENNReal.ofReal (1 + α * ε) ≤ mass dx (legendre (competitor φ θ ε)) := by
    have h := mass_add_le dx (legendre_competitor_le φ θ ε) (hTm ε)
      (c := (k : ℝ) + 1) (fun z hz => hz)
    rw [← hψ, hmass] at h
    rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hα.le hε.le), ENNReal.ofReal_one]
    exact (add_le_add le_rfl (hgain ε hε)).trans h
  have hlog : ((Real.log (1 + α * ε) : ℝ) : EReal) ≤
      ENNReal.log (mass dx (legendre (competitor φ θ ε))) := by
    rw [← ENNReal.log_ofReal_of_pos (by positivity)]
    exact ENNReal.log_le_log hmassε
  have hgainint : ∫ y, gain θ ε y ∂μ = ε * ∫ y, max (⟪θ, y⟫ - ε⁻¹) 0 ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    change max (ε * ⟪θ, y⟫ - 1) 0 = ε * max (⟪θ, y⟫ - ε⁻¹) 0
    rw [mul_max_of_nonneg _ _ hε.le, mul_zero, mul_sub, mul_inv_cancel₀ hε.ne']
  rw [← hgainint]
  generalize ENNReal.log (mass dx (legendre (competitor φ θ ε))) = L at hv hlog
  set a := ∫ y, (φ y).toReal ∂μ
  set g := ∫ y, gain θ ε y ∂μ
  induction L with
  | bot => exact absurd hlog (not_le.mpr (EReal.bot_lt_coe _))
  | top =>
      rw [EReal.top_sub_coe, zero_sub] at hv
      exact absurd hv (not_le.mpr (by rw [← EReal.coe_neg]; exact EReal.coe_lt_top _))
  | coe l =>
      rw [zero_sub, ← EReal.coe_sub, ← EReal.coe_neg, EReal.coe_le_coe_iff] at hv
      have hl := EReal.coe_le_coe_iff.mp hlog
      linarith

/-- **CEK Proposition 10** (Cordero-Erausquin–Klartag, *Moment measures*, arXiv:1304.0630v1,
Proposition 10, existence form): let `dx` be an additive Haar measure, `μ` a finite measure with
finite first moment, and `φ : E → ℝ ∪ {+∞}` a convex `μ`-integrable potential with
`∫ exp(-φ*) dx = 1` such that, for every convex `μ`-integrable `f`,
`log ∫ e^{-f*} dx - ∫ f dμ ≤ log ∫ e^{-φ*} dx - ∫ φ dμ` (CEK (22) and (39)). Then `ψ = φ*` is
essentially continuous (CEK Definition 2).

In the source `μ` is the moment measure of `ψ`; this is used only through `∫ |y| dμ < ∞`
(CEK Lemma 4) and the `μ`-integrability of `φ` (CEK Proposition 7), which are assumed here. -/
theorem essentiallyContinuous_legendre_of_maximizer (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsFiniteMeasure μ] (hfirst : Integrable (fun y : E => y) μ) {φ : E → EReal}
    (hφ : ConvexPotential φ) (hpot : PotentialIntegrable φ μ) (hmass : mass dx (legendre φ) = 1)
    (hmax : ∀ f : E → EReal, ConvexPotential f → PotentialIntegrable f μ →
      variationalFunctional dx μ f ≤ variationalFunctional dx μ φ) :
    EssentiallyContinuous (legendre φ) := by
  set ψ := legendre φ with hψ
  -- `φ` is somewhere finite, otherwise `ψ ≡ -∞` and the mass is infinite
  have hfin : ∃ x, φ x ≠ ⊤ := by
    by_contra hall
    push Not at hall
    have hbot : ∀ y, ψ y = ⊥ := by
      intro y
      rw [hψ, legendre]
      refine le_bot_iff.mp (iSup_le fun x => ?_)
      rw [hall x, EReal.sub_top]
    have htop : mass dx ψ = ⊤ := by
      unfold mass density
      simp only [hbot, EReal.neg_bot, EReal.exp_top, lintegral_const]
      exact ENNReal.top_mul (isOpen_univ.measure_ne_zero dx univ_nonempty)
    rw [htop] at hmass
    exact ENNReal.top_ne_one hmass
  have hψc : ConvexPotential ψ := convexPotential_legendre φ hfin
  have hint : (interior {x | ψ x ≠ ⊤}).Nonempty :=
    interior_domain_nonempty_of_mass_ne_zero dx hψc (by rw [hmass]; exact one_ne_zero)
  rw [hψc.essentiallyContinuous_iff]
  refine ⟨lowerSemicontinuous_legendre φ, ?_⟩
  set A := {x | ψ x ≠ ⊤} \ interior {x | ψ x ≠ ⊤} with hA
  have hloc := fun x₀ (hx₀ : x₀ ∈ A) =>
    exists_nhds_hausdorffMeasure_eq_zero dx μ hfirst hφ hpot hmass hmax hψc.convex_domain hint
      hx₀.2
  choose! U hU hU0 using hloc
  obtain ⟨t, htA, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (fun x hx => mem_nhdsWithin_of_mem_nhds (hU x hx))
  have hsub : A ⊆ ⋃ x ∈ t, ⋃ k : ℕ, U x ∩ A ∩ {y | ψ y ≤ ((k : ℝ) : EReal)} := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hcover hy)
    obtain ⟨k, hk⟩ := exists_nat_ge (ψ y).toReal
    refine mem_iUnion₂.mpr ⟨x, hx, mem_iUnion.mpr ⟨k, ⟨hyx, hy⟩, ?_⟩⟩
    change ψ y ≤ ((k : ℝ) : EReal)
    rw [← EReal.coe_toReal hy.1 (hψc.1 y)]
    exact EReal.coe_le_coe_iff.mpr hk
  refine measure_mono_null hsub ((measure_biUnion_null_iff htc).mpr fun x hx => ?_)
  exact measure_iUnion_null fun k => hU0 x (htA hx) k

end Main

end FunctionalInequalities.KLS.CEK
