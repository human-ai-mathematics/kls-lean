module

public import FunctionalInequalities.Analysis.RieszPotential.Growth
public import FunctionalInequalities.Probability.ExponentialMoments.Growth
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Critical potentials of Lebesgue densities with all-ball Morrey bounds

For a density `f` on a bounded measurable `S ⊆ ℝⁿ` (`n ≥ 2`, diameter at most `D`) with the all-ball
Morrey bound
`∫_{S ∩ B(x,r)} |f| ≤ K r^{n(1-μ)}`, the potential moments `∫_S (∫_S |x-y|^{n(μ-1)} |f(y)| dy)^q dx`
are at most
`ω_n/(1-μ) [((1-μ)/μ) K q]^q D^n` (`ω_n` the unit-ball volume). At `μ = 1/n` the kernel is `|x -
y|^{1-n}`, and for `K > 0`
the potential `P` is finite a.e. with `∫_S exp(P/(2e(n-1)K)) ≤ 2 ω_n n/(n-1) (1 + 4(n-1)²) D^n`.
This is the `p = n`
instance of Gilbarg–Trudinger (2001), Lemma 7.20, with explicit constants, from an explicit Morrey
constant. It is not
the full lemma for `p > 1`, a Morrey-norm identification, Theorem 7.21 (John–Nirenberg) or the
oscillation of a function.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

/--
**Critical potential moments of a density** (`0 < μ ≤ 1/2`, `q ≥ 2`, `n ≥ 2`), from the all-ball
Morrey bound over `S`. -/
theorem lintegral_density_critical_potential_rpow_le {n : ℕ} (hn : 2 ≤ n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S) (hS : S.Nonempty)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEStronglyMeasurable f (volume.restrict S))
    {D K μ q : ℝ} (hD : 0 < D) (hK : 0 ≤ K) (hμ : 0 < μ) (hμ2 : μ ≤ 1 / 2) (hq : 2 ≤ q)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (hmorrey :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ∀ r : ℝ,
          0 < r →
            (∫⁻ y in S ∩ ball x r, ENNReal.ofReal |f y|) ≤
              ENNReal.ofReal (K * r ^ ((n : ℝ) * (1 - μ)))) :
    (∫⁻ x in S, (∫⁻ y in S, ENNReal.ofReal (‖y - x‖ ^ ((n : ℝ) * (μ - 1)) * |f y|)) ^ q) ≤
      ENNReal.ofReal
        (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) / (1 - μ)) *
            ((1 - μ) / μ * K * q) ^ q *
          D ^ (n : ℝ)) := by
  let η := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S
  let ν := η.withDensity (fun y => ENNReal.ofReal |f y|)
  let A := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1)
  have hf' : AEMeasurable (fun y => ENNReal.ofReal |f y|) η := by
    simpa only [Real.norm_eq_abs] using hf.norm.aemeasurable.ennreal_ofReal
  have hηS : ∀ᵐ y ∂η, y ∈ S := ae_restrict_mem hSm
  have hνS : ∀ᵐ y ∂ν, y ∈ S := (withDensity_absolutelyContinuous η _).ae_le hηS
  have hνgrowth (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    ν (ball x r) ≤ ENNReal.ofReal (K * r ^ ((n : ℝ) * (1 - μ))) := by
    dsimp only [ν, η]
    rw [withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
      inter_comm (ball x r) S]
    exact hmorrey x r hr
  have hηgrowth (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    η (ball x r) ≤ ENNReal.ofReal (A * r ^ (n : ℝ)) := by
    have ht : ((volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1)) ≠ ∞ :=
      measure_ball_lt_top.ne
    calc
      _ ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x r) := Measure.restrict_le_self _
      _ = ENNReal.ofReal (r ^ n) * (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) := by
        simpa only [finrank_euclideanSpace_fin] using
          Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) x hr
      _ = _ := by
        rw [Real.rpow_natCast]
        change
          _ =
            ENNReal.ofReal
              ((((volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1)).toReal) * r ^ n)
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ht, mul_comm]
  have hN : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have H :=
    lintegral_critical_radial_potential_rpow_le ν η hS hD hK ENNReal.toReal_nonneg hN hμ hμ2 hq
      hdiam hνS hηS hνgrowth hηgrowth
  have hpot (x : EuclideanSpace ℝ (Fin n)) :
    (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ ((n : ℝ) * (μ - 1))) ∂ν) =
      ∫⁻ y in S, ENNReal.ofReal (‖y - x‖ ^ ((n : ℝ) * (μ - 1)) * |f y|) := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ hf' (by fun_prop)]
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _), mul_comm]
    rfl
  simp_rw [hpot] at H
  simpa only [A, η, measureReal_def] using H

/-- **Kernel `|x - y|^{1-n}`** (`μ = 1/n`): moments at most `ω_n n/(n-1) [(n-1) K q]^q D^n`. -/
theorem lintegral_density_critical_morrey_potential_rpow_le {n : ℕ} (hn : 2 ≤ n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S) (hS : S.Nonempty)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEStronglyMeasurable f (volume.restrict S))
    {D K q : ℝ} (hD : 0 < D) (hK : 0 ≤ K) (hq : 2 ≤ q)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (hmorrey : ∀ x : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
      (∫⁻ y in S ∩ ball x r, ENNReal.ofReal |f y|) ≤
        ENNReal.ofReal (K * r ^ ((n : ℝ) - 1))) :
    (∫⁻ x in S, (∫⁻ y in S, ENNReal.ofReal (‖y - x‖ ^ (1 - (n : ℝ)) * |f y|)) ^ q) ≤
      ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) *
        (n : ℝ) / ((n : ℝ) - 1)) * (((n : ℝ) - 1) * K * q) ^ q * D ^ (n : ℝ)) := by
  have hn2 : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hμ0 : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn0
  have hμ2 : 1 / (n : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hn2
  have he : (n : ℝ) * (1 - 1 / (n : ℝ)) = (n : ℝ) - 1 := by field_simp [hn0.ne']
  have he' : (n : ℝ) * (1 / (n : ℝ) - 1) = 1 - (n : ℝ) := by field_simp [hn0.ne']
  have H := lintegral_density_critical_potential_rpow_le hn hSm hS hf hD hK hμ0 hμ2 hq
    hdiam (by simpa only [he] using hmorrey)
  have hC : (1 - 1 / (n : ℝ)) / (1 / (n : ℝ)) = (n : ℝ) - 1 := by field_simp [hn0.ne']
  have hA (A : ℝ) : A / (1 - 1 / (n : ℝ)) = A * (n : ℝ) / ((n : ℝ) - 1) := by
    field_simp [hn0.ne', hn1.ne']
  simpa only [he', hC, hA] using H

/--
**Exponential integrability of the critical potential.** For `K > 0` and the all-ball Morrey bound
`∫_{S ∩ B(x,r)} |f| ≤ K r^{n-1}`, the potential `P(x) = ∫_S |x-y|^{1-n} |f(y)| dy` is finite a.e. on
`S`,
`exp((σ/K) P)` is integrable with `σ = 1/(2e(n-1))`, and its integral is at most `2 ω_n n/(n-1) (1 +
4(n-1)²) D^n`. -/
theorem integrable_exp_critical_morrey_potential {n : ℕ} (hn : 2 ≤ n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S) (hS : S.Nonempty)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : AEStronglyMeasurable f (volume.restrict S))
    {D K : ℝ} (hD : 0 < D) (hK : 0 < K) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (hmorrey :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ∀ r : ℝ,
          0 < r →
            (∫⁻ y in S ∩ ball x r, ENNReal.ofReal |f y|) ≤
              ENNReal.ofReal (K * r ^ ((n : ℝ) - 1))) :
    let P := fun x => ∫⁻ y in S, ENNReal.ofReal (‖y - x‖ ^ (1 - (n : ℝ)) * |f y|)
    let C := (n : ℝ) - 1
    let σ := (2 * C * Real.exp 1)⁻¹
    0 < σ ∧
      (∀ᵐ x ∂volume.restrict S, P x < ∞) ∧
        Integrable (fun x => Real.exp ((σ / K) * (P x).toReal)) (volume.restrict S) ∧
          (∫ x in S, Real.exp ((σ / K) * (P x).toReal)) ≤
            2 *
                (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (n : ℝ) / C) *
                  (1 + 4 * C ^ 2)) *
              D ^ (n : ℝ) := by
  intro P C σ
  have hn2 : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hC0 : 0 < C := by linarith
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  let η := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S
  let ω := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1)
  let A := (ω * (n : ℝ) / C) * D ^ (n : ℝ)
  have hω : 0 ≤ ω := measureReal_nonneg
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hηgrowth (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    η (ball x r) ≤ ENNReal.ofReal (ω * r ^ (n : ℝ)) := by
    have ht : ((volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1)) ≠ ∞ :=
      measure_ball_lt_top.ne
    calc
      _ ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x r) := Measure.restrict_le_self _
      _ = ENNReal.ofReal (r ^ n) * (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) := by
        simpa only [finrank_euclideanSpace_fin] using
          Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) x hr
      _ = _ := by
        rw [Real.rpow_natCast]
        change
          _ =
            ENNReal.ofReal
              ((((volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1)).toReal) * r ^ n)
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ht, mul_comm]
  obtain ⟨x0, hx0⟩ := hS
  have hsupp : ∀ᵐ y ∂η, y ∈ closedBall x0 D :=
    (ae_restrict_mem hSm).mono fun y hy => hdiam y hy x0 hx0
  have hmass0 := measure_univ_le_of_ae_closedBall_ball_growth η x0 hD hsupp (hηgrowth x0)
  have hωA : ω ≤ ω * (n : ℝ) / C := by
    rw [le_div_iff₀ hC0]
    dsimp only [C]
    nlinarith
  have hmass : η univ ≤ ENNReal.ofReal A :=
    hmass0.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hωA (by positivity)))
  let : IsFiniteMeasure η := ⟨hmass.trans_lt ENNReal.ofReal_lt_top⟩
  have hf' : AEMeasurable (fun y => ENNReal.ofReal |f y|) η := by
    simpa only [Real.norm_eq_abs] using hf.norm.aemeasurable.ennreal_ofReal
  have hker :
    Measurable
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (‖z.2 - z.1‖ ^ (1 - (n : ℝ)))) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((measurable_snd.sub measurable_fst).norm.pow_const _)
  have hP : AEMeasurable P η := by
    have H := (hker.aemeasurable (μ := η.prod η)).mul hf'.comp_snd
    dsimp only [P]
    simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
    exact H.lintegral_prod_right
  have hmom (k : ℕ) (hk : 2 ≤ k) :
    (∫⁻ x, (P x) ^ k ∂η) ≤ ENNReal.ofReal (A * (C * K * (k : ℝ)) ^ k) := by
    have H :=
      lintegral_density_critical_morrey_potential_rpow_le hn hSm ⟨x0, hx0⟩ hf hD hK.le
        (by exact_mod_cast hk : 2 ≤ (k : ℝ)) hdiam hmorrey
    simpa only [ENNReal.rpow_natCast, Real.rpow_natCast, P, η, A, C, ω, mul_assoc, mul_comm,
      mul_left_comm] using H
  have hsmall : σ * C * Real.exp 1 ≤ 1 / 2 := by
    have he : σ * C * Real.exp 1 = 1 / 2 := by
      dsimp only [σ]
      field_simp [hC0.ne', (Real.exp_pos 1).ne']
    exact he.le
  have H :=
    FunctionalInequalities.Probability.integrable_exp_toReal_of_scaled_high_moment_growth η hP
      hA hC hK hσ.le hsmall hmass hmom
  refine ⟨hσ, H.1, H.2.1, ?_⟩
  convert H.2.2 using 1
  dsimp only [A]
  ring

end FunctionalInequalities.Analysis
