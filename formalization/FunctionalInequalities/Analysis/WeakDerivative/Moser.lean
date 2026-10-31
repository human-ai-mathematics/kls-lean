module

public import FunctionalInequalities.Analysis.WeakDerivative.Sobolev
public import FunctionalInequalities.Analysis.Cutoff.SmoothBall
public import FunctionalInequalities.Analysis.Iteration.LpNorm
public import FunctionalInequalities.Analysis.LpExponent

/-!
# Moser endpoints from cutoff power energies

Essential bounds for a positive function `s` with a measurable bounded logarithm from GIVEN weak
cutoff power energies
(the Caccioppoli-type energies of Gilbarg–Trudinger 2001, (8.48)–(8.49), with the constants `2 +
8r²β/((1−2r)²α)` and
`4r²F/((1−2r)α)` and the forcing condition `F R² ≤ α δ`). The energies are premises, not Harnack
conclusions; each constant is
chosen before every center, radius and datum.

* Dimension `n > 2` (critical gain `g = n/(n−2)`, physical radius power `R^{-2}`):
  `inverse_essential_bound_of_cutoff_power_energy` (negative powers, infinite Moser iteration,
  `‖s⁻¹‖_∞(B_R) ≤ C R^{-n/p0}
  ‖s⁻¹‖_{p0}(B̄_{2R})` for every `p0 > 0`) and `positive_norm_bound_of_cutoff_power_energy`
  (positive powers, finite backward
  chain, `R^{-n/p} ‖s‖_p(B_{2R}) ≤ C R^{-n/p0} ‖s‖_{p0}(B_{3R})` for every `p0 > 0` and `0 < p <
  n/(n−2)`).
* Dimension two (finite `q = 2g`, physical radius power `R^{-(2−2/g)}`, normalization `N = 2`):
  `inverse_essential_bound_two_of_cutoff_power_energy` (`g = 2`) and
  `positive_norm_bound_two_of_cutoff_power_energy` (every
  finite `p > 0`, `g = max 2 (p+1)`).
* Dimension one (one cutoff, the essential-supremum gain, one root; no iteration):
  `inverse_essential_bound_one_of_cutoff_power_energy` and
  `positive_essential_bound_one_of_cutoff_power_energy` (`0 < p0 < 1`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

namespace FunctionalInequalities.Analysis

section CriticalInverse


/--
Uniform inverse-power coefficients of the Caccioppoli gain under the actual small-forcing condition.
-/
private theorem inverse_power_coefficients_bound {p α β F δ R : ℝ} (hp : 0 < p) (hα : 0 < α)
    (hβ : 0 ≤ β) (hF : 0 ≤ F) (hδ : 0 < δ) (hR : 0 < R) (hforce : F * R ^ 2 ≤ α * δ) :
    2 + 2 * p ^ 2 * β / ((1 + p) ^ 2 * α) ≤ 2 + 2 * β / α ∧
      (p ^ 2 * F / ((1 + p) * α)) / δ ≤ p / R ^ 2 := by
  have hp1 : 0 < 1 + p := by linarith
  have hfrac : p ^ 2 / (1 + p) ^ 2 ≤ 1 :=
    (div_le_iff₀ (sq_pos_of_pos hp1)).2 (by nlinarith [hp])
  constructor
  · calc
      _ = 2 + (2 * β / α) * (p ^ 2 / (1 + p) ^ 2) := by field_simp
      _ ≤ 2 + (2 * β / α) * 1 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hfrac (show 0 ≤ 2 * β / α by positivity))
      _ = _ := by ring
  · have hratio : p ^ 2 / (1 + p) ≤ p := (div_le_iff₀ hp1).2 (by nlinarith [hp])
    have hFd : F / (α * δ) ≤ 1 / R ^ 2 :=
      (div_le_div_iff₀ (mul_pos hα hδ) (sq_pos_of_pos hR)).2
        (by simpa only [one_mul] using hforce)
    calc
      _ = (p ^ 2 / (1 + p)) * (F / (α * δ)) := by field_simp
      _ ≤ p * (1 / R ^ 2) := mul_le_mul hratio hFd (by positivity) hp.le
      _ = _ := by ring

/-- A geometric coefficient envelope; actual critical gain has kappa<=3<4. -/
private theorem inverse_step_coefficient_envelope {S H p0 κ : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hp : 0 ≤ p0) (hκ : 0 ≤ κ) (hκ4 : κ ≤ 4) :
    1 ≤ 1 + S * (4 * H + p0) ∧
      ∀ m : ℕ,
        S * (H * (4 : ℝ) ^ (m + 1) + p0 * κ ^ m) ≤ (1 + S * (4 * H + p0)) * (4 : ℝ) ^ m := by
  have hbase : 0 ≤ S * (4 * H + p0) := by positivity
  refine ⟨by linarith, fun m => ?_⟩
  have hpm : p0 * κ ^ m ≤ p0 * (4 : ℝ) ^ m :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκ hκ4 m) hp
  calc
    _ ≤ S * (H * ((4 : ℝ) ^ m * 4) + p0 * (4 : ℝ) ^ m) := by rw [pow_succ]; nlinarith [hpm]
    _ = S * (4 * H + p0) * (4 : ℝ) ^ m := by ring
    _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) m]

/-- The full physical coefficient of the inverse Sobolev gain has a uniform geometric envelope.
The radius is arbitrary positive; no upper bound on it is assumed. -/
private theorem inverse_dyadic_coefficient_bound {S N D α β F δ R p0 κ : ℝ} (hS : 0 ≤ S)
    (hN : 0 ≤ N) (hα : 0 < α) (hβ : 0 ≤ β) (hF : 0 ≤ F) (hδ : 0 < δ) (hR : 0 < R) (hp0 : 0 < p0)
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hforce : F * R ^ 2 ≤ α * δ) (m : ℕ) :
    S *
        ((2 + 2 * (p0 * κ ^ m) ^ 2 * β / ((1 + p0 * κ ^ m) ^ 2 * α)) *
            (N * (D * 2 ^ (m + 1) / R) ^ 2) +
          (((p0 * κ ^ m) ^ 2 * F / ((1 + p0 * κ ^ m) * α)) / δ)) ≤
      (1 + S * (4 * ((2 + 2 * β / α) * N * D ^ 2) + p0)) * (4 : ℝ) ^ m / R ^ 2 := by
  have hp : 0 < p0 * κ ^ m := mul_pos hp0 (pow_pos hκ m)
  have hc := inverse_power_coefficients_bound hp hα hβ hF hδ hR hforce
  have hH : 0 ≤ (2 + 2 * β / α) * N * D ^ 2 := by positivity
  have he := (inverse_step_coefficient_envelope hS hH hp0.le hκ.le hκ4).2 m
  have htwo : ((2 : ℝ) ^ (m + 1)) ^ 2 = (4 : ℝ) ^ (m + 1) := by
    calc
      _ = ((2 : ℝ) ^ 2) ^ (m + 1) := by rw [← pow_mul, ← pow_mul]; congr 1; omega
      _ = _ := by norm_num
  calc
    _ ≤ S * ((2 + 2 * β / α) * (N * (D * 2 ^ (m + 1) / R) ^ 2) + (p0 * κ ^ m) / R ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hc.1 (mul_nonneg hN (sq_nonneg _))) hc.2) hS
    _ = S * (((2 + 2 * β / α) * N * D ^ 2) * (4 : ℝ) ^ (m + 1) + p0 * κ ^ m) / R ^ 2 := by
      rw [div_pow, mul_pow, htwo]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right he (sq_nonneg R)

/-- The exact negative-power gain gives the physical inverse-norm step with its uniform dyadic
coefficient. This interface consumes a genuine power estimate with an actual integrability premise.
-/
private theorem inverse_dyadic_norm_step_of_power_gain {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (s : X → ℝ) (hs : ∀ x, 0 < s x) {S N D α β F δ R p0 κ : ℝ} (hS : 0 ≤ S)
    (hN : 0 ≤ N) (hα : 0 < α) (hβ : 0 ≤ β) (hF : 0 ≤ F) (hδ : 0 < δ) (hR : 0 < R) (hp0 : 0 < p0)
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hforce : F * R ^ 2 ≤ α * δ) (m : ℕ)
    (hI : Integrable (fun x => s x ^ (-(p0 * κ ^ m))) μ)
    (hgain :
      (eLpNorm (fun x => s x ^ (-(p0 * κ ^ m) / 2)) (ENNReal.ofReal (2 * κ)) ν) ^ (2 : ℕ) ≤
        ENNReal.ofReal S *
          ENNReal.ofReal
            (((2 + 2 * (p0 * κ ^ m) ^ 2 * β / ((1 + p0 * κ ^ m) ^ 2 * α)) *
                  (N * (D * 2 ^ (m + 1) / R) ^ 2) +
                (((p0 * κ ^ m) ^ 2 * F / ((1 + p0 * κ ^ m) * α)) / δ)) *
              (∫ x, s x ^ (-(p0 * κ ^ m)) ∂μ))) :
    (eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal (κ * (p0 * κ ^ m))) ν) ^ (p0 * κ ^ m) ≤
      ENNReal.ofReal ((1 + S * (4 * ((2 + 2 * β / α) * N * D ^ 2) + p0)) * (4 : ℝ) ^ m) *
          (ENNReal.ofReal R) ^ (-2 : ℝ) *
        (eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal (p0 * κ ^ m)) μ) ^ (p0 * κ ^ m) := by
  have hp : 0 < p0 * κ ^ m := mul_pos hp0 (pow_pos hκ m)
  have hA :
    0 ≤
      (2 + 2 * (p0 * κ ^ m) ^ 2 * β / ((1 + p0 * κ ^ m) ^ 2 * α)) *
          (N * (D * 2 ^ (m + 1) / R) ^ 2) +
        (((p0 * κ ^ m) ^ 2 * F / ((1 + p0 * κ ^ m) * α)) / δ) := by
    positivity
  have H := inverse_norm_power_gain μ ν s hs hp (by positivity : 0 ≤ 2 * κ) hA hI hgain
  have he : (2 * κ / 2) * (p0 * κ ^ m) = κ * (p0 * κ ^ m) := by ring
  rw [he, ← ENNReal.ofReal_mul hS] at H
  have hc :=
    ENNReal.ofReal_le_ofReal
      (inverse_dyadic_coefficient_bound (D := D) hS hN hα hβ hF hδ hR hp0 hκ hκ4 hforce m)
  have hbase : 0 ≤ (1 + S * (4 * ((2 + 2 * β / α) * N * D ^ 2) + p0)) * (4 : ℝ) ^ m := by
    positivity
  have hr :
    ENNReal.ofReal ((1 + S * (4 * ((2 + 2 * β / α) * N * D ^ 2) + p0)) * (4 : ℝ) ^ m / R ^ 2) =
      ENNReal.ofReal ((1 + S * (4 * ((2 + 2 * β / α) * N * D ^ 2) + p0)) * (4 : ℝ) ^ m) *
        (ENNReal.ofReal R) ^ (-2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_pos hR, ← ENNReal.ofReal_mul hbase, Real.rpow_neg hR.le,
      Real.rpow_two, div_eq_mul_inv]
  rw [hr] at hc
  exact H.trans (mul_le_mul_of_nonneg_right hc zero_le)

theorem inverse_essential_bound_of_cutoff_power_energy
    {n : ℕ} (hn : 2 < n) {α β p0 : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hp0 : 0 < p0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      ∀ (s : EuclideanSpace ℝ (Fin n) → ℝ) (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
        (F δ : ℝ), 0 ≤ F → 0 < δ → F * R ^ 2 ≤ α * δ → (∀ x, δ ≤ s x) →
        AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin
          n))) →
        (∃ Clog : ℝ, ∀ x, ‖Real.log (s x)‖ ≤ Clog) →
        (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
          tsupport χ ⊆ closedBall x0 (4 * R) → ∀ r : ℝ, r < 0 →
          let g := fun x => χ x * s x ^ r
          let dg := fun (k : Fin n) x =>
            fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
            χ x * (r * s x ^ (r-1)) * a k x
          LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          HasCompactSupport g ∧ (∃ Cg : ℝ, ∀ x, ‖g x‖ ≤ Cg) ∧
          (∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
            HasCompactSupport (dg k) ∧ MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin
              n)))) ∧
          (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            (2 + 8 * r ^ 2 * β / ((1-2 * r) ^ 2 * α)) *
              (∫ x, s x ^ (2 * r) * ∑ k : Fin n,
                (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (4 * r ^ 2 * F / ((1-2 * r) * α)) *
              (∫ x, χ x ^ 2 * s x ^ (2 * r-1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) →
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) ≤
          ENNReal.ofReal C * ((ENNReal.ofReal R) ^ (-(n : ℝ) / p0) *
            eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0)
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall x0 (2 *
                R)))) := by
  classical
    have hnR : 2 < (n : ℝ) := by exact_mod_cast hn
    let κ : ℝ := (n : ℝ) / ((n : ℝ) - 2)
    have hn2 : 0 < (n : ℝ) - 2 := by linarith
    have hn0 : 0 < (n : ℝ) := by linarith
    have hκ : 1 < κ := by
      dsimp only [κ]
      apply (lt_div_iff₀ hn2).2
      linarith
    have hκ0 : 0 < κ := zero_lt_one.trans hκ
    have hκ4 : κ ≤ 4 := by
      have hn3 : 3 ≤ (n : ℝ) := by exact_mod_cast hn
      dsimp only [κ]
      apply (div_le_iff₀ hn2).2
      linarith
    have hscale : (n : ℝ) / κ + 2 = (n : ℝ) := by
      dsimp only [κ]
      field_simp [hn0.ne', hn2.ne']
      ring
    let q : NNReal := ⟨2 * κ, by positivity⟩
    have hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
      change (2 * κ)⁻¹ = _
      dsimp only [κ]
      field_simp [hn0.ne', hn2.ne']
    obtain ⟨D, hD, hcut⟩ :=
      exists_smooth_concentric_cutoff_norm_fderiv_le (E := EuclideanSpace ℝ (Fin n))
    let G : NNReal :=
      SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2
    let S : ℝ := (G : ℝ) ^ 2 * (n : ℝ)
    let Cbase : ℝ := 1 + S * (4 * ((2 + 2 * β / α) * (n : ℝ) * D ^ 2) + p0)
    have hS : 0 ≤ S := by dsimp only [S]; positivity
    have hCbase : 1 ≤ Cbase := by
      have H : 0 ≤ S * (4 * ((2 + 2 * β / α) * (n : ℝ) * D ^ 2) + p0) := by positivity
      dsimp only [Cbase]
      linarith
    let C : ℝ :=
      Real.exp ((Real.log Cbase / (1 - κ⁻¹) + Real.log 4 * κ⁻¹ / (1 - κ⁻¹) ^ 2) / p0)
    refine ⟨C, Real.exp_pos _, ?_⟩
    intro x0 R hR s a F δ hF hδ hforce hs hlogm hlogB hdata
    obtain ⟨Clog, hlogb⟩ := hlogB
    let ρ := fun m : ℕ => R * (1 + (1 / 2 : ℝ) ^ m)
    have hρpos (m : ℕ) : 0 < ρ m := by dsimp only [ρ]; positivity
    have hρle (m : ℕ) : ρ m ≤ 2 * R := by
      have H : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      dsimp only [ρ]
      nlinarith
    have hρge (m : ℕ) : R ≤ ρ m := by
      have H : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
      dsimp only [ρ]
      nlinarith
    have hgap (m : ℕ) : ρ m - ρ (m + 1) = R * (1 / 2 : ℝ) ^ (m + 1) := by
      dsimp only [ρ]
      rw [pow_succ]
      ring
    have hcutm (m : ℕ) :
      ∃ χ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ ∞ χ ∧
          HasCompactSupport χ ∧
            tsupport χ ⊆ closedBall x0 (ρ m) ∧
              (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
                (∀ x ∈ closedBall x0 (ρ (m + 1)), χ x = 1) ∧
                  ∀ x, ‖fderiv ℝ χ x‖ ≤ D * 2 ^ (m + 1) / R := by
      have hlt : ρ (m + 1) < ρ m := by
        have H : 0 < R * (1 / 2 : ℝ) ^ (m + 1) := by positivity
        linarith [hgap m]
      obtain ⟨χ, hsm, hcs, hts, h01, hone, -, hd⟩ :=
        hcut x0 (ρ (m + 1)) (ρ m) (hρpos _).le hlt
      refine ⟨χ, hsm, hcs, hts, h01, hone, fun x => (hd x).trans_eq ?_⟩
      rw [hgap, one_div_pow]
      field_simp
    choose χ hχ using hcutm
    let μ := fun m : ℕ =>
      (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall x0 (ρ m))
    let ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)
    let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    let : NeZero ν :=
      ⟨by
        intro hz
        have H := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ univ) hz
        have hp :=
          Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) x0 hR
        have Hz : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x0 R) = 0 := by
          simpa [ν] using H
        exact hp.ne' Hz⟩
    have hsp (x : EuclideanSpace ℝ (Fin n)) : 0 < s x := hδ.trans_le (hs x)
    have hmem (m : ℕ) :
      MemLp (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal (p0 * κ ^ m)) (μ m) := by
      let : IsFiniteMeasure (μ m) :=
        isFiniteMeasure_restrict.mpr (isCompact_closedBall x0 (ρ m)).measure_lt_top.ne
      exact memLp_nonpos_power_of_log_measurable _ hδ hs (by norm_num) hlogm.restrict _
    have hνmem : MemLp (fun x => s x ^ (-1 : ℝ)) ∞ ν :=
      memLp_nonpos_power_of_log_measurable _ hδ hs (by norm_num) hlogm.restrict _
    have hνle (m : ℕ) : ν ≤ μ m := by
      exact
        Measure.restrict_mono
          (ball_subset_closedBall.trans (closedBall_subset_closedBall (hρge m))) le_rfl
    have hSENN : ENNReal.ofReal S = (G : ENNReal) ^ 2 * (n : ENNReal) := by
      dsimp only [S]
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
      rw [ENNReal.ofReal_pow G.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_natCast]
    have hstep (m : ℕ) :
      (eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal (p0 * κ ^ (m + 1)))
            (μ (m + 1))) ^
          (p0 * κ ^ m) ≤
        ENNReal.ofReal (Cbase * (4 : ℝ) ^ m) * (ENNReal.ofReal R) ^ (-2 : ℝ) *
          (eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal (p0 * κ ^ m)) (μ m)) ^
            (p0 * κ ^ m) := by
      let P : ℝ := p0 * κ ^ m
      have hP : 0 < P := mul_pos hp0 (pow_pos hκ0 m)
      obtain ⟨hsm, hcs, hts, h01, hone, hd⟩ := hχ m
      have hχ1 : ContDiff ℝ 1 (χ m) := hsm.of_le (by exact_mod_cast le_top)
      have hts4 : tsupport (χ m) ⊆ closedBall x0 (4 * R) :=
        hts.trans (closedBall_subset_closedBall ((hρle m).trans (by linarith)))
      obtain ⟨hgl, hgc, ⟨Cg, hgb⟩, hgd, he⟩ :=
        hdata (χ m) hχ1 hcs hts4 (-P / 2) (by linarith)
      have hden : 0 < 1 - 2 * (-P / 2) := by linarith
      have hg :=
        weak_cutoff_sobolev_gain_of_energy_of_bounded_log hn
          (isCompact_closedBall x0 (ρ m)) measurableSet_closedBall hδ hs hts hone
          (fun x => by rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2) hd hgl hgb hgc hgd
          hχ1 hlogm hlogb (by positivity) (by positivity) he hq
      have he2 : 2 * (-P / 2) = -P := by ring
      have hgam :
        2 + 8 * (-P / 2) ^ 2 * β / ((1 - 2 * (-P / 2)) ^ 2 * α) =
          2 + 2 * P ^ 2 * β / ((1 + P) ^ 2 * α) := by
        ring_nf
      have hf :
        4 * (-P / 2) ^ 2 * F / ((1 - 2 * (-P / 2)) * α) = P ^ 2 * F / ((1 + P) * α) := by
        ring_nf
      rw [hgam, hf, he2] at hg
      have hqENN : (q : ENNReal) = ENNReal.ofReal (2 * κ) := by
        rw [← ENNReal.ofReal_coe_nnreal]; rfl
      rw [hqENN, ← hSENN] at hg
      let : IsFiniteMeasure (μ m) :=
        isFiniteMeasure_restrict.mpr (isCompact_closedBall x0 (ρ m)).measure_lt_top.ne
      have hI : Integrable (fun x => s x ^ (-P)) (μ m) :=
        MemLp.integrable le_rfl
          (memLp_nonpos_power_of_log_measurable _ hδ hs (by linarith : -P ≤ 0)
            hlogm.restrict 1)
      have H :=
        inverse_dyadic_norm_step_of_power_gain (μ m) (μ (m + 1)) s hsp hS hn0.le hα hβ
          hF hδ hR hp0 hκ0 hκ4 hforce m hI hg
      have hexp : p0 * κ ^ (m + 1) = κ * (p0 * κ ^ m) := by rw [pow_succ]; ring
      simpa only [hexp, Cbase] using H
    have H :=
      eLpNorm_top_le_of_shrinking_norm_steps μ ν (fun x => s x ^ (-1 : ℝ)) hνmem hνle hκ
        hp0 hR hCbase hscale hmem hstep
    simpa only [C, ν, μ, ρ, pow_zero, mul_one, show R * (1 + 1) = 2 * R by ring] using H

end CriticalInverse

section CriticalPositive

open Filter
open scoped Topology

/-- For every target exponent below the critical gain, a finite backward geometric chain starts
below any given positive exponent and keeps EVERY source exponent strictly below one. -/
private theorem exists_backward_gain_exponents {κ p0 p : ℝ} (hκ : 1 < κ) (hp0 : 0 < p0)
    (hp : 0 < p) (hpκ : p < κ) :
    ∃ K : ℕ,
      1 ≤ K ∧
        let q0 := p / κ ^ K
        0 < q0 ∧
          q0 ≤ p0 ∧ q0 * κ ^ K = p ∧ ∀ m < K, 0 < q0 * κ ^ m ∧ q0 * κ ^ m ≤ p / κ ∧ p / κ < 1 := by
  have hκ0 : 0 < κ := zero_lt_one.trans hκ
  have hev : ∀ᶠ m : ℕ in atTop, p / p0 ≤ κ ^ m :=
    (tendsto_pow_atTop_atTop_of_one_lt hκ).eventually (eventually_ge_atTop (p / p0))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let K : ℕ := N + 1
  have hK : 1 ≤ K := by dsimp only [K]; omega
  have hpow : 0 < κ ^ K := pow_pos hκ0 K
  have hlarge : p / p0 ≤ κ ^ K := hN K (by dsimp only [K]; omega)
  refine ⟨K, hK, ?_⟩
  intro q0
  have hq0 : 0 < q0 := div_pos hp hpow
  have hqle : q0 ≤ p0 := by
    apply (div_le_iff₀ hpow).2
    have H := (div_le_iff₀ hp0).1 hlarge
    simpa only [mul_comm] using H
  have heq : q0 * κ ^ K = p := div_mul_cancel₀ p hpow.ne'
  refine ⟨hq0, hqle, heq, fun m hm => ⟨mul_pos hq0 (pow_pos hκ0 m), ?_, (div_lt_one hκ0).2 hpκ⟩⟩
  apply (le_div_iff₀ hκ0).2
  have hMK : m + 1 ≤ K := Nat.succ_le_of_lt hm
  have Hpow : κ ^ (m + 1) ≤ κ ^ K := pow_le_pow_right₀ hκ.le hMK
  calc
    q0 * κ ^ m * κ = q0 * κ ^ (m + 1) := by rw [pow_succ]; ring
    _ ≤ q0 * κ ^ K := mul_le_mul_of_nonneg_left Hpow hq0.le
    _ = p := heq

/-- Positive-power source coefficients are uniformly controlled as long as the INPUT exponent
stays below a fixed `t < 1`. The forcing condition is the same actual small-forcing condition. -/
private theorem positive_power_coefficients_bound {u t α β F δ R : ℝ} (hu : 0 < u) (hut : u ≤ t)
    (ht : t < 1) (hα : 0 < α) (hβ : 0 ≤ β) (hF : 0 ≤ F) (hδ : 0 < δ) (hR : 0 < R)
    (hforce : F * R ^ 2 ≤ α * δ) :
    2 + 2 * u ^ 2 * β / ((1 - u) ^ 2 * α) ≤ 2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α) ∧
      (u ^ 2 * F / ((1 - u) * α)) / δ ≤ (t ^ 2 / (1 - t)) / R ^ 2 := by
  have ht0 : 0 < t := hu.trans_le hut
  have hdu : 0 < 1 - u := by linarith
  have hdt : 0 < 1 - t := by linarith
  have hratio : u / (1 - u) ≤ t / (1 - t) := (div_le_div_iff₀ hdu hdt).2 (by nlinarith)
  have hsq : u ^ 2 / (1 - u) ^ 2 ≤ t ^ 2 / (1 - t) ^ 2 := by
    rw [← div_pow, ← div_pow]
    simpa only [pow_two] using mul_self_le_mul_self (show 0 ≤ u / (1 - u) by positivity) hratio
  constructor
  · calc
      _ = 2 + (2 * β / α) * (u ^ 2 / (1 - u) ^ 2) := by field_simp
      _ ≤ 2 + (2 * β / α) * (t ^ 2 / (1 - t) ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 * β / α by positivity))
      _ = _ := by field_simp
  · have hnum : u ^ 2 / (1 - u) ≤ t ^ 2 / (1 - t) := by
      calc
        _ = u * (u / (1 - u)) := by ring
        _ ≤ t * (t / (1 - t)) := mul_le_mul hut hratio (by positivity) ht0.le
        _ = _ := by ring
    have hFd : F / (α * δ) ≤ 1 / R ^ 2 :=
      (div_le_div_iff₀ (mul_pos hα hδ) (sq_pos_of_pos hR)).2
        (by simpa only [one_mul] using hforce)
    calc
      _ = (u ^ 2 / (1 - u)) * (F / (α * δ)) := by field_simp
      _ ≤ (t ^ 2 / (1 - t)) * (1 / R ^ 2) := mul_le_mul hnum hFd (by positivity) (by positivity)
      _ = _ := by ring

/-- The positive-power gain on radii decreasing from `5R/2` to `2R` has a dyadic envelope,
uniform over every INPUT exponent in `(0,t]` with `t < 1`. -/
private theorem positive_dyadic_coefficient_bound {u t S N D α β F δ R : ℝ} (hu : 0 < u)
    (hut : u ≤ t) (ht : t < 1) (hS : 0 ≤ S) (hN : 0 ≤ N) (hα : 0 < α) (hβ : 0 ≤ β) (hF : 0 ≤ F)
    (hδ : 0 < δ) (hR : 0 < R) (hforce : F * R ^ 2 ≤ α * δ) (m : ℕ) :
    S *
        ((2 + 2 * u ^ 2 * β / ((1 - u) ^ 2 * α)) * (N * (D * 2 ^ (m + 2) / R) ^ 2) +
          (u ^ 2 * F / ((1 - u) * α)) / δ) ≤
      (1 + S * (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * N * D ^ 2) + t ^ 2 / (1 - t))) *
          (4 : ℝ) ^ m /
        R ^ 2 := by
  have hdt : 0 < 1 - t := by linarith
  have hc := positive_power_coefficients_bound hu hut ht hα hβ hF hδ hR hforce
  let H := (2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * N * D ^ 2
  let A := t ^ 2 / (1 - t)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hfour : 1 ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have he : S * (H * (4 : ℝ) ^ (m + 2) + A) ≤ (1 + S * (16 * H + A)) * (4 : ℝ) ^ m := by
    rw [pow_succ, pow_succ]
    nlinarith [mul_nonneg hS (mul_nonneg hA (sub_nonneg.mpr hfour))]
  have htwo : ((2 : ℝ) ^ (m + 2)) ^ 2 = (4 : ℝ) ^ (m + 2) := by
    calc
      _ = ((2 : ℝ) ^ 2) ^ (m + 2) := by rw [← pow_mul, ← pow_mul]; congr 1; omega
      _ = _ := by norm_num
  calc
    _ ≤
        S *
          ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * (N * (D * 2 ^ (m + 2) / R) ^ 2) +
            (t ^ 2 / (1 - t)) / R ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hc.1 (mul_nonneg hN (sq_nonneg _))) hc.2) hS
    _ = S * (H * (4 : ℝ) ^ (m + 2) + A) / R ^ 2 := by
      dsimp only [H, A]
      rw [div_pow, mul_pow, htwo]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right he (sq_nonneg R)

/-- A positive-power Sobolev estimate gives a physical norm step whose coefficient is uniform
for every source exponent in `(0,t]`, before taking any real representatives. -/
private theorem positive_dyadic_norm_step_of_power_gain {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (s : X → ℝ) (hs : ∀ x, 0 ≤ s x) {u t κ S N D α β F δ R : ℝ} (hu : 0 < u)
    (hut : u ≤ t) (ht : t < 1) (hκ : 0 < κ) (hS : 0 ≤ S) (hN : 0 ≤ N) (hα : 0 < α) (hβ : 0 ≤ β)
    (hF : 0 ≤ F) (hδ : 0 < δ) (hR : 0 < R) (hforce : F * R ^ 2 ≤ α * δ) (m : ℕ)
    (hI : Integrable (fun x => s x ^ u) μ)
    (hgain :
      (eLpNorm (fun x => s x ^ (u / 2)) (ENNReal.ofReal (2 * κ)) ν) ^ (2 : ℕ) ≤
        ENNReal.ofReal S *
          ENNReal.ofReal
            (((2 + 2 * u ^ 2 * β / ((1 - u) ^ 2 * α)) * (N * (D * 2 ^ (m + 2) / R) ^ 2) +
                (u ^ 2 * F / ((1 - u) * α)) / δ) *
              (∫ x, s x ^ u ∂μ))) :
    (eLpNorm s (ENNReal.ofReal (κ * u)) ν) ^ u ≤
      ENNReal.ofReal
            ((1 +
                S *
                  (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * N * D ^ 2) +
                    t ^ 2 / (1 - t))) *
              (4 : ℝ) ^ m) *
          (ENNReal.ofReal R) ^ (-2 : ℝ) *
        (eLpNorm s (ENNReal.ofReal u) μ) ^ u := by
  have hdu : 0 < 1 - u := by linarith
  have hdt : 0 < 1 - t := by linarith
  have hA :
    0 ≤
      (2 + 2 * u ^ 2 * β / ((1 - u) ^ 2 * α)) * (N * (D * 2 ^ (m + 2) / R) ^ 2) +
        (u ^ 2 * F / ((1 - u) * α)) / δ := by
    positivity
  have H := positive_norm_power_gain μ ν s hs hu (by positivity : 0 ≤ 2 * κ) hA hI hgain
  have he : (2 * κ / 2) * u = κ * u := by ring
  rw [he, ← ENNReal.ofReal_mul hS] at H
  have hc :=
    ENNReal.ofReal_le_ofReal
      (positive_dyadic_coefficient_bound (D := D) hu hut ht hS hN hα hβ hF hδ hR hforce m)
  have hbase :
    0 ≤
      (1 + S * (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * N * D ^ 2) + t ^ 2 / (1 - t))) *
        (4 : ℝ) ^ m := by
    positivity
  have hr :
    ENNReal.ofReal
        ((1 +
              S *
                (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * N * D ^ 2) +
                  t ^ 2 / (1 - t))) *
            (4 : ℝ) ^ m /
          R ^ 2) =
      ENNReal.ofReal
          ((1 +
              S *
                (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * N * D ^ 2) +
                  t ^ 2 / (1 - t))) *
            (4 : ℝ) ^ m) *
        (ENNReal.ofReal R) ^ (-2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_pos hR, ← ENNReal.ofReal_mul hbase, Real.rpow_neg hR.le,
      Real.rpow_two, div_eq_mul_inv]
  rw [hr] at hc
  exact H.trans (mul_le_mul_of_nonneg_right hc zero_le)

/-- **Positive finite boost from the given cutoff power energies** (`n > 2`, every `p0 > 0`, every
`0 < p < n/(n−2)`).
`C` is fixed before every center, radius and datum. A backward geometric chain `pstart = p/g^K ≤ p0`
(`g = n/(n−2)`) keeps every input exponent `pstart g^m ≤ p/g < 1`; dyadic cutoffs run from `5R/2`
down to `2R`; the
critical weak Sobolev gain and the positive dyadic step feed the finite radius-normalized
recurrence; the start is
dominated on the open ball `B(x0,3R)` by finite-measure exponent comparison with mass `ω_n 3^n R^n`.
-/
theorem positive_norm_bound_of_cutoff_power_energy
    {n : ℕ} (hn : 2 < n) {α β p0 p : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hp0 : 0 < p0)
    (hp : 0 < p) (hpcrit : p < (n : ℝ) / ((n : ℝ)-2)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      ∀ (s : EuclideanSpace ℝ (Fin n) → ℝ) (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
        (F δ : ℝ), 0 ≤ F → 0 < δ → F * R ^ 2 ≤ α * δ → (∀ x, δ ≤ s x) →
        AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin
          n))) →
        (∃ Clog : ℝ, ∀ x, ‖Real.log (s x)‖ ≤ Clog) →
        (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
          tsupport χ ⊆ closedBall x0 (4 * R) → ∀ r : ℝ, 0 < r → r < 1 / 2 →
          let g := fun x => χ x * s x ^ r
          let dg := fun (k : Fin n) x =>
            fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
            χ x * (r * s x ^ (r-1)) * a k x
          LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          HasCompactSupport g ∧ (∃ Cg : ℝ, ∀ x, ‖g x‖ ≤ Cg) ∧
          (∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
            HasCompactSupport (dg k) ∧ MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin
              n)))) ∧
          (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            (2 + 8 * r ^ 2 * β / ((1-2 * r) ^ 2 * α)) *
              (∫ x, s x ^ (2 * r) * ∑ k : Fin n,
                (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (4 * r ^ 2 * F / ((1-2 * r) * α)) *
              (∫ x, χ x ^ 2 * s x ^ (2 * r-1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) →
        (ENNReal.ofReal R) ^ (-(n : ℝ) / p) *
          eLpNorm s (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (2 * R))) ≤
          ENNReal.ofReal C * ((ENNReal.ofReal R) ^ (-(n : ℝ) / p0) *
            eLpNorm s (ENNReal.ofReal p0)
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3 * R)))) := by
  classical
  have hnR : 2 < (n : ℝ) := by exact_mod_cast hn
  let g : ℝ := (n : ℝ) / ((n : ℝ) - 2)
  have hn2 : 0 < (n : ℝ)-2 := by linarith
  have hn0 : 0 < (n : ℝ) := by linarith
  have hg : 1 < g := by
    dsimp only [g]
    apply (lt_div_iff₀ hn2).2
    linarith
  have hg0 : 0 < g := zero_lt_one.trans hg
  have hscale : (n : ℝ) / g + 2 = (n : ℝ) := by
    dsimp only [g]
    field_simp [hn0.ne', hn2.ne']
    ring
  let q : NNReal := ⟨2 * g, by positivity⟩
  have hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
    change (2 * g)⁻¹ = _
    dsimp only [g]
    field_simp [hn0.ne', hn2.ne']
  have hqENN : (q : ENNReal) = ENNReal.ofReal (2 * g) := by
    rw [← ENNReal.ofReal_coe_nnreal];
    rfl
  -- the backward exponent chain, chosen before every center, radius and datum
  obtain ⟨K, hK1, hKprop⟩ := exists_backward_gain_exponents hg hp0 hp hpcrit
  let pstart : ℝ := p / g ^ K
  obtain ⟨hps, hpsle, hpseq, hchain⟩ :
    0 < pstart ∧
      pstart ≤ p0 ∧
        pstart * g ^ K = p ∧
          ∀ m < K, 0 < pstart * g ^ m ∧ pstart * g ^ m ≤ p / g ∧ p / g < 1 :=
    hKprop
  let t : ℝ := p / g
  have ht1 : t < 1 := (hchain 0 (by omega)).2.2
  have hdt : 0 < 1-t := by linarith
  obtain ⟨D, hD, hcut⟩ :=
    exists_smooth_concentric_cutoff_norm_fderiv_le (E := EuclideanSpace ℝ (Fin n))
  let G : NNReal := SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2
  let S : ℝ := (G : ℝ) ^ 2 * (n : ℝ)
  let Cbase : ℝ :=
    1 +
      S *
        (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * (n : ℝ) * D ^ 2) +
          t ^ 2 / (1 - t))
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hCbase : 1 ≤ Cbase := by
    have H :
      0 ≤
        S *
          (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * (n : ℝ) * D ^ 2) +
            t ^ 2 / (1 - t)) :=
      mul_nonneg hS (add_nonneg (by positivity) (div_nonneg (sq_nonneg t) hdt.le))
    dsimp only [Cbase]
    linarith
  let E : ℝ :=
    Real.exp
      ((Real.log Cbase / (1 - g⁻¹) + Real.log 4 * g⁻¹ / (1 - g⁻¹) ^ 2) / pstart)
  -- the dimensionless mass of `B(x0,3R)` in units of `R^n`
  let Mball : ℝ≥0∞ :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) *
      ENNReal.ofReal ((3 : ℝ) ^ n)
  have hMtop : Mball ≠ ⊤ := ENNReal.mul_ne_top measure_ball_lt_top.ne ENNReal.ofReal_ne_top
  have hM0 : Mball ≠ 0 := mul_ne_zero (Metric.measure_ball_pos _ _ one_pos).ne'
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have he0 : 0 ≤ 1 / pstart - 1 / p0 := by
    have H := one_div_le_one_div_of_le hps hpsle
    linarith
  let C : ℝ := E * Mball.toReal ^ (1 / pstart - 1 / p0)
  have hC : 0 < C := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (ENNReal.toReal_pos hM0 hMtop)
    _)
  have hCENN : ENNReal.ofReal C = ENNReal.ofReal E * Mball ^ (1 / pstart - 1 / p0) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ←
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg he0,
      ENNReal.ofReal_toReal hMtop]
  refine ⟨C, hC, ?_⟩
  intro x0 R hR s a F δ hF hδ hforce hs hlogm hlogB hdata
  obtain ⟨Clog, hlogb⟩ := hlogB
  have hsp (x : EuclideanSpace ℝ (Fin n)) : 0 < s x := hδ.trans_le (hs x)
  -- radii `5R/2 = ρ 0 > ρ 1 > ... ↓ 2R`
  let ρ := fun m : ℕ => R * (2 + (1 / 2) * (1 / 2 : ℝ) ^ m)
  have hρpos (m : ℕ) : 0 < ρ m := by dsimp only [ρ]; positivity
  have hρge (m : ℕ) : 2 * R ≤ ρ m := by
    have H : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
    dsimp only [ρ]
    nlinarith
  have hρle (m : ℕ) : ρ m ≤ 5 / 2 * R := by
    have H : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [ρ]
    nlinarith
  have hgap (m : ℕ) : ρ m - ρ (m + 1) = R * (1 / 2 : ℝ) ^ (m + 2) := by
    dsimp only [ρ]
    ring
  have hcutm (m : ℕ) :
    ∃ χ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ χ ∧
        HasCompactSupport χ ∧
          tsupport χ ⊆ closedBall x0 (ρ m) ∧
            (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
              (∀ x ∈ closedBall x0 (ρ (m + 1)), χ x = 1) ∧
                ∀ x, ‖fderiv ℝ χ x‖ ≤ D * 2 ^ (m + 2) / R := by
    have hlt : ρ (m + 1) < ρ m := by
      have H : 0 < R * (1 / 2 : ℝ) ^ (m + 2) := by positivity
      linarith [hgap m]
    obtain ⟨χ, hsm, hcs, hts, h01, hone, -, hd⟩ :=
      hcut x0 (ρ (m + 1)) (ρ m) (hρpos _).le hlt
    refine ⟨χ, hsm, hcs, hts, h01, hone, fun x => (hd x).trans_eq ?_⟩
    rw [hgap, one_div_pow]
    field_simp
  choose χ hχ using hcutm
  let μ := fun m : ℕ => (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall x0 (ρ m))
  have hfin (m : ℕ) : IsFiniteMeasure (μ m) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall x0 (ρ m)).measure_lt_top.ne
  -- actual finite norms, before any real representative
  have hmem (m : ℕ) : MemLp s (ENNReal.ofReal (pstart * g ^ m)) (μ m) := by
    have := hfin m
    simpa only [Real.rpow_one] using
      memLp_rpow_of_bounded_log (μ m) hsp hlogm.restrict hlogb (q := 1) (p := _)
  have hSENN : ENNReal.ofReal S = (G : ENNReal) ^ 2 * (n : ENNReal) := by
    dsimp only [S]
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [ENNReal.ofReal_pow G.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_natCast]
  have hstep :
    ∀ m < K,
      (eLpNorm s (ENNReal.ofReal (pstart * g ^ (m + 1))) (μ (m + 1))) ^
          (pstart * g ^ m) ≤
        ENNReal.ofReal (Cbase * (4 : ℝ) ^ m) * (ENNReal.ofReal R) ^ (-2 : ℝ) *
          (eLpNorm s (ENNReal.ofReal (pstart * g ^ m)) (μ m)) ^ (pstart * g ^ m) := by
    intro m hm
    let P : ℝ := pstart * g ^ m
    obtain ⟨hP, hPt, -⟩ := hchain m hm
    have hP1 : P < 1 := hPt.trans_lt ht1
    obtain ⟨hsm, hcs, hts, h01, hone, hd⟩ := hχ m
    have hχ1 : ContDiff ℝ 1 (χ m) := hsm.of_le (by exact_mod_cast le_top)
    have hts4 : tsupport (χ m) ⊆ closedBall x0 (4 * R) :=
      hts.trans (closedBall_subset_closedBall ((hρle m).trans (by linarith)))
    have hr0 : 0 < P / 2 := half_pos hP
    have hr12 : P / 2 < 1 / 2 := by linarith
    obtain ⟨hgl, hgc, ⟨Cg, hgb⟩, hgd, he⟩ := hdata (χ m) hχ1 hcs hts4 (P / 2) hr0 hr12
    have hden : 0 < 1 - 2 * (P / 2) := by linarith
    have hg :=
      weak_cutoff_sobolev_gain_of_energy_of_bounded_log hn
        (isCompact_closedBall x0 (ρ m)) measurableSet_closedBall hδ hs hts hone
        (fun x => by rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2) hd hgl hgb hgc hgd
        hχ1 hlogm hlogb (by positivity) (by positivity) he
        hq
    -- the source coefficients, rewritten BEFORE `2 (P/2) = P` touches the denominators

    have hd1 : 1 - 2 * (P / 2) = 1 - P := by ring
    have hgam :
      2 + 8 * (P / 2) ^ 2 * β / ((1 - 2 * (P / 2)) ^ 2 * α) =
        2 + 2 * P ^ 2 * β / ((1 - P) ^ 2 * α) := by
      rw [hd1]; ring
    have hf :
      4 * (P / 2) ^ 2 * F / ((1 - 2 * (P / 2)) * α) = P ^ 2 * F / ((1 - P) * α) := by
      rw [hd1]; ring
    have he2 : 2 * (P / 2) = P := by ring
    rw [hgam, hf, he2, hqENN, ← hSENN] at hg
    have := hfin m
    have hI : Integrable (fun x => s x ^ P) (μ m) :=
      MemLp.integrable le_rfl
        (memLp_rpow_of_bounded_log (μ m) hsp hlogm.restrict hlogb (q := P) (p := 1))
    have H :=
      positive_dyadic_norm_step_of_power_gain (μ m) (μ (m + 1)) s (fun x => (hsp x).le)
        hP hPt ht1 hg0 hS hn0.le hα hβ hF hδ hR hforce m hI hg
    have hexp : pstart * g ^ (m + 1) = g * (pstart * g ^ m) := by rw [pow_succ]; ring
    simpa only [hexp, Cbase] using H
  have Hit := finite_normalized_eLpNorm_sequence_bound μ s hg hps hR hCbase hscale hmem K hstep
  rw [hpseq] at Hit
  -- the target ball `B(x0,2R)` lies in every `closedBall x0 (ρ m)`; the start `closedBall x0
  -- (5R/2)` in the open `B(x0,3R)`
  have hB2 :
    eLpNorm s (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (2 * R))) ≤
      eLpNorm s (ENNReal.ofReal p) (μ K) :=
    eLpNorm_mono_measure _
      (Measure.restrict_mono
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (hρge K))) le_rfl)
  have hB3 :
    eLpNorm s (ENNReal.ofReal pstart) (μ 0) ≤
      eLpNorm s (ENNReal.ofReal pstart)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3 * R))) :=
    eLpNorm_mono_measure _
      (Measure.restrict_mono (closedBall_subset_ball ((hρle 0).trans_lt (by linarith)))
        le_rfl)
  have hmass :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3 * R)) univ =
      Mball * (ENNReal.ofReal R) ^ (n : ℝ) := by
    rw [Measure.restrict_apply_univ,
      Measure.addHaar_ball_of_pos _ _ (by positivity : (0 : ℝ) < 3 * R),
      finrank_euclideanSpace_fin, ENNReal.rpow_natCast, mul_pow,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hR.le]
    dsimp only [Mball]
    ring
  have hsmeas : AEStronglyMeasurable s (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have H := Real.continuous_exp.comp_aestronglyMeasurable hlogm
    have heq : (fun x => Real.exp (Real.log (s x))) = s := funext fun x => Real.exp_log (hsp x)
    rw [heq] at H
    exact H
  have hcmp :=
    radius_normalized_norm_mono_exponent
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3 * R)))
      hsmeas.restrict hps hp0 hpsle hR hmass
  calc
    _ ≤ (ENNReal.ofReal R) ^ (-(n : ℝ) / p) * eLpNorm s (ENNReal.ofReal p) (μ K) := by gcongr
    _ ≤ ENNReal.ofReal E * ((ENNReal.ofReal R) ^ (-(n : ℝ) / pstart) * eLpNorm s (ENNReal.ofReal
      pstart) (μ 0)) := Hit
    _ ≤ ENNReal.ofReal E * ((ENNReal.ofReal R) ^ (-(n : ℝ) / pstart) *
          eLpNorm s (ENNReal.ofReal pstart) ((volume : Measure (EuclideanSpace ℝ (Fin
            n))).restrict (ball x0 (3 * R)))) := by
      gcongr
    _ ≤ ENNReal.ofReal E * (Mball ^ (1 / pstart-1 / p0) * ((ENNReal.ofReal R) ^ (-(n : ℝ) / p0) *
          eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
            (ball x0 (3 * R))))) := by
      gcongr
    _ = _ := by rw [hCENN, mul_assoc]

end CriticalPositive

section TwoDimensional


/-- The finite-q support factor changes R^-2 to R^(-(2-2/g)); no assumption R>=1. -/
private theorem volume_scaled_coefficient_bound {S A B R g : ℝ} (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hR : 0 < R) (hcoef : S * A ≤ B / R ^ 2) :
    ENNReal.ofReal S * (ENNReal.ofReal R) ^ (2 / g) * ENNReal.ofReal A ≤
      ENNReal.ofReal B * (ENNReal.ofReal R) ^ (-(2 - 2 / g)) := by
  have h0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have ht : ENNReal.ofReal R ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc := ENNReal.ofReal_le_ofReal hcoef
  have hr : ENNReal.ofReal (B / R ^ 2) = ENNReal.ofReal B * (ENNReal.ofReal R) ^ (-2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_pos hR, ← ENNReal.ofReal_mul hB, Real.rpow_neg hR.le,
      Real.rpow_two, div_eq_mul_inv]
  rw [hr] at hc
  calc
    _ = (ENNReal.ofReal R) ^ (2 / g) * ENNReal.ofReal (S * A) := by
      rw [ENNReal.ofReal_mul hS];
      ring
    _ ≤ (ENNReal.ofReal R) ^ (2 / g) * (ENNReal.ofReal B * (ENNReal.ofReal R) ^ (-2 : ℝ)) := by
      gcongr
    _ = ENNReal.ofReal B * (ENNReal.ofReal R) ^ (2 / g + (-2 : ℝ)) := by
      rw [ENNReal.rpow_add _ _ h0 ht]; ring
    _ = _ := by congr 2; ring

/-- The exact negative-power gain gives the physical inverse-norm step with its uniform dyadic
coefficient. This interface consumes a genuine power estimate with an actual integrability premise.
-/
private theorem inverse_dyadic_norm_step_with_support_gain {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (s : X → ℝ) (hs : ∀ x, 0 < s x) {S N D α β F δ R p0 κ : ℝ} (hS : 0 ≤ S)
    (hN : 0 ≤ N) (hα : 0 < α) (hβ : 0 ≤ β) (hF : 0 ≤ F) (hδ : 0 < δ) (hR : 0 < R) (hp0 : 0 < p0)
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hforce : F * R ^ 2 ≤ α * δ) (m : ℕ)
    (hI : Integrable (fun x => s x ^ (-(p0 * κ ^ m))) μ)
    (hgain :
      (eLpNorm (fun x => s x ^ (-(p0 * κ ^ m) / 2)) (ENNReal.ofReal (2 * κ)) ν) ^ (2 : ℕ) ≤
        ENNReal.ofReal S * (ENNReal.ofReal R) ^ (2 / κ) *
          ENNReal.ofReal
            (((2 + 2 * (p0 * κ ^ m) ^ 2 * β / ((1 + p0 * κ ^ m) ^ 2 * α)) *
                  (N * (D * 2 ^ (m + 1) / R) ^ 2) +
                (((p0 * κ ^ m) ^ 2 * F / ((1 + p0 * κ ^ m) * α)) / δ)) *
              (∫ x, s x ^ (-(p0 * κ ^ m)) ∂μ))) :
    (eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal (κ * (p0 * κ ^ m))) ν) ^ (p0 * κ ^ m) ≤
      ENNReal.ofReal ((1 + S * (4 * ((2 + 2 * β / α) * N * D ^ 2) + p0)) * (4 : ℝ) ^ m) *
          (ENNReal.ofReal R) ^ (-(2 - 2 / κ)) *
        (eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal (p0 * κ ^ m)) μ) ^ (p0 * κ ^ m) := by
  have hp : 0 < p0 * κ ^ m := mul_pos hp0 (pow_pos hκ m)
  have hA :
    0 ≤
      (2 + 2 * (p0 * κ ^ m) ^ 2 * β / ((1 + p0 * κ ^ m) ^ 2 * α)) *
          (N * (D * 2 ^ (m + 1) / R) ^ 2) +
        (((p0 * κ ^ m) ^ 2 * F / ((1 + p0 * κ ^ m) * α)) / δ) := by
    positivity
  have H := inverse_norm_power_gain μ ν s hs hp (by positivity : 0 ≤ 2 * κ) hA hI hgain
  have he : (2 * κ / 2) * (p0 * κ ^ m) = κ * (p0 * κ ^ m) := by ring
  rw [he] at H
  have hc := inverse_dyadic_coefficient_bound (D := D) hS hN hα hβ hF hδ hR hp0 hκ hκ4 hforce m
  have hbase : 0 ≤ (1 + S * (4 * ((2 + 2 * β / α) * N * D ^ 2) + p0)) * (4 : ℝ) ^ m := by
    positivity
  have hscaled := volume_scaled_coefficient_bound (g := κ) hS hbase hR hc
  exact H.trans (mul_le_mul_of_nonneg_right hscaled zero_le)

/-- A positive-power Sobolev estimate gives a physical norm step whose coefficient is uniform
for every source exponent in `(0,t]`, before taking any real representatives. -/
private theorem positive_dyadic_norm_step_with_support_gain {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (s : X → ℝ) (hs : ∀ x, 0 ≤ s x) {u t κ S N D α β F δ R : ℝ} (hu : 0 < u)
    (hut : u ≤ t) (ht : t < 1) (hκ : 0 < κ) (hS : 0 ≤ S) (hN : 0 ≤ N) (hα : 0 < α) (hβ : 0 ≤ β)
    (hF : 0 ≤ F) (hδ : 0 < δ) (hR : 0 < R) (hforce : F * R ^ 2 ≤ α * δ) (m : ℕ)
    (hI : Integrable (fun x => s x ^ u) μ)
    (hgain :
      (eLpNorm (fun x => s x ^ (u / 2)) (ENNReal.ofReal (2 * κ)) ν) ^ (2 : ℕ) ≤
        ENNReal.ofReal S * (ENNReal.ofReal R) ^ (2 / κ) *
          ENNReal.ofReal
            (((2 + 2 * u ^ 2 * β / ((1 - u) ^ 2 * α)) * (N * (D * 2 ^ (m + 2) / R) ^ 2) +
                (u ^ 2 * F / ((1 - u) * α)) / δ) *
              (∫ x, s x ^ u ∂μ))) :
    (eLpNorm s (ENNReal.ofReal (κ * u)) ν) ^ u ≤
      ENNReal.ofReal
            ((1 +
                S *
                  (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * N * D ^ 2) +
                    t ^ 2 / (1 - t))) *
              (4 : ℝ) ^ m) *
          (ENNReal.ofReal R) ^ (-(2 - 2 / κ)) *
        (eLpNorm s (ENNReal.ofReal u) μ) ^ u := by
  have hdu : 0 < 1 - u := by linarith
  have hdt : 0 < 1 - t := by linarith
  have hA :
    0 ≤
      (2 + 2 * u ^ 2 * β / ((1 - u) ^ 2 * α)) * (N * (D * 2 ^ (m + 2) / R) ^ 2) +
        (u ^ 2 * F / ((1 - u) * α)) / δ := by
    positivity
  have H := positive_norm_power_gain μ ν s hs hu (by positivity : 0 ≤ 2 * κ) hA hI hgain
  have he : (2 * κ / 2) * u = κ * u := by ring
  rw [he] at H
  have hc := positive_dyadic_coefficient_bound (D := D) hu hut ht hS hN hα hβ hF hδ hR hforce m
  have hbase :
    0 ≤
      (1 + S * (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * N * D ^ 2) + t ^ 2 / (1 - t))) *
        (4 : ℝ) ^ m := by
    positivity
  have hscaled := volume_scaled_coefficient_bound (g := κ) hS hbase hR hc
  exact H.trans (mul_le_mul_of_nonneg_right hscaled zero_le)

/--
A finite dimensionless Sobolev/support factor has an actual nonnegative real representative. -/
private theorem sobolev_support_factor_eq_ofReal (G : NNReal) {M : ENNReal} (hM : M ≠ ⊤) {e : ℝ}
    (he : 0 ≤ e) :
    (G : ENNReal) ^ 2 * M ^ e * 2 = ENNReal.ofReal ((G : ℝ) ^ 2 * M.toReal ^ e * 2) := by
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (G : ℝ) ^ 2 * M.toReal ^ e),
    ENNReal.ofReal_mul (sq_nonneg (G : ℝ)), ENNReal.ofReal_pow G.coe_nonneg,
    ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg he,
    ENNReal.ofReal_toReal hM]
  norm_num

theorem inverse_essential_bound_two_of_cutoff_power_energy
    {α β p0 : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hp0 : 0 < p0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R →
      ∀ (s : EuclideanSpace ℝ (Fin 2) → ℝ) (a : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ)
        (F δ : ℝ), 0 ≤ F → 0 < δ → F * R ^ 2 ≤ α * δ → (∀ x, δ ≤ s x) →
        AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin
          2))) →
        (∃ Clog : ℝ, ∀ x, ‖Real.log (s x)‖ ≤ Clog) →
        (∀ χ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
          tsupport χ ⊆ closedBall x0 (4 * R) → ∀ r : ℝ, r < 0 →
          let g := fun x => χ x * s x ^ r
          let dg := fun (k : Fin 2) x =>
            fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k) * s x ^ r +
            χ x * (r * s x ^ (r-1)) * a k x
          LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
          HasCompactSupport g ∧ (∃ Cg : ℝ, ∀ x, ‖g x‖ ≤ Cg) ∧
          (∀ k : Fin 2, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧
            HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧ MemLp (dg k) 2
              (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
          (∫ x, ∑ k : Fin 2, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
            (2 + 8 * r ^ 2 * β / ((1-2 * r) ^ 2 * α)) *
              (∫ x, s x ^ (2 * r) * ∑ k : Fin 2,
                (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2
                ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
            (4 * r ^ 2 * F / ((1-2 * r) * α)) *
              (∫ x, χ x ^ 2 * s x ^ (2 * r-1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))) →
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 R)) ≤
          ENNReal.ofReal C * ((ENNReal.ofReal R) ^ (-(2 : ℝ) / p0) *
            eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0)
              ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (closedBall x0 (2 *
                R)))) := by
  classical
  have hκ : (1 : ℝ) < 2 := by norm_num
  have hκ0 : (0 : ℝ) < 2 := by norm_num
  have hκ4 : (2 : ℝ) ≤ 4 := by norm_num
  have hscale : (2 : ℝ) / 2 + (2 - 2 / 2) = 2 := by norm_num
  let q : NNReal := 4
  have hq2 : (2 : NNReal) ≤ q := by norm_num [q]
  have hqENN : (q : ENNReal) = ENNReal.ofReal (2 * 2) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    norm_num [q]
  have hR4 : (4 : ℝ) / ((q : NNReal) : ℝ) = 2 / 2 := by norm_num [q]
  have he0 : (0 : ℝ) ≤ 2 / ((q : NNReal) : ℝ) := by positivity
  obtain ⟨D, hD, hcut⟩ :=
    exists_smooth_concentric_cutoff_norm_fderiv_le (E := EuclideanSpace ℝ (Fin 2))
  -- the exact pinned source GNS constant at `2q/(q+2) = 4/3` and the dimensionless support envelope
  -- `ω₂ · 9`
  let G : NNReal :=
    SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (2 * q / (q + 2))
  let Mv : ENNReal :=
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) (ball 0 1) * ENNReal.ofReal (9 : ℝ)
  have hMtop : Mv ≠ ⊤ := ENNReal.mul_ne_top measure_ball_lt_top.ne ENNReal.ofReal_ne_top
  let S : ℝ := (G : ℝ) ^ 2 * Mv.toReal ^ (2 / ((q : NNReal) : ℝ)) * 2
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let Cbase : ℝ := 1 + S * (4 * ((2 + 2 * β / α) * (2 : ℝ) * D ^ 2) + p0)
  have hCbase : 1 ≤ Cbase := by
    have H : 0 ≤ S * (4 * ((2 + 2 * β / α) * (2 : ℝ) * D ^ 2) + p0) := by positivity
    dsimp only [Cbase]
    linarith
  let C : ℝ :=
    Real.exp
      ((Real.log Cbase / (1 - (2 : ℝ)⁻¹) +
          Real.log 4 * (2 : ℝ)⁻¹ / (1 - (2 : ℝ)⁻¹) ^ 2) /
        p0)
  refine ⟨C, Real.exp_pos _, ?_⟩
  intro x0 R hR s a F δ hF hδ hforce hs hlogm hlogB hdata
  obtain ⟨Clog, hlogb⟩ := hlogB
  let ρ := fun m : ℕ => R * (1 + (1 / 2 : ℝ) ^ m)
  have hρpos (m : ℕ) : 0 < ρ m := by dsimp only [ρ]; positivity
  have hρle (m : ℕ) : ρ m ≤ 2 * R := by
    have H : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [ρ]
    nlinarith
  have hρge (m : ℕ) : R ≤ ρ m := by
    have H : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
    dsimp only [ρ]
    nlinarith
  have hgap (m : ℕ) : ρ m - ρ (m + 1) = R * (1 / 2 : ℝ) ^ (m + 1) := by
    dsimp only [ρ]
    rw [pow_succ]
    ring
  have hcutm (m : ℕ) :
    ∃ χ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ ∞ χ ∧
        HasCompactSupport χ ∧
          tsupport χ ⊆ closedBall x0 (ρ m) ∧
            (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
              (∀ x ∈ closedBall x0 (ρ (m + 1)), χ x = 1) ∧
                ∀ x, ‖fderiv ℝ χ x‖ ≤ D * 2 ^ (m + 1) / R := by
    have hlt : ρ (m + 1) < ρ m := by
      have H : 0 < R * (1 / 2 : ℝ) ^ (m + 1) := by positivity
      linarith [hgap m]
    obtain ⟨χ, hsm, hcs, hts, h01, hone, -, hd⟩ :=
      hcut x0 (ρ (m + 1)) (ρ m) (hρpos _).le hlt
    refine ⟨χ, hsm, hcs, hts, h01, hone, fun x => (hd x).trans_eq ?_⟩
    rw [hgap, one_div_pow]
    field_simp
  choose χ hχ using hcutm
  let μ := fun m : ℕ => (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (closedBall x0 (ρ m))
  let ν := (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 R)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : NeZero ν := ⟨by
    intro hz
    have H := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 2)) => μ univ) hz
    have hp := Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin 2))) x0 hR
    have Hz : (volume : Measure (EuclideanSpace ℝ (Fin 2))) (ball x0 R) = 0 := by simpa [ν] using H
    exact hp.ne' Hz⟩
  have hsp (x : EuclideanSpace ℝ (Fin 2)) : 0 < s x := hδ.trans_le (hs x)
  have hmem (m : ℕ) :
    MemLp (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal (p0 * 2 ^ m)) (μ m) := by
    let : IsFiniteMeasure (μ m) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall x0 (ρ m)).measure_lt_top.ne
    exact memLp_nonpos_power_of_log_measurable _ hδ hs (by norm_num) hlogm.restrict _
  have hνmem : MemLp (fun x => s x ^ (-1 : ℝ)) ⊤ ν :=
    memLp_nonpos_power_of_log_measurable _ hδ hs (by norm_num) hlogm.restrict _
  have hνle (m : ℕ) : ν ≤ μ m :=
    Measure.restrict_mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (hρge m))) le_rfl
  have hstep (m : ℕ) :
    (eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal (p0 * 2 ^ (m + 1)))
          (μ (m + 1))) ^
        (p0 * 2 ^ m) ≤
      ENNReal.ofReal (Cbase * (4 : ℝ) ^ m) * (ENNReal.ofReal R) ^ (-(2 - 2 / 2 : ℝ)) *
        (eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal (p0 * 2 ^ m)) (μ m)) ^
          (p0 * 2 ^ m) := by
    let P : ℝ := p0 * 2 ^ m
    have hP : 0 < P := mul_pos hp0 (pow_pos hκ0 m)
    obtain ⟨hsm, hcs, hts, h01, hone, hd⟩ := hχ m
    have hχ1 : ContDiff ℝ 1 (χ m) := hsm.of_le (by exact_mod_cast le_top)
    have hts4 : tsupport (χ m) ⊆ closedBall x0 (4 * R) :=
      hts.trans (closedBall_subset_closedBall ((hρle m).trans (by linarith)))
    have hUs : closedBall x0 (ρ m) ⊆ closedBall x0 (5 / 2 * R) :=
      closedBall_subset_closedBall ((hρle m).trans (by linarith))
    obtain ⟨hgl, hgc, ⟨Cg, hgb⟩, hgd, he⟩ :=
      hdata (χ m) hχ1 hcs hts4 (-P / 2) (by linarith)
    have hden : 0 < 1 - 2 * (-P / 2) := by linarith
    have hg :=
      scaled_weak_cutoff_sobolev_gain_two_of_bounded_log (isCompact_closedBall x0 (ρ m))
        measurableSet_closedBall hδ hs hts hone
        (fun x => by rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2) hd hgl hgb
        (fun k => ⟨(hgd k).1, (hgd k).2.2.1.trans hts, (hgd k).2.2.2⟩) hχ1 hlogm hlogb
        (by positivity) (by positivity) he hq2 x0 hR hUs
    dsimp only at hg
    have hd1 : 1 - 2 * (-P / 2) = 1 + P := by ring
    have hgam :
      2 + 8 * (-P / 2) ^ 2 * β / ((1 - 2 * (-P / 2)) ^ 2 * α) =
        2 + 2 * P ^ 2 * β / ((1 + P) ^ 2 * α) := by
      rw [hd1]; ring
    have hf :
      4 * (-P / 2) ^ 2 * F / ((1 - 2 * (-P / 2)) * α) = P ^ 2 * F / ((1 + P) * α) := by
      rw [hd1]; ring
    have he2 : 2 * (-P / 2) = -P := by ring
    rw [hgam, hf, he2, hqENN, hR4, sobolev_support_factor_eq_ofReal _ hMtop he0] at hg
    let : IsFiniteMeasure (μ m) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall x0 (ρ m)).measure_lt_top.ne
    have hI : Integrable (fun x => s x ^ (-P)) (μ m) :=
      MemLp.integrable le_rfl
        (memLp_nonpos_power_of_log_measurable _ hδ hs (by linarith : -P ≤ 0)
          hlogm.restrict 1)
    have H :=
      inverse_dyadic_norm_step_with_support_gain (μ m) (μ (m + 1)) s hsp hS
        (by norm_num : (0 : ℝ) ≤ 2) hα hβ hF hδ hR hp0 hκ0 hκ4 hforce m hI hg
    have hexp : p0 * 2 ^ (m + 1) = 2 * (p0 * 2 ^ m) := by rw [pow_succ]; ring
    simpa only [hexp, Cbase] using H
  have H := eLpNorm_top_le_of_shrinking_norm_steps μ ν
    (fun x => s x ^ (-1 : ℝ)) hνmem hνle hκ hp0 hR hCbase hscale hmem hstep
  simpa only [C, ν, μ, ρ, pow_zero, mul_one, show R * (1 + 1) = 2 * R by ring] using H

theorem positive_norm_bound_two_of_cutoff_power_energy
    {α β p0 p : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hp0 : 0 < p0)
    (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R →
      ∀ (s : EuclideanSpace ℝ (Fin 2) → ℝ) (a : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ)
        (F δ : ℝ), 0 ≤ F → 0 < δ → F * R ^ 2 ≤ α * δ → (∀ x, δ ≤ s x) →
        AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin
          2))) →
        (∃ Clog : ℝ, ∀ x, ‖Real.log (s x)‖ ≤ Clog) →
        (∀ χ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
          tsupport χ ⊆ closedBall x0 (4 * R) → ∀ r : ℝ, 0 < r → r < 1 / 2 →
          let g := fun x => χ x * s x ^ r
          let dg := fun (k : Fin 2) x =>
            fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k) * s x ^ r +
            χ x * (r * s x ^ (r-1)) * a k x
          LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
          HasCompactSupport g ∧ (∃ Cg : ℝ, ∀ x, ‖g x‖ ≤ Cg) ∧
          (∀ k : Fin 2, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧
            HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧ MemLp (dg k) 2
              (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
          (∫ x, ∑ k : Fin 2, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
            (2 + 8 * r ^ 2 * β / ((1-2 * r) ^ 2 * α)) *
              (∫ x, s x ^ (2 * r) * ∑ k : Fin 2,
                (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2
                ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
            (4 * r ^ 2 * F / ((1-2 * r) * α)) *
              (∫ x, χ x ^ 2 * s x ^ (2 * r-1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))) →
        (ENNReal.ofReal R) ^ (-(2 : ℝ) / p) *
          eLpNorm s (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (2 * R))) ≤
          ENNReal.ofReal C * ((ENNReal.ofReal R) ^ (-(2 : ℝ) / p0) *
            eLpNorm s (ENNReal.ofReal p0)
              ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (3 * R)))) := by
  classical
  let g : ℝ := max 2 (p + 1)
  have hg2 : 2 ≤ g := le_max_left _ _
  have hgp : p < g := (lt_add_one p).trans_le (le_max_right _ _)
  have hg : 1 < g := by linarith
  have hg0 : 0 < g := by linarith
  have hscale : (2 : ℝ) / g + (2 - 2 / g) = 2 := by ring
  let q : NNReal := ⟨2 * g, by positivity⟩
  have hq2 : (2 : NNReal) ≤ q := by
    change ((2 : NNReal) : ℝ) ≤ 2 * g
    norm_num
    linarith
  have hqENN : (q : ENNReal) = ENNReal.ofReal (2 * g) := by
    rw [← ENNReal.ofReal_coe_nnreal]; rfl
  have hR4 : (4 : ℝ) / ((q : NNReal) : ℝ) = 2 / g := by
    change (4 : ℝ) / (2 * g) = 2 / g
    field_simp
    ring
  have he0 : (0 : ℝ) ≤ 2 / ((q : NNReal) : ℝ) := by
    positivity
  -- the backward exponent chain, chosen before every center, radius and datum
  obtain ⟨K, hK1, hKprop⟩ := exists_backward_gain_exponents hg hp0 hp hgp
  let pstart : ℝ := p / g ^ K
  obtain ⟨hps, hpsle, hpseq, hchain⟩ :
    0 < pstart ∧
      pstart ≤ p0 ∧
        pstart * g ^ K = p ∧
          ∀ m < K, 0 < pstart * g ^ m ∧ pstart * g ^ m ≤ p / g ∧ p / g < 1 :=
    hKprop
  let t : ℝ := p / g
  have ht1 : t < 1 := (hchain 0 (by omega)).2.2
  have hdt : 0 < 1-t := by linarith
  obtain ⟨D, hD, hcut⟩ :=
    exists_smooth_concentric_cutoff_norm_fderiv_le (E := EuclideanSpace ℝ (Fin 2))
  -- the exact pinned source GNS constant at `2q/(q+2)` and the dimensionless support envelope `ω₂ ·
  -- 9`
  let G : NNReal :=
    SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (2 * q / (q + 2))
  let Mv : ENNReal :=
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) (ball 0 1) * ENNReal.ofReal (9 : ℝ)
  have hMvtop : Mv ≠ ⊤ := ENNReal.mul_ne_top measure_ball_lt_top.ne ENNReal.ofReal_ne_top
  let S : ℝ := (G : ℝ) ^ 2 * Mv.toReal ^ (2 / ((q : NNReal) : ℝ)) * 2
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let Cbase : ℝ :=
    1 +
      S *
        (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * (2 : ℝ) * D ^ 2) +
          t ^ 2 / (1 - t))
  have hCbase : 1 ≤ Cbase := by
    have H :
      0 ≤
        S *
          (16 * ((2 + 2 * t ^ 2 * β / ((1 - t) ^ 2 * α)) * (2 : ℝ) * D ^ 2) +
            t ^ 2 / (1 - t)) :=
      mul_nonneg hS (add_nonneg (by positivity) (div_nonneg (sq_nonneg t) hdt.le))
    dsimp only [Cbase]
    linarith
  let E : ℝ :=
    Real.exp
      ((Real.log Cbase / (1 - g⁻¹) + Real.log 4 * g⁻¹ / (1 - g⁻¹) ^ 2) / pstart)
  -- the dimensionless mass of `B(x0,3R)` in units of `R²`
  let Mball : ℝ≥0∞ :=
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) (ball 0 1) *
      ENNReal.ofReal ((3 : ℝ) ^ 2)
  have hMtop : Mball ≠ ⊤ := ENNReal.mul_ne_top measure_ball_lt_top.ne ENNReal.ofReal_ne_top
  have hM0 : Mball ≠ 0 := mul_ne_zero (Metric.measure_ball_pos _ _ one_pos).ne'
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hd0 : 0 ≤ 1 / pstart - 1 / p0 := by
    have H := one_div_le_one_div_of_le hps hpsle
    linarith
  let C : ℝ := E * Mball.toReal ^ (1 / pstart - 1 / p0)
  have hC : 0 < C := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (ENNReal.toReal_pos hM0 hMtop)
    _)
  have hCENN : ENNReal.ofReal C = ENNReal.ofReal E * Mball ^ (1 / pstart - 1 / p0) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ←
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hd0,
      ENNReal.ofReal_toReal hMtop]
  refine ⟨C, hC, ?_⟩
  intro x0 R hR s a F δ hF hδ hforce hs hlogm hlogB hdata
  obtain ⟨Clog, hlogb⟩ := hlogB
  have hsp (x : EuclideanSpace ℝ (Fin 2)) : 0 < s x := hδ.trans_le (hs x)
  -- radii `5R/2 = ρ 0 > ρ 1 > ... ↓ 2R`
  let ρ := fun m : ℕ => R * (2 + (1 / 2) * (1 / 2 : ℝ) ^ m)
  have hρpos (m : ℕ) : 0 < ρ m := by dsimp only [ρ]; positivity
  have hρge (m : ℕ) : 2 * R ≤ ρ m := by
    have H : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
    dsimp only [ρ]
    nlinarith
  have hρle (m : ℕ) : ρ m ≤ 5 / 2 * R := by
    have H : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [ρ]
    nlinarith
  have hgap (m : ℕ) : ρ m - ρ (m + 1) = R * (1 / 2 : ℝ) ^ (m + 2) := by
    dsimp only [ρ]
    ring
  have hcutm (m : ℕ) :
    ∃ χ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ ∞ χ ∧
        HasCompactSupport χ ∧
          tsupport χ ⊆ closedBall x0 (ρ m) ∧
            (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
              (∀ x ∈ closedBall x0 (ρ (m + 1)), χ x = 1) ∧
                ∀ x, ‖fderiv ℝ χ x‖ ≤ D * 2 ^ (m + 2) / R := by
    have hlt : ρ (m + 1) < ρ m := by
      have H : 0 < R * (1 / 2 : ℝ) ^ (m + 2) := by positivity
      linarith [hgap m]
    obtain ⟨χ, hsm, hcs, hts, h01, hone, -, hd⟩ :=
      hcut x0 (ρ (m + 1)) (ρ m) (hρpos _).le hlt
    refine ⟨χ, hsm, hcs, hts, h01, hone, fun x => (hd x).trans_eq ?_⟩
    rw [hgap, one_div_pow]
    field_simp
  choose χ hχ using hcutm
  let μ := fun m : ℕ => (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (closedBall x0 (ρ m))
  have hfin (m : ℕ) : IsFiniteMeasure (μ m) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall x0 (ρ m)).measure_lt_top.ne
  -- actual finite norms, before any real representative (from the bounded logarithm)
  have hmem (m : ℕ) : MemLp s (ENNReal.ofReal (pstart * g ^ m)) (μ m) := by
    have := hfin m
    simpa only [Real.rpow_one] using
      FunctionalInequalities.Analysis.memLp_rpow_of_bounded_log (μ m) hsp hlogm.restrict
        hlogb (q := 1) (p := ENNReal.ofReal (pstart * g ^ m))
  have hstep :
    ∀ m < K,
      (eLpNorm s (ENNReal.ofReal (pstart * g ^ (m + 1))) (μ (m + 1))) ^
          (pstart * g ^ m) ≤
        ENNReal.ofReal (Cbase * (4 : ℝ) ^ m) * (ENNReal.ofReal R) ^ (-(2 - 2 / g) : ℝ) *
          (eLpNorm s (ENNReal.ofReal (pstart * g ^ m)) (μ m)) ^ (pstart * g ^ m) := by
    intro m hm
    let P : ℝ := pstart * g ^ m
    obtain ⟨hP, hPt, -⟩ := hchain m hm
    have hP1 : P < 1 := hPt.trans_lt ht1
    obtain ⟨hsm, hcs, hts, h01, hone, hd⟩ := hχ m
    have hχ1 : ContDiff ℝ 1 (χ m) := hsm.of_le (by exact_mod_cast le_top)
    have hts4 : tsupport (χ m) ⊆ closedBall x0 (4 * R) :=
      hts.trans (closedBall_subset_closedBall ((hρle m).trans (by linarith)))
    have hUs : closedBall x0 (ρ m) ⊆ closedBall x0 (5 / 2 * R) :=
      closedBall_subset_closedBall (hρle m)
    have hr0 : 0 < P / 2 := half_pos hP
    have hr12 : P / 2 < 1 / 2 := by linarith
    obtain ⟨hgl, hgc, ⟨Cg, hgb⟩, hgd, he⟩ := hdata (χ m) hχ1 hcs hts4 (P / 2) hr0 hr12
    have hden : 0 < 1 - 2 * (P / 2) := by linarith
    have hgn :=
      scaled_weak_cutoff_sobolev_gain_two_of_bounded_log (isCompact_closedBall x0 (ρ m))
        measurableSet_closedBall hδ hs hts hone
        (fun x => by rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2) hd hgl hgb
        (fun k => ⟨(hgd k).1, (hgd k).2.2.1.trans hts, (hgd k).2.2.2⟩) hχ1 hlogm hlogb
        (by positivity) (by positivity) he hq2 x0 hR hUs
    dsimp only at hgn
    -- the source coefficients, rewritten BEFORE `2 (P/2) = P` touches the denominators

    have hd1 : 1 - 2 * (P / 2) = 1 - P := by ring
    have hgam :
      2 + 8 * (P / 2) ^ 2 * β / ((1 - 2 * (P / 2)) ^ 2 * α) =
        2 + 2 * P ^ 2 * β / ((1 - P) ^ 2 * α) := by
      rw [hd1]; ring
    have hf :
      4 * (P / 2) ^ 2 * F / ((1 - 2 * (P / 2)) * α) = P ^ 2 * F / ((1 - P) * α) := by
      rw [hd1]; ring
    have he2 : 2 * (P / 2) = P := by ring
    rw [hgam, hf, he2, hqENN, hR4, sobolev_support_factor_eq_ofReal _ hMvtop he0] at hgn
    have := hfin m
    have hI : Integrable (fun x => s x ^ P) (μ m) :=
      MemLp.integrable le_rfl
        (FunctionalInequalities.Analysis.memLp_rpow_of_bounded_log (μ m) hsp
          hlogm.restrict hlogb (q := P) (p := 1))
    have H :=
      positive_dyadic_norm_step_with_support_gain (μ m) (μ (m + 1)) s
        (fun x => (hsp x).le) hP hPt ht1 hg0 hS (by norm_num : (0 : ℝ) ≤ 2) hα hβ hF hδ
        hR hforce m hI hgn
    have hexp : pstart * g ^ (m + 1) = g * (pstart * g ^ m) := by rw [pow_succ]; ring
    simpa only [hexp, Cbase] using H
  have Hit := finite_normalized_eLpNorm_sequence_bound μ s hg hps hR hCbase hscale
    hmem K hstep
  rw [hpseq] at Hit
  -- the target ball `B(x0,2R)` lies in every `closedBall x0 (ρ m)`; the start `closedBall x0
  -- (5R/2)` in the open `B(x0,3R)`
  have hB2 :
    eLpNorm s (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (2 * R))) ≤
      eLpNorm s (ENNReal.ofReal p) (μ K) :=
    eLpNorm_mono_measure _
      (Measure.restrict_mono
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (hρge K))) le_rfl)
  have hB3 :
    eLpNorm s (ENNReal.ofReal pstart) (μ 0) ≤
      eLpNorm s (ENNReal.ofReal pstart)
        ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (3 * R))) :=
    eLpNorm_mono_measure _
      (Measure.restrict_mono (closedBall_subset_ball ((hρle 0).trans_lt (by linarith)))
        le_rfl)
  have hmass :
    (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (3 * R)) univ =
      Mball * (ENNReal.ofReal R) ^ (2 : ℝ) := by
    rw [Measure.restrict_apply_univ,
      Measure.addHaar_ball_of_pos _ _ (by positivity : (0 : ℝ) < 3 * R),
      finrank_euclideanSpace_fin, ENNReal.rpow_two, mul_pow,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hR.le]
    dsimp only [Mball]
    ring
  have hsmeas : AEStronglyMeasurable s (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
    have H := Real.continuous_exp.comp_aestronglyMeasurable hlogm
    have heq : (fun x => Real.exp (Real.log (s x))) = s := funext fun x => Real.exp_log (hsp x)
    rw [heq] at H
    exact H
  have hcmp :=
    radius_normalized_norm_mono_exponent
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (3 * R)))
      hsmeas.restrict hps hp0 hpsle hR hmass
  calc
    _ ≤ (ENNReal.ofReal R) ^ (-(2 : ℝ) / p) * eLpNorm s (ENNReal.ofReal p) (μ K) := by gcongr
    _ ≤ ENNReal.ofReal E * ((ENNReal.ofReal R) ^ (-(2 : ℝ) / pstart) * eLpNorm s (ENNReal.ofReal
      pstart) (μ 0)) := Hit
    _ ≤ ENNReal.ofReal E * ((ENNReal.ofReal R) ^ (-(2 : ℝ) / pstart) *
          eLpNorm s (ENNReal.ofReal pstart) ((volume : Measure (EuclideanSpace ℝ (Fin
            2))).restrict (ball x0 (3 * R)))) := by
      gcongr
    _ ≤ ENNReal.ofReal E * (Mball ^ (1 / pstart-1 / p0) * ((ENNReal.ofReal R) ^ (-(2 : ℝ) / p0) *
          eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict
            (ball x0 (3 * R))))) := by
      gcongr
    _ = _ := by rw [hCENN, mul_assoc]

end TwoDimensional

section OneDimensional


theorem inverse_essential_bound_one_of_cutoff_power_energy
    {α β p0 : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hp0 : 0 < p0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin 1)) (R : ℝ), 0 < R →
      ∀ (s : EuclideanSpace ℝ (Fin 1) → ℝ) (a : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ)
        (F δ : ℝ), 0 ≤ F → 0 < δ → F * R ^ 2 ≤ α * δ → (∀ x, δ ≤ s x) →
        AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin
          1))) →
        (∃ Clog : ℝ, ∀ x, ‖Real.log (s x)‖ ≤ Clog) →
        (∀ χ : EuclideanSpace ℝ (Fin 1) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
          tsupport χ ⊆ closedBall x0 (4 * R) → ∀ r : ℝ, r < 0 →
          let g := fun x => χ x * s x ^ r
          let dg := fun (k : Fin 1) x =>
            fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k) * s x ^ r +
            χ x * (r * s x ^ (r-1)) * a k x
          LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin 1))) ∧
          HasCompactSupport g ∧ (∃ Cg : ℝ, ∀ x, ‖g x‖ ≤ Cg) ∧
          (∀ k : Fin 1, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin 1) ℝ k) ∧
            HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧ MemLp (dg k) 2
              (volume : Measure (EuclideanSpace ℝ (Fin 1)))) ∧
          (∫ x, ∑ k : Fin 1, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 1)))) ≤
            (2 + 8 * r ^ 2 * β / ((1-2 * r) ^ 2 * α)) *
              (∫ x, s x ^ (2 * r) * ∑ k : Fin 1,
                (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k)) ^ 2
                ∂(volume : Measure (EuclideanSpace ℝ (Fin 1)))) +
            (4 * r ^ 2 * F / ((1-2 * r) * α)) *
              (∫ x, χ x ^ 2 * s x ^ (2 * r-1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))))) →
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 R)) ≤
          ENNReal.ofReal C * ((ENNReal.ofReal R) ^ (-(1 : ℝ) / p0) *
            eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0)
              ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (closedBall x0 (2 *
                R)))) := by
  classical
  obtain ⟨Dc, hDc, hcut⟩ :=
    exists_smooth_concentric_cutoff_norm_fderiv_le (E := EuclideanSpace ℝ (Fin 1))
  -- the source inverse coefficients at the fixed exponent p0, and the dimensionless support
  -- envelope ω₁ · 3
  let Γ : ℝ := 2 + 2 * p0 ^ 2 * β / ((1 + p0) ^ 2 * α)
  let Bi : ℝ := Γ * Dc ^ 2 + p0 ^ 2 / (1 + p0)
  have hBi : 0 < Bi := by
    have h1 : 0 < p0 ^ 2 / (1 + p0) := by positivity
    have h2 : 0 ≤ Γ * Dc ^ 2 := by dsimp only [Γ]; positivity
    dsimp only [Bi]
    linarith
  let M : ℝ≥0∞ :=
    (volume : Measure (EuclideanSpace ℝ (Fin 1))) (ball 0 1) *
      ENNReal.ofReal ((3 : ℝ) ^ 1)
  have hMtop : M ≠ ⊤ := ENNReal.mul_ne_top measure_ball_lt_top.ne ENNReal.ofReal_ne_top
  have hM0 : M ≠ 0 := mul_ne_zero (Metric.measure_ball_pos _ _ one_pos).ne'
    (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  let C : ℝ := (Bi * M.toReal) ^ (1 / p0)
  have hC : 0 < C := Real.rpow_pos_of_pos (mul_pos hBi (ENNReal.toReal_pos hM0 hMtop)) _
  refine ⟨C, hC, ?_⟩
  intro x0 R hR s a F δ hF hδ hforce hs hlogm hlogB hdata
  obtain ⟨Clog, hlogb⟩ := hlogB
  have hsp : ∀ x, 0 < s x := fun x => hδ.trans_le (hs x)
  obtain ⟨χ, hsm, hcs, hts, h01, hone, -, hd⟩ := hcut x0 R (2 * R) hR.le (by linarith)
  have hχ1 : ContDiff ℝ 1 χ := hsm.of_le (by exact_mod_cast le_top)
  have hdR : ∀ x, ‖fderiv ℝ χ x‖ ≤ Dc / R := fun x => (hd x).trans_eq (by congr 1; ring)
  have hts4 : tsupport χ ⊆ closedBall x0 (4 * R) :=
    hts.trans (closedBall_subset_closedBall (by linarith))
  have hUs : closedBall x0 (2 * R) ⊆ closedBall x0 (5 / 2 * R) :=
    closedBall_subset_closedBall (by linarith)
  obtain ⟨hgl, hgc, ⟨Cg, hgb⟩, hgd, he⟩ := hdata χ hχ1 hcs hts4 (-p0 / 2) (by linarith)
  have hden : 0 < 1 - 2 * (-p0 / 2) := by linarith
  have hg :=
    weak_cutoff_sobolev_gain_of_energy_one_of_support_of_bounded_log (U :=
      closedBall x0 (2 * R)) (V := ball x0 R) (isCompact_closedBall x0 (2 * R))
      measurableSet_ball hδ hs hts (fun x hx => hone x (ball_subset_closedBall hx))
      (fun x => by rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2) hdR hgl hgb
      (fun k => ⟨(hgd k).1, (hgd k).2.2.1.trans hts, (hgd k).2.2.2⟩) hχ1 hlogm hlogb
      (by positivity) (by positivity) he
      (by positivity : (0 : ℝ) < R / 4)
  -- the source coefficients, rewritten BEFORE `2 (-p0/2) = -p0` touches the denominators
  have hd1 : 1 - 2 * (-p0 / 2) = 1 + p0 := by ring
  have hgam : 2 + 8 * (-p0 / 2) ^ 2 * β / ((1 - 2 * (-p0 / 2)) ^ 2 * α) = Γ := by
    rw [hd1]; dsimp only [Γ]; ring
  have hf :
    4 * (-p0 / 2) ^ 2 * F / ((1 - 2 * (-p0 / 2)) * α) = p0 ^ 2 * F / ((1 + p0) * α) := by
    rw [hd1]; ring
  have he2 : 2 * (-p0 / 2) = -p0 := by ring
  rw [hgam, hf, he2, inverse_power_eLpNorm_top_square _ s hsp hp0] at hg
  -- the forcing coefficient under `F R² ≤ α δ`
  have hFd : F / (α * δ) ≤ 1 / R ^ 2 :=
    (div_le_div_iff₀ (mul_pos hα hδ) (sq_pos_of_pos hR)).2
      (by simpa only [one_mul] using hforce)
  have hA :
    Γ * ((1 : ℝ) * (Dc / R) ^ 2) + p0 ^ 2 * F / ((1 + p0) * α) / δ ≤ Bi / R ^ 2 := by
    have hfo : p0 ^ 2 * F / ((1 + p0) * α) / δ ≤ (p0 ^ 2 / (1 + p0)) / R ^ 2 := by
      calc
        _ = (p0 ^ 2 / (1 + p0)) * (F / (α * δ)) := by field_simp
        _ ≤ (p0 ^ 2 / (1 + p0)) * (1 / R ^ 2) :=
          mul_le_mul_of_nonneg_left hFd (by positivity)
        _ = _ := by ring
    calc
      _ = Γ * Dc ^ 2 / R ^ 2 + p0 ^ 2 * F / ((1 + p0) * α) / δ := by ring
      _ ≤ Γ * Dc ^ 2 / R ^ 2 + (p0 ^ 2 / (1 + p0)) / R ^ 2 := by linarith
      _ = Bi / R ^ 2 := by dsimp only [Bi]; ring
  let J : ℝ := ∫ x in closedBall x0 (2 * R), s x ^ (-p0)
  have hJ : 0 ≤ J := integral_nonneg fun x => (Real.rpow_pos_of_pos (hsp x) _).le
  have hvol := volume_cthickening_le_of_subset_closedBall x0 hR hUs
  rw [Nat.cast_one, ENNReal.rpow_one] at hvol
  let :
    IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
        (closedBall x0 (2 * R))) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall x0 (2 * R)).measure_lt_top.ne
  have hI :
    Integrable (fun x => (s x ^ (-1 : ℝ)) ^ p0)
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
        (closedBall x0 (2 * R))) := by
    have heqf : (fun x => (s x ^ (-1 : ℝ)) ^ p0) = fun x => s x ^ (-p0) :=
      funext fun x => by rw [← Real.rpow_mul (hsp x).le]; ring_nf
    rw [heqf]
    exact
      MemLp.integrable le_rfl
        (memLp_nonpos_power_of_log_measurable _ hδ hs (by linarith) hlogm.restrict 1)
  have hconv := ofReal_integral_rpow_eq_eLpNorm_rpow _ (fun x => s x ^ (-1 : ℝ))
    (fun x => (Real.rpow_pos_of_pos (hsp x) _).le) hp0 hI
  have heqI : (∫ x in closedBall x0 (2 * R), (s x ^ (-1 : ℝ)) ^ p0) = J := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← Real.rpow_mul (hsp x).le]
    ring_nf
  rw [heqI] at hconv
  have hpow :
    (eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 R))) ^
        p0 ≤
      ENNReal.ofReal (Bi * M.toReal) *
        ((ENNReal.ofReal R) ^ (-(1 : ℝ) / p0) *
            eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0)
              ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
                (closedBall x0 (2 * R)))) ^
          p0 := by
    calc
      _ ≤ _ := hg
      _ ≤ (M * ENNReal.ofReal R) * ENNReal.ofReal ((Bi / R ^ 2) * J) := by gcongr
      _ = M * ENNReal.ofReal (Bi * (R⁻¹ * J)) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul hR.le]
        congr 2
        field_simp
      _ =
          ENNReal.ofReal (Bi * M.toReal) * (ENNReal.ofReal R) ^ (-1 : ℝ) *
            ENNReal.ofReal J := by
        rw [ENNReal.ofReal_rpow_of_pos hR, Real.rpow_neg_one, ENNReal.ofReal_mul hBi.le,
          ENNReal.ofReal_mul hBi.le, ENNReal.ofReal_toReal hMtop,
          ENNReal.ofReal_mul (inv_nonneg.mpr hR.le)]
        ring
      _ = _ := by
        rw [hconv, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
          show -(1 : ℝ) / p0 * p0 = -1 by field_simp]
        ring
  have H := le_rpow_one_div_mul_of_rpow_le hp0 hpow
  rwa [ENNReal.ofReal_rpow_of_nonneg (mul_pos hBi (ENNReal.toReal_pos hM0 hMtop)).le
      (by positivity)] at H

theorem positive_essential_bound_one_of_cutoff_power_energy
    {α β p0 : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hp0 : 0 < p0)
    (hp01 : p0 < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin 1)) (R : ℝ), 0 < R →
      ∀ (s : EuclideanSpace ℝ (Fin 1) → ℝ) (a : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ)
        (F δ : ℝ), 0 ≤ F → 0 < δ → F * R ^ 2 ≤ α * δ → (∀ x, δ ≤ s x) →
        AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin
          1))) →
        (∃ Clog : ℝ, ∀ x, ‖Real.log (s x)‖ ≤ Clog) →
        (∀ χ : EuclideanSpace ℝ (Fin 1) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
          tsupport χ ⊆ closedBall x0 (4 * R) → ∀ r : ℝ, 0 < r → r < 1 / 2 →
          let g := fun x => χ x * s x ^ r
          let dg := fun (k : Fin 1) x =>
            fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k) * s x ^ r +
            χ x * (r * s x ^ (r-1)) * a k x
          LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin 1))) ∧
          HasCompactSupport g ∧ (∃ Cg : ℝ, ∀ x, ‖g x‖ ≤ Cg) ∧
          (∀ k : Fin 1, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin 1) ℝ k) ∧
            HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧ MemLp (dg k) 2
              (volume : Measure (EuclideanSpace ℝ (Fin 1)))) ∧
          (∫ x, ∑ k : Fin 1, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 1)))) ≤
            (2 + 8 * r ^ 2 * β / ((1-2 * r) ^ 2 * α)) *
              (∫ x, s x ^ (2 * r) * ∑ k : Fin 1,
                (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k)) ^ 2
                ∂(volume : Measure (EuclideanSpace ℝ (Fin 1)))) +
            (4 * r ^ 2 * F / ((1-2 * r) * α)) *
              (∫ x, χ x ^ 2 * s x ^ (2 * r-1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))))) →
        eLpNorm s ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (2 * R))) ≤
          ENNReal.ofReal C * ((ENNReal.ofReal R) ^ (-(1 : ℝ) / p0) *
            eLpNorm s (ENNReal.ofReal p0)
              ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3 * R)))) := by
  classical
  obtain ⟨Dc, hDc, hcut⟩ :=
    exists_smooth_concentric_cutoff_norm_fderiv_le (E := EuclideanSpace ℝ (Fin 1))
  -- the source positive coefficients at the fixed exponent p0 < 1, and the dimensionless support
  -- envelope ω₁ · 3
  have hdp : 0 < 1-p0 := by linarith
  let Γ : ℝ := 2 + 2 * p0 ^ 2 * β / ((1 - p0) ^ 2 * α)
  let Bi : ℝ := 4 * Γ * Dc ^ 2 + p0 ^ 2 / (1 - p0)
  have hBi : 0 < Bi := by
    have h1 : 0 < p0 ^ 2 / (1 - p0) := by positivity
    have h2 : 0 ≤ 4 * Γ * Dc ^ 2 := by dsimp only [Γ]; positivity
    dsimp only [Bi]
    linarith
  let M : ℝ≥0∞ :=
    (volume : Measure (EuclideanSpace ℝ (Fin 1))) (ball 0 1) *
      ENNReal.ofReal ((3 : ℝ) ^ 1)
  have hMtop : M ≠ ⊤ := ENNReal.mul_ne_top measure_ball_lt_top.ne ENNReal.ofReal_ne_top
  have hM0 : M ≠ 0 := mul_ne_zero (Metric.measure_ball_pos _ _ one_pos).ne'
    (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  let C : ℝ := (Bi * M.toReal) ^ (1 / p0)
  have hC : 0 < C := Real.rpow_pos_of_pos (mul_pos hBi (ENNReal.toReal_pos hM0 hMtop)) _
  refine ⟨C, hC, ?_⟩
  intro x0 R hR s a F δ hF hδ hforce hs hlogm hlogB hdata
  obtain ⟨Clog, hlogb⟩ := hlogB
  have hsp : ∀ x, 0 < s x := fun x => hδ.trans_le (hs x)
  obtain ⟨χ, hsm, hcs, hts, h01, hone, -, hd⟩ :=
    hcut x0 (2 * R) (5 / 2 * R) (by positivity) (by linarith)
  have hχ1 : ContDiff ℝ 1 χ := hsm.of_le (by exact_mod_cast le_top)
  have hdR : ∀ x, ‖fderiv ℝ χ x‖ ≤ 2 * Dc / R := fun x =>
    (hd x).trans_eq (by field_simp; ring)
  have hts4 : tsupport χ ⊆ closedBall x0 (4 * R) :=
    hts.trans (closedBall_subset_closedBall (by linarith))
  have hUs : closedBall x0 (5 / 2 * R) ⊆ closedBall x0 (5 / 2 * R) := subset_rfl
  obtain ⟨hgl, hgc, ⟨Cg, hgb⟩, hgd, he⟩ :=
    hdata χ hχ1 hcs hts4 (p0 / 2) (by linarith) (by linarith)
  have hden : 0 < 1 - 2 * (p0 / 2) := by linarith
  have hg :=
    weak_cutoff_sobolev_gain_of_energy_one_of_support_of_bounded_log (U :=
      closedBall x0 (5 / 2 * R)) (V := ball x0 (2 * R))
      (isCompact_closedBall x0 (5 / 2 * R)) measurableSet_ball hδ hs hts
      (fun x hx => hone x (ball_subset_closedBall hx))
      (fun x => by rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2) hdR hgl hgb
      (fun k => ⟨(hgd k).1, (hgd k).2.2.1.trans hts, (hgd k).2.2.2⟩) hχ1 hlogm hlogb
      (by positivity) (by positivity) he
      (by positivity : (0 : ℝ) < R / 4)
  -- the source coefficients, rewritten BEFORE `2 (p0/2) = p0` touches the denominators
  have hd1 : 1 - 2 * (p0 / 2) = 1 - p0 := by ring
  have hgam : 2 + 8 * (p0 / 2) ^ 2 * β / ((1 - 2 * (p0 / 2)) ^ 2 * α) = Γ := by
    rw [hd1]; dsimp only [Γ]; ring
  have hf :
    4 * (p0 / 2) ^ 2 * F / ((1 - 2 * (p0 / 2)) * α) = p0 ^ 2 * F / ((1 - p0) * α) := by
    rw [hd1]; ring
  have he2 : 2 * (p0 / 2) = p0 := by ring
  rw [hgam, hf, he2, positive_power_eLpNorm_top_square _ s (fun x => (hsp x).le) hp0] at hg
  -- the forcing coefficient under `F R² ≤ α δ` (`positive_power_coefficients_bound` at u = t = p0)
  have hfo := (positive_power_coefficients_bound hp0 le_rfl hp01 hα hβ hF hδ hR hforce).2
  have hA :
    Γ * ((1 : ℝ) * (2 * Dc / R) ^ 2) + p0 ^ 2 * F / ((1 - p0) * α) / δ ≤ Bi / R ^ 2 := by
    calc
      _ = 4 * Γ * Dc ^ 2 / R ^ 2 + p0 ^ 2 * F / ((1 - p0) * α) / δ := by ring
      _ ≤ 4 * Γ * Dc ^ 2 / R ^ 2 + (p0 ^ 2 / (1 - p0)) / R ^ 2 := by linarith
      _ = Bi / R ^ 2 := by dsimp only [Bi]; ring
  let J : ℝ := ∫ x in closedBall x0 (5 / 2 * R), s x ^ p0
  have hJ : 0 ≤ J := integral_nonneg fun x => (Real.rpow_pos_of_pos (hsp x) _).le
  have hvol := volume_cthickening_le_of_subset_closedBall x0 hR hUs
  rw [Nat.cast_one, ENNReal.rpow_one] at hvol
  let :
    IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
        (closedBall x0 (5 / 2 * R))) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall x0 (5 / 2 * R)).measure_lt_top.ne
  have hI :
    Integrable (fun x => s x ^ p0)
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
        (closedBall x0 (5 / 2 * R))) :=
    MemLp.integrable le_rfl
      (FunctionalInequalities.Analysis.memLp_rpow_of_bounded_log _ hsp hlogm.restrict
        hlogb (q := p0) (p := 1))
  have hconv := ofReal_integral_rpow_eq_eLpNorm_rpow _ s (fun x => (hsp x).le) hp0 hI
  have hpow :
    (eLpNorm s ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (2 * R)))) ^
        p0 ≤
      ENNReal.ofReal (Bi * M.toReal) *
        ((ENNReal.ofReal R) ^ (-(1 : ℝ) / p0) *
            eLpNorm s (ENNReal.ofReal p0)
              ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
                (closedBall x0 (5 / 2 * R)))) ^
          p0 := by
    calc
      _ ≤ _ := hg
      _ ≤ (M * ENNReal.ofReal R) * ENNReal.ofReal ((Bi / R ^ 2) * J) := by gcongr
      _ = M * ENNReal.ofReal (Bi * (R⁻¹ * J)) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul hR.le]
        congr 2
        field_simp
      _ =
          ENNReal.ofReal (Bi * M.toReal) * (ENNReal.ofReal R) ^ (-1 : ℝ) *
            ENNReal.ofReal J := by
        rw [ENNReal.ofReal_rpow_of_pos hR, Real.rpow_neg_one, ENNReal.ofReal_mul hBi.le,
          ENNReal.ofReal_mul hBi.le, ENNReal.ofReal_toReal hMtop,
          ENNReal.ofReal_mul (inv_nonneg.mpr hR.le)]
        ring
      _ = _ := by
        rw [hconv, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
          show -(1 : ℝ) / p0 * p0 = -1 by field_simp]
        ring
  have H := le_rpow_one_div_mul_of_rpow_le hp0 hpow
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_pos hBi (ENNReal.toReal_pos hM0 hMtop)).le
      (by positivity)] at H
  -- the start `closedBall x0 (5R/2)` lies in the open `B(x0,3R)`
  have hmono :
    eLpNorm s (ENNReal.ofReal p0)
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict
          (closedBall x0 (5 / 2 * R))) ≤
      eLpNorm s (ENNReal.ofReal p0)
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3 * R))) :=
    eLpNorm_mono_measure _
      (Measure.restrict_mono (closedBall_subset_ball (by linarith)) le_rfl)
  exact H.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono zero_le) zero_le)

end OneDimensional

end FunctionalInequalities.Analysis
