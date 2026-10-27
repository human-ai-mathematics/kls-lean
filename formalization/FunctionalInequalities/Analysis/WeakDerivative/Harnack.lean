import FunctionalInequalities.Analysis.WeakDerivative.Caccioppoli
import FunctionalInequalities.Analysis.WeakDerivative.Moser
import FunctionalInequalities.Analysis.WeakDerivative.Representation
import FunctionalInequalities.Analysis.MorreyGrowth
import FunctionalInequalities.Probability.ExponentialMoments.Growth
import FunctionalInequalities.Analysis.LpExponent

/-!
# Weak Harnack inequality for given bounded weak supersolutions

Gilbarg–Trudinger (2001), Theorem 8.18 with (8.47)–(8.49), pp. 194–196, in the bounded symmetric pure-divergence case, for a
GIVEN globally bounded weak `H¹_loc` function `w`, a.e. measurable coefficients `A` with `α ≤ A ≤ β` a.e. on `B̄(x0,4R)`,
`w ≥ 0` a.e. there and the weak supersolution inequality against bounded nonnegative weak tests supported in `B̄(x0,4R)`:
`R^{−n/p} ‖w‖_{L^p(B(x0,2R))} ≤ C(p) (essinf_{B(x0,R)} w + F R²/α)` for every `n > 0` and every `p > 0` with `n ≤ 2` or
`p < n/(n−2)`, with `C(p)` chosen before all data (`bounded_weak_harnack_of_given_data`).

Proof: the given-data energies of `WeakDerivative/Caccioppoli` and one weak logarithm (identified only a.e. on the ball), the
Morrey bound and John–Nirenberg (`n ≥ 2`) or the kernel-one representation (`n = 1`) give two-sided moments of
`δ + max w 0`; the Moser endpoints of `WeakDerivative/Moser` and the moment-to-product bridge give a shift-uniform product,
and the finite-constant shift removal of `LpExponent` gives the essential-infimum form. The dimension cases `n > 2`, `n = 2`
and `n = 1` are private steps. The full unbounded, nonsymmetric, lower-order or domain-only Theorem 8.18 is not claimed.
-/

noncomputable section

namespace FunctionalInequalities.Analysis

section ShiftedLog
open MeasureTheory Set
/-- Measurability and boundedness of the shifted positive-part logarithm; no global weak derivative is asserted.
Input for the bounded pure-divergence weak Harnack proof (Gilbarg–Trudinger 2001, Theorem 8.18). -/
private theorem shifted_log_measurable_bounded {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C) (hδ : 0 < δ) :
    AEStronglyMeasurable (fun x => Real.log (δ + max (w x) 0))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∃ Clog : ℝ, 0 ≤ Clog ∧ ∀ x, ‖Real.log (δ + max (w x) 0)‖ ≤ Clog := by
  have hC : 0 ≤ C := (norm_nonneg (w 0)).trans (hbound 0)
  have hcont : Continuous (fun t : ℝ => Real.log (δ + max t 0)) :=
    (show Continuous (fun t : ℝ => δ + max t 0) by fun_prop).log
      (fun t => ne_of_gt (by linarith [le_max_right t 0]))
  refine ⟨hcont.comp_aestronglyMeasurable hw.aestronglyMeasurable, ?_⟩
  obtain ⟨Clog, hClog⟩ := (isCompact_Icc : IsCompact (Icc δ (δ+C))).exists_bound_of_continuousOn
    (f := Real.log) (Real.continuousOn_log.mono (fun t ht => ne_of_gt (hδ.trans_le ht.1)))
  refine ⟨Clog, (norm_nonneg (Real.log δ)).trans (hClog δ ⟨le_rfl, by linarith⟩), fun x => ?_⟩
  have hwC : w x ≤ C := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound x)
  exact hClog (δ + max (w x) 0) ⟨by linarith [le_max_right (w x) 0], by linarith [max_le hwC hC]⟩
end ShiftedLog

section LogMorrey
open MeasureTheory Matrix Set FunctionalInequalities.Analysis
open scoped ContDiff ENNReal
/-- A cutoff constant depending only on dimension is chosen before every weak datum. The same bounded weak log extension
has all-ball buffered Morrey bounds for every ball contained in S. Gilbarg–Trudinger (2001), (8.49) to (7.51). -/
private theorem exists_uniform_log_morrey_of_weak_data {n : ℕ} (hn : 0 < n) :
    ∃ D : ℝ, 0 < D ∧ ∀
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {C α β F δ : ℝ}
    (_hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hbound : ∀ x, ‖w x‖ ≤ C)
    (_hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (_ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (_hAm : ∀ i j : Fin n, AEStronglyMeasurable (fun x => A x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {S : Set (EuclideanSpace ℝ (Fin n))} (_hSm : MeasurableSet S)
    (_hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)), 0 ≤ w x)
    (_hα : 0 < α) (_hβ : 0 < β) (_hF : 0 ≤ F)
    (_hcoeff : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)),
      (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (_hsub : ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ)
        (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) → HasCompactSupport η →
      Function.support η ⊆ S → (∀ x, 0 ≤ η x) →
      (∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ S ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hδ : 0 < δ),
    ∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖H x‖ ≤ B) ∧
      (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
          MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K)) ∧
      (H =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)]
        (fun x => Real.log (δ + max (w x) 0))) ∧
      (∀ k : Fin n, (dH k) =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)]
        (fun x => (δ + max (w x) 0)⁻¹ * a k x)) ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → Metric.closedBall x0 (4*R) ⊆ S →
      let K := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (16:ℝ)^n *
        (1 + (4*β/α)*(n:ℝ)*D^2 + (2*F/(α*δ))*R^2)
      ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
        (∫⁻ x in Metric.ball x0 (3*R) ∩ Metric.ball c r,
          ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (dH i x)^2))) ≤
          ENNReal.ofReal (K * r ^ ((n:ℝ)-1)) := by
  obtain ⟨D,hD,hM⟩ := exists_centered_buffered_morrey_bound_of_cutoff_energy hn
  refine ⟨D,hD,?_⟩
  intro w a A C α β F δ hw hbound hweak ha2 hAm S hSm hnonneg hα hβ hF hcoeff hsub hδ
  obtain ⟨H,dH,hl,hb,hd,hHe,hde,hE⟩ := exists_weak_log_extension_with_energy_on_set
    hw hbound hweak ha2 hAm hSm hnonneg hα hβ hF hcoeff hsub hδ
  refine ⟨H,dH,hl,hb,hd,hHe,hde,fun x0 R hR hBS => ?_⟩
  exact hM x0 R (4*β/α) (2*F/(α*δ)) dH hR (by positivity) (by positivity)
    (fun i => (hd i).1.2.1.aestronglyMeasurable) (fun i => (hd i).2)
    (fun χ hχ hχc hχB _h01 => by
      have he := hE χ hχ hχc (hχB.trans hBS)
      exact ⟨he.1, he.2.2.2⟩)
end LogMorrey

section JohnNirenberg
open MeasureTheory Matrix Set Metric FunctionalInequalities.Analysis
open scoped ContDiff ENNReal
/- Two private arithmetic/geometry steps: the critical John–Nirenberg exponent on `B(c, 3R)` and its uniform small-forcing
form. -/
private theorem ball_jn_sigma_eq {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) (τ : ℝ) :
    τ * (n : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball c (3 * R)) /
      (6 * R) ^ (n : ℝ) = τ * (n : ℝ) *
        (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) / (2 : ℝ)^n := by
  have h3 : 0 < 3 * R := by linarith
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball c (3 * R)) =
      (3 * R)^n * (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) := by
    have H := congrArg ENNReal.toReal (Measure.addHaar_ball_of_pos
      (volume : Measure (EuclideanSpace ℝ (Fin n))) c h3)
    simpa only [finrank_euclideanSpace_fin,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg h3.le n),measureReal_def] using H
  have h6 : (6 * R)^n = (2 : ℝ)^n * (3 * R)^n := by
    rw [← mul_pow]
    congr 1
    ring
  rw [Real.rpow_natCast,hvol,h6]
  field_simp [(pow_pos h3 n).ne']

/-- Under `F R² ≤ α δ` the exponent `p0 = τ n/(32^n U)` is positive and at most `(τ n «ω»/2^n)/K16` (`n > 0`; algebra only). -/
private theorem small_forcing_uniform_jn_exponent {n : ℕ} (hn : 0 < n)
    {«ω» τ α β D F δ R : ℝ} (hω : 0 < «ω») (hτ : 0 < τ) (hα : 0 < α)
    (hβ : 0 ≤ β) (hF : 0 ≤ F) (hδ : 0 < δ) (hforce : F * R^2 ≤ α * δ) :
    let U := 3 + (4 * β / α) * (n : ℝ) * D^2
    let K := «ω» * (16 : ℝ)^n * (1 + (4 * β / α) * (n : ℝ) * D^2 + (2 * F / (α * δ)) * R^2)
    let p0 := τ * (n : ℝ) / ((32 : ℝ)^n * U)
    0 < p0 ∧ 0 < K ∧ p0 ≤ (τ * (n : ℝ) * «ω» / (2 : ℝ)^n) / K := by
  intro U K p0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hQ : 0 ≤ (4 * β / α) * (n : ℝ) * D^2 := by positivity
  have hU : 0 < U := by dsimp only [U]; linarith
  have hp : 0 < p0 := by dsimp only [p0]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hterm : (2 * F / (α * δ)) * R^2 ≤ 2 := by
    calc
      _ = (2 * F * R^2) / (α * δ) := by ring
      _ ≤ 2 := (div_le_iff₀ (mul_pos hα hδ)).2 (by nlinarith [hforce])
  have hKb : K ≤ «ω» * (16 : ℝ)^n * U := by
    exact mul_le_mul_of_nonneg_left (by dsimp only [U]; linarith) (by positivity)
  refine ⟨hp,hK,(le_div_iff₀ hK).2 ?_⟩
  calc
    _ ≤ p0 * («ω» * (16 : ℝ)^n * U) := mul_le_mul_of_nonneg_left hKb hp.le
    _ = _ := by
      dsimp only [p0]
      have h32 : (32 : ℝ)^n = (2 : ℝ)^n * (16 : ℝ)^n := by rw [← mul_pow]; norm_num
      rw [h32]
      field_simp [hU.ne']

/-- Uniform shifted-log exponential moment from GIVEN bounded weak PDE data, n>=2, under the small-forcing scale.
Input for Gilbarg–Trudinger (2001), Theorem 8.18, via Theorems 7.16/7.21; no Harnack conclusion. -/
private theorem exists_uniform_log_exp_of_weak_data {n : ℕ} (h2 : 2 ≤ n) :
    ∃ D : ℝ, 0 < D ∧ ∀
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {C α β F δ : ℝ}
    (_hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hbound : ∀ x, ‖w x‖ ≤ C)
    (_hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (_ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (_hAm : ∀ i j : Fin n, AEStronglyMeasurable (fun x => A x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {S : Set (EuclideanSpace ℝ (Fin n))} (_hSm : MeasurableSet S)
    (_hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)), 0 ≤ w x)
    (_hα : 0 < α) (_hβ : 0 < β) (_hF : 0 ≤ F)
    (_hcoeff : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)),
      (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (_hsub : ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ)
        (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) → HasCompactSupport η →
      Function.support η ⊆ S → (∀ x, 0 ≤ η x) →
      (∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ S ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hδ : 0 < δ),
    ∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖H x‖ ≤ B) ∧
      (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
          MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K)) ∧
      (H =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)]
        (fun x => Real.log (δ + max (w x) 0))) ∧
      (∀ k : Fin n, (dH k) =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)]
        (fun x => (δ + max (w x) 0)⁻¹ * a k x)) ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → Metric.closedBall x0 (4*R) ⊆ S →
      F * R^2 ≤ α * δ →
      let p0 := (2 * ((n:ℝ)-1) * Real.exp 1)⁻¹ * (n:ℝ) /
        ((32:ℝ)^n * (3 + (4*β/α)*(n:ℝ)*D^2))
      0 < p0 ∧
      Integrable (fun x => Real.exp (p0 * |H x - ⨍ y in Metric.ball x0 (3*R), H y|))
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R))) ∧
      (∫ x in Metric.ball x0 (3*R), Real.exp (p0 * |H x - ⨍ y in Metric.ball x0 (3*R), H y|)) ≤
        2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
          (n:ℝ) / ((n:ℝ)-1)) * (1 + 4 * ((n:ℝ)-1)^2)) * (6*R)^(n:ℝ) := by
  have hn : 0 < n := by omega
  obtain ⟨D,hD,hM⟩ := exists_uniform_log_morrey_of_weak_data hn
  refine ⟨D,hD,?_⟩
  intro w a A C α β F δ hw hbound hweak ha2 hAm S hSm hnonneg hα hβ hF hcoeff hsub hδ
  obtain ⟨H,dH,hl,⟨BH,hBH0,hBH⟩,hd,hHe,hde,hmor⟩ :=
    hM hw hbound hweak ha2 hAm hSm hnonneg hα hβ hF hcoeff hsub hδ
  refine ⟨H,dH,hl,⟨BH,hBH0,hBH⟩,hd,hHe,hde,fun x0 R hR hBS hforce => ?_⟩
  intro p0
  let «ω» := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1)
  let τ := (2 * ((n:ℝ)-1) * Real.exp 1)⁻¹
  let K := «ω» * (16:ℝ)^n * (1 + (4*β/α)*(n:ℝ)*D^2 + (2*F/(α*δ))*R^2)
  have hω : 0 < «ω» := ENNReal.toReal_pos (Metric.measure_ball_pos
    (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne' measure_ball_lt_top.ne
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast h2
  have hnm1 : 0 < (n:ℝ)-1 := by linarith
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  obtain ⟨hp0,hK,hpcomp⟩ := small_forcing_uniform_jn_exponent (D := D) hn hω hτ hα hβ.le hF hδ hforce
  have hdiam : ∀ y ∈ ball x0 (3*R), ∀ z ∈ ball x0 (3*R), dist y z ≤ 6*R := by
    intro y hy z hz
    have hy' := Metric.mem_ball.mp hy
    have hz' := Metric.mem_ball.mp hz
    have hdist := dist_triangle y x0 z
    rw [dist_comm x0 z] at hdist
    linarith
  have hJ := integrable_exp_abs_sub_average_of_bounded_weak_morrey h2 Metric.isOpen_ball
    (convex_ball x0 (3*R)) ⟨x0, Metric.mem_ball_self (by linarith)⟩ (by linarith : 0 < 6*R)
    hK hdiam hl hBH (fun i => (hd i).1) (fun i => (hd i).2) (hmor x0 R hR hBS)
  let t := (τ * (n:ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball x0 (3*R)) /
    (6*R)^(n:ℝ)) / K
  have hpt : p0 ≤ t := by
    dsimp only [t]
    rw [ball_jn_sigma_eq x0 hR τ]
    exact hpcomp
  have hint : Integrable (fun x => Real.exp (t * |H x - ⨍ y in ball x0 (3*R), H y|))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R))) := hJ.2.1
  have he (x : EuclideanSpace ℝ (Fin n)) :
      Real.exp (p0 * |H x - ⨍ y in ball x0 (3*R), H y|) ≤
        Real.exp (t * |H x - ⨍ y in ball x0 (3*R), H y|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hpt (abs_nonneg _))
  have hm : AEStronglyMeasurable (fun x => Real.exp (p0 * |H x - ⨍ y in ball x0 (3*R), H y|))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R))) := by
    apply Real.continuous_exp.comp_aestronglyMeasurable
    have hdH : AEStronglyMeasurable (fun x => H x - ⨍ y in ball x0 (3*R), H y)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R))) :=
      (show AEStronglyMeasurable H
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R))) from
          hl.aestronglyMeasurable.restrict).sub aestronglyMeasurable_const
    simpa only [Real.norm_eq_abs] using hdH.norm.const_mul p0
  have hi := hint.mono_nonneg hm (ae_of_all _ fun x => (Real.exp_pos _).le) (ae_of_all _ he)
  exact ⟨hp0,hi,(integral_mono_ae hi hint (ae_of_all _ he)).trans hJ.2.2⟩
end JohnNirenberg

section Moments
open MeasureTheory Matrix Set Metric FunctionalInequalities.Analysis
open scoped ContDiff ENNReal
/-- At the same GIVEN weak data and the same log extension, uniform positive/negative shifted moments.
The moment input for Gilbarg–Trudinger (2001), Theorem 8.18, `n ≥ 2`; not a Harnack conclusion. -/
private theorem exists_uniform_log_moments_of_weak_data {n : ℕ} (h2 : 2 ≤ n) :
    ∃ D : ℝ, 0 < D ∧ ∀
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {C α β F δ : ℝ}
    (_hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hbound : ∀ x, ‖w x‖ ≤ C)
    (_hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (_ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (_hAm : ∀ i j : Fin n, AEStronglyMeasurable (fun x => A x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {S : Set (EuclideanSpace ℝ (Fin n))} (_hSm : MeasurableSet S)
    (_hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)), 0 ≤ w x)
    (_hα : 0 < α) (_hβ : 0 < β) (_hF : 0 ≤ F)
    (_hcoeff : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)),
      (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (_hsub : ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ)
        (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) → HasCompactSupport η →
      Function.support η ⊆ S → (∀ x, 0 ≤ η x) →
      (∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ S ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hδ : 0 < δ),
    ∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖H x‖ ≤ B) ∧
      (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
          MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K)) ∧
      (H =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)]
        (fun x => Real.log (δ + max (w x) 0))) ∧
      (∀ k : Fin n, (dH k) =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)]
        (fun x => (δ + max (w x) 0)⁻¹ * a k x)) ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → Metric.closedBall x0 (4*R) ⊆ S →
      F * R^2 ≤ α * δ →
      let p0 := (2 * ((n:ℝ)-1) * Real.exp 1)⁻¹ * (n:ℝ) /
        ((32:ℝ)^n * (3 + (4*β/α)*(n:ℝ)*D^2))
      let s := fun x => δ + max (w x) 0
      0 < p0 ∧
      Integrable (fun x => Real.exp (p0 * |H x - ⨍ y in Metric.ball x0 (3*R), H y|))
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R))) ∧
      (∫ x in Metric.ball x0 (3*R), Real.exp (p0 * |H x - ⨍ y in Metric.ball x0 (3*R), H y|)) ≤
        2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
          (n:ℝ) / ((n:ℝ)-1)) * (1 + 4 * ((n:ℝ)-1)^2)) * (6*R)^(n:ℝ) ∧
      Integrable (fun x => s x ^ p0)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R))) ∧
      Integrable (fun x => s x ^ (-p0))
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R))) ∧
      (∫ x in ball x0 (3*R), s x ^ p0) * (∫ x in ball x0 (3*R), s x ^ (-p0)) ≤
        (2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
          (n:ℝ) / ((n:ℝ)-1)) * (1 + 4 * ((n:ℝ)-1)^2)) * (6*R)^(n:ℝ))^2 := by
  obtain ⟨D,hD,hJ⟩ := exists_uniform_log_exp_of_weak_data h2
  refine ⟨D,hD,?_⟩
  intro w a A C α β F δ hw hbound hweak ha2 hAm S hSm hnonneg hα hβ hF hcoeff hsub hδ
  obtain ⟨H,dH,hl,hb,hd,hHe,hde,hball⟩ :=
    hJ hw hbound hweak ha2 hAm hSm hnonneg hα hβ hF hcoeff hsub hδ
  refine ⟨H,dH,hl,hb,hd,hHe,hde,fun x0 R hR hBS hforce => ?_⟩
  intro p0 s
  obtain ⟨hp0,hi,hA⟩ := hball x0 R hR hBS hforce
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R))
  have hB3S : ball x0 (3*R) ⊆ S :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).trans hBS
  have hHe3 : H =ᵐ[μ] (fun x => Real.log (s x)) := ae_restrict_of_ae_restrict_of_subset hB3S hHe
  have hslog : AEStronglyMeasurable (fun x => Real.log (s x)) μ :=
    (show AEStronglyMeasurable H μ from hl.aestronglyMeasurable.restrict).congr hHe3
  have he : (fun x => Real.exp (p0 * |H x - ⨍ y in ball x0 (3*R), H y|)) =ᵐ[μ]
      (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in ball x0 (3*R), H y|)) := by
    filter_upwards [hHe3] with x hx
    rw [hx]
  have his : Integrable (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in ball x0 (3*R), H y|)) μ := hi.congr he
  have hAs : (∫ x, Real.exp (p0 * |Real.log (s x) - ⨍ y in ball x0 (3*R), H y|) ∂μ) ≤
      2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) *
        (n:ℝ) / ((n:ℝ)-1)) * (1 + 4 * ((n:ℝ)-1)^2)) * (6*R)^(n:ℝ) := by
    rw [← integral_congr_ae he]
    exact hA
  obtain ⟨hp,hn,hprod⟩ := FunctionalInequalities.Probability.integral_rpow_mul_integral_rpow_neg_le_of_log_exp
    hp0.le (ae_of_all μ fun x => show 0 < s x from by dsimp only [s]; linarith [le_max_right (w x) 0])
    hslog his hAs
  exact ⟨hp0,hi,hA,hp,hn,hprod⟩
end Moments

section MomentsOne
open MeasureTheory Matrix Set Metric FunctionalInequalities.Analysis
open scoped ContDiff ENNReal
/- Two private one-dimensional steps: the uniform exponent arithmetic and the Haar volume of `B(x, 3R)`. -/
private theorem uniform_one_dimensional_exponent
    {«ω» α β D F δ R : ℝ} (hω : 0 < «ω») (hα : 0 < α) (hβ : 0 ≤ β)
    (hF : 0 ≤ F) (hδ : 0 < δ) (hR : 0 < R) (hforce : F*R^2 ≤ α*δ) :
    let U := 3+(4*β/α)*D^2
    let K := «ω»*16*(1+(4*β/α)*D^2+(2*F/(α*δ))*R^2)
    let p0 := (32*U)⁻¹
    0<p0 ∧ p0<1 ∧ 0<K ∧ p0*(6*R)*K ≤ «ω»*(3*R) := by
  intro U K p0
  have hQ : 0 ≤ (4*β/α)*D^2 := by positivity
  have hU : 0 < U := by dsimp only [U]; linarith
  have hU3 : 3 ≤ U := by dsimp only [U]; linarith
  have hp0 : 0 < p0 := by dsimp only [p0]; positivity
  have hp1 : p0<1 := by
    dsimp only [p0]
    exact (inv_lt_one₀ (by positivity : 0 < 32*U)).2 (by linarith)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hf : (2*F/(α*δ))*R^2 ≤ 2 := by
    calc
      _ = (2*F*R^2)/(α*δ) := by ring
      _ ≤ 2 := (div_le_iff₀ (mul_pos hα hδ)).2 (by nlinarith [hforce])
  have hKb : K ≤ «ω»*16*U := by
    exact mul_le_mul_of_nonneg_left (by dsimp only [U]; linarith) (by positivity)
  refine ⟨hp0,hp1,hK,?_⟩
  calc
    _ ≤ p0*(6*R)*(«ω»*16*U) := mul_le_mul_of_nonneg_left hKb (by positivity)
    _ = _ := by dsimp only [p0]; field_simp [hU.ne']; ring

/-- Exact Haar-volume scaling of the source ball in dimension one; omega1 remains explicit. -/
private theorem volume_ball_three_one (x0 : EuclideanSpace ℝ (Fin 1)) {R : ℝ} (hR : 0<R) :
    (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (ball x0 (3*R)) =
      (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (ball 0 1) * (3*R) := by
  have h3 : 0<3*R := by positivity
  have H := congrArg ENNReal.toReal (Measure.addHaar_ball_of_pos
    (volume : Measure (EuclideanSpace ℝ (Fin 1))) x0 h3)
  rw [finrank_euclideanSpace_fin,pow_one,ENNReal.toReal_mul,ENNReal.toReal_ofReal h3.le] at H
  simp only [measureReal_def]
  exact H.trans (mul_comm _ _)

/-- The separate one-dimensional shifted log and power moments at GIVEN weak PDE data, kernel1 and direct oscillation.
The exponent is uniform before centers and radii; no singular critical-potential exponent is used. -/
private theorem exists_uniform_log_moments_one_of_weak_data :
    ∃ D : ℝ, 0 < D ∧ ∀
    {w : EuclideanSpace ℝ (Fin 1) → ℝ}
    {a : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ}
    {A : EuclideanSpace ℝ (Fin 1) → Matrix (Fin 1) (Fin 1) ℝ}
    {C α β F δ : ℝ}
    (_hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (_hbound : ∀ x, ‖w x‖ ≤ C)
    (_hweak : ∀ k : Fin 1, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin 1) ℝ k))
    (_ha2 : ∀ k : Fin 1, ∀ S : Set (EuclideanSpace ℝ (Fin 1)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict S))
    (_hAm : ∀ i j : Fin 1, AEStronglyMeasurable (fun x => A x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    {S : Set (EuclideanSpace ℝ (Fin 1))} (_hSm : MeasurableSet S)
    (_hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (S)), 0 ≤ w x)
    (_hα : 0 < α) (_hβ : 0 < β) (_hF : 0 ≤ F)
    (_hcoeff : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (S)),
      (A x - α • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef ∧
      (β • (1 : Matrix (Fin 1) (Fin 1) ℝ) - A x).PosSemidef)
    (_hsub : ∀ (η : EuclideanSpace ℝ (Fin 1) → ℝ)
        (dη : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ),
      LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin 1))) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) → HasCompactSupport η →
      Function.support η ⊆ S → (∀ x, 0 ≤ η x) →
      (∀ k : Fin 1, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin 1) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ S ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1)))) →
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin 1)))) ≤
        ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (_hδ : 0 < δ),
    ∃ (H : EuclideanSpace ℝ (Fin 1) → ℝ) (dH : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ),
      LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin 1))) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖H x‖ ≤ B) ∧
      (∀ k : Fin 1, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin 1) ℝ k) ∧
        ∀ K : Set (EuclideanSpace ℝ (Fin 1)), IsCompact K →
          MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict K)) ∧
      (H =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict S)]
        (fun x => Real.log (δ + max (w x) 0))) ∧
      (∀ k : Fin 1, (dH k) =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict S)]
        (fun x => (δ + max (w x) 0)⁻¹ * a k x)) ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin 1)) (R : ℝ), 0 < R → Metric.closedBall x0 (4*R) ⊆ S →
      F * R^2 ≤ α * δ →
      let p0 := (32 * (3 + (4*β/α)*D^2))⁻¹
      let s := fun x => δ + max (w x) 0
      0 < p0 ∧ p0 < 1 ∧
      Integrable (fun x => Real.exp (p0 * |H x - ⨍ y in ball x0 (3*R), H y|))
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3*R))) ∧
      (∫ x in ball x0 (3*R), Real.exp (p0 * |H x - ⨍ y in ball x0 (3*R), H y|)) ≤
        Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (ball 0 1) * (3*R) ∧
      Integrable (fun x => s x ^ p0)
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3*R))) ∧
      Integrable (fun x => s x ^ (-p0))
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3*R))) ∧
      (∫ x in ball x0 (3*R), s x ^ p0) * (∫ x in ball x0 (3*R), s x ^ (-p0)) ≤
        (Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (ball 0 1) * (3*R))^2 := by
  obtain ⟨D,hD,hM⟩ := exists_uniform_log_morrey_of_weak_data (n := 1) (by decide)
  refine ⟨D,hD,?_⟩
  intro w a A C α β F δ hw hbound hweak ha2 hAm S hSm hnonneg hα hβ hF hcoeff hsub hδ
  obtain ⟨H,dH,hl,⟨BH,hBH0,hBH⟩,hd,hHe,hde,hmor⟩ :=
    hM hw hbound hweak ha2 hAm hSm hnonneg hα hβ hF hcoeff hsub hδ
  refine ⟨H,dH,hl,⟨BH,hBH0,hBH⟩,hd,hHe,hde,fun x0 R hR hBS hforce => ?_⟩
  intro p0 s
  let «ω» := (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (ball 0 1)
  let K := «ω»*16*(1+(4*β/α)*D^2+(2*F/(α*δ))*R^2)
  have hω : 0 < «ω» := ENNReal.toReal_pos (Metric.measure_ball_pos
    (volume : Measure (EuclideanSpace ℝ (Fin 1))) 0 one_pos).ne' measure_ball_lt_top.ne
  obtain ⟨hp0,hp1,hK,hpK⟩ := uniform_one_dimensional_exponent (D := D) hω hα hβ.le hF hδ hR hforce
  have hdiam : ∀ y ∈ ball x0 (3*R), ∀ z ∈ ball x0 (3*R), dist y z ≤ 6*R := by
    intro y hy z hz
    have hy' := Metric.mem_ball.mp hy
    have hz' := Metric.mem_ball.mp hz
    have hdist := dist_triangle y x0 z
    rw [dist_comm x0 z] at hdist
    linarith
  have hmass : (∫⁻ x in ball x0 (3*R), ENNReal.ofReal (Real.sqrt (∑ i : Fin 1, (dH i x)^2))) ≤
      ENNReal.ofReal K := by
    have hm := hmor x0 R hR hBS x0 (3*R) (by positivity)
    simpa only [Set.inter_self, Nat.cast_one, pow_one, mul_one, sub_self, Real.rpow_zero] using hm
  have hpK' : p0*(6*R)*K ≤ (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (ball x0 (3*R)) := by
    rw [volume_ball_three_one x0 hR]
    exact hpK
  have hJ := integrable_exp_abs_sub_average_one_of_density_mass Metric.isOpen_ball
    (convex_ball x0 (3*R)) ⟨x0, Metric.mem_ball_self (by positivity)⟩ (by positivity : 0 < 6*R)
    hK hp0.le hdiam hl hBH (fun i => (hd i).1) (fun i => (hd i).2) hmass hpK'
  have hA : (∫ x in ball x0 (3*R), Real.exp (p0 * |H x - ⨍ y in ball x0 (3*R), H y|)) ≤
      Real.exp 1 * «ω» * (3*R) := by
    simpa only [volume_ball_three_one x0 hR, mul_assoc] using hJ.2.2
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3*R))
  have hB3S : ball x0 (3*R) ⊆ S :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).trans hBS
  have hHe3 : H =ᵐ[μ] (fun x => Real.log (s x)) := ae_restrict_of_ae_restrict_of_subset hB3S hHe
  have hslog : AEStronglyMeasurable (fun x => Real.log (s x)) μ :=
    (show AEStronglyMeasurable H μ from hl.aestronglyMeasurable.restrict).congr hHe3
  have he : (fun x => Real.exp (p0 * |H x - ⨍ y in ball x0 (3*R), H y|)) =ᵐ[μ]
      (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in ball x0 (3*R), H y|)) := by
    filter_upwards [hHe3] with x hx
    rw [hx]
  have his : Integrable (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in ball x0 (3*R), H y|)) μ := hJ.2.1.congr he
  have hAs : (∫ x, Real.exp (p0 * |Real.log (s x) - ⨍ y in ball x0 (3*R), H y|) ∂μ) ≤
      Real.exp 1 * «ω» * (3*R) := by
    rw [← integral_congr_ae he]
    exact hA
  obtain ⟨hp,hn,hprod⟩ := FunctionalInequalities.Probability.integral_rpow_mul_integral_rpow_neg_le_of_log_exp
    hp0.le (ae_of_all μ fun x => show 0 < s x from by dsimp only [s]; linarith [le_max_right (w x) 0])
    hslog his hAs
  exact ⟨hp0,hp1,hJ.2.1,hA,hp,hn,hprod⟩
end MomentsOne

section ProductHigh
open MeasureTheory Matrix Set Metric FunctionalInequalities.Analysis
open scoped ContDiff ENNReal
/-- Uniform shifted Harnack product at the given bounded weak PDE data, n>2.
All-p critical range; the constant precedes every ball, function, matrix, forcing and shift.
Input for Gilbarg–Trudinger (2001), Theorem 8.18; not the full unbounded/lower-order theorem. -/
private theorem shifted_harnack_product_of_weak_data_high {n : ℕ} (h3 : 2 < n)
    {α β p : ℝ} (hα : 0 < α) (hβ : 0 < β) (hp : 0 < p)
    (hpcrit : p < (n:ℝ)/((n:ℝ)-2)) :
    ∃ Ch : ℝ, 0 < Ch ∧ ∀
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {C F δ : ℝ}
    (_hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hbound : ∀ x, ‖w x‖ ≤ C)
    (_hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (_ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (_hAm : ∀ i j : Fin n, AEStronglyMeasurable (fun x => A x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {S : Set (EuclideanSpace ℝ (Fin n))} (_hSm : MeasurableSet S)
    (_hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)), 0 ≤ w x)
    (_hF : 0 ≤ F)
    (_hcoeff : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)),
      (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (_hsub : ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ)
        (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) → HasCompactSupport η →
      Function.support η ⊆ S → (∀ x, 0 ≤ η x) →
      (∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ S ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hδ : 0 < δ),
    ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → closedBall x0 (4*R) ⊆ S →
      F*R^2 ≤ α*δ →
      let s := fun x => δ + max (w x) 0
      ((ENNReal.ofReal R)^(-(n:ℝ)/p) *
        eLpNorm s (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (2*R)))) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) ≤
        ENNReal.ofReal Ch := by
  classical
  obtain ⟨D, -, hJ⟩ := exists_uniform_log_moments_of_weak_data (show 2 ≤ n by omega)
  let p0 : ℝ := (2 * ((n:ℝ)-1) * Real.exp 1)⁻¹ * (n:ℝ) /
    ((32:ℝ)^n * (3 + (4*β/α)*(n:ℝ)*D^2))
  have hn1 : 0 < (n:ℝ)-1 := by
    have hnR : (2:ℝ) < n := by exact_mod_cast h3
    linarith
  have hn0 : 0 < (n:ℝ) := by linarith
  have hp0 : 0 < p0 := by dsimp only [p0]; positivity
  obtain ⟨Cinv,hCinv,hinverse⟩ := inverse_essential_bound_of_cutoff_power_energy h3 hα hβ.le hp0
  obtain ⟨Cpos,hCpos,hpositive⟩ := positive_norm_bound_of_cutoff_power_energy h3 hα hβ.le hp0 hp hpcrit
  let c2 : ℝ := 2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) *
    (n:ℝ)/((n:ℝ)-1)) * (1 + 4*((n:ℝ)-1)^2))
  have hvol : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne'
      measure_ball_lt_top.ne
  have hc2 : 0 < c2 := by dsimp only [c2]; positivity
  let Cweak : ℝ := Cinv * (c2*(6:ℝ)^(n:ℝ))^(2/p0)
  have hCweak : 0 < Cweak := mul_pos hCinv (Real.rpow_pos_of_pos (mul_pos hc2 (Real.rpow_pos_of_pos (by norm_num) _)) _)
  refine ⟨Cpos*Cweak,mul_pos hCpos hCweak,?_⟩
  intro w a A C F δ hw hbound hweak ha2 hAm S hSm hnonneg hF hcoeff hsub hδ x0 R hR hBS hforce s
  have hsδ : ∀ x, δ ≤ s x := fun x => by dsimp only [s]; linarith [le_max_right (w x) 0]
  have hs : ∀ x, 0 < s x := fun x => hδ.trans_le (hsδ x)
  obtain ⟨hlogm,Clog,-,hlogb⟩ := shifted_log_measurable_bounded hw hbound hδ
  have hdata (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ 1 χ)
      (hχc : HasCompactSupport χ) (hχB : tsupport χ ⊆ closedBall x0 (4*R))
      (r : ℝ) (hr : r < 1/2) :=
    cutoff_power_data_of_weak_supersolution_on_set hw hbound hweak ha2 hAm hχ hχc
      (hχB.trans hBS) hnonneg hα hβ hF hcoeff hsub hδ hr
  have hinv := hinverse x0 R hR s a F δ hF hδ hforce hsδ hlogm ⟨Clog,hlogb⟩
    (fun χ hχ hχc hχB r hr => by
      obtain ⟨hl,hc,hb,hd,he⟩ := hdata χ hχ hχc hχB r (by linarith)
      exact ⟨hl,hc,hb,fun k => ⟨(hd k).1,(hd k).2.1,(hd k).2.2.2⟩,he.2.2.2⟩)
  have hμ23 : (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall x0 (2*R)) ≤
      (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R)) :=
    Measure.restrict_mono (closedBall_subset_ball (by linarith)) le_rfl
  have hinv3 : eLpNorm (fun x => s x ^ (-1:ℝ)) ∞
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) ≤
      ENNReal.ofReal Cinv * ((ENNReal.ofReal R)^(-(n:ℝ)/p0) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) (ENNReal.ofReal p0)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R)))) := by
    exact hinv.trans (by gcongr)
  obtain ⟨H,dH,-,-,-,-,-,hball⟩ :=
    hJ hw hbound hweak ha2 hAm hSm hnonneg hα hβ hF hcoeff hsub hδ
  obtain ⟨-, -, -, hpos,hneg,hprod⟩ := hball x0 R hR hBS hforce
  have hbridge : ((ENNReal.ofReal R)^(-(n:ℝ)/p0) *
      eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R)))) *
      eLpNorm (fun x => s x ^ (-1:ℝ)) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) ≤
      ENNReal.ofReal Cweak :=
    mul_eLpNorm_inv_top_le_of_moment_product _ _ _ le_rfl s hs hp0 hR hCinv.le hc2.le (by norm_num) hpos hneg hprod hinv3
  have hboost := hpositive x0 R hR s a F δ hF hδ hforce hsδ hlogm ⟨Clog,hlogb⟩
    (fun χ hχ hχc hχB r _hr hr => by
      obtain ⟨hl,hc,hb,hd,he⟩ := hdata χ hχ hχc hχB r hr
      exact ⟨hl,hc,hb,fun k => ⟨(hd k).1,(hd k).2.1,(hd k).2.2.2⟩,he.2.2.2⟩)
  calc
    _ ≤ (ENNReal.ofReal Cpos * ((ENNReal.ofReal R)^(-(n:ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R))))) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) := by gcongr
    _ = ENNReal.ofReal Cpos * (((ENNReal.ofReal R)^(-(n:ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (3*R)))) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R))) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal Cpos * ENNReal.ofReal Cweak := by gcongr
    _ = ENNReal.ofReal (Cpos*Cweak) := (ENNReal.ofReal_mul hCpos.le).symm
end ProductHigh

section ProductTwo
open MeasureTheory Matrix Set Metric FunctionalInequalities.Analysis
open scoped ContDiff ENNReal
/-- Uniform shifted Harnack product at the given bounded weak PDE data, 2>2.
Every finite p>0; the constant precedes every ball, function, matrix, forcing and shift.
Input for Gilbarg–Trudinger (2001), Theorem 8.18; not the full unbounded/lower-order theorem. -/
private theorem shifted_harnack_product_of_weak_data_two
    {α β p : ℝ} (hα : 0 < α) (hβ : 0 < β) (hp : 0 < p)
    :
    ∃ Ch : ℝ, 0 < Ch ∧ ∀
    {w : EuclideanSpace ℝ (Fin 2) → ℝ}
    {a : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ}
    {A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
    {C F δ : ℝ}
    (_hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (_hbound : ∀ x, ‖w x‖ ≤ C)
    (_hweak : ∀ k : Fin 2, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin 2) ℝ k))
    (_ha2 : ∀ k : Fin 2, ∀ S : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S))
    (_hAm : ∀ i j : Fin 2, AEStronglyMeasurable (fun x => A x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    {S : Set (EuclideanSpace ℝ (Fin 2))} (_hSm : MeasurableSet S)
    (_hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (S)), 0 ≤ w x)
    (_hF : 0 ≤ F)
    (_hcoeff : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (S)),
      (A x - α • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef ∧
      (β • (1 : Matrix (Fin 2) (Fin 2) ℝ) - A x).PosSemidef)
    (_hsub : ∀ (η : EuclideanSpace ℝ (Fin 2) → ℝ)
        (dη : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ),
      LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin 2))) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) → HasCompactSupport η →
      Function.support η ⊆ S → (∀ x, 0 ≤ η x) →
      (∀ k : Fin 2, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ S ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) →
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
        ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (_hδ : 0 < δ),
    ∀ (x0 : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R → closedBall x0 (4*R) ⊆ S →
      F*R^2 ≤ α*δ →
      let s := fun x => δ + max (w x) 0
      ((ENNReal.ofReal R)^(-(2:ℝ)/p) *
        eLpNorm s (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (2*R)))) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 R)) ≤
        ENNReal.ofReal Ch := by
  classical
  obtain ⟨D, -, hJ⟩ := exists_uniform_log_moments_of_weak_data (n := 2) (by omega)
  let p0 : ℝ := (2 * ((2:ℝ)-1) * Real.exp 1)⁻¹ * (2:ℝ) /
    ((32:ℝ)^2 * (3 + (4*β/α)*(2:ℝ)*D^2))
  have hn1 : 0 < (2:ℝ)-1 := by norm_num
  have hn0 : 0 < (2:ℝ) := by norm_num
  have hp0 : 0 < p0 := by dsimp only [p0]; positivity
  obtain ⟨Cinv,hCinv,hinverse⟩ := inverse_essential_bound_two_of_cutoff_power_energy hα hβ.le hp0
  obtain ⟨Cpos,hCpos,hpositive⟩ := positive_norm_bound_two_of_cutoff_power_energy hα hβ.le hp0 hp
  let c2 : ℝ := 2 * (((volume : Measure (EuclideanSpace ℝ (Fin 2))).real (ball 0 1) *
    (2:ℝ)/((2:ℝ)-1)) * (1 + 4*((2:ℝ)-1)^2))
  have hvol : 0 < (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin 2))) 0 one_pos).ne'
      measure_ball_lt_top.ne
  have hc2 : 0 < c2 := by dsimp only [c2]; positivity
  let Cweak : ℝ := Cinv * (c2*(6:ℝ)^(2:ℝ))^(2/p0)
  have hCweak : 0 < Cweak := mul_pos hCinv (Real.rpow_pos_of_pos (mul_pos hc2 (Real.rpow_pos_of_pos (by norm_num) _)) _)
  refine ⟨Cpos*Cweak,mul_pos hCpos hCweak,?_⟩
  intro w a A C F δ hw hbound hweak ha2 hAm S hSm hnonneg hF hcoeff hsub hδ x0 R hR hBS hforce s
  have hsδ : ∀ x, δ ≤ s x := fun x => by dsimp only [s]; linarith [le_max_right (w x) 0]
  have hs : ∀ x, 0 < s x := fun x => hδ.trans_le (hsδ x)
  obtain ⟨hlogm,Clog,-,hlogb⟩ := shifted_log_measurable_bounded hw hbound hδ
  have hdata (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (hχ : ContDiff ℝ 1 χ)
      (hχc : HasCompactSupport χ) (hχB : tsupport χ ⊆ closedBall x0 (4*R))
      (r : ℝ) (hr : r < 1/2) :=
    cutoff_power_data_of_weak_supersolution_on_set hw hbound hweak ha2 hAm hχ hχc
      (hχB.trans hBS) hnonneg hα hβ hF hcoeff hsub hδ hr
  have hinv := hinverse x0 R hR s a F δ hF hδ hforce hsδ hlogm ⟨Clog,hlogb⟩
    (fun χ hχ hχc hχB r hr => by
      obtain ⟨hl,hc,hb,hd,he⟩ := hdata χ hχ hχc hχB r (by linarith)
      exact ⟨hl,hc,hb,hd,he.2.2.2⟩)
  have hμ23 : (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (closedBall x0 (2*R)) ≤
      (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (3*R)) :=
    Measure.restrict_mono (closedBall_subset_ball (by linarith)) le_rfl
  have hinv3 : eLpNorm (fun x => s x ^ (-1:ℝ)) ∞
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 R)) ≤
      ENNReal.ofReal Cinv * ((ENNReal.ofReal R)^(-(2:ℝ)/p0) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) (ENNReal.ofReal p0)
          ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (3*R)))) := by
    exact hinv.trans (by gcongr)
  obtain ⟨H,dH,-,-,-,-,-,hball⟩ :=
    hJ hw hbound hweak ha2 hAm hSm hnonneg hα hβ hF hcoeff hsub hδ
  obtain ⟨-, -, -, hpos,hneg,hprod⟩ := hball x0 R hR hBS hforce
  have hbridge : ((ENNReal.ofReal R)^(-(2:ℝ)/p0) *
      eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (3*R)))) *
      eLpNorm (fun x => s x ^ (-1:ℝ)) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 R)) ≤
      ENNReal.ofReal Cweak :=
    mul_eLpNorm_inv_top_le_of_moment_product _ _ _ le_rfl s hs hp0 hR hCinv.le hc2.le (by norm_num) hpos hneg hprod hinv3
  have hboost := hpositive x0 R hR s a F δ hF hδ hforce hsδ hlogm ⟨Clog,hlogb⟩
    (fun χ hχ hχc hχB r _hr hr => by
      obtain ⟨hl,hc,hb,hd,he⟩ := hdata χ hχ hχc hχB r hr
      exact ⟨hl,hc,hb,hd,he.2.2.2⟩)
  calc
    _ ≤ (ENNReal.ofReal Cpos * ((ENNReal.ofReal R)^(-(2:ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (3*R))))) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 R)) := by gcongr
    _ = ENNReal.ofReal Cpos * (((ENNReal.ofReal R)^(-(2:ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 (3*R)))) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (ball x0 R))) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal Cpos * ENNReal.ofReal Cweak := by gcongr
    _ = ENNReal.ofReal (Cpos*Cweak) := (ENNReal.ofReal_mul hCpos.le).symm
end ProductTwo

section ProductOne
open MeasureTheory Matrix Set Metric FunctionalInequalities.Analysis
open scoped ContDiff ENNReal
/-- Uniform shifted Harnack product at the given bounded weak PDE data, n = 1.
Every finite p>0; the constant precedes every ball, function, matrix, forcing and shift.
Input for Gilbarg–Trudinger (2001), Theorem 8.18; not the full unbounded/lower-order theorem. -/
private theorem shifted_harnack_product_of_weak_data_one
    {α β p : ℝ} (hα : 0 < α) (hβ : 0 < β) (hp : 0 < p)
    :
    ∃ Ch : ℝ, 0 < Ch ∧ ∀
    {w : EuclideanSpace ℝ (Fin 1) → ℝ}
    {a : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ}
    {A : EuclideanSpace ℝ (Fin 1) → Matrix (Fin 1) (Fin 1) ℝ}
    {C F δ : ℝ}
    (_hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (_hbound : ∀ x, ‖w x‖ ≤ C)
    (_hweak : ∀ k : Fin 1, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin 1) ℝ k))
    (_ha2 : ∀ k : Fin 1, ∀ S : Set (EuclideanSpace ℝ (Fin 1)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict S))
    (_hAm : ∀ i j : Fin 1, AEStronglyMeasurable (fun x => A x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    {S : Set (EuclideanSpace ℝ (Fin 1))} (_hSm : MeasurableSet S)
    (_hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (S)), 0 ≤ w x)
    (_hF : 0 ≤ F)
    (_hcoeff : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (S)),
      (A x - α • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef ∧
      (β • (1 : Matrix (Fin 1) (Fin 1) ℝ) - A x).PosSemidef)
    (_hsub : ∀ (η : EuclideanSpace ℝ (Fin 1) → ℝ)
        (dη : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ),
      LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin 1))) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) → HasCompactSupport η →
      Function.support η ⊆ S → (∀ x, 0 ≤ η x) →
      (∀ k : Fin 1, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin 1) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ S ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1)))) →
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin 1)))) ≤
        ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (_hδ : 0 < δ),
    ∀ (x0 : EuclideanSpace ℝ (Fin 1)) (R : ℝ), 0 < R → closedBall x0 (4*R) ⊆ S →
      F*R^2 ≤ α*δ →
      let s := fun x => δ + max (w x) 0
      ((ENNReal.ofReal R)^(-(1:ℝ)/p) *
        eLpNorm s (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (2*R)))) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 R)) ≤
        ENNReal.ofReal Ch := by
  classical
  obtain ⟨D, -, hJ⟩ := exists_uniform_log_moments_one_of_weak_data
  let p0 : ℝ := (32 * (3 + (4*β/α)*D^2))⁻¹
  have hp0 : 0 < p0 := by dsimp only [p0]; positivity
  have hp01 : p0 < 1 := by
    have hQ : 0 ≤ (4*β/α)*D^2 := by positivity
    dsimp only [p0]
    exact (inv_lt_one₀ (by positivity)).2 (by linarith)
  obtain ⟨Cinv,hCinv,hinverse⟩ := inverse_essential_bound_one_of_cutoff_power_energy hα hβ.le hp0
  obtain ⟨Cpos,hCpos,hpositive⟩ := positive_essential_bound_one_of_cutoff_power_energy hα hβ.le hp0 hp01
  let c2 : ℝ := Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (ball 0 1)
  have hω : 0 < (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin 1))) 0 one_pos).ne'
      measure_ball_lt_top.ne
  have hc2 : 0 < c2 := by dsimp only [c2]; positivity
  let Cweak : ℝ := Cinv * (c2*(3:ℝ)^(1:ℝ))^(2/p0)
  have hCweak : 0 < Cweak := mul_pos hCinv (Real.rpow_pos_of_pos (mul_pos hc2 (by positivity)) _)
  let Cstrong : ℝ := Cpos*Cweak
  have hCstrong : 0 < Cstrong := mul_pos hCpos hCweak
  refine ⟨Cstrong * ((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (ball 0 1) * 2)^(1/p),
    mul_pos hCstrong (Real.rpow_pos_of_pos (by positivity) _),?_⟩
  intro w a A C F δ hw hbound hweak ha2 hAm S hSm hnonneg hF hcoeff hsub hδ x0 R hR hBS hforce s
  have hsδ : ∀ x, δ ≤ s x := fun x => by dsimp only [s]; linarith [le_max_right (w x) 0]
  have hs : ∀ x, 0 < s x := fun x => hδ.trans_le (hsδ x)
  obtain ⟨hlogm,Clog,-,hlogb⟩ := shifted_log_measurable_bounded hw hbound hδ
  have hdata (χ : EuclideanSpace ℝ (Fin 1) → ℝ) (hχ : ContDiff ℝ 1 χ)
      (hχc : HasCompactSupport χ) (hχB : tsupport χ ⊆ closedBall x0 (4*R))
      (r : ℝ) (hr : r < 1/2) :=
    cutoff_power_data_of_weak_supersolution_on_set hw hbound hweak ha2 hAm hχ hχc
      (hχB.trans hBS) hnonneg hα hβ hF hcoeff hsub hδ hr
  have hinv := hinverse x0 R hR s a F δ hF hδ hforce hsδ hlogm ⟨Clog,hlogb⟩
    (fun χ hχ hχc hχB r hr => by
      obtain ⟨hl,hc,hb,hd,he⟩ := hdata χ hχ hχc hχB r (by linarith)
      exact ⟨hl,hc,hb,hd,he.2.2.2⟩)
  have hμ23 : (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (closedBall x0 (2*R)) ≤
      (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3*R)) :=
    Measure.restrict_mono (closedBall_subset_ball (by linarith)) le_rfl
  have hinv3 : eLpNorm (fun x => s x ^ (-1:ℝ)) ∞
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 R)) ≤
      ENNReal.ofReal Cinv * ((ENNReal.ofReal R)^(-(1:ℝ)/p0) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) (ENNReal.ofReal p0)
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3*R)))) := by
    exact hinv.trans (by gcongr)
  obtain ⟨H,dH,-,-,-,-,-,hball⟩ :=
    hJ hw hbound hweak ha2 hAm hSm hnonneg hα hβ hF hcoeff hsub hδ
  obtain ⟨-, -, -, -, hpos,hneg,hprod0⟩ := hball x0 R hR hBS hforce
  have hprod : (∫ x in ball x0 (3*R), s x ^ p0) * (∫ x in ball x0 (3*R), s x ^ (-p0)) ≤
      (c2*(3*R)^(1:ℝ))^2 := by simpa only [Real.rpow_one,c2] using hprod0
  have hbridge : ((ENNReal.ofReal R)^(-(1:ℝ)/p0) *
      eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3*R)))) *
      eLpNorm (fun x => s x ^ (-1:ℝ)) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 R)) ≤
      ENNReal.ofReal Cweak :=
    mul_eLpNorm_inv_top_le_of_moment_product _ _ _ le_rfl s hs hp0 hR hCinv.le hc2.le (by norm_num) hpos hneg hprod hinv3
  have hboost := hpositive x0 R hR s a F δ hF hδ hforce hsδ hlogm ⟨Clog,hlogb⟩
    (fun χ hχ hχc hχB r _hr hr => by
      obtain ⟨hl,hc,hb,hd,he⟩ := hdata χ hχ hχc hχB r hr
      exact ⟨hl,hc,hb,hd,he.2.2.2⟩)
  have hstrong : eLpNorm s ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (2*R))) *
      eLpNorm (fun x => s x ^ (-1:ℝ)) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 R)) ≤
      ENNReal.ofReal Cstrong := by
    calc
      _ ≤ (ENNReal.ofReal Cpos * ((ENNReal.ofReal R)^(-(1:ℝ)/p0) *
          eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3*R))))) *
          eLpNorm (fun x => s x ^ (-1:ℝ)) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 R)) := by gcongr
      _ = ENNReal.ofReal Cpos * (((ENNReal.ofReal R)^(-(1:ℝ)/p0) *
          eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 (3*R)))) *
          eLpNorm (fun x => s x ^ (-1:ℝ)) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (ball x0 R))) := mul_assoc _ _ _
      _ ≤ ENNReal.ofReal Cpos * ENNReal.ofReal Cweak := by gcongr
      _ = ENNReal.ofReal Cstrong := (ENNReal.ofReal_mul hCpos.le).symm
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hsm : AEStronglyMeasurable s ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2*R))) := by
    have Hm := Real.continuous_exp.comp_aestronglyMeasurable hlogm
    have heq : (fun x => Real.exp (Real.log (s x))) = s := funext fun x => Real.exp_log (hs x)
    rw [heq] at Hm
    exact Hm.restrict
  have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := ENNReal.ofReal p) (q := ∞) le_top hsm
  simp only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_top, div_zero, sub_zero] at hle
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2*R)) Set.univ =
      ENNReal.ofReal R * ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 2) := by
    rw [Measure.restrict_apply_univ, Measure.addHaar_ball_of_pos _ _ (by positivity : (0 : ℝ) < 2*R),
      finrank_euclideanSpace_fin, pow_one, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul hω.le, measureReal_def, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
    ring
  rw [hvol, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1/p)] at hle
  have hpnorm : (ENNReal.ofReal R)^(-(1 : ℝ)/p) *
      eLpNorm s (ENNReal.ofReal p) ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2*R))) ≤
      eLpNorm s ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2*R))) *
        ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 2) ^ (1/p)) := by
    calc
      _ ≤ (ENNReal.ofReal R)^(-(1 : ℝ)/p) *
          (eLpNorm s ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2*R))) *
            ((ENNReal.ofReal R)^(1/p) *
              (ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 2))^(1/p))) := by
        gcongr
      _ = eLpNorm s ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2*R))) *
            (ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 2))^(1/p) *
            ((ENNReal.ofReal R)^(-(1 : ℝ)/p) * (ENNReal.ofReal R)^(1/p)) := by ring
      _ = _ := by
        rw [← ENNReal.rpow_add _ _ hR0 ENNReal.ofReal_ne_top, show -(1 : ℝ)/p + 1/p = 0 by ring, ENNReal.rpow_zero,
          mul_one, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  calc
    _ ≤ (eLpNorm s ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2*R))) *
          ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 2) ^ (1/p))) *
          eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
            ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 R)) := by
      gcongr
    _ = (eLpNorm s ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2*R))) *
          eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
            ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 R))) *
          ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 2) ^ (1/p)) := by ring
    _ ≤ ENNReal.ofReal Cstrong *
          ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 2) ^ (1/p)) := by
      gcongr
    _ = ENNReal.ofReal (Cstrong * ((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 2) ^ (1/p)) :=
      (ENNReal.ofReal_mul hCstrong.le).symm

end ProductOne

section Product
open MeasureTheory Matrix Set Metric FunctionalInequalities.Analysis
open scoped ContDiff ENNReal
/-- Uniform shifted norm-times-inverse product at given weak data, all n>0. -/
private theorem shifted_harnack_product_of_weak_data {n : ℕ} (hn : 0 < n)
    {α β p : ℝ} (hα : 0 < α) (hβ : 0 < β) (hp : 0 < p)
    (hpcrit : n ≤ 2 ∨ p < (n:ℝ)/((n:ℝ)-2)) :
    ∃ Ch : ℝ, 0 < Ch ∧ ∀
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {C F δ : ℝ}
    (_hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hbound : ∀ x, ‖w x‖ ≤ C)
    (_hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (_ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (_hAm : ∀ i j : Fin n, AEStronglyMeasurable (fun x => A x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {S : Set (EuclideanSpace ℝ (Fin n))} (_hSm : MeasurableSet S)
    (_hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)), 0 ≤ w x)
    (_hF : 0 ≤ F)
    (_hcoeff : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)),
      (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (_hsub : ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ)
        (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) → HasCompactSupport η →
      Function.support η ⊆ S → (∀ x, 0 ≤ η x) →
      (∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ S ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hδ : 0 < δ),
    ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → closedBall x0 (4*R) ⊆ S →
      F*R^2 ≤ α*δ →
      let s := fun x => δ + max (w x) 0
      ((ENNReal.ofReal R)^(-(n:ℝ)/p) *
        eLpNorm s (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (2*R)))) *
        eLpNorm (fun x => s x ^ (-1:ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) ≤
        ENNReal.ofReal Ch := by
  rcases lt_or_ge 2 n with h3 | hsmall
  · exact shifted_harnack_product_of_weak_data_high h3 hα hβ hp (hpcrit.resolve_left (by omega))
  · have h12 : n = 1 ∨ n = 2 := by omega
    rcases h12 with rfl | rfl
    · simpa only [Nat.cast_one] using shifted_harnack_product_of_weak_data_one hα hβ hp
    · exact shifted_harnack_product_of_weak_data_two hα hβ hp
end Product

section Harnack
open MeasureTheory Matrix Set FunctionalInequalities.Analysis
open scoped ENNReal
/-- **Weak Harnack inequality for given bounded weak supersolutions** (Gilbarg–Trudinger 2001, Theorem 8.18, bounded
symmetric pure-divergence case). For every `n > 0` and `0 < α ≤ β`-type ellipticity data there is `C(p)`, chosen before
every ball, coefficient matrix, function, derivative, bound and forcing, such that a globally bounded weak `H¹_loc`
function `w ≥ 0` a.e. on `B̄(x0,4R)`, with `α ≤ A ≤ β` a.e. there and `−F∫η ≤ ∫ aᵀ A ∇η` for every bounded nonnegative
compactly supported weak test in `B̄(x0,4R)`, satisfies
`R^{−n/p} ‖w‖_{L^p(B(x0,2R))} ≤ C(p) (essinf_{B(x0,R)} w + F R²/α)` for every `p > 0` with `n ≤ 2` or `p < n/(n−2)`.
Essential infimum only; no regular representative, unbounded solution or lower-order term. -/
theorem bounded_weak_harnack_of_given_data {n : ℕ} (hn : 0 < n)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ → ℝ, (∀ p : ℝ, 0 < p → (n ≤ 2 ∨ p < (n : ℝ) / ((n : ℝ)-2)) → 0 < C p) ∧
      ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      ∀ (A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
        (w : EuclideanSpace ℝ (Fin n) → ℝ)
        (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (F : ℝ),
      LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖w x‖ ≤ B) →
      (∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k)) →
      (∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) →
      (∀ i j : Fin n, AEStronglyMeasurable (fun x => A x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4*R))),
        0 ≤ w x) →
      (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4*R))),
        (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
        (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef) →
      0 ≤ F →
      (∀ (η : EuclideanSpace ℝ (Fin n) → ℝ)
          (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
        LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
        (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) → HasCompactSupport η →
        Function.support η ⊆ Metric.closedBall x0 (4*R) → (∀ x, 0 ≤ η x) →
        (∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ Metric.closedBall x0 (4*R) ∧
          MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
        -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
          ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      ∀ p : ℝ, 0 < p → (n ≤ 2 ∨ p < (n : ℝ) / ((n : ℝ)-2)) →
        (ENNReal.ofReal R) ^ (-(n : ℝ)/p) *
          eLpNorm w (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R))) ≤
          ENNReal.ofReal (C p) *
            (essInf (fun x => ENNReal.ofReal (w x))
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) +
             ENNReal.ofReal (F * R^2 / α)) := by
  classical
  let C : ℝ → ℝ := fun p => if h : 0 < p ∧ (n ≤ 2 ∨ p < (n:ℝ)/((n:ℝ)-2)) then
    Classical.choose (shifted_harnack_product_of_weak_data hn hα hβ h.1 h.2) else 1
  have hCp (p : ℝ) (hp : 0 < p) (hcl : n ≤ 2 ∨ p < (n:ℝ)/((n:ℝ)-2)) :
      C p = Classical.choose (shifted_harnack_product_of_weak_data hn hα hβ hp hcl) :=
    dif_pos ⟨hp,hcl⟩
  refine ⟨C,fun p hp hcl => ?_,?_⟩
  · rw [hCp p hp hcl]
    exact (Classical.choose_spec (shifted_harnack_product_of_weak_data hn hα hβ hp hcl)).1
  intro x0 R hR A w a F hw hB hweak ha2 hAm hnonneg hcoeff hF hsub p hp hcl
  obtain ⟨B,-,hbound⟩ := hB
  have h1 : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)), 0 ≤ w x :=
    ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) hnonneg
  have h2 : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R))), 0 ≤ w x :=
    ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) hnonneg
  have : NeZero ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) :=
    ⟨by rw [Ne, Measure.restrict_eq_zero]; exact (Metric.measure_ball_pos _ x0 hR).ne'⟩
  have hk : 0 ≤ F*R^2/α := by positivity
  refine unshifted_bound_of_shifted_inverse_norm_products
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R))
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R))) w h1 h2 hk
    ((ENNReal.ofReal R)^(-(n:ℝ)/p)) (ENNReal.ofReal (C p)) ENNReal.ofReal_ne_top (ENNReal.ofReal p)
    (fun δ hkδ => ?_) (fun δ hkδ => ?_)
  · exact (shifted_log_measurable_bounded hw hbound (hk.trans_lt hkδ)).1.restrict
  · have hforce : F*R^2 ≤ α*δ := by
      have h := (div_lt_iff₀ hα).1 hkδ
      rw [mul_comm α δ]
      exact h.le
    rw [hCp p hp hcl]
    exact (Classical.choose_spec (shifted_harnack_product_of_weak_data hn hα hβ hp hcl)).2
      hw hbound hweak ha2 hAm measurableSet_closedBall hnonneg hF hcoeff hsub (hk.trans_lt hkδ)
      x0 R hR Subset.rfl hforce
end Harnack

end FunctionalInequalities.Analysis
