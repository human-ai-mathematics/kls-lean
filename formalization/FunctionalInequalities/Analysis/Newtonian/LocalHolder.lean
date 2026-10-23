import FunctionalInequalities.Analysis.Holder.Cutoff
import FunctionalInequalities.Analysis.Newtonian.Schauder
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Lemma 4.4 for locally Hölder sources (qualitative form)

The qualitative assertion of Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations
of Second Order*, Classics 2001 (ISBN 3-540-41160-7), pp. 51–53 and 57–59, in the source notation.
`newtonianPotential_localHolder`: for `n ≥ 2`, `0 < α < 1` and `f` integrable on `B₂ = B_{2R}(c)` and locally
`α`-Hölder there (uniformly `α`-Hölder on every compact subset, p. 52), the Newtonian potential `w` of `f`
in `B₂` is `C²` on the open ball `B_{5R/4}(c) ⊃ closedBall c R`, and its Hessian is bounded and
`α`-Hölder on `closedBall c R`, i.e. `w ∈ C^{2,α}(B̄_R)`. No global bound or global Hölder cap of `f` on
`B₂` is assumed.

Proof: a smooth cutoff `η` (`= 1` near `B̄_{3R/2}`, `0` off `B_{7R/4}`) splits `f = ηf + (1 - η)f`. The
quantitative estimate `newtonianPotential_schauder` applies to `g = ηf`, whose bound and Hölder cap are
derived from the hypothesis on `B̄_{7R/4}` (`exists_cutoff_holder_source`). The far part is the
convolution of `1_{B₂}(f - g)` with the compactly supported smooth kernel `Γ_{R/8} β`
(`exists_newtonianFarKernel`), which coincides with `Γ` at the relevant distances
`R/4 ≤ |x - y| ≤ 4R`, hence is `C^∞` (`HasCompactSupport.contDiff_convolution_left`).
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace FunctionalInequalities.Analysis

section Local

variable {n : ℕ} {c : EuclideanSpace ℝ (Fin n)} {R : ℝ}

/-- Cutoff source: from the compact-form local Hölder hypothesis on `B₂`, a smooth cutoff `η` (`1` on `B̄_{3R/2}`, `0` off
`B_{7R/4}`, values in `[0,1]`) such that `ηf` is bounded and uniformly `α`-Hölder on all of `B₂` (caps derived, depending on `f`). -/
theorem exists_cutoff_holder_source (hR : 0 < R) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hloc : ∀ K, IsCompact K → K ⊆ ball c (2 * R) → ∃ H : ℝ≥0, HolderOnWith H α f K) :
    ∃ η : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ η ∧ (∀ y ∈ closedBall c (3 * R / 2), η y = 1) ∧
      (∀ y, 0 ≤ η y ∧ η y ≤ 1) ∧ (∀ y, y ∉ ball c (7 * R / 4) → η y = 0) ∧
      ∃ M : ℝ, ∃ H : ℝ≥0, (∀ y ∈ ball c (2 * R), |η y * f y| ≤ M) ∧
        HolderOnWith H α (fun y => η y * f y) (ball c (2 * R)) := by
  let β : ContDiffBump c := ⟨3 * R / 2, 7 * R / 4, by positivity, by linarith⟩
  have hβ0 : ∀ y, y ∉ ball c (7 * R / 4) → β y = 0 := fun y hy =>
    Function.notMem_support.mp (by rw [β.support_eq]; exact hy)
  obtain ⟨Lη, hLη⟩ := ContDiff.lipschitzWith_of_hasCompactSupport β.hasCompactSupport (β.contDiff (n := ⊤)) (by simp)
  set K0 := closedBall c (7 * R / 4)
  have hK0 : K0 ⊆ ball c (2 * R) := closedBall_subset_ball (by linarith)
  obtain ⟨H0, hH0⟩ := hloc K0 (isCompact_closedBall c _) hK0
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall c (7 * R / 4)).exists_bound_of_continuousOn (hH0.continuousOn hα0)
  set M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hfM : ∀ y ∈ K0, |f y| ≤ M := fun y hy => by
    have := hM0 y hy; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hη0 : ∀ y, y ∉ K0 → β y = 0 := fun y hy => hβ0 y (fun h => hy (ball_subset_closedBall h))
  have hη1 : ∀ y, |β y| ≤ 1 := fun y => abs_le.mpr ⟨by linarith [β.nonneg (x := y)], β.le_one⟩
  have hηL : ∀ x y, |β x - β y| ≤ (Lη:ℝ) * dist x y := fun x y => by
    have := hLη.dist_le_mul x y; rwa [Real.dist_eq] at this
  have hfH : ∀ x ∈ K0, ∀ y ∈ K0, |f x - f y| ≤ (H0:ℝ) * dist x y ^ (α:ℝ) := fun x hx y hy => by
    have := hH0.dist_le hx hy; rwa [Real.dist_eq] at this
  have hdiam : ∀ x ∈ ball c (2 * R), ∀ y ∈ ball c (2 * R), dist x y ≤ 4 * R := fun x hx y hy => by
    rw [mem_ball] at hx hy; linarith [dist_triangle x c y, dist_comm y c]
  have hprod := abs_mul_sub_mul_le_of_cutoff (by exact_mod_cast hα1) Lη.coe_nonneg H0.coe_nonneg hM
    (by positivity : (0:ℝ) ≤ 4 * R) hηL hη1 hη0 hfH hfM hdiam
  refine ⟨β, β.contDiff, fun y hy => β.one_of_mem_closedBall hy, fun y => ⟨β.nonneg, β.le_one⟩, hβ0, M,
    Real.toNNReal ((H0:ℝ) + M * Lη * (4 * R) ^ (1 - (α:ℝ))),
    fun y hy => ?_, holderOnWith_of_dist_le (C := (H0:ℝ) + M * Lη * (4 * R) ^ (1 - (α:ℝ))) (by positivity)
      fun x hx y hy => ?_⟩
  · by_cases hyK : y ∈ K0
    · rw [abs_mul]; exact (mul_le_mul (hη1 y) (hfM y hyK) (abs_nonneg _) zero_le_one).trans (by linarith)
    · rw [hη0 y hyK, zero_mul, abs_zero]; exact hM
  · rw [Real.dist_eq]; exact hprod x hx y hy

/-- A compactly supported smooth kernel equal to `Γ` on `R/4 ≤ |z| ≤ 4R`: the scalar truncation `Γ_{R/8}` times a bump
`β` (`= 1` on `B̄_{4R}(0)`). -/
theorem exists_newtonianFarKernel (hn : 2 ≤ n) (hR : 0 < R) :
    ∃ Kc : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ Kc ∧ HasCompactSupport Kc ∧
      ∀ z, R / 4 ≤ ‖z‖ → ‖z‖ ≤ 4 * R → Kc z = newtonianKernel n z := by
  let β : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨4 * R, 5 * R, by positivity, by linarith⟩
  refine ⟨fun z => truncatedNewtonianKernel n (R / 8) z * β z,
    (contDiff_truncatedNewtonianKernel hn (by positivity)).mul β.contDiff, β.hasCompactSupport.mul_left, fun z h1 h2 => ?_⟩
  have hβ : β z = 1 := β.one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact h2)
  show truncatedNewtonianKernel n (R / 8) z * β z = newtonianKernel n z
  rw [hβ, mul_one, truncatedNewtonianKernel_eq_of_far (by positivity) z (by linarith)]

/-- Decomposition on `B_{5R/4}(c)`: if `g = f` on `B̄_{3R/2}`, `g` is measurable and bounded on `B₂` and `f` integrable on `B₂`, then
`w_f(x) = w_g(x) + (K_cut ⋆ 1_{B₂}(f − g))(x)` for the kernel of `exists_newtonianFarKernel`. -/
theorem newtonianPotential_ball_eq_add_convolution (hn : 2 ≤ n) {f g : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}
    (hfi : IntegrableOn f (ball c (2 * R)) volume) (hgm : AEMeasurable g (volume.restrict (ball c (2 * R))))
    (hgM : ∀ y ∈ ball c (2 * R), |g y| ≤ M) (hfg : ∀ y ∈ closedBall c (3 * R / 2), g y = f y)
    {Kc : EuclideanSpace ℝ (Fin n) → ℝ} (hKc : ContDiff ℝ ∞ Kc) (hKcs : HasCompactSupport Kc)
    (hKeq : ∀ z, R / 4 ≤ ‖z‖ → ‖z‖ ≤ 4 * R → Kc z = newtonianKernel n z)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball c (5 * R / 4)) :
    newtonianPotential n (ball c (2 * R)) f x =
      newtonianPotential n (ball c (2 * R)) g x +
        convolution Kc ((ball c (2 * R)).indicator fun y => f y - g y) (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  have hB : MeasurableSet (ball c (2 * R)) := measurableSet_ball
  have hgB : ∀ᵐ y ∂(volume.restrict (ball c (2 * R))), |g y| ≤ M := ae_restrict_of_forall_mem hB hgM
  have hΓg := integrableOn_newtonianKernel_sub_mul hn isBounded_ball hgm hgB x
  have hgi : IntegrableOn g (ball c (2 * R)) volume :=
    (integrableOn_const (C := M) measure_ball_lt_top.ne).mono' hgm.aestronglyMeasurable
      (hgB.mono fun y hy => by rw [Real.norm_eq_abs]; exact hy)
  have hxc : dist x c < 5 * R / 4 := hx
  have hpt : ∀ y ∈ ball c (2 * R), newtonianKernel n (x - y) * (f y - g y) = Kc (x - y) * (f y - g y) := by
    intro y hy
    by_cases hy3 : y ∈ closedBall c (3 * R / 2)
    · rw [hfg y hy3, sub_self, mul_zero, mul_zero]
    · have hyc : 3 * R / 2 < dist y c := by rw [mem_closedBall, not_le] at hy3; exact hy3
      have hyc2 : dist y c < 2 * R := hy
      have h1 : R / 4 ≤ ‖x - y‖ := by
        rw [← dist_eq_norm]; linarith [dist_triangle y x c, dist_comm x y]
      have h2 : ‖x - y‖ ≤ 4 * R := by
        rw [← dist_eq_norm]; linarith [dist_triangle x c y, dist_comm y c]
      rw [hKeq (x - y) h1 h2]
  obtain ⟨CK, hCK⟩ := hKc.continuous.bounded_above_of_compact_support hKcs
  have hKI : IntegrableOn (fun y => Kc (x - y) * (f y - g y)) (ball c (2 * R)) volume :=
    (hfi.sub hgi).bdd_mul (c := CK) (hKc.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y => hCK (x - y))
  have hΓI : IntegrableOn (fun y => newtonianKernel n (x - y) * (f y - g y)) (ball c (2 * R)) volume :=
    hKI.congr_fun (fun y hy => (hpt y hy).symm) hB
  have hsplit : newtonianPotential n (ball c (2 * R)) f x =
      newtonianPotential n (ball c (2 * R)) g x + ∫ y in ball c (2 * R), newtonianKernel n (x - y) * (f y - g y) := by
    unfold newtonianPotential
    rw [← integral_add hΓg hΓI]
    congr 1; funext y; ring
  rw [hsplit, setIntegral_congr_fun hB hpt, ← integral_indicator hB, convolution_mul]
  congr 1
  have he : (ball c (2 * R)).indicator (fun y => Kc (x - y) * (f y - g y)) =
      fun y => Kc (x - y) * (ball c (2 * R)).indicator (fun y => f y - g y) y := by
    funext y; by_cases hy : y ∈ ball c (2 * R)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [he]
  have h := integral_sub_left_eq_self (fun t => Kc t * (ball c (2 * R)).indicator (fun y => f y - g y) (x - t)) volume x
  simp only [sub_sub_cancel] at h
  exact h

/-- Second derivatives add on an open set where `w = a + b`, `a` is `C²` on an open `V ⊇ U` and `b` is globally `C²`. -/
theorem fderiv_fderiv_eq_add_of_eqOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {w a b : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (ha : ContDiffOn ℝ 2 a V) (hb : ContDiff ℝ 2 b) (hw : ∀ x ∈ U, w x = a x + b x) {x : E} (hx : x ∈ U) :
    fderiv ℝ (fderiv ℝ w) x = fderiv ℝ (fderiv ℝ a) x + fderiv ℝ (fderiv ℝ b) x := by
  have haA : ∀ z ∈ U, ContDiffAt ℝ 2 a z := fun z hz => ha.contDiffAt (hV.mem_nhds (hUV hz))
  have h1 : ∀ z ∈ U, fderiv ℝ w z = fderiv ℝ a z + fderiv ℝ b z := by
    intro z hz
    rw [(Filter.eventuallyEq_of_mem (hU.mem_nhds hz) hw).fderiv_eq]
    exact fderiv_add ((haA z hz).differentiableAt (by simp)) ((hb.differentiable (by simp)) z)
  rw [(Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h1).fderiv_eq]
  exact fderiv_add (((haA x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    ((hb.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)

/-- **GT2001 Lemma 4.4 — qualitative assertion for the source class `f ∈ C^α(B₂)` (p. 52: locally Hölder) with `f` integrable
(p. 51).** For `n ≥ 2` (including `2`), `R > 0`, `0 < α < 1`, `f` integrable on `B_{2R}(c)` and uniformly `α`-Hölder on every compact
subset of `B_{2R}(c)`, the Newtonian potential `w` of `f` in `B_{2R}(c)` is `C²` on the open ball `B_{5R/4}(c)` (a neighbourhood of
`closedBall c R`), and its Hessian `D²w = fderiv ℝ (fderiv ℝ w)` is bounded and `α`-Hölder on `closedBall c R`. The bound and the cap
depend on `f`, `R`, `c` (qualitative statement); no global bound or Hölder cap of `f` on `B_{2R}(c)` is assumed. -/
theorem newtonianPotential_localHolder (hn : 2 ≤ n) (hR : 0 < R) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfi : IntegrableOn f (ball c (2 * R)) volume)
    (hloc : ∀ K, IsCompact K → K ⊆ ball c (2 * R) → ∃ H : ℝ≥0, HolderOnWith H α f K) :
    ContDiffOn ℝ 2 (newtonianPotential n (ball c (2 * R)) f) (ball c (5 * R / 4)) ∧
    (∃ B : ℝ, ∀ x ∈ closedBall c R, ‖fderiv ℝ (fderiv ℝ (newtonianPotential n (ball c (2 * R)) f)) x‖ ≤ B) ∧
    ∃ K : ℝ≥0, HolderOnWith K α (fderiv ℝ (fderiv ℝ (newtonianPotential n (ball c (2 * R)) f))) (closedBall c R) := by
  obtain ⟨η, hηC, hη1, hη01, -, M, H, hgM, hgH⟩ := exists_cutoff_holder_source hR hα0 hα1.le hloc
  set g := fun y => η y * f y
  obtain ⟨C, hC, hprod⟩ := newtonianPotential_schauder hn hα0 hα1
  obtain ⟨hgC2, hgsup, hgdiff, -, -⟩ := hprod c R hR g M H hgM hgH
  obtain ⟨Kc, hKc, hKcs, hKeq⟩ := exists_newtonianFarKernel hn hR
  have hB : MeasurableSet (ball c (2 * R)) := measurableSet_ball
  have hgm : AEMeasurable g (volume.restrict (ball c (2 * R))) := hηC.continuous.aemeasurable.mul hfi.aemeasurable
  have hgi : IntegrableOn g (ball c (2 * R)) volume :=
    (integrableOn_const (C := M) measure_ball_lt_top.ne).mono' hgm.aestronglyMeasurable
      ((ae_restrict_mem hB).mono fun y hy => by rw [Real.norm_eq_abs]; exact hgM y hy)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hgM c (mem_ball_self (by positivity)))
  set F := (ball c (2 * R)).indicator fun y => f y - g y
  have hFi : Integrable F volume := (integrable_indicator_iff hB).mpr (hfi.sub hgi)
  set v := convolution Kc F (ContinuousLinearMap.mul ℝ ℝ) volume
  have hv : ContDiff ℝ 3 v := by
    have h := hKcs.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (n := 3)
      (hKc.of_le (WithTop.coe_le_coe.mpr le_top)) hFi.locallyIntegrable
    exact_mod_cast h
  have hfg : ∀ y ∈ closedBall c (3 * R / 2), g y = f y := fun y hy => by simp only [g, hη1 y hy, one_mul]
  set w := newtonianPotential n (ball c (2 * R)) f
  set wg := newtonianPotential n (ball c (2 * R)) g
  have hdec : ∀ x ∈ ball c (5 * R / 4), w x = wg x + v x := fun x hx =>
    newtonianPotential_ball_eq_add_convolution hn hfi hgm hgM hfg hKc hKcs hKeq hx
  have hUB : ball c (5 * R / 4) ⊆ ball c (2 * R) := ball_subset_ball (by linarith)
  have hRU : closedBall c R ⊆ ball c (5 * R / 4) := closedBall_subset_ball (by linarith)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hC2 : ContDiffOn ℝ 2 w (ball c (5 * R / 4)) :=
    ((hgC2.mono hUB).add hv2.contDiffOn).congr hdec
  have hD : ∀ x ∈ closedBall c R,
      fderiv ℝ (fderiv ℝ w) x = fderiv ℝ (fderiv ℝ wg) x + fderiv ℝ (fderiv ℝ v) x := fun x hx =>
    fderiv_fderiv_eq_add_of_eqOn isOpen_ball isOpen_ball hUB hgC2 hv2 hdec (hRU hx)
  -- the far Hessian is `C¹`: bounded and Lipschitz on the convex compact `closedBall c R`
  have hvH : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ v)) :=
    (hv.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hn2 : Continuous fun x => ‖fderiv ℝ (fderiv ℝ v) x‖ :=
    Continuous.norm (E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) hvH.continuous
  obtain ⟨B2, hB2'⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hn2.continuousOn
  have hB2 : ∀ x ∈ closedBall c R, ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ B2 := fun x hx => by
    have := hB2' x hx; rw [Real.norm_eq_abs] at this; exact (le_abs_self _).trans this
  obtain ⟨L3, hL3⟩ := hvH.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall c R) (isCompact_closedBall c R)
  set B3' : ℝ := (L3 : ℝ)
  have hlip : ∀ x ∈ closedBall c R, ∀ z ∈ closedBall c R,
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) z‖ ≤ B3' * ‖x - z‖ := fun x hx z hz => by
    have := hL3.dist_le_mul x hx z hz; rwa [dist_eq_norm, dist_eq_norm] at this
  have hdiam : ∀ x ∈ closedBall c R, ∀ z ∈ closedBall c R, ‖x - z‖ ≤ 2 * R := fun x hx z hz => by
    rw [← dist_eq_norm]; rw [mem_closedBall] at hx hz; linarith [dist_triangle x c z, dist_comm z c]
  set Cg := C * (M * R ^ (-(α:ℝ)) + H)
  have hCg : 0 ≤ Cg := by positivity
  refine ⟨hC2, ⟨C * (M + R ^ (α:ℝ) * H) + B2, fun x hx => ?_⟩, Real.toNNReal (Cg + B3' * (2 * R) ^ (1 - (α:ℝ))),
    holderOnWith_of_dist_le (by positivity) fun x hx z hz => ?_⟩
  · rw [hD x hx]
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add (hgsup x hx) (hB2 x hx))
  · rw [dist_eq_norm, dist_eq_norm, hD x hx, hD z hz,
      show fderiv ℝ (fderiv ℝ wg) x + fderiv ℝ (fderiv ℝ v) x - (fderiv ℝ (fderiv ℝ wg) z + fderiv ℝ (fderiv ℝ v) z) =
        (fderiv ℝ (fderiv ℝ wg) x - fderiv ℝ (fderiv ℝ wg) z) + (fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) z) by abel]
    have e2 : B3' * ‖x - z‖ ≤ B3' * (2 * R) ^ (1 - (α:ℝ)) * ‖x - z‖ ^ (α:ℝ) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (le_rpow_one_sub_mul_rpow (norm_nonneg _) (hdiam x hx z hz)
        (by exact_mod_cast hα1.le)) L3.coe_nonneg
    calc _ ≤ _ := ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ Cg * ‖x - z‖ ^ (α:ℝ) + B3' * (2 * R) ^ (1 - (α:ℝ)) * ‖x - z‖ ^ (α:ℝ) :=
          add_le_add (hgdiff x hx z hz) ((hlip x hx z hz).trans e2)
      _ = (Cg + B3' * (2 * R) ^ (1 - (α:ℝ))) * ‖x - z‖ ^ (α:ℝ) := by ring

end Local

end FunctionalInequalities.Analysis
