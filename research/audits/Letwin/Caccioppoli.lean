import FunctionalInequalities.Analysis.WeakDerivative.Sobolev
import FunctionalInequalities.Analysis.WeakDerivative.Caccioppoli
import FunctionalInequalities.Analysis.Cutoff.SmoothBall
import FunctionalInequalities.Analysis.LpExponent
import FunctionalInequalities.L2.Components
import FunctionalInequalities.Analysis.MorreyGrowth
import FunctionalInequalities.Analysis.RieszPotential.Critical
import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian
import FunctionalInequalities.Analysis.WeakDerivative.Representation
import FunctionalInequalities.Analysis.WeakDerivative.Moser
import FunctionalInequalities.Probability.ExponentialMoments.Growth
import FunctionalInequalities.Analysis.WeakDerivative.Harnack

/-!
# Audit client: Caccioppoli, Moser and bounded weak Harnack data at the regular-class witness

One witness `u, L, LF, T` of `exists_regular_moment_directional_hessian_subsolution` is selected ONCE, with its
normalization and actual gradient pushforward. The quantifier order is the one needed by an iteration over finitely many
directions and nested cutoffs:

* for each compact `S`, the constants `α, β` and a bound `B` for the density `e^{-u}` on `S` are chosen once, with
  `α ≤ A ≤ β` a.e. on `S` for `A = e^{-u} (∇²u)⁻¹`;
* then for EVERY direction `v` and EVERY `C¹` compactly supported cutoff `χ` with `tsupport χ ⊆ S`, at the same `u, T, A,
  α, β, B`: the deficit `w = M_v - vᵀ∇²u v` (`M_v = (16/κ) Σ vᵢ²`) is bounded and a.e. nonnegative with weak derivatives
  `a = -∂(vᵀ∇²u v)`, the weak supersolution inequality holds for every admissible test in `tsupport χ` with
  `F_v = M_v · B`, the Caccioppoli inequality holds for all `δ, p > 0`, and the energy variables `χ (δ + max w 0)^r`
  carry exact weak data for all `δ > 0` and real `r`.

The dimension-specialized clients add, at the same witness and constants, the weak Sobolev bound of the energy
variables: critical GNS for `n > 2`, the fixed `L⁶` gain for `n = 2` and the essential `L^∞` bound for `n = 1`, the last
two with closed-ball corollaries. Actual bump instances use every direction and every bump of outer radius at most two
at one `u, α, β, B`.

The unified theorems `moser_inputs_unified_same_witness` (every `n > 0`) and `moser_inputs_unified_two_same_witness`
(`n = 2`) combine the Moser inputs at ONE witness: the actual logarithmic data and energy, the power and coordinate
energies, uniform dyadic cutoffs (one `D` before all radii, the same `α, β, B` for every `m` and direction), the normalized
closed-ball `L^p → L^∞` limit and, in dimension two, finite-exponent Sobolev bounds of the same energy variables.
`actual_log_gradient_morrey_same_witness` gives the ALL-ball Morrey bound (GT (7.51)) of the actual logarithmic gradient
at ONE witness, and `actual_log_gradient_potential_exp_same_witness` (`n ≥ 2`) gives the exponential integrability of its
critical potential at that witness. This is not the exponential integrability of `log − mean` (GT Lemma 7.16 /
John–Nirenberg).

`actual_dyadic_power_gain_same_witness` (`n > 2`) gives ONE critical dyadic gain step at the master witness (global
deficit class). `actual_local_deficit_log_morrey_same_witness` treats the LOCAL deficit `w = M − h_v` with a cap `M` only on
`closedBall 0 (4R)`: the local log energy, ONE weak log extension identified on `closedBall 0 (4R)`, and the buffered
ALL-ball Morrey bound on `B_3R`; `actual_local_deficit_potential_exp_same_witness` (`n ≥ 2`) adds, at the same witness and
extension, the exponential integrability of the critical potential on `B_3R`. The coefficients are chosen once per `R`
(not once per fixed compact set before all radii), and the Morrey domain is centered at the origin.

`actual_local_deficit_john_nirenberg_same_witness` and `actual_local_deficit_log_moment_product_same_witness` (`n ≥ 2`) add,
at that per-`R` witness and the ONE extension, the actual John–Nirenberg estimate of `log s` on `B_3R` at the radius-dependent
exponent `σ/K16` and the product of power moments. `actual_local_inputs_fixed_compact_same_witness` chooses the
coefficients ONCE per fixed compact `S` before every domain center and radius, and gives all linear power data, the power
and log energies, ONE weak extension and the centered Morrey bound; `actual_joint_jn_moments_fixed_compact_same_witness`
adds, inside the SAME `H`, the JN and power moments at the uniform `p0` under the small-forcing condition `F R² ≤ α δ`.

The final section (namespace `LetwinHarnackAudit`) consumes these fixed-compact producers and proves the bounded actual weak
Harnack inequality (Gilbarg–Trudinger 2001, Theorem 8.18 for bounded data) by the Moser iteration of the library: the
full-exponent same-witness products for `n > 2` (`0 < p < n/(n−2)`), `n = 2` and `n = 1` (every finite `p > 0`), and the
essential-infimum form for every `n > 0` with the unshifted forcing `M B R²/α`.

`LetwinHarnackAudit.harnack_joint_regular_potential` selects the regular moment potential ONCE and keeps all its regularity,
log-determinant, positivity and weak Hessian data, and for every compact `S` coefficients `α, β, B` and a constant family
`C(p)` before every center, radius, direction and local cap `M`, applies the given-data weak Harnack inequality
(`FunctionalInequalities.Analysis.bounded_weak_harnack_of_given_data`) to the deficit `M − vᵀ ∇²u v` with forcing `M B`.

None of this is the full Theorem 8.18 for unbounded data or rough coefficients, a pointwise infimum or regular
representative, oscillation decay, Hölder, `C^{2,α}` or Schauder theory, the merely convex source class, full Letwin
Lemma 2.2/2.7 or Theorem 1.1, or uncut Eldan.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace LetwinCaccioppoliAudit

open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

section SameWitness

variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- Proof-local uniform source data: one witness `u, T`; measurable coefficients `A = e^{-u}(∇²u)⁻¹`; for each compact
`S` one choice of `α, β, B`; then for every direction `v` and every cutoff with `tsupport χ ⊆ S`, the weak data of
`w = M_v - h_v`, `a = -∂h_v` and the weak supersolution inequality with `F_v = M_v · B`. -/
private theorem uniform_source_data :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ i j : Fin n, AEStronglyMeasurable (fun x => (Real.exp (-u x) • (hessianMatrix u x)⁻¹) i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧ (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∀ (v : Fin n → ℝ) (χ : EuclideanSpace ℝ (Fin n) → ℝ), tsupport χ ⊆ S →
          let A := fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹
          let w := fun x => (16 / κ) * (∑ i : Fin n, v i ^ 2) -
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧ (∃ Cw : ℝ, ∀ x, ‖w x‖ ≤ Cw) ∧
          (∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
          (∀ k : Fin n, ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
            MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S')) ∧
          (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x) ∧
          (∀ (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
            (∃ Bη : ℝ, 0 ≤ Bη ∧ ∀ x, ‖η x‖ ≤ Bη) → HasCompactSupport η →
            Function.support η ⊆ tsupport χ → (∀ x, 0 ≤ η x) →
            (∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
              MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
            -((16 / κ) * (∑ i : Fin n, v i ^ 2) * B) *
                (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨u, L, LF, T, hold, -, hcoef⟩ :=
    exists_regular_moment_directional_hessian_subsolution hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨-, hl, hnorm, hmap, hC1, hG, hF, -, hd, hT, -, hfirst, hInv, -⟩ := hold
  have hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
    filter_upwards [hd] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]
  have hVc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he : (fun y => W y - κ / 2 * ‖y‖ ^ 2) + (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  have hρc : Continuous fun x => Real.exp (-u x) := Real.continuous_exp.comp hC1.continuous.neg
  -- measurability of the coefficient entries, independent of `S`, `v` and `χ`
  have hAm (i j : Fin n) : AEStronglyMeasurable (fun x => (Real.exp (-u x) • (hessianMatrix u x)⁻¹) i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hLoc : LocallyIntegrable (fun x => (hessianMatrix u x)⁻¹ i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply locallyIntegrable_iff.mpr
      intro S hS
      let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
        isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
      exact ((hInv i i j).2.2 S hS).integrable (by simp)
    change AEStronglyMeasurable (fun x => Real.exp (-u x) * (hessianMatrix u x)⁻¹ i j) volume
    exact hρc.aestronglyMeasurable.mul hLoc.aestronglyMeasurable
  refine ⟨u, T, hnorm, hmap, hAm, fun S hS => ?_⟩
  -- one choice of `α, β` and of the density bound `B` on `S`
  obtain ⟨c0, c1, hc0, hc1, hcb⟩ := hcoef S hS
  obtain ⟨Cρ, hCρ⟩ := hS.exists_bound_of_continuousOn hρc.continuousOn
  have hρB (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) : Real.exp (-u x) ≤ max Cρ 0 := by
    have h := hCρ x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    exact h.trans (le_max_left _ _)
  refine ⟨c0, c1, max Cρ 0, hc0, hc1, le_max_right _ _, hρB, hcb, fun v χ hχS => ?_⟩
  intro A w a
  classical
  set M : ℝ := (16 / κ) * ∑ i : Fin n, v i ^ 2 with hM
  set hv := fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j with hhvdef
  -- 0 ≤ h_v ≤ M a.e.
  have hquad (Bm : Matrix (Fin n) (Fin n) ℝ) :
      dotProduct v (Bm.mulVec v) = ∑ i : Fin n, ∑ j : Fin n, v i * v j * Bm i j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hrange : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ hv x ∧ hv x ≤ M := by
    filter_upwards [hd] with x hx
    have h0 := hx.1.posSemidef.dotProduct_mulVec_nonneg v
    have h1 := hx.2.2.dotProduct_mulVec_nonneg v
    simp only [star_trivial] at h0 h1
    rw [hquad] at h0
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hquad,
      smul_eq_mul] at h1
    have hvv : dotProduct v v = ∑ i : Fin n, v i ^ 2 := by simp only [dotProduct, sq]
    rw [hvv] at h1
    exact ⟨h0, by simp only [M]; linarith⟩
  have hw0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x := by
    filter_upwards [hrange] with x hx
    simp only [w]; linarith [hx.2]
  -- weak derivative of w from the weak Hessian tensor
  have hsum (k : Fin n) := hasWeakDerivAlong_finsetSum_mul (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v p.1 * v p.2) (f := fun p x => hessianMatrix u x p.1 p.2) (df := fun p x => T x k p.1 p.2)
    (v := EuclideanSpace.basisFun (Fin n) ℝ k) (fun p _ => (hT k p.1 p.2).1) (fun p _ => (hT k p.1 p.2).2)
  have hhv (k : Fin n) : HasWeakDerivAlong hv (fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    (hsum k).1.congr_ae (ae_of_all _ fun x => by simp only [hv, Fintype.sum_prod_type])
      (ae_of_all _ fun x => by simp only [Fintype.sum_prod_type])
  have htv2 (k : Fin n) : ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
      MemLp (fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') := by
    intro S' hS'
    have h := (hsum k).2 S' hS'
    simpa only [Fintype.sum_prod_type] using h
  have hwweak (k : Fin n) : HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    ((hhv k).const_add_mul M (-1)).congr_ae
      (ae_of_all _ fun x => by simp only [w, hv, M]; ring) (ae_of_all _ fun x => by simp only [a]; ring)
  have ha2 (k : Fin n) : ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') :=
    fun S' hS' => (htv2 k S' hS').neg
  set Hb : ℝ := ∑ i : Fin n, ∑ j : Fin n, ‖v i * v j‖ * ((Real.toNNReal (16 / κ) : NNReal) : ℝ)
  have hvb (x : EuclideanSpace ℝ (Fin n)) : ‖hv x‖ ≤ Hb := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j) (norm_nonneg _)
  have hwb (x : EuclideanSpace ℝ (Fin n)) : ‖w x‖ ≤ ‖M‖ + Hb :=
    (norm_sub_le _ _).trans (by linarith [hvb x])
  -- the weak supersolution inequality for every admissible test, from the canonical bounded directional theorem
  refine ⟨(hwweak ⟨0, hn⟩).1, ⟨_, hwb⟩, hwweak, ha2, hw0, ?_⟩
  intro η dη hηl hηb hηc hηs hη0 hηd
  obtain ⟨Bη, -, hBη⟩ := hηb
  obtain ⟨h1, h2, h3⟩ := integral_directional_hessian_flux_le_of_bounded_weak_test hC1 hl hG
    (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet T hT hInv (fun i => (hfirst i).2.2.2.2) hVc
    (hd.mono fun x hx => hx.1) v hηl hBη hηc (fun k => (hηd k).1) (fun k => (hηd k).2.1) (fun k => (hηd k).2.2.2)
    (ae_of_all _ hη0)
  have hηint : Integrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport η)).1 (hηl.integrableOn_isCompact hηc)
  -- orientation: aᵀ A dη = -(e^{-u} Σ_k (Σ_b (∇²u)⁻¹_{bk} ∂_b h_v) dη_k), with a = -∂h_v
  have hL : (fun x => dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))) =
      fun x => -(Real.exp (-u x) * (∑ k : Fin n,
        (∑ b : Fin n, (hessianMatrix u x)⁻¹ b k *
          (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) * dη k x)) := by
    funext x
    simp only [dotProduct, Matrix.mulVec, A, a, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
      neg_mul, Finset.sum_neg_distrib, neg_inj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hL, integral_neg]
  have hR : (∫ x, Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) * η x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ ∫ x, (M * max Cρ 0) * η x ∂volume := by
    refine integral_mono_ae h2 (hηint.const_mul _) ?_
    filter_upwards [hrange] with x hx
    by_cases hxs : x ∈ tsupport χ
    · have hh : Real.exp (-u x) * hv x ≤ M * max Cρ 0 := by
        calc Real.exp (-u x) * hv x ≤ max Cρ 0 * M :=
              mul_le_mul (hρB x (hχS hxs)) hx.2 hx.1 (le_max_right _ _)
          _ = M * max Cρ 0 := mul_comm _ _
      exact mul_le_mul_of_nonneg_right hh (hη0 x)
    · have h0 : η x = 0 := by
        by_contra h; exact hxs (hηs h)
      simp only [h0, mul_zero, le_refl]
  rw [integral_const_mul] at hR
  linarith

/-- **Uniform energy and linear data at one witness.** One `u, T` with the normalization and the actual pushforward;
for each compact `S` one `α, β, B` with `e^{-u} ≤ B` and `α ≤ A ≤ β` a.e. on `S`; then for EVERY direction `v` and
EVERY `C¹` compactly supported `χ` with `tsupport χ ⊆ S`, at the same `u, T, A, α, β, B` and `F_v = M_v · B`:
the weak deficit data of `w`, the weak supersolution inequality, the Caccioppoli inequality for all `δ, p > 0`, and the
linear energy variables `χ (δ + max w 0)^r` for all `δ > 0` and real `r`. -/
theorem uniform_energy_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧ (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∀ (v : Fin n → ℝ) (χ : EuclideanSpace ℝ (Fin n) → ℝ),
          ContDiff ℝ 1 χ → HasCompactSupport χ → tsupport χ ⊆ S →
          let A := fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹
          let w := fun x => (16 / κ) * (∑ i : Fin n, v i ^ 2) -
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := (16 / κ) * (∑ i : Fin n, v i ^ 2) * B
          (∃ Cw : ℝ, ∀ x, ‖w x‖ ≤ Cw) ∧
          (∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
          (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x) ∧
          (∀ (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
            (∃ Bη : ℝ, 0 ≤ Bη ∧ ∀ x, ‖η x‖ ≤ Bη) → HasCompactSupport η →
            Function.support η ⊆ tsupport χ → (∀ x, 0 ≤ η x) →
            (∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
              MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
            -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
          (∀ δ : ℝ, 0 < δ → ∀ p : ℝ, 0 < p →
            let s := fun x => δ + max (w x) 0
            Integrable (fun x => χ x ^ 2 * s x ^ (-p - 1) * ∑ k : Fin n, (a k x) ^ 2)
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            Integrable (fun x => s x ^ (1 - p) * ∑ k : Fin n,
              (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            Integrable (fun x => χ x ^ 2 * s x ^ (-p)) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∫ x, χ x ^ 2 * s x ^ (-p - 1) * ∑ k : Fin n, (a k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / (p ^ 2 * α)) *
                (∫ x, s x ^ (1 - p) * ∑ k : Fin n,
                  (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (p * α)) *
                (∫ x, χ x ^ 2 * s x ^ (-p) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
          (∀ δ : ℝ, 0 < δ → ∀ r : ℝ,
            let g := fun x => χ x * (δ + max (w x) 0) ^ r
            let dg := fun (k : Fin n) x =>
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * (δ + max (w x) 0) ^ r +
              χ x * (r * (δ + max (w x) 0) ^ (r - 1)) * a k x
            LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
              HasCompactSupport g ∧ Function.support g ⊆ tsupport χ ∧
              (∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x, ‖g x‖ ≤ Cg) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
              ∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧
                MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨u, T, hnorm, hmap, hAm, hS⟩ := uniform_source_data hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, fun S hSc => ?_⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hvχ⟩ := hS S hSc
  refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, fun v χ hχ hχc hχS => ?_⟩
  intro A w a F
  obtain ⟨hwl, ⟨Cw, hwb⟩, hww, ha2, hw0, hsub⟩ := hvχ v χ hχS
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hB
  have hcbχ := ae_restrict_of_ae_restrict_of_subset hχS hcb
  exact ⟨⟨Cw, hwb⟩, hww, hw0, hsub,
    fun δ hδ p hp => bounded_weak_supersolution_caccioppoli hwl hwb hww ha2 hw0 hAm hχ hχc hα hβ hF hcbχ hsub hδ hp,
    fun δ hδ r => bounded_rpow_cutoff_weak_data hwl hwb hww ha2 hw0 hχ hχc hδ r⟩

/-- **High dimension `n > 2`, uniform.** At the uniform witness and constants, for every direction and every cutoff
supported in `S`: the Caccioppoli inequality and the weak GNS bound of the energy variables `g = χ s^r`, every `δ > 0`,
real `r` and `q` with `1/q = 1/2 - 1/n`. -/
theorem uniform_sobolev_high_same_witness (h2n : 2 < n) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧ (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        ∀ (v : Fin n → ℝ) (χ : EuclideanSpace ℝ (Fin n) → ℝ),
          ContDiff ℝ 1 χ → HasCompactSupport χ → tsupport χ ⊆ S →
          let w := fun x => (16 / κ) * (∑ i : Fin n, v i ^ 2) -
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := (16 / κ) * (∑ i : Fin n, v i ^ 2) * B
          (∀ δ : ℝ, 0 < δ → ∀ p : ℝ, 0 < p →
            let s := fun x => δ + max (w x) 0
            (∫ x, χ x ^ 2 * s x ^ (-p - 1) * ∑ k : Fin n, (a k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / (p ^ 2 * α)) *
                (∫ x, s x ^ (1 - p) * ∑ k : Fin n,
                  (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (p * α)) *
                (∫ x, χ x ^ 2 * s x ^ (-p) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
          (∀ δ : ℝ, 0 < δ → ∀ r : ℝ, ∀ q : NNReal, (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹ →
            let g := fun x => χ x * (δ + max (w x) 0) ^ r
            let dg := fun (k : Fin n) x =>
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * (δ + max (w x) 0) ^ r +
              χ x * (r * (δ + max (w x) 0) ^ (r - 1)) * a k x
            eLpNorm g q (volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
              (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) *
                ∑ k : Fin n, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨u, T, hnorm, hmap, hU⟩ := uniform_energy_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, fun S hSc => ?_⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, -, hvχ⟩ := hU S hSc
  refine ⟨α, β, B, hα, hβ, hB, hρB, fun v χ hχ hχc hχS => ?_⟩
  intro w a F
  obtain ⟨-, -, -, -, hcac, hlin⟩ := hvχ v χ hχ hχc hχS
  refine ⟨fun δ hδ p hp => (hcac δ hδ p hp).2.2.2, ?_⟩
  intro δ hδ r q hq g dg
  obtain ⟨hgl, hgc, -, ⟨Cg, -, hgb⟩, -, hgd⟩ := hlin δ hδ r
  exact eLpNorm_le_sum_eLpNorm_weak_deriv_of_compact_bounded h2n hgl hgb hgc (fun k => (hgd k).1)
    (fun k => (hgd k).2.1) (fun k => (hgd k).2.2.2) hq

/-- **Actual bumps, every direction, one `u, α, β, B`.** With `S = closedBall 0 2`, for every direction `v` and every
bump of outer radius at most two: the Caccioppoli inequality at `δ = 1` with `p = 1` and `p = 2`, and the energy variable
`φ s^(-1/2)` with its exact weak derivative and nonnegativity. -/
theorem uniform_bump_instances :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
      ∀ (v : Fin n → ℝ) (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))), φ.rOut ≤ 2 →
        let w := fun x => (16 / κ) * (∑ i : Fin n, v i ^ 2) -
          ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
        let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
        let F := (16 / κ) * (∑ i : Fin n, v i ^ 2) * B
        let s := fun x => 1 + max (w x) 0
        (∀ p : ℝ, p = 1 ∨ p = 2 →
          (∫ x, φ x ^ 2 * s x ^ (-p - 1) * ∑ k : Fin n, (a k x) ^ 2
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            (4 * β / (p ^ 2 * α)) *
              (∫ x, s x ^ (1 - p) * ∑ k : Fin n,
                (fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (2 * F / (p * α)) *
              (∫ x, φ x ^ 2 * s x ^ (-p) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
        (∀ k : Fin n, HasWeakDerivAlong (fun x => φ x * s x ^ (-1 / 2 : ℝ))
          (fun x => fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ k) *
              s x ^ (-1 / 2 : ℝ) +
            φ x * ((-1 / 2 : ℝ) * s x ^ ((-1 / 2 : ℝ) - 1)) * a k x)
          (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        ∀ x, 0 ≤ φ x * s x ^ (-1 / 2 : ℝ) := by
  obtain ⟨u, T, hnorm, hmap, hU⟩ := uniform_energy_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨α, β, B, hα, hβ, hB, -, -, hvχ⟩ :=
    hU (Metric.closedBall 0 2) (isCompact_closedBall 0 2)
  refine ⟨u, T, hnorm, hmap, α, β, B, hα, hβ, hB, fun v φ hφ => ?_⟩
  intro w a F s
  have hφS : tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ Metric.closedBall 0 2 := by
    rw [φ.tsupport_eq]
    exact Metric.closedBall_subset_closedBall hφ
  obtain ⟨-, -, -, -, hcac, hlin⟩ := hvχ v φ φ.contDiff φ.hasCompactSupport hφS
  refine ⟨fun p hp => (hcac 1 one_pos p (by rcases hp with rfl | rfl <;> norm_num)).2.2.2, ?_, ?_⟩
  · intro k
    exact ((hlin 1 one_pos (-1 / 2)).2.2.2.2.2 k).1
  · exact (hlin 1 one_pos (-1 / 2)).2.2.2.2.1 fun x => φ.nonneg

/-- The canonical producer's first component elaborates as `exists_regular_moment_weak_hessian_evolution` at the
selected `u, L, LF, T`. -/
example : True := by
  obtain ⟨u, L, LF, T, hold, -⟩ :=
    exists_regular_moment_directional_hessian_subsolution hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have _ : type_of% (exists_regular_moment_weak_hessian_evolution hn hκ hK hKc hKint hW hstrong μ hμ hiso) :=
    ⟨u, L, LF, T, hold⟩
  trivial

end SameWitness

section DimTwo

variable {K : Set (EuclideanSpace ℝ (Fin 2))} {W : EuclideanSpace ℝ (Fin 2) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin 2))) =
    (volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hκ hK hKc hKint hW hstrong hμ hiso

/-- **Dimension two, uniform.** At the uniform witness and constants, for every direction and every cutoff supported in
`S`: the Caccioppoli inequality and the fixed `L⁶` gain of `g = χ s^r` with the exact factor
`C_GNS(3/2) · volume(cthickening ε (tsupport χ))^(1/6)`, and its closed-ball form when `tsupport χ ⊆ closedBall 0 ρ`. -/
theorem uniform_sobolev_two_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin 2) → ℝ) (T : EuclideanSpace ℝ (Fin 2) → Fin 2 → Fin 2 → Fin 2 → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin 2))) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧ (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        ∀ (v : Fin 2 → ℝ) (χ : EuclideanSpace ℝ (Fin 2) → ℝ),
          ContDiff ℝ 1 χ → HasCompactSupport χ → tsupport χ ⊆ S →
          let w := fun x => (16 / κ) * (∑ i : Fin 2, v i ^ 2) -
            ∑ i : Fin 2, ∑ j : Fin 2, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin 2) x => -(∑ i : Fin 2, ∑ j : Fin 2, v i * v j * T x k i j)
          let F := (16 / κ) * (∑ i : Fin 2, v i ^ 2) * B
          (∀ δ : ℝ, 0 < δ → ∀ p : ℝ, 0 < p →
            let s := fun x => δ + max (w x) 0
            (∫ x, χ x ^ 2 * s x ^ (-p - 1) * ∑ k : Fin 2, (a k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
              (4 * β / (p ^ 2 * α)) *
                (∫ x, s x ^ (1 - p) * ∑ k : Fin 2,
                  (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
              (2 * F / (p * α)) *
                (∫ x, χ x ^ 2 * s x ^ (-p) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))) ∧
          (∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ r : ℝ,
            let g := fun x => χ x * (δ + max (w x) 0) ^ r
            let dg := fun (k : Fin 2) x =>
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k) * (δ + max (w x) 0) ^ r +
              χ x * (r * (δ + max (w x) 0) ^ (r - 1)) * a k x
            eLpNorm g 6 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
              (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (3 / 2) : ENNReal) *
                (volume (Metric.cthickening ε (tsupport χ))) ^ (1 / 6 : ℝ) *
                  ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
            ∀ ρ : ℝ, 0 ≤ ρ → tsupport χ ⊆ Metric.closedBall 0 ρ →
              eLpNorm g 6 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
                (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (3 / 2) : ENNReal) *
                  (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (ε + ρ))) ^ (1 / 6 : ℝ) *
                    ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) := by
  obtain ⟨u, T, hnorm, hmap, hU⟩ :=
    uniform_energy_same_witness (n := 2) (by norm_num) hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, fun S hSc => ?_⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, -, hvχ⟩ := hU S hSc
  refine ⟨α, β, B, hα, hβ, hB, hρB, fun v χ hχ hχc hχS => ?_⟩
  intro w a F
  obtain ⟨-, -, -, -, hcac, hlin⟩ := hvχ v χ hχ hχc hχS
  refine ⟨fun δ hδ p hp => (hcac δ hδ p hp).2.2.2, ?_⟩
  intro ε hε δ hδ r g dg
  obtain ⟨hgl, -, hgs, ⟨Cg, -, hgb⟩, -, hgd⟩ := hlin δ hδ r
  have hmain := eLpNorm_six_le_sum_eLpNorm_weak_deriv_of_support_subset_two hgl hgb hχc hgs
    (fun k => (hgd k).2.2.1) (fun k => (hgd k).1) (fun k => (hgd k).2.2.2) hε
  refine ⟨hmain, fun ρ hρ hball => hmain.trans ?_⟩
  have hsub : Metric.cthickening ε (tsupport χ) ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (ε + ρ) := by
    rw [← cthickening_closedBall hε.le hρ]
    exact Metric.cthickening_subset_of_subset ε hball
  gcongr

end DimTwo

section DimOne

variable {K : Set (EuclideanSpace ℝ (Fin 1))} {W : EuclideanSpace ℝ (Fin 1) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 1)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin 1))) =
    (volume : Measure (EuclideanSpace ℝ (Fin 1))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hκ hK hKc hKint hW hstrong hμ hiso

/-- **Dimension one, uniform** (a separate FTC-based argument, not the printed `n ≥ 2` route). At the uniform witness
and constants, for every direction and every cutoff supported in `S`: the Caccioppoli inequality and the essential
`L^∞` bound of `g = χ s^r` with the exact factor `volume(cthickening ε (tsupport χ))^(1/2)`, and its closed-ball form. -/
theorem uniform_sobolev_one_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin 1) → ℝ) (T : EuclideanSpace ℝ (Fin 1) → Fin 1 → Fin 1 → Fin 1 → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin 1)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin 1))) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin 1)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧ (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        ∀ (v : Fin 1 → ℝ) (χ : EuclideanSpace ℝ (Fin 1) → ℝ),
          ContDiff ℝ 1 χ → HasCompactSupport χ → tsupport χ ⊆ S →
          let w := fun x => (16 / κ) * (∑ i : Fin 1, v i ^ 2) -
            ∑ i : Fin 1, ∑ j : Fin 1, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin 1) x => -(∑ i : Fin 1, ∑ j : Fin 1, v i * v j * T x k i j)
          let F := (16 / κ) * (∑ i : Fin 1, v i ^ 2) * B
          (∀ δ : ℝ, 0 < δ → ∀ p : ℝ, 0 < p →
            let s := fun x => δ + max (w x) 0
            (∫ x, χ x ^ 2 * s x ^ (-p - 1) * ∑ k : Fin 1, (a k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin 1)))) ≤
              (4 * β / (p ^ 2 * α)) *
                (∫ x, s x ^ (1 - p) * ∑ k : Fin 1,
                  (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin 1)))) +
              (2 * F / (p * α)) *
                (∫ x, χ x ^ 2 * s x ^ (-p) ∂(volume : Measure (EuclideanSpace ℝ (Fin 1))))) ∧
          (∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ r : ℝ,
            let g := fun x => χ x * (δ + max (w x) 0) ^ r
            let dg := fun (k : Fin 1) x =>
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k) * (δ + max (w x) 0) ^ r +
              χ x * (r * (δ + max (w x) 0) ^ (r - 1)) * a k x
            eLpNorm g ⊤ (volume : Measure (EuclideanSpace ℝ (Fin 1))) ≤
              (volume (Metric.cthickening ε (tsupport χ))) ^ (1 / 2 : ℝ) *
                eLpNorm (dg 0) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1))) ∧
            ∀ ρ : ℝ, 0 ≤ ρ → tsupport χ ⊆ Metric.closedBall 0 ρ →
              eLpNorm g ⊤ (volume : Measure (EuclideanSpace ℝ (Fin 1))) ≤
                (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) (ε + ρ))) ^ (1 / 2 : ℝ) *
                  eLpNorm (dg 0) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1)))) := by
  obtain ⟨u, T, hnorm, hmap, hU⟩ :=
    uniform_energy_same_witness (n := 1) (by norm_num) hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, fun S hSc => ?_⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, -, hvχ⟩ := hU S hSc
  refine ⟨α, β, B, hα, hβ, hB, hρB, fun v χ hχ hχc hχS => ?_⟩
  intro w a F
  obtain ⟨-, -, -, -, hcac, hlin⟩ := hvχ v χ hχ hχc hχS
  refine ⟨fun δ hδ p hp => (hcac δ hδ p hp).2.2.2, ?_⟩
  intro ε hε δ hδ r g dg
  obtain ⟨hgl, -, hgs, ⟨Cg, -, hgb⟩, -, hgd⟩ := hlin δ hδ r
  have hmain := eLpNorm_top_le_eLpNorm_weak_deriv_of_support_subset_one hgl hgb hχc hgs
    (fun k => (hgd k).2.2.1) (fun k => (hgd k).1) (fun k => (hgd k).2.2.2) hε
  refine ⟨hmain, fun ρ hρ hball => hmain.trans ?_⟩
  have hsub : Metric.cthickening ε (tsupport χ) ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) (ε + ρ) := by
    rw [← cthickening_closedBall hε.le hρ]
    exact Metric.cthickening_subset_of_subset ε hball
  gcongr

end DimOne

/-! ### Unified witness for the Moser inputs

The phase-two Moser inputs are combined at ONE witness, from ONE call of the original producer through the private
`uniform_source_data` above. The proof-local GIVEN-`u` helpers below are generic consequences of the source-data fields;
they bundle no source and no desired estimate. -/

open Filter

/-- Given bounded weak supersolution data on `tsupport χ`: the logarithmic data and energy, the exact linear data of
`g = χ s^r`, the coordinate energy, and the power energy for `r < 1/2` with its coordinate-norm form. -/
private theorem energy_block {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C α β F : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x)
    (hAm : ∀ i j : Fin n, AEStronglyMeasurable (fun x => A x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hα : 0 < α) (hβ : 0 < β) (hF : 0 ≤ F)
    (hcoeff : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)),
      (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (hsub : ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ)
        (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) → HasCompactSupport η →
      Function.support η ⊆ tsupport χ → (∀ x, 0 ≤ η x) →
      (∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, dotProduct (fun k => a k x) ((A x).mulVec (fun k => dη k x))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    :
    (∀ δ : ℝ, 0 < δ →
      let s := fun x => δ + max (w x) 0
      (∃ Bl : ℝ, 0 ≤ Bl ∧ ∀ x, ‖Real.log (s x)‖ ≤ Bl) ∧
      (∀ k : Fin n, HasWeakDerivAlong (fun x => Real.log (s x)) (fun x => (s x)⁻¹ * a k x) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
          MemLp (fun x => (s x)⁻¹ * a k x) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S')) ∧
      Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, ((s x)⁻¹ * a k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, χ x ^ 2 * ∑ k : Fin n, ((s x)⁻¹ * a k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        (4 * β / α) * (∫ x, ∑ k : Fin n, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
    (∀ δ : ℝ, 0 < δ → ∀ r : ℝ,
      let s := fun x => δ + max (w x) 0
      let g := fun x => χ x * s x ^ r
      let dg := fun (k : Fin n) x => fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r + χ x * (r * s x ^ (r - 1)) * a k x
      (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧ HasCompactSupport g ∧ Function.support g ⊆ tsupport (χ) ∧
        (∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x, ‖g x‖ ≤ Cg) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
        (∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧ HasCompactSupport (dg k) ∧
          Function.support (dg k) ⊆ tsupport (χ) ∧ MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∑ k : Fin n, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 ≤
          ((n : ℕ) : ENNReal) * ENNReal.ofReal (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (r < 1 / 2 →
          Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
              (∫ x, s x ^ (2 * r) * ∑ k : Fin n, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
          (∑ k : Fin n, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 ≤
            ((n : ℕ) : ENNReal) * ENNReal.ofReal
              ((2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                (∫ x, s x ^ (2 * r) * ∑ k : Fin n, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))))))
 := by
  refine ⟨fun δ hδ => ?_, fun δ hδ r => ?_⟩
  · intro s
    have hlog := hasWeakDerivAlong_log_max_shift_of_ae_nonneg_bounded hw hbound hweak ha2 hnonneg hδ
    have hle := bounded_weak_supersolution_log_caccioppoli hw hbound hweak ha2 hnonneg hAm hχ hχc hα hβ hF hcoeff hsub hδ
    exact ⟨hlog.2.1, hlog.2.2, hle.2.1, hle.2.2.2.2⟩
  · intro s g dg
    have hd := bounded_rpow_cutoff_weak_data hw hbound hweak ha2 hnonneg hχ hχc hδ r
    have hdm : ∀ k : Fin n, MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := fun k => (hd.2.2.2.2.2 k).2.2.2
    have hce := L2.sq_sum_eLpNorm_le_dim_mul_integral_sum_sq (volume : Measure (EuclideanSpace ℝ (Fin n))) hdm
    refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2, hce, fun hr => ?_⟩
    have hpe := bounded_weak_supersolution_power_energy hw hbound hweak ha2 hnonneg hAm hχ hχc hα hβ hF hcoeff hsub hδ hr
    exact ⟨hpe.1, hpe.2.2.2, hce.trans (by gcongr; exact hpe.2.2.2)⟩

/-- One `D > 0` before all radii: for every `R > 0` a dyadic family `χ m`, one on `closedBall 0 (R (1 + 2^{-(m+1)}))`,
supported in `closedBall 0 (R (1 + 2^{-m})) ⊆ closedBall 0 (2R)`, gap `R 2^{-(m+1)}`, `‖Dχ m‖ ≤ D 2^{m+1} / R`. -/
private theorem dyadic_cutoffs {n : ℕ} :
    ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 < R → ∃ χ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ, ∀ m : ℕ,
    (ContDiff ℝ ∞ (χ m) ∧ HasCompactSupport (χ m) ∧ (∀ x, 0 ≤ χ m x ∧ χ m x ≤ 1) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R * (1 + (1 / 2) ^ (m + 1))), χ m x = 1) ∧
      tsupport (χ m) ⊆ Metric.closedBall 0 (R * (1 + (1 / 2) ^ m)) ∧
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R * (1 + (1 / 2) ^ m)) ⊆ Metric.closedBall 0 (2 * R) ∧
      R * (1 + (1 / 2) ^ m) - R * (1 + (1 / 2) ^ (m + 1)) = R * (1 / 2) ^ (m + 1) ∧
      ∀ x, ‖fderiv ℝ (χ m) x‖ ≤ D * 2 ^ (m + 1) / R)
 := by
  obtain ⟨D, hD, hcut⟩ := exists_smooth_concentric_cutoff_norm_fderiv_le (E := EuclideanSpace ℝ (Fin n))
  refine ⟨D, hD, fun R hR => ?_⟩
  have hhalf (m : ℕ) : (1 / 2 : ℝ) ^ (m + 1) < (1 / 2) ^ m :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self m)
  have hgap (m : ℕ) : R * (1 + (1 / 2) ^ m) - R * (1 + (1 / 2) ^ (m + 1)) = R * (1 / 2) ^ (m + 1) := by
    rw [pow_succ]; ring
  have hlt (m : ℕ) : R * (1 + (1 / 2) ^ (m + 1)) < R * (1 + (1 / 2) ^ m) := by
    have := hhalf m
    nlinarith
  have hr0 (m : ℕ) : 0 ≤ R * (1 + (1 / 2) ^ (m + 1)) := by positivity
  have hex (m : ℕ) := hcut 0 (R * (1 + (1 / 2) ^ (m + 1))) (R * (1 + (1 / 2) ^ m)) (hr0 m) (hlt m)
  choose χ hχ using hex
  refine ⟨χ, fun m => ?_⟩
  obtain ⟨hsm, hcs, hts, h01, hone, -, hder⟩ := hχ m
  have hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R * (1 + (1 / 2) ^ m)) ⊆ Metric.closedBall 0 (2 * R) := by
    apply Metric.closedBall_subset_closedBall
    have : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hbound (x : EuclideanSpace ℝ (Fin n)) : ‖fderiv ℝ (χ m) x‖ ≤ D * 2 ^ (m + 1) / R := by
    refine (hder x).trans (le_of_eq ?_)
    rw [hgap m]
    field_simp
    rw [← mul_pow]
    norm_num
  exact ⟨hsm, hcs, h01, hone, hts, hball, hgap m, hbound⟩

/-- Given a locally integrable `w`, `ρ > 0` and `δ > 0`: the closed ball has finite nonzero volume `V`, its normalized
restricted volume `ν` is a probability measure, `f = (δ + max w 0)⁻¹` is essentially bounded, with the explicit norm
factor and the same essential supremum, and the `L^p` norms along every exponent sequence tending to infinity converge
to the essential supremum on the ball. -/
private theorem ball_limit {n : ℕ} {w : EuclideanSpace ℝ (Fin n) → ℝ} (hwl : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    let f := fun x => (δ + max (w x) 0)⁻¹
    let V := (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.closedBall 0 ρ)
    let ν := V⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 ρ)
    V ≠ 0 ∧ V ≠ ⊤ ∧ IsProbabilityMeasure ν ∧ MemLp f ⊤ ν ∧
    (∀ p : ENNReal, eLpNorm f p ν = V⁻¹ ^ (1 / p).toReal • eLpNorm f p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 ρ))) ∧
    eLpNorm f ⊤ ν = eLpNorm f ⊤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 ρ)) ∧
    ∀ p : ℕ → NNReal, Tendsto p atTop atTop →
      Tendsto (fun k => eLpNorm f (p k : ENNReal) ν) atTop (nhds (eLpNorm f ⊤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 ρ))))
 := by
  intro f V ν
  have hV0 : V ≠ 0 := (Metric.measure_closedBall_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 hρ).ne'
  have hVt : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hc0 : V⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hVt
  have hprob : IsProbabilityMeasure ν := by
    constructor
    simp only [ν, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hV0 hVt
  have hgc : Continuous fun t : ℝ => (δ + max t 0)⁻¹ :=
    (continuous_const.add (continuous_id.max continuous_const)).inv₀ fun t =>
      (show (0 : ℝ) < δ + max t 0 by linarith [le_max_right t 0]).ne'
  have hfm : AEStronglyMeasurable f (volume : Measure (EuclideanSpace ℝ (Fin n))) := hgc.comp_aestronglyMeasurable hwl.aestronglyMeasurable
  have hfb (x : EuclideanSpace ℝ (Fin n)) : ‖f x‖ ≤ δ⁻¹ := by
    have h0 : 0 ≤ max (w x) 0 := le_max_right _ _
    have hpos : 0 < δ + max (w x) 0 := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    exact inv_anti₀ hδ (le_add_of_nonneg_right h0)
  have hfν : MemLp f ⊤ ν := memLp_top_of_bound (hfm.restrict.smul_measure _) δ⁻¹ (ae_of_all _ hfb)
  have hfac (p : ENNReal) : eLpNorm f p ν =
      V⁻¹ ^ (1 / p).toReal • eLpNorm f p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 ρ)) :=
    eLpNorm_smul_measure_of_ne_zero hc0 f p _
  have htop : eLpNorm f ⊤ ν = eLpNorm f ⊤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 ρ)) := by
    rw [hfac ⊤]
    simp
  refine ⟨hV0, hVt, hprob, hfν, hfac, htop, fun p hp => ?_⟩
  rw [← htop]
  exact tendsto_eLpNorm_of_exponents_tendsto_atTop ν hfν p hp

/-- In dimension two, the energy block for `χ` together with the finite-exponent Sobolev bounds of the SAME `g, dg`:
every finite `q ≥ 2`, and the `q = 2` and `q = 6` (canonical `L⁶`) instances. -/
private theorem block_two_extend {w : EuclideanSpace ℝ (Fin 2) → ℝ} {a : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ} {α β F : ℝ} {χ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hχc : HasCompactSupport χ)
    (h :
    (∀ δ : ℝ, 0 < δ →
      let s := fun x => δ + max (w x) 0
      (∃ Bl : ℝ, 0 ≤ Bl ∧ ∀ x, ‖Real.log (s x)‖ ≤ Bl) ∧
      (∀ k : Fin 2, HasWeakDerivAlong (fun x => Real.log (s x)) (fun x => (s x)⁻¹ * a k x) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧
        ∀ S' : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S' →
          MemLp (fun x => (s x)⁻¹ * a k x) 2 ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S')) ∧
      Integrable (fun x => χ x ^ 2 * ∑ k : Fin 2, ((s x)⁻¹ * a k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
      (∫ x, χ x ^ 2 * ∑ k : Fin 2, ((s x)⁻¹ * a k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
        (4 * β / α) * (∫ x, ∑ k : Fin 2, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
        (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))) ∧
    (∀ δ : ℝ, 0 < δ → ∀ r : ℝ,
      let s := fun x => δ + max (w x) 0
      let g := fun x => χ x * s x ^ r
      let dg := fun (k : Fin 2) x => fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k) * s x ^ r + χ x * (r * s x ^ (r - 1)) * a k x
      (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧ HasCompactSupport g ∧ Function.support g ⊆ tsupport (χ) ∧
        (∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x, ‖g x‖ ≤ Cg) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
        (∀ k : Fin 2, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧ HasCompactSupport (dg k) ∧
          Function.support (dg k) ⊆ tsupport (χ) ∧ MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
        (∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ^ 2 ≤
          ((2 : ℕ) : ENNReal) * ENNReal.ofReal (∫ x, ∑ k : Fin 2, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
        (r < 1 / 2 →
          Integrable (fun x => ∑ k : Fin 2, (dg k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
          (∫ x, ∑ k : Fin 2, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
            (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
              (∫ x, s x ^ (2 * r) * ∑ k : Fin 2, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
            (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
          (∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ^ 2 ≤
            ((2 : ℕ) : ENNReal) * ENNReal.ofReal
              ((2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                (∫ x, s x ^ (2 * r) * ∑ k : Fin 2, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
              (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))))))
    ) :
    (∀ δ : ℝ, 0 < δ →
      let s := fun x => δ + max (w x) 0
      (∃ Bl : ℝ, 0 ≤ Bl ∧ ∀ x, ‖Real.log (s x)‖ ≤ Bl) ∧
      (∀ k : Fin 2, HasWeakDerivAlong (fun x => Real.log (s x)) (fun x => (s x)⁻¹ * a k x) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧
        ∀ S' : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S' →
          MemLp (fun x => (s x)⁻¹ * a k x) 2 ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S')) ∧
      Integrable (fun x => χ x ^ 2 * ∑ k : Fin 2, ((s x)⁻¹ * a k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
      (∫ x, χ x ^ 2 * ∑ k : Fin 2, ((s x)⁻¹ * a k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
        (4 * β / α) * (∫ x, ∑ k : Fin 2, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
        (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))) ∧
    (∀ δ : ℝ, 0 < δ → ∀ r : ℝ,
      let s := fun x => δ + max (w x) 0
      let g := fun x => χ x * s x ^ r
      let dg := fun (k : Fin 2) x => fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k) * s x ^ r + χ x * (r * s x ^ (r - 1)) * a k x
      (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧ HasCompactSupport g ∧ Function.support g ⊆ tsupport (χ) ∧
        (∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x, ‖g x‖ ≤ Cg) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
        (∀ k : Fin 2, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧ HasCompactSupport (dg k) ∧
          Function.support (dg k) ⊆ tsupport (χ) ∧ MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
        (∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ^ 2 ≤
          ((2 : ℕ) : ENNReal) * ENNReal.ofReal (∫ x, ∑ k : Fin 2, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
        (r < 1 / 2 →
          Integrable (fun x => ∑ k : Fin 2, (dg k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
          (∫ x, ∑ k : Fin 2, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
            (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
              (∫ x, s x ^ (2 * r) * ∑ k : Fin 2, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
            (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
          (∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ^ 2 ≤
            ((2 : ℕ) : ENNReal) * ENNReal.ofReal
              ((2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                (∫ x, s x ^ (2 * r) * ∑ k : Fin 2, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
              (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))))) ∧
      ((∀ ε : ℝ, 0 < ε → ∀ q : NNReal, 2 ≤ q →
          eLpNorm g q (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
            (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (2 * q / (q + 2)) : ENNReal) *
              (volume (Metric.cthickening ε (tsupport (χ)))) ^ ((q : ℝ)⁻¹) * ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
        (∀ ε : ℝ, 0 < ε →
          eLpNorm g 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
            (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) 1 : ENNReal) *
              (volume (Metric.cthickening ε (tsupport (χ)))) ^ (1 / 2 : ℝ) * ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
        (∀ ε : ℝ, 0 < ε →
          eLpNorm g 6 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
            (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (3 / 2) : ENNReal) *
              (volume (Metric.cthickening ε (tsupport (χ)))) ^ (1 / 6 : ℝ) * ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))))
 := by
  refine ⟨h.1, fun δ hδ r => ?_⟩
  intro s g dg
  obtain ⟨hgl, -, hgs, ⟨Cg, -, hgb⟩, -, hgd, -, -⟩ := h.2 δ hδ r
  refine ⟨h.2 δ hδ r, fun ε hε q hq => ?_, fun ε hε => ?_, fun ε hε => ?_⟩
  · exact eLpNorm_finite_le_sum_eLpNorm_weak_deriv_of_support_subset_two hgl hgb hχc hgs (fun k => (hgd k).2.2.1)
      (fun k => (hgd k).1) (fun k => (hgd k).2.2.2) hε hq
  · convert eLpNorm_finite_le_sum_eLpNorm_weak_deriv_of_support_subset_two hgl hgb hχc hgs (fun k => (hgd k).2.2.1)
      (fun k => (hgd k).1) (fun k => (hgd k).2.2.2) hε (q := (2 : NNReal)) le_rfl using 3 <;> norm_num
  · exact eLpNorm_six_le_sum_eLpNorm_weak_deriv_of_support_subset_two hgl hgb hχc hgs (fun k => (hgd k).2.2.1)
      (fun k => (hgd k).1) (fun k => (hgd k).2.2.2) hε

section UnifiedWitness

variable {n : ℕ} (hn : 0 < n)
  {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- **Moser inputs at ONE witness (general `n > 0`).** One call of the original producer gives ONE `u, T`, with the
normalization and the actual gradient pushforward. ONE `D > 0` is fixed before every compact set and radius. For each
compact `S`, ONE `α, β, B` (`e^{-u} ≤ B` and `α ≤ e^{-u}(∇²u)⁻¹ ≤ β` a.e. on `S`) serves:
* every direction `v` and every `C¹` compactly supported cutoff with `tsupport χ ⊆ S`;
* for every `R > 0` with `closedBall 0 (2R) ⊆ S`, one dyadic family `χ m` (chosen before `m`, `v`, `δ`, `r`) for every
  `m` and every `v`.
Each such cutoff gets, at `w = M_v − vᵀ∇²u v`, `a = −∂(vᵀ∇²u v)` and `F_v = M_v · B`:
* the actual logarithmic data and logarithmic energy;
* the exact linear data of `g = χ s^r`, the coordinate `L²` energy, and the power energy for `r < 1/2`.
At the same `u`, the normalized closed-ball `L^p → L^∞` limit of `(δ + max w 0)⁻¹` holds. These are inputs, not the Moser
recurrence, John–Nirenberg or a Harnack inequality. -/
theorem moser_inputs_unified_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) = (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧
      (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧ (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        (∀ (v : Fin n → ℝ) (χ : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ 1 χ → HasCompactSupport χ → tsupport χ ⊆ S →
          let w := fun x => (16 / κ) * (∑ i : Fin n, v i ^ 2) - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := (16 / κ) * (∑ i : Fin n, v i ^ 2) * B
          (∀ δ : ℝ, 0 < δ →
            let s := fun x => δ + max (w x) 0
            (∃ Bl : ℝ, 0 ≤ Bl ∧ ∀ x, ‖Real.log (s x)‖ ≤ Bl) ∧
            (∀ k : Fin n, HasWeakDerivAlong (fun x => Real.log (s x)) (fun x => (s x)⁻¹ * a k x) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
                MemLp (fun x => (s x)⁻¹ * a k x) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S')) ∧
            Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, ((s x)⁻¹ * a k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∫ x, χ x ^ 2 * ∑ k : Fin n, ((s x)⁻¹ * a k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / α) * (∫ x, ∑ k : Fin n, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
          (∀ δ : ℝ, 0 < δ → ∀ r : ℝ,
            let s := fun x => δ + max (w x) 0
            let g := fun x => χ x * s x ^ r
            let dg := fun (k : Fin n) x => fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r + χ x * (r * s x ^ (r - 1)) * a k x
            (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧ HasCompactSupport g ∧ Function.support g ⊆ tsupport (χ) ∧
              (∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x, ‖g x‖ ≤ Cg) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
              (∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧ HasCompactSupport (dg k) ∧
                Function.support (dg k) ⊆ tsupport (χ) ∧ MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
              (∑ k : Fin n, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 ≤
                ((n : ℕ) : ENNReal) * ENNReal.ofReal (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
              (r < 1 / 2 →
                Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
                (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                  (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                    (∫ x, s x ^ (2 * r) * ∑ k : Fin n, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
                  (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
                (∑ k : Fin n, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 ≤
                  ((n : ℕ) : ENNReal) * ENNReal.ofReal
                    ((2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                      (∫ x, s x ^ (2 * r) * ∑ k : Fin n, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
                    (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))))))) ∧
        (∀ R : ℝ, 0 < R → Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * R) ⊆ S →
          ∃ χ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ, ∀ m : ℕ,
            (ContDiff ℝ ∞ (χ m) ∧ HasCompactSupport (χ m) ∧ (∀ x, 0 ≤ χ m x ∧ χ m x ≤ 1) ∧
              (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R * (1 + (1 / 2) ^ (m + 1))), χ m x = 1) ∧
              tsupport (χ m) ⊆ Metric.closedBall 0 (R * (1 + (1 / 2) ^ m)) ∧
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R * (1 + (1 / 2) ^ m)) ⊆ Metric.closedBall 0 (2 * R) ∧
              R * (1 + (1 / 2) ^ m) - R * (1 + (1 / 2) ^ (m + 1)) = R * (1 / 2) ^ (m + 1) ∧
              ∀ x, ‖fderiv ℝ (χ m) x‖ ≤ D * 2 ^ (m + 1) / R) ∧
            ∀ v : Fin n → ℝ,
              let w := fun x => (16 / κ) * (∑ i : Fin n, v i ^ 2) - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
              let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
              let F := (16 / κ) * (∑ i : Fin n, v i ^ 2) * B
              (∀ δ : ℝ, 0 < δ →
                let s := fun x => δ + max (w x) 0
                (∃ Bl : ℝ, 0 ≤ Bl ∧ ∀ x, ‖Real.log (s x)‖ ≤ Bl) ∧
                (∀ k : Fin n, HasWeakDerivAlong (fun x => Real.log (s x)) (fun x => (s x)⁻¹ * a k x) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                  ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
                    MemLp (fun x => (s x)⁻¹ * a k x) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S')) ∧
                Integrable (fun x => χ m x ^ 2 * ∑ k : Fin n, ((s x)⁻¹ * a k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
                (∫ x, χ m x ^ 2 * ∑ k : Fin n, ((s x)⁻¹ * a k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                  (4 * β / α) * (∫ x, ∑ k : Fin n, (fderiv ℝ (χ m) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
                  (2 * F / (α * δ)) * (∫ x, χ m x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
              (∀ δ : ℝ, 0 < δ → ∀ r : ℝ,
                let s := fun x => δ + max (w x) 0
                let g := fun x => χ m x * s x ^ r
                let dg := fun (k : Fin n) x => fderiv ℝ (χ m) x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r + χ m x * (r * s x ^ (r - 1)) * a k x
                (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧ HasCompactSupport g ∧ Function.support g ⊆ tsupport (χ m) ∧
                  (∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x, ‖g x‖ ≤ Cg) ∧ ((∀ x, 0 ≤ χ m x) → ∀ x, 0 ≤ g x) ∧
                  (∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧ HasCompactSupport (dg k) ∧
                    Function.support (dg k) ⊆ tsupport (χ m) ∧ MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
                  (∑ k : Fin n, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 ≤
                    ((n : ℕ) : ENNReal) * ENNReal.ofReal (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
                  (r < 1 / 2 →
                    Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
                    (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                      (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                        (∫ x, s x ^ (2 * r) * ∑ k : Fin n, (fderiv ℝ (χ m) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
                      (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ m x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
                    (∑ k : Fin n, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 ≤
                      ((n : ℕ) : ENNReal) * ENNReal.ofReal
                        ((2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                          (∫ x, s x ^ (2 * r) * ∑ k : Fin n, (fderiv ℝ (χ m) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
                        (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ m x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))))))) ∧
      (∀ (v : Fin n → ℝ) (ρ δ : ℝ), 0 < ρ → 0 < δ →
        let w := fun x => (16 / κ) * (∑ i : Fin n, v i ^ 2) - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
        let f := fun x => (δ + max (w x) 0)⁻¹
        let V := (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.closedBall 0 ρ)
        let ν := V⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 ρ)
        V ≠ 0 ∧ V ≠ ⊤ ∧ IsProbabilityMeasure ν ∧ MemLp f ⊤ ν ∧
        (∀ p : ENNReal, eLpNorm f p ν = V⁻¹ ^ (1 / p).toReal • eLpNorm f p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 ρ))) ∧
        eLpNorm f ⊤ ν = eLpNorm f ⊤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 ρ)) ∧
        ∀ p : ℕ → NNReal, Tendsto p atTop atTop →
          Tendsto (fun k => eLpNorm f (p k : ENNReal) ν) atTop (nhds (eLpNorm f ⊤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 ρ)))))
 := by
  obtain ⟨u, T, hnorm, hmap, hAm, hS⟩ := uniform_source_data hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨D, hD, hdy⟩ := dyadic_cutoffs (n := n)
  refine ⟨u, T, hnorm, hmap, D, hD, fun S hSc => ?_, fun v ρ δ hρ hδ => ?_⟩
  · obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hvχ⟩ := hS S hSc
    have hF (v : Fin n → ℝ) : 0 ≤ (16 / κ) * (∑ i : Fin n, v i ^ 2) * B :=
      mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hB
    refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, fun v χ hχ hχc hχS => ?_, fun R hR hRS => ?_⟩
    · obtain ⟨hwl, ⟨Cw, hwb⟩, hww, ha2, hw0, hsub⟩ := hvχ v χ hχS
      exact energy_block hwl hwb hww ha2 hw0 hAm hχ hχc hα hβ (hF v) (ae_restrict_of_ae_restrict_of_subset hχS hcb) hsub
    · obtain ⟨χ, hχ⟩ := hdy R hR
      refine ⟨χ, fun m => ⟨hχ m, fun v => ?_⟩⟩
      obtain ⟨hsm, hcs, -, -, hts, hball, -, -⟩ := hχ m
      have hχS : tsupport (χ m) ⊆ S := (hts.trans hball).trans hRS
      obtain ⟨hwl, ⟨Cw, hwb⟩, hww, ha2, hw0, hsub⟩ := hvχ v (χ m) hχS
      exact energy_block hwl hwb hww ha2 hw0 hAm (hsm.of_le (by exact_mod_cast le_top)) hcs hα hβ (hF v)
        (ae_restrict_of_ae_restrict_of_subset hχS hcb) hsub
  · -- measurability of the same `w` from the same source data (the zero cutoff has empty support)
    obtain ⟨α₀, β₀, B₀, -, -, -, -, -, hvχ₀⟩ := hS (Metric.closedBall 0 ρ) (isCompact_closedBall 0 ρ)
    obtain ⟨hwl, -⟩ := hvχ₀ v (fun _ => 0) (by simp)
    exact ball_limit hwl hρ hδ

end UnifiedWitness

section UnifiedWitnessTwo

variable {K : Set (EuclideanSpace ℝ (Fin 2))} {W : EuclideanSpace ℝ (Fin 2) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin 2))) =
    (volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hκ hK hKc hKint hW hstrong hμ hiso

/-- **Moser inputs at ONE witness in dimension two.** The statement of `moser_inputs_unified_same_witness` at `n = 2`,
and for every cutoff (arbitrary, or dyadic) and every `δ, r` the finite-exponent Sobolev bounds of the SAME `g, dg`:
every finite `q ≥ 2`, and the `q = 2` and `q = 6` instances. Its ONE witness is the witness of the general theorem at
`n = 2`; the Sobolev side uses that witness and selects no new source. -/
theorem moser_inputs_unified_two_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin 2) → ℝ) (T : EuclideanSpace ℝ (Fin 2) → Fin 2 → Fin 2 → Fin 2 → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).tilted (-u)).map (gradient u) = (μ : Measure (EuclideanSpace ℝ (Fin 2))) ∧
      ∃ D : ℝ, 0 < D ∧
      (∀ S : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧ (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin 2) (Fin 2) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        (∀ (v : Fin 2 → ℝ) (χ : EuclideanSpace ℝ (Fin 2) → ℝ), ContDiff ℝ 1 χ → HasCompactSupport χ → tsupport χ ⊆ S →
          let w := fun x => (16 / κ) * (∑ i : Fin 2, v i ^ 2) - ∑ i : Fin 2, ∑ j : Fin 2, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin 2) x => -(∑ i : Fin 2, ∑ j : Fin 2, v i * v j * T x k i j)
          let F := (16 / κ) * (∑ i : Fin 2, v i ^ 2) * B
          (∀ δ : ℝ, 0 < δ →
            let s := fun x => δ + max (w x) 0
            (∃ Bl : ℝ, 0 ≤ Bl ∧ ∀ x, ‖Real.log (s x)‖ ≤ Bl) ∧
            (∀ k : Fin 2, HasWeakDerivAlong (fun x => Real.log (s x)) (fun x => (s x)⁻¹ * a k x) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧
              ∀ S' : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S' →
                MemLp (fun x => (s x)⁻¹ * a k x) 2 ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S')) ∧
            Integrable (fun x => χ x ^ 2 * ∑ k : Fin 2, ((s x)⁻¹ * a k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
            (∫ x, χ x ^ 2 * ∑ k : Fin 2, ((s x)⁻¹ * a k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
              (4 * β / α) * (∫ x, ∑ k : Fin 2, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
              (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))) ∧
          (∀ δ : ℝ, 0 < δ → ∀ r : ℝ,
            let s := fun x => δ + max (w x) 0
            let g := fun x => χ x * s x ^ r
            let dg := fun (k : Fin 2) x => fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k) * s x ^ r + χ x * (r * s x ^ (r - 1)) * a k x
            (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧ HasCompactSupport g ∧ Function.support g ⊆ tsupport (χ) ∧
              (∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x, ‖g x‖ ≤ Cg) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
              (∀ k : Fin 2, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧ HasCompactSupport (dg k) ∧
                Function.support (dg k) ⊆ tsupport (χ) ∧ MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
              (∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ^ 2 ≤
                ((2 : ℕ) : ENNReal) * ENNReal.ofReal (∫ x, ∑ k : Fin 2, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
              (r < 1 / 2 →
                Integrable (fun x => ∑ k : Fin 2, (dg k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
                (∫ x, ∑ k : Fin 2, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
                  (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                    (∫ x, s x ^ (2 * r) * ∑ k : Fin 2, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
                  (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
                (∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ^ 2 ≤
                  ((2 : ℕ) : ENNReal) * ENNReal.ofReal
                    ((2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                      (∫ x, s x ^ (2 * r) * ∑ k : Fin 2, (fderiv ℝ (χ) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
                    (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))))) ∧
            ((∀ ε : ℝ, 0 < ε → ∀ q : NNReal, 2 ≤ q →
                eLpNorm g q (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
                  (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (2 * q / (q + 2)) : ENNReal) *
                    (volume (Metric.cthickening ε (tsupport (χ)))) ^ ((q : ℝ)⁻¹) * ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
              (∀ ε : ℝ, 0 < ε →
                eLpNorm g 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
                  (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) 1 : ENNReal) *
                    (volume (Metric.cthickening ε (tsupport (χ)))) ^ (1 / 2 : ℝ) * ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
              (∀ ε : ℝ, 0 < ε →
                eLpNorm g 6 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
                  (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (3 / 2) : ENNReal) *
                    (volume (Metric.cthickening ε (tsupport (χ)))) ^ (1 / 6 : ℝ) * ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))))) ∧
        (∀ R : ℝ, 0 < R → Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (2 * R) ⊆ S →
          ∃ χ : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ, ∀ m : ℕ,
            (ContDiff ℝ ∞ (χ m) ∧ HasCompactSupport (χ m) ∧ (∀ x, 0 ≤ χ m x ∧ χ m x ≤ 1) ∧
              (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (R * (1 + (1 / 2) ^ (m + 1))), χ m x = 1) ∧
              tsupport (χ m) ⊆ Metric.closedBall 0 (R * (1 + (1 / 2) ^ m)) ∧
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (R * (1 + (1 / 2) ^ m)) ⊆ Metric.closedBall 0 (2 * R) ∧
              R * (1 + (1 / 2) ^ m) - R * (1 + (1 / 2) ^ (m + 1)) = R * (1 / 2) ^ (m + 1) ∧
              ∀ x, ‖fderiv ℝ (χ m) x‖ ≤ D * 2 ^ (m + 1) / R) ∧
            ∀ v : Fin 2 → ℝ,
              let w := fun x => (16 / κ) * (∑ i : Fin 2, v i ^ 2) - ∑ i : Fin 2, ∑ j : Fin 2, v i * v j * hessianMatrix u x i j
              let a := fun (k : Fin 2) x => -(∑ i : Fin 2, ∑ j : Fin 2, v i * v j * T x k i j)
              let F := (16 / κ) * (∑ i : Fin 2, v i ^ 2) * B
              (∀ δ : ℝ, 0 < δ →
                let s := fun x => δ + max (w x) 0
                (∃ Bl : ℝ, 0 ≤ Bl ∧ ∀ x, ‖Real.log (s x)‖ ≤ Bl) ∧
                (∀ k : Fin 2, HasWeakDerivAlong (fun x => Real.log (s x)) (fun x => (s x)⁻¹ * a k x) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧
                  ∀ S' : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S' →
                    MemLp (fun x => (s x)⁻¹ * a k x) 2 ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S')) ∧
                Integrable (fun x => χ m x ^ 2 * ∑ k : Fin 2, ((s x)⁻¹ * a k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
                (∫ x, χ m x ^ 2 * ∑ k : Fin 2, ((s x)⁻¹ * a k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
                  (4 * β / α) * (∫ x, ∑ k : Fin 2, (fderiv ℝ (χ m) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
                  (2 * F / (α * δ)) * (∫ x, χ m x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))) ∧
              (∀ δ : ℝ, 0 < δ → ∀ r : ℝ,
                let s := fun x => δ + max (w x) 0
                let g := fun x => χ m x * s x ^ r
                let dg := fun (k : Fin 2) x => fderiv ℝ (χ m) x (EuclideanSpace.basisFun (Fin 2) ℝ k) * s x ^ r + χ m x * (r * s x ^ (r - 1)) * a k x
                (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧ HasCompactSupport g ∧ Function.support g ⊆ tsupport (χ m) ∧
                  (∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x, ‖g x‖ ≤ Cg) ∧ ((∀ x, 0 ≤ χ m x) → ∀ x, 0 ≤ g x) ∧
                  (∀ k : Fin 2, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧ HasCompactSupport (dg k) ∧
                    Function.support (dg k) ⊆ tsupport (χ m) ∧ MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
                  (∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ^ 2 ≤
                    ((2 : ℕ) : ENNReal) * ENNReal.ofReal (∫ x, ∑ k : Fin 2, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
                  (r < 1 / 2 →
                    Integrable (fun x => ∑ k : Fin 2, (dg k x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin 2))) ∧
                    (∫ x, ∑ k : Fin 2, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ≤
                      (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                        (∫ x, s x ^ (2 * r) * ∑ k : Fin 2, (fderiv ℝ (χ m) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
                      (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ m x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
                    (∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ^ 2 ≤
                      ((2 : ℕ) : ENNReal) * ENNReal.ofReal
                        ((2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                          (∫ x, s x ^ (2 * r) * ∑ k : Fin 2, (fderiv ℝ (χ m) x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin 2)))) +
                        (4 * r ^ 2 * F / ((1 - 2 * r) * α)) * (∫ x, χ m x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))))))) ∧
                ((∀ ε : ℝ, 0 < ε → ∀ q : NNReal, 2 ≤ q →
                    eLpNorm g q (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
                      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (2 * q / (q + 2)) : ENNReal) *
                        (volume (Metric.cthickening ε (tsupport (χ m)))) ^ ((q : ℝ)⁻¹) * ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
                  (∀ ε : ℝ, 0 < ε →
                    eLpNorm g 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
                      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) 1 : ENNReal) *
                        (volume (Metric.cthickening ε (tsupport (χ m)))) ^ (1 / 2 : ℝ) * ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))) ∧
                  (∀ ε : ℝ, 0 < ε →
                    eLpNorm g 6 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
                      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (3 / 2) : ENNReal) *
                        (volume (Metric.cthickening ε (tsupport (χ m)))) ^ (1 / 6 : ℝ) * ∑ k : Fin 2, eLpNorm (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2)))))))) ∧
      (∀ (v : Fin 2 → ℝ) (ρ δ : ℝ), 0 < ρ → 0 < δ →
        let w := fun x => (16 / κ) * (∑ i : Fin 2, v i ^ 2) - ∑ i : Fin 2, ∑ j : Fin 2, v i * v j * hessianMatrix u x i j
        let f := fun x => (δ + max (w x) 0)⁻¹
        let V := (volume : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.closedBall 0 ρ)
        let ν := V⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.closedBall 0 ρ)
        V ≠ 0 ∧ V ≠ ⊤ ∧ IsProbabilityMeasure ν ∧ MemLp f ⊤ ν ∧
        (∀ p : ENNReal, eLpNorm f p ν = V⁻¹ ^ (1 / p).toReal • eLpNorm f p ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.closedBall 0 ρ))) ∧
        eLpNorm f ⊤ ν = eLpNorm f ⊤ ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.closedBall 0 ρ)) ∧
        ∀ p : ℕ → NNReal, Tendsto p atTop atTop →
          Tendsto (fun k => eLpNorm f (p k : ENNReal) ν) atTop (nhds (eLpNorm f ⊤ ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.closedBall 0 ρ)))))
 := by
  obtain ⟨u, T, hnorm, hmap, D, hD, hS, hE⟩ :=
    moser_inputs_unified_same_witness (n := 2) (by norm_num) hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, D, hD, fun S hSc => ?_, hE⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hvχ, hdy⟩ := hS S hSc
  refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, fun v χ hχ hχc hχS => ?_, fun R hR hRS => ?_⟩
  · intro w a F
    exact block_two_extend hχc (hvχ v χ hχ hχc hχS)
  · obtain ⟨χ, hχ⟩ := hdy R hR hRS
    refine ⟨χ, fun m => ⟨(hχ m).1, fun v => ?_⟩⟩
    intro w a F
    exact block_two_extend (hχ m).1.2.1 ((hχ m).2 v)

end UnifiedWitnessTwo

/-! ### All-ball Morrey bounds and the critical potential at one witness -/

section MorreyWitness

open Metric
open scoped ENNReal

variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- **All-ball Morrey bound of the actual logarithmic gradient at ONE witness.** One `u, T`; one `D_M > 0` before every
radius; for each `R > 0` one `α, β, B` on `closedBall 0 (4R)`; then for EVERY direction `v` and EVERY `δ > 0`:
* the exact weak derivatives `b_k = (δ + max w 0)⁻¹ a_k` of `log (δ + max w 0)`, in `L²_loc`;
* for EVERY center `c` and EVERY radius `r > 0`, `∫_{B_R ∩ B_r(c)} √(Σ b_k²) ≤ K r^{n-1}`, where
  `K = ω_n 2^n (1 + (4β/α) n D_M² + (2F_v/(αδ)) R²)`;
* when `F_v R² ≤ α δ`, the forcing-normalized bound `K ≤ ω_n 2^n (3 + 4β n D_M²/α)`, independent of `δ` and `F_v`. -/
theorem actual_log_gradient_morrey_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ DM : ℝ, 0 < DM ∧ ∀ R : ℝ, 0 < R →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R), Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∀ (v : Fin n → ℝ) (δ : ℝ), 0 < δ →
          let w := fun x => (16 / κ) * (∑ i : Fin n, v i ^ 2) -
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := (16 / κ) * (∑ i : Fin n, v i ^ 2) * B
          let bk := fun (k : Fin n) x => (δ + max (w x) 0)⁻¹ * a k x
          let KM := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (2 : ℝ) ^ n *
            (1 + (4 * β / α) * (n : ℝ) * DM ^ 2 + (2 * F / (α * δ)) * R ^ 2)
          (∀ k : Fin n, HasWeakDerivAlong (fun x => Real.log (δ + max (w x) 0)) (bk k)
              (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
            ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
              MemLp (bk k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S')) ∧
          (∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
            (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) R ∩ ball c r,
              ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (bk k x) ^ 2))) ≤
              ENNReal.ofReal (KM * r ^ ((n : ℝ) - 1))) ∧
          (F * R ^ 2 ≤ α * δ →
            KM ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (2 : ℝ) ^ n *
              (3 + 4 * β * (n : ℝ) * DM ^ 2 / α)) := by
  -- the master origin-dyadic constant `D0` is not needed here (it need not equal `D_M`)
  obtain ⟨u, T, hnorm, hmap, D0, _hD0, hS, -⟩ :=
    moser_inputs_unified_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨DM, hDM, hmorrey⟩ := exists_morrey_bound_of_cutoff_energy hn
  refine ⟨u, T, hnorm, hmap, DM, hDM, fun R hR => ?_⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hvχ, -⟩ :=
    hS (closedBall 0 (4 * R)) (isCompact_closedBall 0 (4 * R))
  refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, fun v δ hδ => ?_⟩
  intro w a F bk KM
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hB
  -- the actual logarithmic weak data, from the master at the zero cutoff (empty support)
  have h0 := hvχ v (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp)
  have hlog : ∀ k : Fin n, HasWeakDerivAlong (fun x => Real.log (δ + max (w x) 0)) (bk k)
      (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
        MemLp (bk k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') :=
    (h0.1 δ hδ).2.1
  refine ⟨hlog, fun c r hr => ?_, fun hFR => ?_⟩
  · -- the master's logarithmic energy for every admissible cutoff in `closedBall 0 (4R)`
    have henergy : ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
        tsupport χ ⊆ closedBall 0 (4 * R) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        Integrable (fun x => χ x ^ 2 * ∑ i : Fin n, (bk i x) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, χ x ^ 2 * ∑ i : Fin n, (bk i x) ^ 2) ≤
          (4 * β / α) * (∫ x, ∑ i : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) +
          (2 * F / (α * δ)) * (∫ x, χ x ^ 2) := by
      intro χ hχ hχc hχS _h01
      have hb := (hvχ v χ hχ hχc hχS).1 δ hδ
      exact ⟨hb.2.2.1, hb.2.2.2⟩
    exact hmorrey R (4 * β / α) (2 * F / (α * δ)) bk hR (by positivity) (by positivity)
      (fun i => (hlog i).1.2.1.aestronglyMeasurable) (fun i => (hlog i).2) henergy c r hr
  · -- forcing normalization
    have hE1 : (2 * F / (α * δ)) * R ^ 2 ≤ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hvol : 0 ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (2 : ℝ) ^ n := by positivity
    have he : (4 * β / α) * (n : ℝ) * DM ^ 2 = 4 * β * (n : ℝ) * DM ^ 2 / α := by ring
    dsimp only [KM]
    rw [he]
    apply mul_le_mul_of_nonneg_left _ hvol
    linarith

/-- **Exponential integrability of the actual critical potential at ONE witness** (`n ≥ 2`). The witness, `D_M`, and for
each `R > 0` the coefficients `α, β, B` on `closedBall 0 (4R)` are those of ONE call of
`actual_log_gradient_morrey_same_witness`; no source is reselected. For every direction `v` and `δ > 0`, with the actual
logarithmic gradient `b_k = (δ + max w 0)⁻¹ a_k` and `f = √(Σ b_k²)` on `B_R`:
* the weak logarithmic data and the ALL-ball Morrey bound with `K_M = ω_n 2^n (1 + (4β/α) n D_M² + (2F_v/(αδ)) R²)`,
  where `K_M > 0` is derived;
* the potential `P(x) = ∫_{B_R} |x - y|^{1-n} f(y) dy` is finite a.e. on `B_R`, `exp(P/(2e(n-1)K_M))` is integrable on
  `B_R`, and its integral is at most `2 ω_n n/(n-1) (1 + 4(n-1)²) (2R)^n`.
This is the exponential integrability of the critical POTENTIAL of the logarithmic gradient. It is not the exponential
integrability of `log − mean`, which needs the weak-Sobolev oscillation bound of GT Lemma 7.16; it is not John–Nirenberg
or a weak Harnack inequality. -/
theorem actual_log_gradient_potential_exp_same_witness (h2 : 2 ≤ n) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) = (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ DM : ℝ, 0 < DM ∧ ∀ R : ℝ, 0 < R →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R), Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∀ (v : Fin n → ℝ) (δ : ℝ), 0 < δ →
          let w := fun x => (16 / κ) * (∑ i : Fin n, v i ^ 2) -
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := (16 / κ) * (∑ i : Fin n, v i ^ 2) * B
          let bk := fun (k : Fin n) x => (δ + max (w x) 0)⁻¹ * a k x
          let KM := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (2 : ℝ) ^ n *
            (1 + (4 * β / α) * (n : ℝ) * DM ^ 2 + (2 * F / (α * δ)) * R ^ 2)
          let f := fun x => Real.sqrt (∑ k : Fin n, (bk k x) ^ 2)
          let P := fun x => ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin n)) R, ENNReal.ofReal (‖y - x‖ ^ (1 - (n : ℝ)) * |f y|)
          let σ := (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹
          (∀ k : Fin n, HasWeakDerivAlong (fun x => Real.log (δ + max (w x) 0)) (bk k)
              (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
            ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' → MemLp (bk k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S')) ∧
          (∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
            (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) R ∩ ball c r, ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (bk k x) ^ 2))) ≤
              ENNReal.ofReal (KM * r ^ ((n : ℝ) - 1))) ∧
          0 < KM ∧ 0 < σ ∧
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 R)), P x < ⊤) ∧
          Integrable (fun x => Real.exp ((σ / KM) * (P x).toReal)) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 R)) ∧
          (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R, Real.exp ((σ / KM) * (P x).toReal)) ≤
            2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) * (1 + 4 * ((n : ℝ) - 1) ^ 2)) *
              (2 * R) ^ (n : ℝ) := by
  obtain ⟨u, T, hnorm, hmap, DM, hDM, hR⟩ :=
    actual_log_gradient_morrey_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, DM, hDM, fun R hRpos => ?_⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hv⟩ := hR R hRpos
  refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, fun v δ hδ => ?_⟩
  intro w a F bk KM f P σ
  obtain ⟨hlog, hmor, -⟩ := hv v δ hδ
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hB
  have hω : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) :=
    ENNReal.toReal_pos (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne' measure_ball_lt_top.ne
  have hKM : 0 < KM := by
    have h1 : 0 ≤ (4 * β / α) * (n : ℝ) * DM ^ 2 := by positivity
    have h2' : 0 ≤ (2 * F / (α * δ)) * R ^ 2 := mul_nonneg (div_nonneg (by linarith) (by positivity)) (sq_nonneg R)
    exact mul_pos (mul_pos hω (pow_pos two_pos n)) (by linarith)
  -- measurability of `f` from the exported weak logarithmic data
  have hb (k : Fin n) : AEStronglyMeasurable (bk k) (volume : Measure (EuclideanSpace ℝ (Fin n))) := (hlog k).1.2.1.aestronglyMeasurable
  have hfm : AEStronglyMeasurable f ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 R)) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hb k).pow 2)).restrict
  have hdiam : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) R, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) R, dist x y ≤ 2 * R := by
    intro x hx y hy
    have hx' := mem_ball.mp hx
    have hy' := mem_ball.mp hy
    linarith [dist_triangle_right x y 0]
  have hmorrey : ∀ x : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
      (∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin n)) R ∩ ball x r, ENNReal.ofReal |f y|) ≤ ENNReal.ofReal (KM * r ^ ((n : ℝ) - 1)) := by
    intro x r hr
    have he : (fun y => ENNReal.ofReal |f y|) =
        fun y => ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (bk k y) ^ 2)) :=
      funext fun y => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [he]
    exact hmor x r hr
  obtain ⟨hσ, hfin, hint, hle⟩ := integrable_exp_critical_morrey_potential h2 measurableSet_ball
    ⟨0, mem_ball_self hRpos⟩ hfm (by linarith : 0 < 2 * R) hKM hdiam hmorrey
  exact ⟨hlog, hmor, hKM, hσ, hfin, hint, hle⟩

end MorreyWitness

section DyadicGainWitness

open Metric

variable {n : ℕ} (hn : 2 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- **Actual one-step dyadic power gain at ONE witness** (`n > 2`, GLOBAL deficit class). ONE call of
`moser_inputs_unified_same_witness` gives `u, T` and `D` before every `R`; for each `R > 0` the coefficients `α, β, B` on
`closedBall 0 (4R)` are fixed before the dyadic cutoff family, the family before `m`; then for every `m`, direction `v`,
`δ > 0`, `r < 1/2` and `1/q = 1/2 − 1/n`: the actual log bound, the actual weak log derivative `b_k = s⁻¹ a_k` in `L²_loc`,
and the critical gain from radius `R(1 + 2^{-m})` to `R(1 + 2^{-m-1})`. Only exported master fields are used. One step,
not the iteration; the deficit `w = (16/κ)|v|² − h_v` is globally nonnegative, not the locally nonnegative class. -/
theorem actual_dyadic_power_gain_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 < R →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R), Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∃ χ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ, ∀ m : ℕ,
          (ContDiff ℝ ∞ (χ m) ∧ HasCompactSupport (χ m) ∧ (∀ x, 0 ≤ χ m x ∧ χ m x ≤ 1) ∧
            (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (R * (1 + (1 / 2) ^ (m + 1))), χ m x = 1) ∧
            tsupport (χ m) ⊆ closedBall 0 (R * (1 + (1 / 2) ^ m)) ∧
            closedBall (0 : EuclideanSpace ℝ (Fin n)) (R * (1 + (1 / 2) ^ m)) ⊆ closedBall 0 (2 * R) ∧
            R * (1 + (1 / 2) ^ m) - R * (1 + (1 / 2) ^ (m + 1)) = R * (1 / 2) ^ (m + 1) ∧
            ∀ x, ‖fderiv ℝ (χ m) x‖ ≤ D * 2 ^ (m + 1) / R) ∧
          ∀ (v : Fin n → ℝ) (δ : ℝ), 0 < δ → ∀ r : ℝ, r < 1 / 2 →
            ∀ q : NNReal, (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹ →
            let w := fun x => (16 / κ) * (∑ i : Fin n, v i ^ 2) -
              ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
            let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
            let F := (16 / κ) * (∑ i : Fin n, v i ^ 2) * B
            let s := fun x => δ + max (w x) 0
            let bk := fun (k : Fin n) x => (s x)⁻¹ * a k x
            (∃ Bl : ℝ, 0 ≤ Bl ∧ ∀ x, ‖Real.log (s x)‖ ≤ Bl) ∧
            (∀ k : Fin n, HasWeakDerivAlong (fun x => Real.log (s x)) (bk k)
                (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
                MemLp (bk k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S')) ∧
            (eLpNorm (fun x => s x ^ r) q ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (closedBall 0 (R * (1 + (1 / 2) ^ (m + 1)))))) ^ (2 : ℕ) ≤
              (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) ^ (2 : ℕ) *
              (n : ENNReal) * ENNReal.ofReal
                (((2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                    ((n : ℝ) * (D * 2 ^ (m + 1) / R) ^ 2) +
                    (4 * r ^ 2 * F / ((1 - 2 * r) * α)) / δ) *
                  (∫ x in closedBall 0 (R * (1 + (1 / 2) ^ m)), s x ^ (2 * r))) := by
  obtain ⟨u, T, hnorm, hmap, D, hD, hS, -⟩ :=
    moser_inputs_unified_same_witness (by omega : 0 < n) hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, D, hD, fun R hR => ?_⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, _hvχ, hdy⟩ :=
    hS (closedBall 0 (4 * R)) (isCompact_closedBall 0 (4 * R))
  obtain ⟨χ, hχ⟩ := hdy R hR (closedBall_subset_closedBall (by linarith))
  refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, χ, fun m => ⟨(hχ m).1, ?_⟩⟩
  intro v δ hδ r hr q hq w a F s bk
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hB
  have hb := (hχ m).2 v
  have hlog := hb.1 δ hδ
  obtain ⟨Blog, hBlog0, hlogb⟩ := hlog.1
  refine ⟨⟨Blog, hBlog0, hlogb⟩, hlog.2.1, ?_⟩
  have hlogm : AEStronglyMeasurable (fun x => Real.log (s x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ((hlog.2.1 ⟨0, by omega⟩).1.1).aestronglyMeasurable
  obtain ⟨hgl, hgc, -, ⟨Cg, -, hgb⟩, -, hgd, -, hepow⟩ := hb.2 δ hδ r
  obtain ⟨hsm, hcs, h01, hone, hts, -, -, hder⟩ := (hχ m).1
  have hχ1 : ContDiff ℝ 1 (χ m) := hsm.of_le (by exact_mod_cast le_top)
  have hp : 0 < 1 - 2 * r := by linarith
  exact weak_cutoff_sobolev_gain_of_energy_of_bounded_log hn
    (isCompact_closedBall 0 _) measurableSet_closedBall hδ
    (fun x => by dsimp only [s]; linarith [le_max_right (w x) 0])
    hts hone (fun x => by rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2) hder
    hgl hgb hgc (fun k => ⟨(hgd k).1, (hgd k).2.1, (hgd k).2.2.2⟩)
    hχ1 hlogm hlogb (by positivity) (by positivity) (hepow hr).2.1 hq

end DyadicGainWitness

section LocalDeficitWitness

open Metric
open scoped ENNReal

variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- **Actual LOCAL deficit: log energy, weak log extension and buffered Morrey at ONE witness.** The public directional
producer is called ONCE (`u, T`); `D_M` is fixed before every `R`; for each `R > 0` the coefficients `α, β, B` on
`closedBall 0 (4R)` are fixed before every direction `v`, local cap `M ≥ 0` with `h_v ≤ M` a.e. on `closedBall 0 (4R)`,
and `δ > 0`. The deficit `w = M − h_v` is nonnegative only on `closedBall 0 (4R)` and bounded everywhere through the
global Hessian cap; the forcing `F = M B` is derived on the test supports. Concluded: the local log energy for every
cutoff in `closedBall 0 (4R)`, ONE bounded weak extension `H, dH` identified on `closedBall 0 (4R)`, and the ALL-ball
Morrey bound of `b = s⁻¹ a` on `B_3R`. No global weak derivative of `log (δ + max w 0)`, local power energy or raw
supersolution field is exported. -/
theorem actual_local_deficit_log_morrey_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 < R →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R), Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 (4 * R))),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          ∀ δ : ℝ, 0 < δ →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := M * B
          let s := fun x => δ + max (w x) 0
          let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall 0 (4 * R) →
            Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2)
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∫ x, χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / α) *
                (∫ x, ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
          (∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∃ BH : ℝ, 0 ≤ BH ∧ ∀ x, ‖H x‖ ≤ BH) ∧
            (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
                MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            (H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 (4 * R))]
              (fun x => Real.log (s x))) ∧
            ∀ k : Fin n, dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (Metric.closedBall 0 (4 * R))] b k) ∧
          ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
            (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ∩ Metric.ball c r,
              ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2))) ≤
              ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
                (16 : ℝ) ^ n * (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2) *
                r ^ ((n : ℝ) - 1)) := by
  obtain ⟨u, L, LF, T, hold, -, hcoef⟩ :=
    exists_regular_moment_directional_hessian_subsolution hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨-, hl, hnorm, hmap, hC1, hG, hF, -, hd, hT, -, hfirst, hInv, -⟩ := hold
  have hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
    filter_upwards [hd] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]
  have hVc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he : (fun y => W y - κ / 2 * ‖y‖ ^ 2) + (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  have hρc : Continuous fun x => Real.exp (-u x) := Real.continuous_exp.comp hC1.continuous.neg
  have hAm (i j : Fin n) : AEStronglyMeasurable (fun x => (Real.exp (-u x) • (hessianMatrix u x)⁻¹) i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hLoc : LocallyIntegrable (fun x => (hessianMatrix u x)⁻¹ i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply locallyIntegrable_iff.mpr
      intro S hS
      let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
        isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
      exact ((hInv i i j).2.2 S hS).integrable (by simp)
    change AEStronglyMeasurable (fun x => Real.exp (-u x) * (hessianMatrix u x)⁻¹ i j) volume
    exact hρc.aestronglyMeasurable.mul hLoc.aestronglyMeasurable
  -- the buffered Morrey constant, fixed before every radius
  obtain ⟨D, hD, hmor⟩ := exists_buffered_morrey_bound_of_cutoff_energy hn
  refine ⟨u, T, hnorm, hmap, D, hD, fun R hR => ?_⟩
  have hSc : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R)) := isCompact_closedBall 0 _
  have hSm : MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R)) := Metric.isClosed_closedBall.measurableSet
  -- one choice of `α, β` and of the density bound `B` on `B_4R`
  obtain ⟨c0, c1, hc0, hc1, hcb⟩ := hcoef _ hSc
  obtain ⟨Cρ, hCρ⟩ := hSc.exists_bound_of_continuousOn hρc.continuousOn
  have hρB (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R)) :
      Real.exp (-u x) ≤ max Cρ 0 := by
    have h := hCρ x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    exact h.trans (le_max_left _ _)
  refine ⟨c0, c1, max Cρ 0, hc0, hc1, le_max_right _ _, hρB, hcb, fun v M hM0 hcap δ hδ => ?_⟩
  intro w a F s b
  classical
  set hv := fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j with hhvdef
  -- `0 ≤ h_v` everywhere a.e. (positive Hessian); `h_v ≤ M` only on `B_4R`
  have hv0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ hv x := by
    filter_upwards [hd] with x hx
    have h0 := hx.1.posSemidef.dotProduct_mulVec_nonneg v
    simp only [star_trivial] at h0
    have hquad : dotProduct v ((hessianMatrix u x).mulVec v) =
        ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hquad] at h0
    exact h0
  have hcap' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R) → hv x ≤ M :=
    (ae_restrict_iff' hSm).1 hcap
  have hw0S : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall 0 (4 * R))),
      0 ≤ w x := hcap.mono fun x hx => by simp only [w]; linarith
  -- weak data of `w` from the weak Hessian tensor
  have hsum (k : Fin n) := hasWeakDerivAlong_finsetSum_mul (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v p.1 * v p.2) (f := fun p x => hessianMatrix u x p.1 p.2) (df := fun p x => T x k p.1 p.2)
    (v := EuclideanSpace.basisFun (Fin n) ℝ k) (fun p _ => (hT k p.1 p.2).1) (fun p _ => (hT k p.1 p.2).2)
  have hhv (k : Fin n) : HasWeakDerivAlong hv (fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    (hsum k).1.congr_ae (ae_of_all _ fun x => by simp only [hv, Fintype.sum_prod_type])
      (ae_of_all _ fun x => by simp only [Fintype.sum_prod_type])
  have htv2 (k : Fin n) : ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
      MemLp (fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') := by
    intro S' hS'
    have h := (hsum k).2 S' hS'
    simpa only [Fintype.sum_prod_type] using h
  have hwweak (k : Fin n) : HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    ((hhv k).const_add_mul M (-1)).congr_ae
      (ae_of_all _ fun x => by simp only [w, hv]; ring) (ae_of_all _ fun x => by simp only [a]; ring)
  have ha2 (k : Fin n) : ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') :=
    fun S' hS' => (htv2 k S' hS').neg
  -- the global Hessian cap bounds `w` everywhere, also where it is negative
  set Hb : ℝ := ∑ i : Fin n, ∑ j : Fin n, ‖v i * v j‖ * ((Real.toNNReal (16 / κ) : NNReal) : ℝ)
  have hvb (x : EuclideanSpace ℝ (Fin n)) : ‖hv x‖ ≤ Hb := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j) (norm_nonneg _)
  have hwb (x : EuclideanSpace ℝ (Fin n)) : ‖w x‖ ≤ ‖M‖ + Hb :=
    (norm_sub_le _ _).trans (by linarith [hvb x])
  have hwl : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))) := (hwweak ⟨0, hn⟩).1
  have hF0 : 0 ≤ F := mul_nonneg hM0 (le_max_right _ _)
  -- the weak supersolution inequality with the LOCAL forcing `F = M B`, for every cutoff in `B_4R`
  have hsubχ (χ : EuclideanSpace ℝ (Fin n) → ℝ)
      (hχS : tsupport χ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R))
      (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
      (hηl : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (hηb : ∃ Bη : ℝ, 0 ≤ Bη ∧ ∀ x, ‖η x‖ ≤ Bη) (hηc : HasCompactSupport η)
      (hηs : Function.support η ⊆ tsupport χ) (hη0 : ∀ x, 0 ≤ η x)
      (hηd : ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, dotProduct (fun k => a k x) (((fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹) x).mulVec
          (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨Bη, -, hBη⟩ := hηb
    obtain ⟨h1, h2, h3⟩ := integral_directional_hessian_flux_le_of_bounded_weak_test hC1 hl hG
      (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet T hT hInv (fun i => (hfirst i).2.2.2.2) hVc
      (hd.mono fun x hx => hx.1) v hηl hBη hηc (fun k => (hηd k).1) (fun k => (hηd k).2.1) (fun k => (hηd k).2.2.2)
      (ae_of_all _ hη0)
    have hηint : Integrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (integrableOn_iff_integrable_of_support_subset (subset_tsupport η)).1 (hηl.integrableOn_isCompact hηc)
    have hL : (fun x => dotProduct (fun k => a k x)
        (((fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹) x).mulVec (fun k => dη k x))) =
        fun x => -(Real.exp (-u x) * (∑ k : Fin n,
          (∑ b : Fin n, (hessianMatrix u x)⁻¹ b k *
            (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) * dη k x)) := by
      funext x
      simp only [dotProduct, Matrix.mulVec, a, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
        neg_mul, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hL, integral_neg]
    have hR' : (∫ x, Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) * η x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ ∫ x, (M * max Cρ 0) * η x ∂volume := by
      refine integral_mono_ae h2 (hηint.const_mul _) ?_
      filter_upwards [hv0, hcap'] with x hx0 hxc
      by_cases hxs : x ∈ tsupport χ
      · have hh : Real.exp (-u x) * hv x ≤ M * max Cρ 0 := by
          calc Real.exp (-u x) * hv x ≤ max Cρ 0 * M :=
                mul_le_mul (hρB x (hχS hxs)) (hxc (hχS hxs)) hx0 (le_max_right _ _)
            _ = M * max Cρ 0 := mul_comm _ _
        exact mul_le_mul_of_nonneg_right hh (hη0 x)
      · have h0 : η x = 0 := by
          by_contra h; exact hxs (hηs h)
        simp only [h0, mul_zero, le_refl]
    rw [integral_const_mul] at hR'
    change -(M * max Cρ 0) * _ ≤ _
    linarith
  -- the LOCAL log energy for every cutoff in `B_4R`
  have henergy (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
      (hχS : tsupport χ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R)) :=
    local_weak_supersolution_log_energy hwl hwb hwweak ha2 hAm hχ hχc
      (ae_restrict_of_ae_restrict_of_subset hχS hw0S) hc0 hc1 hF0
      (ae_restrict_of_ae_restrict_of_subset hχS hcb) (hsubχ χ hχS) hδ
  -- one weak log extension, identified on `B_4R`
  obtain ⟨H, dH, hHl, hHb, hHd, hid⟩ := exists_bounded_weak_log_extension hwl hwb hwweak ha2 hδ
  obtain ⟨hHe, hdHe⟩ := hid _ hSm hw0S
  -- measurability and local `L²` of the log gradient `b = s⁻¹ a`
  have hslo (x : EuclideanSpace ℝ (Fin n)) : δ ≤ s x := by
    simp only [s]; linarith [le_max_right (w x) 0]
  have hinvc : Continuous fun t : ℝ => (δ + max t 0)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => ne_of_gt (by linarith [le_max_right t 0])
  have hbm (k : Fin n) : AEStronglyMeasurable (b k) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hinvc.comp_aestronglyMeasurable hwl.aestronglyMeasurable).mul (hwweak k).2.1.aestronglyMeasurable
  have hb2 (k : Fin n) (S' : Set (EuclideanSpace ℝ (Fin n))) (hS' : IsCompact S') :
      MemLp (b k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') :=
    (ha2 k S' hS').of_le_mul (hbm k).restrict (ae_of_all _ fun x => by
      simp only [b, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos (lt_of_lt_of_le hδ (hslo x))]
      exact inv_anti₀ hδ (hslo x))
  refine ⟨fun χ hχ hχc hχS => ⟨(henergy χ hχ hχc hχS).1, (henergy χ hχ hχc hχS).2.2.2⟩,
    ⟨H, dH, hHl, hHb, hHd, hHe, hdHe⟩, ?_⟩
  exact hmor R (4 * c1 / c0) (2 * F / (c0 * δ)) b hR (by positivity) (by positivity) hbm hb2
    (fun χ hχ hχc hχS _h01 => ⟨(henergy χ hχ hχc hχS).1, (henergy χ hχ hχc hχS).2.2.2⟩)

/-- **Exponential integrability of the actual critical potential of the LOCAL deficit at ONE witness** (`n ≥ 2`). One call
of `actual_local_deficit_log_morrey_same_witness` gives the witness `u, T`, `D_M` before every `R`, and for each `R > 0` the
coefficients `α, β, B` on `closedBall 0 (4R)`; then for every direction `v`, local cap `M ≥ 0` with `h_v ≤ M` a.e. on
`closedBall 0 (4R)` and `δ > 0`, with `b_k = (δ + max w 0)⁻¹ a_k` and `f = √(Σ b_k²)`, inside ONE weak extension `H, dH`:
* the extension facts (`H` bounded, weak derivatives `dH k` in `L²_loc`, `H = log (δ + max w 0)` and `dH k = b k` a.e. on
  `closedBall 0 (4R)`) and the ALL-ball Morrey bound on `B_3R` with `K = ω_n 16^n (1 + (4β/α) n D_M² + (2MB/(αδ)) R²)`;
* `K > 0` (derived), and for `P(x) = ∫_{B_3R} |x - y|^{1-n} f(y) dy`: `P < ∞` a.e. on `B_3R`, `exp(P/(2e(n-1)K))` is
  integrable on `B_3R`, with integral at most `2 ω_n n/(n-1) (1 + 4(n-1)²) (6R)^n`.
The measurability of `f` on `B_3R` comes only from the exported weak data of `dH` and the a.e. identity `dH k = b k`. This
is the exponential integrability of the critical POTENTIAL, not of `log − mean` (GT Lemma 7.16 / John–Nirenberg). -/
theorem actual_local_deficit_potential_exp_same_witness (h2 : 2 ≤ n) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 < R →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R), Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          ∀ δ : ℝ, 0 < δ →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := M * B
          let s := fun x => δ + max (w x) 0
          let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
          let K := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (16 : ℝ) ^ n *
            (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2)
          let f := fun x => Real.sqrt (∑ k : Fin n, (b k x) ^ 2)
          let P := fun x => ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R),
            ENNReal.ofReal (‖y - x‖ ^ (1 - (n : ℝ)) * |f y|)
          let σ := (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹
          ∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∃ BH : ℝ, 0 ≤ BH ∧ ∀ x, ‖H x‖ ≤ BH) ∧
            (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
                MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            (H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))]
              (fun x => Real.log (s x))) ∧
            (∀ k : Fin n, dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (closedBall 0 (4 * R))] b k) ∧
            (∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
              (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ∩ ball c r,
                ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2))) ≤
                ENNReal.ofReal (K * r ^ ((n : ℝ) - 1))) ∧
            0 < K ∧ 0 < σ ∧
            (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))), P x < ⊤) ∧
            Integrable (fun x => Real.exp ((σ / K) * (P x).toReal))
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) ∧
            (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R), Real.exp ((σ / K) * (P x).toReal)) ≤
              2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                (1 + 4 * ((n : ℝ) - 1) ^ 2)) * (6 * R) ^ (n : ℝ) := by
  -- ONE call of the actual local Morrey producer: the same `u, T, D_M`, coefficients, local cap and extension
  obtain ⟨u, T, hnorm, hmap, D, hD, hR⟩ :=
    actual_local_deficit_log_morrey_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, D, hD, fun R hRpos => ?_⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hv⟩ := hR R hRpos
  refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, fun v M hM0 hcap δ hδ => ?_⟩
  intro w a F s b K f P σ
  obtain ⟨-, ⟨H, dH, hHl, hHb, hHd, hHe, hdHe⟩, hmor⟩ := hv v M hM0 hcap δ hδ
  have hF : 0 ≤ F := mul_nonneg hM0 hB
  have hω : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) :=
    ENNReal.toReal_pos (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne'
      measure_ball_lt_top.ne
  have hK0 : 0 < K := by
    have h1 : 0 ≤ (4 * β / α) * (n : ℝ) * D ^ 2 := by positivity
    have h2' : 0 ≤ (2 * F / (α * δ)) * R ^ 2 :=
      mul_nonneg (div_nonneg (by linarith) (by positivity)) (sq_nonneg R)
    exact mul_pos (mul_pos hω (pow_pos (by norm_num) n)) (by linarith)
  -- measurability of `f` on `B_3R`, only from the exported weak data of `dH` and `dH = b` a.e. on `closedBall 0 (4R)`
  have hsub : ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ⊆ closedBall 0 (4 * R) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hbS (k : Fin n) : AEStronglyMeasurable (b k)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) :=
    (((hHd k).1.2.1.aestronglyMeasurable.restrict).congr (hdHe k)).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hfm : AEStronglyMeasurable f ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hbS k).pow 2)
  have hdiam : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R), ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R),
      dist x y ≤ 6 * R := by
    intro x hx y hy
    have hx' := mem_ball.mp hx
    have hy' := mem_ball.mp hy
    linarith [dist_triangle_right x y 0]
  have hmorrey : ∀ x : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
      (∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ∩ ball x r, ENNReal.ofReal |f y|) ≤
        ENNReal.ofReal (K * r ^ ((n : ℝ) - 1)) := by
    intro x r hr
    have he : (fun y => ENNReal.ofReal |f y|) =
        fun y => ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k y) ^ 2)) :=
      funext fun y => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [he]
    exact hmor x r hr
  obtain ⟨hσ, hfin, hint, hle⟩ := integrable_exp_critical_morrey_potential h2 measurableSet_ball
    ⟨0, mem_ball_self (by linarith : (0 : ℝ) < 3 * R)⟩ hfm (by linarith : (0 : ℝ) < 6 * R) hK0 hdiam hmorrey
  exact ⟨H, dH, hHl, hHb, hHd, hHe, hdHe, hmor, hK0, hσ, hfin, hint, hle⟩

end LocalDeficitWitness

section JnExponentArithmetic

open Metric

/-- The normalized JN exponent on `B(c, 3R)` does not depend on the center or the radius (every `n`). -/
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

/-- Under `F R² ≤ α δ` the exponent `p0 = τ n/(32^n U)` is positive and at most `(τ n ω/2^n)/K16` (`n > 0`; algebra only). -/
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

end JnExponentArithmetic

section BoundedJnWitness

open Metric
open scoped ENNReal

variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- **Actual local John–Nirenberg at ONE witness (per `R`, unconditional)** (`n ≥ 2`). One call of
`actual_local_deficit_log_morrey_same_witness`: the same `u, T, D_M`, the per-`R` coefficients, the local cap only on
`B_4R`, `δ` and the ONE `H, dH`. On `B_3R` the actual `log s − ⨍ log s` has the exponential moment at `σ/K16` with
`σ = [2(n−1)e]⁻¹ n |B_3R|/(6R)^n`, integral at most `c2(n) (6R)^n`; `dH = b` is used only a.e. on `B_4R`. -/
theorem actual_local_deficit_john_nirenberg_same_witness (h2 : 2 ≤ n) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 < R →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R), Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          ∀ δ : ℝ, 0 < δ →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := M * B
          let s := fun x => δ + max (w x) 0
          let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
          let K := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (16 : ℝ) ^ n *
            (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2)
          let σ := (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹ * (n : ℝ) *
            (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 (3 * R)) / (6 * R) ^ (n : ℝ)
          ∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∃ BH : ℝ, 0 ≤ BH ∧ ∀ x, ‖H x‖ ≤ BH) ∧
            (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
                MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            (H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))]
              (fun x => Real.log (s x))) ∧
            (∀ k : Fin n, dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (closedBall 0 (4 * R))] b k) ∧
            (∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
              (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ∩ ball c r,
                ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2))) ≤
                ENNReal.ofReal (K * r ^ ((n : ℝ) - 1))) ∧
            0 < K ∧ 0 < σ ∧
            Integrable (fun x => Real.log (s x))
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) ∧
            Integrable (fun x => Real.exp ((σ / K) * |Real.log (s x) - ⨍ y in ball 0 (3 * R), Real.log (s y)|))
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) ∧
            (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R),
              Real.exp ((σ / K) * |Real.log (s x) - ⨍ y in ball 0 (3 * R), Real.log (s y)|)) ≤
              2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                (1 + 4 * ((n : ℝ) - 1) ^ 2)) * (6 * R) ^ (n : ℝ) := by
  obtain ⟨u,T,hnorm,hmap,D,hD,hR⟩ :=
    LetwinCaccioppoliAudit.actual_local_deficit_log_morrey_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u,T,hnorm,hmap,D,hD,fun R hRpos => ?_⟩
  obtain ⟨α,β,B,hα,hβ,hB,hρB,hcb,hv⟩ := hR R hRpos
  refine ⟨α,β,B,hα,hβ,hB,hρB,hcb,fun v M hM0 hcap δ hδ => ?_⟩
  intro w a F s b K σ
  obtain ⟨-,⟨H,dH,hHl,hHb,hHd,hHe,hdHe⟩,hmor⟩ := hv v M hM0 hcap δ hδ
  obtain ⟨BH,hBH0,hBH⟩ := hHb
  have hF : 0 ≤ F := mul_nonneg hM0 hB
  have hω : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) :=
    ENNReal.toReal_pos (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne'
      measure_ball_lt_top.ne
  have hK0 : 0 < K := by
    have h1 : 0 ≤ (4 * β / α) * (n : ℝ) * D ^ 2 := by positivity
    have h2' : 0 ≤ (2 * F / (α * δ)) * R ^ 2 := by positivity
    exact mul_pos (mul_pos hω (pow_pos (by norm_num) n)) (by linarith)
  have hsub : ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ⊆ closedBall 0 (4 * R) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hdeq (k : Fin n) : dH k =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R)))] b k :=
    ae_restrict_of_ae_restrict_of_subset hsub (hdHe k)
  have hmorH : ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
      (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ∩ ball c r,
        ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (dH k x)^2))) ≤ ENNReal.ofReal (K * r ^ ((n : ℝ) - 1)) := by
    intro c r hr
    have heq : (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ∩ ball c r,
        ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (dH k x)^2))) =
        ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ∩ ball c r,
          ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x)^2)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left (ae_all_iff.2 hdeq)] with x hx
      simp_rw [hx]
    rw [heq]
    exact hmor c r hr
  have hdiam : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R),
      ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R), dist x y ≤ 6 * R := by
    intro x hx y hy
    have hx' := mem_ball.mp hx
    have hy' := mem_ball.mp hy
    linarith [dist_triangle_right x y 0]
  obtain ⟨hσ,hJI,hJbound⟩ := integrable_exp_abs_sub_average_of_bounded_weak_morrey h2
    isOpen_ball (convex_ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R))
    ⟨0,mem_ball_self (by linarith : (0 : ℝ) < 3 * R)⟩ (by linarith : (0 : ℝ) < 6 * R)
    hK0 hdiam hHl hBH (fun k => (hHd k).1) (fun k => (hHd k).2) hmorH
  have hHeS : H =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R)))]
      (fun x => Real.log (s x)) := ae_restrict_of_ae_restrict_of_subset hsub hHe
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hHI : Integrable H ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) :=
    (integrable_const BH).mono' hHl.aestronglyMeasurable.restrict (ae_of_all _ hBH)
  have hlogI : Integrable (fun x => Real.log (s x))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) := hHI.congr hHeS
  have havg : (⨍ y in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R), H y) =
      ⨍ y in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R), Real.log (s y) := average_congr hHeS
  have hexp : (fun x => Real.exp ((σ / K) * |H x - ⨍ y in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R), H y|))
      =ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R)))]
      fun x => Real.exp ((σ / K) * |Real.log (s x) - ⨍ y in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R), Real.log (s y)|) := by
    filter_upwards [hHeS] with x hx
    rw [hx,havg]
  refine ⟨H,dH,hHl,⟨BH,hBH0,hBH⟩,hHd,hHe,hdHe,hmor,hK0,hσ,hlogI,hJI.congr hexp,?_⟩
  rw [← integral_congr_ae hexp]
  exact hJbound

/-- **Actual local power moments (per `R`)** (`n ≥ 2`): at the same witness and the ONE `H`,
`∫_{B_3R} s^{σ/K} · ∫_{B_3R} s^{−σ/K} ≤ (c2(n) (6R)^n)²`. -/
theorem actual_local_deficit_log_moment_product_same_witness (h2 : 2 ≤ n) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 < R →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * R), Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          ∀ δ : ℝ, 0 < δ →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := M * B
          let s := fun x => δ + max (w x) 0
          let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
          let K := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (16 : ℝ) ^ n *
            (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2)
          let σ := (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹ * (n : ℝ) *
            (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 (3 * R)) / (6 * R) ^ (n : ℝ)
          ∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∃ BH : ℝ, 0 ≤ BH ∧ ∀ x, ‖H x‖ ≤ BH) ∧
            (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
                MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            (H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall 0 (4 * R))]
              (fun x => Real.log (s x))) ∧
            (∀ k : Fin n, dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (closedBall 0 (4 * R))] b k) ∧
            (∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
              (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ∩ ball c r,
                ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2))) ≤
                ENNReal.ofReal (K * r ^ ((n : ℝ) - 1))) ∧
            0 < K ∧ 0 < σ ∧
            Integrable (fun x => Real.log (s x))
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) ∧
            Integrable (fun x => Real.exp ((σ / K) * |Real.log (s x) - ⨍ y in ball 0 (3 * R), Real.log (s y)|))
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) ∧
            (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R),
              Real.exp ((σ / K) * |Real.log (s x) - ⨍ y in ball 0 (3 * R), Real.log (s y)|)) ≤
              2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                (1 + 4 * ((n : ℝ) - 1) ^ 2)) * (6 * R) ^ (n : ℝ) ∧
            Integrable (fun x => (s x)^(σ / K))
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) ∧
            Integrable (fun x => (s x)^(-(σ / K)))
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))) ∧
            (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R), (s x)^(σ / K)) *
              (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R), (s x)^(-(σ / K))) ≤
                (2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                  (1 + 4 * ((n : ℝ) - 1)^2)) * (6 * R)^(n : ℝ))^2 := by
  -- ONE call of the actual local JN producer: the same u, T, D, coefficients, local cap, δ and ONE H, dH
  obtain ⟨u, T, hnorm, hmap, D, hD, hR⟩ :=
    actual_local_deficit_john_nirenberg_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso h2
  refine ⟨u, T, hnorm, hmap, D, hD, fun R hRpos => ?_⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hv⟩ := hR R hRpos
  refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, fun v M hM0 hcap δ hδ => ?_⟩
  intro w a F s b K σ
  obtain ⟨H, dH, hHl, hHb, hHd, hHe, hdHe, hmor, hK0, hσ, hlogI, hJI, hJle⟩ := hv v M hM0 hcap δ hδ
  -- s = δ + max w 0 is positive everywhere
  have hs : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 (3 * R))), 0 < s x :=
    ae_of_all _ fun x => by
      change 0 < δ + max (w x) 0
      linarith [le_max_right (w x) 0]
  -- the centered log exponential moment at p = σ/K, m = the actual average of log s on B_3R; measurability of log s
  -- comes from its EXPORTED integrability
  obtain ⟨hplus, hminus, hprod⟩ := FunctionalInequalities.Probability.integral_rpow_mul_integral_rpow_neg_le_of_log_exp
    (div_pos hσ hK0).le hs hlogI.aestronglyMeasurable hJI hJle
  exact ⟨H, dH, hHl, hHb, hHd, hHe, hdHe, hmor, hK0, hσ, hlogI, hJI, hJle, hplus, hminus, hprod⟩

/-- **Fixed-compact joint local inputs at ONE witness.** One public producer call; `D_M` before every compact `S`; ONE
`α, β, B` on `S` before every domain center `x0` and radius `R` with `closedBall x0 (4R) ⊆ S`; then every direction, local
cap `M` (only on `B(x0,4R)`) and `δ`: the globally bounded measurable actual `log s`, the linear power data of every
cutoff and every real `r`, the power energies (`r < 1/2`), the local log energy, ONE weak `H, dH` identified on
`B(x0,4R)`, and the centered `B(x0,3R)` all-ball Morrey bound. No global weak derivative of `log max w`. -/
theorem actual_local_inputs_fixed_compact_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → Metric.closedBall x0 (4 * R) ⊆ S →
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          ∀ δ : ℝ, 0 < δ →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := M * B
          let s := fun x => δ + max (w x) 0
          let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
          AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∃ Clog : ℝ, 0 ≤ Clog ∧ ∀ x, ‖Real.log (s x)‖ ≤ Clog) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) → ∀ r : ℝ,
            let g := fun x => χ x * s x ^ r
            let dg := fun (k : Fin n) x =>
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
              χ x * (r * s x ^ (r - 1)) * a k x
            (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport g ∧ Function.support g ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖g x‖ ≤ Cη) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
      ∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧
        MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧ (r < 1 / 2 →
    Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => s x ^ (2 * r) * ∑ k : Fin n,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
        (∫ x, s x ^ (2 * r) * ∑ k : Fin n,
          (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
      (4 * r ^ 2 * F / ((1 - 2 * r) * α)) *
        (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) →
            Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2)
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∫ x, χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / α) *
                (∫ x, ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
          (∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∃ BH : ℝ, 0 ≤ BH ∧ ∀ x, ‖H x‖ ≤ BH) ∧
            (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
                MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            (H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))]
              (fun x => Real.log (s x))) ∧
            ∀ k : Fin n, dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (Metric.closedBall x0 (4 * R))] b k) ∧
          ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
            (∫⁻ x in Metric.ball x0 (3 * R) ∩ Metric.ball c r,
              ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2))) ≤
              ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
                (16 : ℝ) ^ n * (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2) *
                r ^ ((n : ℝ) - 1)) := by
  obtain ⟨u, L, LF, T, hold, -, hcoef⟩ :=
    exists_regular_moment_directional_hessian_subsolution hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨-, hl, hnorm, hmap, hC1, hG, hF, -, hd, hT, -, hfirst, hInv, -⟩ := hold
  have hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
    filter_upwards [hd] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]
  have hVc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he : (fun y => W y - κ / 2 * ‖y‖ ^ 2) + (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  have hρc : Continuous fun x => Real.exp (-u x) := Real.continuous_exp.comp hC1.continuous.neg
  have hAm (i j : Fin n) : AEStronglyMeasurable (fun x => (Real.exp (-u x) • (hessianMatrix u x)⁻¹) i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hLoc : LocallyIntegrable (fun x => (hessianMatrix u x)⁻¹ i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply locallyIntegrable_iff.mpr
      intro S hS
      let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
        isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
      exact ((hInv i i j).2.2 S hS).integrable (by simp)
    change AEStronglyMeasurable (fun x => Real.exp (-u x) * (hessianMatrix u x)⁻¹ i j) volume
    exact hρc.aestronglyMeasurable.mul hLoc.aestronglyMeasurable
  -- the buffered Morrey constant, fixed before every radius
  obtain ⟨D, hD, hmor⟩ := exists_centered_buffered_morrey_bound_of_cutoff_energy hn
  refine ⟨u, T, hnorm, hmap, D, hD, fun S hSc => ?_⟩
  -- one choice of `α, β` and of the density bound `B` on `B_4R`
  obtain ⟨c0, c1, hc0, hc1, hcb⟩ := hcoef S hSc
  obtain ⟨Cρ, hCρ⟩ := hSc.exists_bound_of_continuousOn hρc.continuousOn
  have hρB (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) :
      Real.exp (-u x) ≤ max Cρ 0 := by
    have h := hCρ x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    exact h.trans (le_max_left _ _)
  refine ⟨c0, c1, max Cρ 0, hc0, hc1, le_max_right _ _, hρB, hcb, fun x0 R hR hBallS v M hM0 hcap δ hδ => ?_⟩
  intro w a F s b
  have hSm : MeasurableSet (Metric.closedBall x0 (4 * R)) := Metric.isClosed_closedBall.measurableSet
  classical
  set hv := fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j with hhvdef
  -- `0 ≤ h_v` everywhere a.e. (positive Hessian); `h_v ≤ M` only on `B_4R`
  have hv0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ hv x := by
    filter_upwards [hd] with x hx
    have h0 := hx.1.posSemidef.dotProduct_mulVec_nonneg v
    simp only [star_trivial] at h0
    have hquad : dotProduct v ((hessianMatrix u x).mulVec v) =
        ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hquad] at h0
    exact h0
  have hcap' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ Metric.closedBall x0 (4 * R) → hv x ≤ M :=
    (ae_restrict_iff' hSm).1 hcap
  have hw0S : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
      0 ≤ w x := hcap.mono fun x hx => by simp only [w]; linarith
  -- weak data of `w` from the weak Hessian tensor
  have hsum (k : Fin n) := hasWeakDerivAlong_finsetSum_mul (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v p.1 * v p.2) (f := fun p x => hessianMatrix u x p.1 p.2) (df := fun p x => T x k p.1 p.2)
    (v := EuclideanSpace.basisFun (Fin n) ℝ k) (fun p _ => (hT k p.1 p.2).1) (fun p _ => (hT k p.1 p.2).2)
  have hhv (k : Fin n) : HasWeakDerivAlong hv (fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    (hsum k).1.congr_ae (ae_of_all _ fun x => by simp only [hv, Fintype.sum_prod_type])
      (ae_of_all _ fun x => by simp only [Fintype.sum_prod_type])
  have htv2 (k : Fin n) : ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
      MemLp (fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') := by
    intro S' hS'
    have h := (hsum k).2 S' hS'
    simpa only [Fintype.sum_prod_type] using h
  have hwweak (k : Fin n) : HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    ((hhv k).const_add_mul M (-1)).congr_ae
      (ae_of_all _ fun x => by simp only [w, hv]; ring) (ae_of_all _ fun x => by simp only [a]; ring)
  have ha2 (k : Fin n) : ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') :=
    fun S' hS' => (htv2 k S' hS').neg
  -- the global Hessian cap bounds `w` everywhere, also where it is negative
  set Hb : ℝ := ∑ i : Fin n, ∑ j : Fin n, ‖v i * v j‖ * ((Real.toNNReal (16 / κ) : NNReal) : ℝ)
  have hvb (x : EuclideanSpace ℝ (Fin n)) : ‖hv x‖ ≤ Hb := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j) (norm_nonneg _)
  have hwb (x : EuclideanSpace ℝ (Fin n)) : ‖w x‖ ≤ ‖M‖ + Hb :=
    (norm_sub_le _ _).trans (by linarith [hvb x])
  have hwl : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))) := (hwweak ⟨0, hn⟩).1
  have hF0 : 0 ≤ F := mul_nonneg hM0 (le_max_right _ _)
  -- the weak supersolution inequality with the LOCAL forcing `F = M B`, for every cutoff in `B_4R`
  have hsubχ (χ : EuclideanSpace ℝ (Fin n) → ℝ)
      (hχS : tsupport χ ⊆ Metric.closedBall x0 (4 * R))
      (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
      (hηl : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (hηb : ∃ Bη : ℝ, 0 ≤ Bη ∧ ∀ x, ‖η x‖ ≤ Bη) (hηc : HasCompactSupport η)
      (hηs : Function.support η ⊆ tsupport χ) (hη0 : ∀ x, 0 ≤ η x)
      (hηd : ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, dotProduct (fun k => a k x) (((fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹) x).mulVec
          (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨Bη, -, hBη⟩ := hηb
    obtain ⟨h1, h2, h3⟩ := integral_directional_hessian_flux_le_of_bounded_weak_test hC1 hl hG
      (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet T hT hInv (fun i => (hfirst i).2.2.2.2) hVc
      (hd.mono fun x hx => hx.1) v hηl hBη hηc (fun k => (hηd k).1) (fun k => (hηd k).2.1) (fun k => (hηd k).2.2.2)
      (ae_of_all _ hη0)
    have hηint : Integrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (integrableOn_iff_integrable_of_support_subset (subset_tsupport η)).1 (hηl.integrableOn_isCompact hηc)
    have hL : (fun x => dotProduct (fun k => a k x)
        (((fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹) x).mulVec (fun k => dη k x))) =
        fun x => -(Real.exp (-u x) * (∑ k : Fin n,
          (∑ b : Fin n, (hessianMatrix u x)⁻¹ b k *
            (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) * dη k x)) := by
      funext x
      simp only [dotProduct, Matrix.mulVec, a, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
        neg_mul, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hL, integral_neg]
    have hR' : (∫ x, Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) * η x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ ∫ x, (M * max Cρ 0) * η x ∂volume := by
      refine integral_mono_ae h2 (hηint.const_mul _) ?_
      filter_upwards [hv0, hcap'] with x hx0 hxc
      by_cases hxs : x ∈ tsupport χ
      · have hh : Real.exp (-u x) * hv x ≤ M * max Cρ 0 := by
          calc Real.exp (-u x) * hv x ≤ max Cρ 0 * M :=
                mul_le_mul (hρB x (hBallS (hχS hxs))) (hxc (hχS hxs)) hx0 (le_max_right _ _)
            _ = M * max Cρ 0 := mul_comm _ _
        exact mul_le_mul_of_nonneg_right hh (hη0 x)
      · have h0 : η x = 0 := by
          by_contra h; exact hxs (hηs h)
        simp only [h0, mul_zero, le_refl]
    rw [integral_const_mul] at hR'
    change -(M * max Cρ 0) * _ ≤ _
    linarith
  have hlogc : Continuous fun t : ℝ => Real.log (δ + max t 0) :=
    Continuous.log (by fun_prop) fun t => ne_of_gt (by linarith [le_max_right t 0])
  have hlogm : AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hlogc.comp_aestronglyMeasurable hwl.aestronglyMeasurable
  let Clog := |Real.log δ| + |Real.log (δ + (‖M‖ + Hb))|
  have hClog : 0 ≤ Clog := by dsimp only [Clog]; positivity
  have hlogb (x : EuclideanSpace ℝ (Fin n)) : ‖Real.log (s x)‖ ≤ Clog := by
    have hCw : 0 ≤ ‖M‖ + Hb := (norm_nonneg (w 0)).trans (hwb 0)
    have hwU : w x ≤ ‖M‖ + Hb := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hwb x)
    have hmax : max (w x) 0 ≤ ‖M‖ + Hb := max_le hwU hCw
    have hsL : δ ≤ s x := by dsimp only [s]; linarith [le_max_right (w x) 0]
    have hsU : s x ≤ δ + (‖M‖ + Hb) := by dsimp only [s]; linarith
    have hlo := Real.log_le_log hδ hsL
    have hhi := Real.log_le_log (lt_of_lt_of_le hδ hsL) hsU
    rw [Real.norm_eq_abs,abs_le]
    dsimp only [Clog]
    constructor <;> nlinarith [neg_abs_le (Real.log δ),le_abs_self (Real.log (δ + (‖M‖ + Hb))),
      abs_nonneg (Real.log δ),abs_nonneg (Real.log (δ + (‖M‖ + Hb)))]
  -- the LOCAL log energy for every cutoff in `B_4R`
  have henergy (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
      (hχS : tsupport χ ⊆ Metric.closedBall x0 (4 * R)) :=
    local_weak_supersolution_log_energy hwl hwb hwweak ha2 hAm hχ hχc
      (ae_restrict_of_ae_restrict_of_subset hχS hw0S) hc0 hc1 hF0
      (ae_restrict_of_ae_restrict_of_subset (hχS.trans hBallS) hcb) (hsubχ χ hχS) hδ
  -- one weak log extension, identified on `B_4R`
  obtain ⟨H, dH, hHl, hHb, hHd, hid⟩ := exists_bounded_weak_log_extension hwl hwb hwweak ha2 hδ
  obtain ⟨hHe, hdHe⟩ := hid _ hSm hw0S
  -- measurability and local `L²` of the log gradient `b = s⁻¹ a`
  have hslo (x : EuclideanSpace ℝ (Fin n)) : δ ≤ s x := by
    simp only [s]; linarith [le_max_right (w x) 0]
  have hinvc : Continuous fun t : ℝ => (δ + max t 0)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t => ne_of_gt (by linarith [le_max_right t 0])
  have hbm (k : Fin n) : AEStronglyMeasurable (b k) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hinvc.comp_aestronglyMeasurable hwl.aestronglyMeasurable).mul (hwweak k).2.1.aestronglyMeasurable
  have hb2 (k : Fin n) (S' : Set (EuclideanSpace ℝ (Fin n))) (hS' : IsCompact S') :
      MemLp (b k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') :=
    (ha2 k S' hS').of_le_mul (hbm k).restrict (ae_of_all _ fun x => by
      simp only [b, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos (lt_of_lt_of_le hδ (hslo x))]
      exact inv_anti₀ hδ (hslo x))
  refine ⟨hlogm,⟨Clog,hClog,hlogb⟩,?_,
    (fun χ hχ hχc hχS => ⟨(henergy χ hχ hχc hχS).1, (henergy χ hχ hχc hχS).2.2.2⟩),
    ⟨H, dH, hHl, hHb, hHd, hHe, hdHe⟩,?_⟩
  · intro χ hχ hχc hχS r g dg
    refine ⟨local_rpow_cutoff_weak_data hwl hwb hwweak ha2 hχ hχc
      (ae_restrict_of_ae_restrict_of_subset hχS hw0S) hδ r,?_⟩
    intro hr
    exact local_weak_supersolution_power_energy hwl hwb hwweak ha2 hAm hχ hχc
      (ae_restrict_of_ae_restrict_of_subset hχS hw0S) hc0 hc1 hF0
      (ae_restrict_of_ae_restrict_of_subset (hχS.trans hBallS) hcb) (hsubχ χ hχS) hδ hr
  · exact hmor x0 R (4 * c1 / c0) (2 * F / (c0 * δ)) b hR (by positivity) (by positivity) hbm hb2
      (fun χ hχ hχc hχS _h01 => ⟨(henergy χ hχ hχc hχS).1, (henergy χ hχ hχc hχS).2.2.2⟩)

/-- **Uniform joint JN moments at ONE fixed-compact witness** (`n ≥ 2`). `p0 = τ n/(32^n U)` is fixed after the
coefficients on `S` and before every center, radius, local cap and `δ`; under `F R² ≤ α δ`, inside the SAME `H, dH`, the
actual `log s − ⨍ log s` on `B(x0,3R)` has the exponential moment at `p0` and `∫ s^{p0} · ∫ s^{−p0} ≤ (c2(n) (6R)^n)²`,
with every producer field retained. -/
theorem actual_joint_jn_moments_fixed_compact_same_witness (h2 : 2 ≤ n) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        let p0 := (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹ * (n : ℝ) /
          ((32 : ℝ)^n * (3 + (4 * β / α) * (n : ℝ) * D^2))
        0 < p0 ∧
        ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → Metric.closedBall x0 (4 * R) ⊆ S →
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          ∀ δ : ℝ, 0 < δ →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := M * B
          let s := fun x => δ + max (w x) 0
          let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
          AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∃ Clog : ℝ, 0 ≤ Clog ∧ ∀ x, ‖Real.log (s x)‖ ≤ Clog) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) → ∀ r : ℝ,
            let g := fun x => χ x * s x ^ r
            let dg := fun (k : Fin n) x =>
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
              χ x * (r * s x ^ (r - 1)) * a k x
            (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport g ∧ Function.support g ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖g x‖ ≤ Cη) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
      ∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧
        MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧ (r < 1 / 2 →
    Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => s x ^ (2 * r) * ∑ k : Fin n,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
        (∫ x, s x ^ (2 * r) * ∑ k : Fin n,
          (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
      (4 * r ^ 2 * F / ((1 - 2 * r) * α)) *
        (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) →
            Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2)
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∫ x, χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / α) *
                (∫ x, ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
          (∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∃ BH : ℝ, 0 ≤ BH ∧ ∀ x, ‖H x‖ ≤ BH) ∧
            (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
                MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            (H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))]
              (fun x => Real.log (s x))) ∧
            (∀ k : Fin n, dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (Metric.closedBall x0 (4 * R))] b k) ∧
            (F * R^2 ≤ α * δ →
              Integrable (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              (∫ x in Metric.ball x0 (3 * R),
                Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|)) ≤
                2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                  (1 + 4 * ((n : ℝ) - 1)^2)) * (6 * R)^(n : ℝ) ∧
              Integrable (fun x => (s x)^p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              Integrable (fun x => (s x)^(-p0))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              (∫ x in Metric.ball x0 (3 * R), (s x)^p0) * (∫ x in Metric.ball x0 (3 * R), (s x)^(-p0)) ≤
                (2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                  (1 + 4 * ((n : ℝ) - 1)^2)) * (6 * R)^(n : ℝ))^2)) ∧
          ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
            (∫⁻ x in Metric.ball x0 (3 * R) ∩ Metric.ball c r,
              ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2))) ≤
              ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
                (16 : ℝ) ^ n * (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2) *
                r ^ ((n : ℝ) - 1)) := by
  -- ONE call of the fixed-compact joint producer
  obtain ⟨u, T, hnorm, hmap, D, hD, hS⟩ :=
    actual_local_inputs_fixed_compact_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, D, hD, fun S hSc => ?_⟩
  -- the coefficients on S, chosen once before every domain center and radius
  obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hball⟩ := hS S hSc
  refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, ?_⟩
  intro p0
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
  have hτ : 0 < (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹ := by
    have : 0 < (n : ℝ) - 1 := by linarith
    positivity
  have hω : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne'
      measure_ball_lt_top.ne
  have hU : 0 < 3 + (4 * β / α) * (n : ℝ) * D ^ 2 := by positivity
  -- p0 depends only on n, α, β and D: fixed before every center, radius, local cap and δ
  have hp0 : 0 < p0 :=
    div_pos (mul_pos hτ (by positivity)) (mul_pos (by positivity) hU)
  refine ⟨hp0, fun x0 R hR hBS v M hM0 hcap δ hδ => ?_⟩
  intro w a F s b
  obtain ⟨hlogm, hlogB, hlin, hlogE, ⟨H, dH, hHl, hHb, hHd, hHe, hdHe⟩, hmor⟩ :=
    hball x0 R hR hBS v M hM0 hcap δ hδ
  refine ⟨hlogm, hlogB, hlin, hlogE, ⟨H, dH, hHl, hHb, hHd, hHe, hdHe, fun hFR => ?_⟩, hmor⟩
  obtain ⟨BH, -, hBH⟩ := hHb
  have hF : 0 ≤ F := mul_nonneg hM0 hB
  -- the small-forcing exponent bound at this ball
  have hsf := small_forcing_uniform_jn_exponent (D := D) (by omega : 0 < n) hω hτ hα hβ.le hF
    hδ hFR
  dsimp only at hsf
  obtain ⟨-, hK0, hp0le⟩ := hsf
  have hσeq := ball_jn_sigma_eq x0 hR (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹
  -- dH = b only a.e. on closedBall x0 (4R), transferred to B(x0, 3R) and the query intersections
  have hsub : Metric.ball x0 (3 * R) ⊆ Metric.closedBall x0 (4 * R) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hdeq (k : Fin n) : dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))] b k :=
    ae_restrict_of_ae_restrict_of_subset hsub (hdHe k)
  have hmorH : ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.ball x0 (3 * R) ∩ Metric.ball c r,
        ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (dH k x) ^ 2))) ≤
        ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
          (16 : ℝ) ^ n * (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2) *
          r ^ ((n : ℝ) - 1)) := by
    intro c r hr
    have heq : (∫⁻ x in Metric.ball x0 (3 * R) ∩ Metric.ball c r,
        ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (dH k x) ^ 2))) =
        ∫⁻ x in Metric.ball x0 (3 * R) ∩ Metric.ball c r,
          ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left (ae_all_iff.2 hdeq)] with x hx
      simp_rw [hx]
    rw [heq]
    exact hmor c r hr
  have hdiam : ∀ x ∈ Metric.ball x0 (3 * R), ∀ y ∈ Metric.ball x0 (3 * R), dist x y ≤ 6 * R := by
    intro x hx y hy
    have hx' := Metric.mem_ball.mp hx
    have hy' := Metric.mem_ball.mp hy
    linarith [dist_triangle_right x y x0]
  -- the bounded weak JN for the SAME H on the convex ball B(x0, 3R), D_pot = 6R
  have hJN := integrable_exp_abs_sub_average_of_bounded_weak_morrey h2
    Metric.isOpen_ball (convex_ball x0 (3 * R)) ⟨x0, Metric.mem_ball_self (by linarith : (0 : ℝ) < 3 * R)⟩
    (by linarith : (0 : ℝ) < 6 * R) hK0 hdiam hHl hBH (fun k => (hHd k).1) (fun k => (hHd k).2) hmorH
  dsimp only at hJN
  obtain ⟨-, hJI, hJle⟩ := hJN
  rw [hσeq] at hJI hJle
  -- lower the exponent to the uniform p0 ≤ σ/K
  let μB := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))
  have hmono : ∀ x, Real.exp (p0 * |H x - ⨍ y in Metric.ball x0 (3 * R), H y|) ≤
      Real.exp (((2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹ * (n : ℝ) *
        (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) / (2 : ℝ) ^ n /
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (16 : ℝ) ^ n *
          (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2))) *
        |H x - ⨍ y in Metric.ball x0 (3 * R), H y|) := fun x =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hp0le (abs_nonneg _))
  have hEm : AEStronglyMeasurable (fun x => Real.exp (p0 * |H x - ⨍ y in Metric.ball x0 (3 * R), H y|)) μB := by
    apply Real.continuous_exp.comp_aestronglyMeasurable
    have hd : AEStronglyMeasurable (fun x => H x - ⨍ y in Metric.ball x0 (3 * R), H y) μB :=
      (show AEStronglyMeasurable H μB from hHl.aestronglyMeasurable.restrict).sub aestronglyMeasurable_const
    simpa only [Real.norm_eq_abs] using hd.norm.const_mul p0
  have hEI : Integrable (fun x => Real.exp (p0 * |H x - ⨍ y in Metric.ball x0 (3 * R), H y|)) μB :=
    hJI.mono_nonneg hEm (ae_of_all _ fun x => (Real.exp_pos _).le) (ae_of_all _ hmono)
  have hEle : (∫ x in Metric.ball x0 (3 * R), Real.exp (p0 * |H x - ⨍ y in Metric.ball x0 (3 * R), H y|)) ≤
      2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
        (1 + 4 * ((n : ℝ) - 1) ^ 2)) * (6 * R) ^ (n : ℝ) :=
    (integral_mono_ae hEI hJI (ae_of_all _ hmono)).trans hJle
  -- transfer H = log s and its average, a.e. on B(x0, 3R)
  have hHeS : H =ᵐ[μB] (fun x => Real.log (s x)) := ae_restrict_of_ae_restrict_of_subset hsub hHe
  have havg : (⨍ y in Metric.ball x0 (3 * R), H y) = ⨍ y in Metric.ball x0 (3 * R), Real.log (s y) :=
    average_congr hHeS
  have hexp : (fun x => Real.exp (p0 * |H x - ⨍ y in Metric.ball x0 (3 * R), H y|)) =ᵐ[μB]
      fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|) := by
    filter_upwards [hHeS] with x hx
    rw [hx, havg]
  have hLI : Integrable (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|)) μB :=
    hEI.congr hexp
  have hLle : (∫ x in Metric.ball x0 (3 * R),
      Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|)) ≤
      2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
        (1 + 4 * ((n : ℝ) - 1) ^ 2)) * (6 * R) ^ (n : ℝ) := by
    rw [← integral_congr_ae hexp]; exact hEle
  -- the actual s > 0 and the moment product at p0, m = the actual average of log s
  have hspos : ∀ᵐ x ∂μB, 0 < s x := ae_of_all _ fun x => by
    change 0 < δ + max (w x) 0
    linarith [le_max_right (w x) 0]
  obtain ⟨hplus, hminus, hprod⟩ := FunctionalInequalities.Probability.integral_rpow_mul_integral_rpow_neg_le_of_log_exp
    hp0.le hspos hlogm.restrict hLI hLle
  exact ⟨hLI, hLle, hplus, hminus, hprod⟩

end BoundedJnWitness

/-- An instance of the critical exponent in dimension three: `1/6 = 1/2 - 1/3`. -/
example : ((6 : NNReal) : ℝ)⁻¹ = (2 : ℝ)⁻¹ - ((3 : ℕ) : ℝ)⁻¹ := by norm_num

#print axioms uniform_energy_same_witness
#print axioms uniform_sobolev_high_same_witness
#print axioms uniform_bump_instances
#print axioms uniform_sobolev_two_same_witness
#print axioms uniform_sobolev_one_same_witness
#print axioms FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening_of_rOut_le
#print axioms FunctionalInequalities.Analysis.HasWeakDerivAlong.const_add_mul
#print axioms FunctionalInequalities.Analysis.exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset
#print axioms FunctionalInequalities.Analysis.bounded_rpow_cutoff_weak_data
#print axioms FunctionalInequalities.Analysis.bounded_rpow_cutoff_weak_test
#print axioms FunctionalInequalities.Analysis.rpow_cutoff_quadratic_young
#print axioms FunctionalInequalities.Analysis.eLpNorm_le_sum_eLpNorm_weak_deriv_of_compact_bounded
#print axioms FunctionalInequalities.Analysis.eLpNorm_six_le_sum_eLpNorm_weak_deriv_of_support_subset_two
#print axioms FunctionalInequalities.Analysis.eLpNorm_top_le_eLpNorm_weak_deriv_of_support_subset_one
#print axioms FunctionalInequalities.Analysis.bounded_weak_supersolution_caccioppoli
#print axioms LetwinCaccioppoliAudit.moser_inputs_unified_same_witness
#print axioms LetwinCaccioppoliAudit.moser_inputs_unified_two_same_witness
#print axioms FunctionalInequalities.Analysis.hasWeakDerivAlong_comp_of_bounded
#print axioms FunctionalInequalities.Analysis.hasWeakDerivAlong_log_max_shift_of_ae_nonneg_bounded
#print axioms FunctionalInequalities.Analysis.bounded_weak_supersolution_log_caccioppoli
#print axioms FunctionalInequalities.Analysis.bounded_weak_supersolution_power_energy
#print axioms FunctionalInequalities.Analysis.eLpNorm_finite_le_sum_eLpNorm_weak_deriv_of_support_subset_two
#print axioms FunctionalInequalities.Analysis.exists_smooth_concentric_cutoff_norm_fderiv_le
#print axioms FunctionalInequalities.Analysis.tendsto_eLpNorm_of_exponents_tendsto_atTop
#print axioms FunctionalInequalities.L2.sq_sum_eLpNorm_le_dim_mul_integral_sum_sq
#print axioms LetwinCaccioppoliAudit.actual_log_gradient_morrey_same_witness
#print axioms LetwinCaccioppoliAudit.actual_log_gradient_potential_exp_same_witness
#print axioms FunctionalInequalities.Probability.integrable_exp_abs_of_moment_growth
#print axioms FunctionalInequalities.Probability.integrable_exp_toReal_of_moment_growth
#print axioms FunctionalInequalities.Probability.integrable_exp_toReal_of_scaled_high_moment_growth
#print axioms FunctionalInequalities.Analysis.measure_univ_le_of_ae_closedBall_ball_growth
#print axioms FunctionalInequalities.Analysis.restrict_ball_growth_of_local_ball_growth
#print axioms FunctionalInequalities.Analysis.exists_morrey_bound_of_cutoff_energy
#print axioms FunctionalInequalities.Analysis.lintegral_norm_sub_rpow_neg_le_of_ae_closedBall_ball_growth
#print axioms FunctionalInequalities.Analysis.lintegral_critical_radial_potential_rpow_le
#print axioms FunctionalInequalities.Analysis.lintegral_density_critical_potential_rpow_le
#print axioms FunctionalInequalities.Analysis.lintegral_density_critical_morrey_potential_rpow_le
#print axioms FunctionalInequalities.Analysis.integrable_exp_critical_morrey_potential
#print axioms FunctionalInequalities.Analysis.local_rpow_cutoff_weak_data
#print axioms FunctionalInequalities.Analysis.local_rpow_cutoff_weak_test
#print axioms FunctionalInequalities.Analysis.exists_bounded_weak_log_extension
#print axioms FunctionalInequalities.Analysis.local_weak_supersolution_caccioppoli
#print axioms FunctionalInequalities.Analysis.local_weak_supersolution_power_energy
#print axioms FunctionalInequalities.Analysis.local_weak_supersolution_log_energy
#print axioms FunctionalInequalities.Analysis.weak_cutoff_sobolev_gain_of_energy
#print axioms FunctionalInequalities.Analysis.weak_cutoff_sobolev_gain_of_energy_of_bounded_log
#print axioms FunctionalInequalities.Analysis.restrict_ball_growth_of_small_ball_growth_and_mass
#print axioms FunctionalInequalities.Analysis.exists_buffered_morrey_bound_of_cutoff_energy
#print axioms LetwinCaccioppoliAudit.actual_dyadic_power_gain_same_witness
#print axioms LetwinCaccioppoliAudit.actual_local_deficit_log_morrey_same_witness
#print axioms LetwinCaccioppoliAudit.actual_local_deficit_potential_exp_same_witness
#print axioms FunctionalInequalities.Analysis.map_restrict_convex_ray_le
#print axioms FunctionalInequalities.Analysis.measure_mul_abs_sub_average_le_riesz_of_contDiffOn
#print axioms FunctionalInequalities.Analysis.lintegral_riesz_potential_le_diameter_mul_lintegral
#print axioms FunctionalInequalities.L2.memLp_sqrt_sum_sq
#print axioms FunctionalInequalities.L2.gradient_density_l1_of_coordinate_l2
#print axioms FunctionalInequalities.Analysis.measure_mul_abs_sub_average_le_riesz_of_bounded_weak_data
#print axioms FunctionalInequalities.Analysis.integrable_exp_abs_sub_average_of_bounded_weak_morrey
#print axioms FunctionalInequalities.Probability.integral_rpow_mul_integral_rpow_neg_le_of_log_exp
#print axioms FunctionalInequalities.Analysis.exists_centered_buffered_morrey_bound_of_cutoff_energy
#print axioms LetwinCaccioppoliAudit.actual_local_deficit_john_nirenberg_same_witness
#print axioms LetwinCaccioppoliAudit.actual_local_deficit_log_moment_product_same_witness
#print axioms LetwinCaccioppoliAudit.actual_local_inputs_fixed_compact_same_witness
#print axioms LetwinCaccioppoliAudit.actual_joint_jn_moments_fixed_compact_same_witness

end LetwinCaccioppoliAudit

/-!
## Bounded actual weak Harnack inequality for the Letwin deficit

Proof clients of the weak Harnack inequality (Gilbarg–Trudinger 2001, Theorem 8.18, bounded data) for the normalized
Letwin deficit (Letwin, arXiv:2607.24164v1, Lemmas 2.2 and 2.7, smooth route), at ONE fixed-compact source witness. Each
client calls exactly one of the producers above in this file (the joint John–Nirenberg/moment producer for `n ≥ 2`, the
local inputs producer for `n = 1`), keeps the same transport potential `u`, the same `T`, the same weak logarithm `H, dH` and all
linear/power/log/Morrey fields, and chooses every constant before all centers, radii, caps and shifts.

* `actual_full_exponent_harnack_product_fixed_compact_same_witness` (`n > 2`, `0 < p < n/(n−2)`),
  `actual_full_exponent_harnack_product_two_fixed_compact_same_witness` (`n = 2`, every finite `p > 0`) and
  `actual_full_exponent_harnack_product_one_fixed_compact_same_witness` (`n = 1`, every finite `p > 0`, kernel 1, the
  exponential envelope `e ω₁ 3R` and `p0 = (32 U)⁻¹`): the small-exponent product on `B(x0,3R)` and `B(x0,2R)` and the full
  product `R^{−n/p} ‖s‖_{p, B(x0,2R)} ‖s⁻¹‖_{∞, B(x0,R)} ≤ Cfull p` under `F R² ≤ α δ`.
* `actual_essential_harnack_fixed_compact_same_witness` (every `n > 0`): the unshifted essential-infimum form
  `R^{−n/p} ‖w‖_{p, B(x0,2R)} ≤ C(p) (essinf_{B(x0,R)} w + M B R²/α)`, by case analysis on the dimension and the generic shift
  removal. Essential infimum (a.e.) only: no pointwise infimum, regular representative, oscillation decay or smoothness.

The local energy/Morrey/John–Nirenberg producers are the `LetwinCaccioppoliAudit` theorems above; this section adds only
their Moser/Harnack consumers.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace LetwinHarnackAudit
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

section OneDimensionalExponent

open Metric

/-- Uniform positive exponent for the separate one-dimensional log oscillation argument. -/
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

end OneDimensionalExponent

section HarnackWitness

variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

private theorem actual_joint_inverse_bound_fixed_compact_same_witness (h3 : 2 < n) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        let p0 := (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹ * (n : ℝ) /
          ((32 : ℝ)^n * (3 + (4 * β / α) * (n : ℝ) * D^2))
        0 < p0 ∧
        ∃ Cinv : ℝ, 0 < Cinv ∧
        ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → Metric.closedBall x0 (4 * R) ⊆ S →
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          ∀ δ : ℝ, 0 < δ →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := M * B
          let s := fun x => δ + max (w x) 0
          let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
          AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∃ Clog : ℝ, 0 ≤ Clog ∧ ∀ x, ‖Real.log (s x)‖ ≤ Clog) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) → ∀ r : ℝ,
            let g := fun x => χ x * s x ^ r
            let dg := fun (k : Fin n) x =>
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
              χ x * (r * s x ^ (r - 1)) * a k x
            (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport g ∧ Function.support g ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖g x‖ ≤ Cη) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
      ∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧
        MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧ (r < 1 / 2 →
    Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => s x ^ (2 * r) * ∑ k : Fin n,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
        (∫ x, s x ^ (2 * r) * ∑ k : Fin n,
          (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
      (4 * r ^ 2 * F / ((1 - 2 * r) * α)) *
        (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) →
            Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2)
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∫ x, χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / α) *
                (∫ x, ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
          (∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∃ BH : ℝ, 0 ≤ BH ∧ ∀ x, ‖H x‖ ≤ BH) ∧
            (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
                MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            (H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))]
              (fun x => Real.log (s x))) ∧
            (∀ k : Fin n, dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (Metric.closedBall x0 (4 * R))] b k) ∧
            (F * R^2 ≤ α * δ →
              Integrable (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              (∫ x in Metric.ball x0 (3 * R),
                Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|)) ≤
                2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                  (1 + 4 * ((n : ℝ) - 1)^2)) * (6 * R)^(n : ℝ) ∧
              Integrable (fun x => (s x)^p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              Integrable (fun x => (s x)^(-p0))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              (∫ x in Metric.ball x0 (3 * R), (s x)^p0) * (∫ x in Metric.ball x0 (3 * R), (s x)^(-p0)) ≤
                (2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                  (1 + 4 * ((n : ℝ) - 1)^2)) * (6 * R)^(n : ℝ))^2 ∧
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
                ENNReal.ofReal Cinv * ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
                  eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0)
                    ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R)))))) ∧
          ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
            (∫⁻ x in Metric.ball x0 (3 * R) ∩ Metric.ball c r,
              ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2))) ≤
              ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
                (16 : ℝ) ^ n * (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2) *
                r ^ ((n : ℝ) - 1)) := by
  obtain ⟨u,T,hnorm,hmap,D,hD,hS⟩ :=
    LetwinCaccioppoliAudit.actual_joint_jn_moments_fixed_compact_same_witness
      hn hκ hK hKc hKint hW hstrong μ hμ hiso (by omega : 2 ≤ n)
  refine ⟨u,T,hnorm,hmap,D,hD,fun S hSc => ?_⟩
  obtain ⟨α,β,B,hα,hβ,hB,hρB,hcb,hball⟩ := hS S hSc
  refine ⟨α,β,B,hα,hβ,hB,hρB,hcb,?_⟩
  intro p0
  obtain ⟨hp0,hball⟩ := hball
  obtain ⟨Cinv,hCinv,hinverse⟩ :=
    FunctionalInequalities.Analysis.inverse_essential_bound_of_cutoff_power_energy h3 hα hβ.le hp0
  refine ⟨hp0,Cinv,hCinv,fun x0 R hR hBS v M hM0 hcap δ hδ => ?_⟩
  intro w a F s b
  obtain ⟨hlogm,hlogB,hlin,hlogE,⟨H,dH,hHl,hHb,hHd,hHe,hdHe,hJN⟩,hmor⟩ :=
    hball x0 R hR hBS v M hM0 hcap δ hδ
  refine ⟨hlogm,hlogB,hlin,hlogE,⟨H,dH,hHl,hHb,hHd,hHe,hdHe,fun hFR => ?_⟩,hmor⟩
  obtain ⟨hexp,hbound,hpos,hneg,hprod⟩ := hJN hFR
  refine ⟨hexp,hbound,hpos,hneg,hprod,?_⟩
  have hF : 0 ≤ F := mul_nonneg hM0 hB
  have hs : ∀ x, δ ≤ s x := fun x => by dsimp only [s]; linarith [le_max_right (w x) 0]
  have hlogs : ∃ Clog : ℝ, ∀ x, ‖Real.log (s x)‖ ≤ Clog := by
    obtain ⟨Clog,-,hClog⟩ := hlogB
    exact ⟨Clog,hClog⟩
  have hi := hinverse x0 R hR s a F δ hF hδ hFR hs hlogm hlogs (by
    intro χ hχ hχc hχs r hr
    obtain ⟨⟨hgl,hgc,-,⟨Cg,-,hgb⟩,-,hgd⟩,he⟩ := hlin χ hχ hχc hχs r
    exact ⟨hgl,hgc,⟨Cg,hgb⟩,(fun k => ⟨(hgd k).1,(hgd k).2.1,(hgd k).2.2.2⟩),
      (he (by linarith : r < 1/2)).2.2.2⟩)
  have hμ : (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (2*R)) ≤
      (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R)) :=
    Measure.restrict_mono (Metric.closedBall_subset_ball (by linarith)) le_rfl
  have hnormle := eLpNorm_mono_measure (fun x => s x ^ (-1 : ℝ)) hμ (p := ENNReal.ofReal p0)
  exact hi.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hnormle zero_le) zero_le)

/-- **Full `0 < p < n/(n−2)` weak-Harnack PRODUCT at ONE fixed-compact witness** (`n > 2`). One call of the actual
inverse client; `Cweak = Cinv (c2(n) 6^n)^{2/p0}` and the family `Cfull p = Cpos p · Cweak` (`Cpos` from the generic
positive-energy endpoint) are fixed after `S`, its coefficients, `p0` and `Cinv`, before every center, radius, cap and
`δ`. The SAME-H moments and inverse endpoint give the small-`p0` product on `B(x0,3R)` (the bridge) and on
`B(x0,2R)`; the positive boost from `B(x0,3R)` gives every `p`. Not a pointwise infimum, oscillation or smoothness. -/
theorem actual_full_exponent_harnack_product_fixed_compact_same_witness (h3 : 2 < n) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        let p0 := (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹ * (n : ℝ) /
          ((32 : ℝ)^n * (3 + (4 * β / α) * (n : ℝ) * D^2))
        0 < p0 ∧
        ∃ Cinv : ℝ, 0 < Cinv ∧
        ∃ Cweak : ℝ, 0 < Cweak ∧
        ∃ Cfull : ℝ → ℝ,
          (∀ p : ℝ, 0 < p → p < (n : ℝ)/((n : ℝ)-2) → 0 < Cfull p) ∧
        ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → Metric.closedBall x0 (4 * R) ⊆ S →
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          ∀ δ : ℝ, 0 < δ →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := M * B
          let s := fun x => δ + max (w x) 0
          let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
          AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∃ Clog : ℝ, 0 ≤ Clog ∧ ∀ x, ‖Real.log (s x)‖ ≤ Clog) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) → ∀ r : ℝ,
            let g := fun x => χ x * s x ^ r
            let dg := fun (k : Fin n) x =>
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
              χ x * (r * s x ^ (r - 1)) * a k x
            (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport g ∧ Function.support g ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖g x‖ ≤ Cη) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
      ∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧
        MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧ (r < 1 / 2 →
    Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => s x ^ (2 * r) * ∑ k : Fin n,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
        (∫ x, s x ^ (2 * r) * ∑ k : Fin n,
          (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
      (4 * r ^ 2 * F / ((1 - 2 * r) * α)) *
        (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) →
            Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2)
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∫ x, χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / α) *
                (∫ x, ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
          (∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∃ BH : ℝ, 0 ≤ BH ∧ ∀ x, ‖H x‖ ≤ BH) ∧
            (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
                MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            (H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))]
              (fun x => Real.log (s x))) ∧
            (∀ k : Fin n, dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (Metric.closedBall x0 (4 * R))] b k) ∧
            (F * R^2 ≤ α * δ →
              Integrable (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              (∫ x in Metric.ball x0 (3 * R),
                Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|)) ≤
                2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                  (1 + 4 * ((n : ℝ) - 1)^2)) * (6 * R)^(n : ℝ) ∧
              Integrable (fun x => (s x)^p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              Integrable (fun x => (s x)^(-p0))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              (∫ x in Metric.ball x0 (3 * R), (s x)^p0) * (∫ x in Metric.ball x0 (3 * R), (s x)^(-p0)) ≤
                (2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                  (1 + 4 * ((n : ℝ) - 1)^2)) * (6 * R)^(n : ℝ))^2 ∧
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
                ENNReal.ofReal Cinv * ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
                  eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0)
                    ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R)))))) ∧
          (F*R^2 ≤ α*δ →
            ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
              eLpNorm s (ENNReal.ofReal p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R)))) *
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
              ENNReal.ofReal Cweak) ∧
          (F*R^2 ≤ α*δ →
            ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
              eLpNorm s (ENNReal.ofReal p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R)))) *
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
              ENNReal.ofReal Cweak) ∧
          (F*R^2 ≤ α*δ → ∀ p : ℝ, 0 < p → p < (n : ℝ)/((n : ℝ)-2) →
            ((ENNReal.ofReal R)^(-(n : ℝ)/p) *
              eLpNorm s (ENNReal.ofReal p)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R)))) *
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
              ENNReal.ofReal (Cfull p)) ∧
          ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
            (∫⁻ x in Metric.ball x0 (3 * R) ∩ Metric.ball c r,
              ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2))) ≤
              ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
                (16 : ℝ) ^ n * (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2) *
                r ^ ((n : ℝ) - 1)) := by
  -- ONE call of the actual inverse client `actual_joint_inverse_bound_fixed_compact_same_witness` (which calls the
  -- joint John–Nirenberg/moment producer of `Letwin.Caccioppoli` once)
  obtain ⟨u, T, hnorm, hmap, D, hD, hS⟩ :=
    actual_joint_inverse_bound_fixed_compact_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso h3
  refine ⟨u, T, hnorm, hmap, D, hD, fun S hSc => ?_⟩
  obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hrest⟩ := hS S hSc
  refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, ?_⟩
  intro p0
  obtain ⟨hp0, Cinv, hCinv, hball⟩ := hrest
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hvB : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne'
      measure_ball_lt_top.ne
  have hc2 : 0 < 2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) /
      ((n : ℝ) - 1)) * (1 + 4 * ((n : ℝ) - 1) ^ 2)) := by
    have : 0 < (n : ℝ) - 1 := by linarith
    positivity
  have hc6 : 0 < 2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) /
      ((n : ℝ) - 1)) * (1 + 4 * ((n : ℝ) - 1) ^ 2)) * (6 : ℝ) ^ (n : ℝ) :=
    mul_pos hc2 (Real.rpow_pos_of_pos (by norm_num) _)
  -- Cweak = Cinv (c2(n) 6^n)^(2/p0), constructed here after S, the coefficients, p0 and Cinv
  let Cweak : ℝ := Cinv * (2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
      (n : ℝ) / ((n : ℝ) - 1)) * (1 + 4 * ((n : ℝ) - 1) ^ 2)) * (6 : ℝ) ^ (n : ℝ)) ^ (2 / p0)
  have hCweak : 0 < Cweak := mul_pos hCinv (Real.rpow_pos_of_pos hc6 _)
  -- the positive-boost constants of the GENERIC endpoint at (α, β, p0, p), one for every admissible p, default 1
  let Cpos : ℝ → ℝ := fun p => if h : 0 < p ∧ p < (n : ℝ)/((n : ℝ)-2) then
    Classical.choose (FunctionalInequalities.Analysis.positive_norm_bound_of_cutoff_power_energy h3 hα hβ.le hp0 h.1 h.2)
    else 1
  have hCpos (p : ℝ) (hp : 0 < p) (hpg : p < (n : ℝ)/((n : ℝ)-2)) : Cpos p = Classical.choose
      (FunctionalInequalities.Analysis.positive_norm_bound_of_cutoff_power_energy h3 hα hβ.le hp0 hp hpg) :=
    dif_pos ⟨hp, hpg⟩
  refine ⟨hp0, Cinv, hCinv, Cweak, hCweak, fun p => Cpos p * Cweak, fun p hp hpg => ?_,
    fun x0 R hR hBS v M hM0 hcap δ hδ => ?_⟩
  · show 0 < Cpos p * Cweak
    rw [hCpos p hp hpg]
    exact mul_pos (Classical.choose_spec
      (FunctionalInequalities.Analysis.positive_norm_bound_of_cutoff_power_energy h3 hα hβ.le hp0 hp hpg)).1 hCweak
  intro w a F s b
  obtain ⟨hlogm, hlogB, hlin, hlogE, ⟨H, dH, hHl, hHb, hHd, hHe, hdHe, hJN⟩, hmor⟩ :=
    hball x0 R hR hBS v M hM0 hcap δ hδ
  have hsδ : ∀ x, δ ≤ s x := fun x => by
    change δ ≤ δ + max (w x) 0
    linarith [le_max_right (w x) 0]
  have hs : ∀ x, 0 < s x := fun x => hδ.trans_le (hsδ x)
  -- the SAME-H small-p0 product on B(x0,3R): the B3R bridge
  have hbridge : F*R^2 ≤ α*δ →
      ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R)))) *
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
        ENNReal.ofReal Cweak := fun hFR => by
    obtain ⟨-, -, hpos, hneg, hprod, hinv⟩ := hJN hFR
    exact FunctionalInequalities.Analysis.mul_eLpNorm_inv_top_le_of_moment_product _ _ _ le_rfl s hs hp0 hR hCinv.le hc2.le (by norm_num) hpos hneg hprod hinv
  -- the same product on B(x0,2R), by restriction
  have hsmall : F*R^2 ≤ α*δ →
      ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R)))) *
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
        ENNReal.ofReal Cweak := fun hFR => by
    obtain ⟨-, -, hpos, hneg, hprod, hinv⟩ := hJN hFR
    have hμ23 : (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2 * R)) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R)) :=
      Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl
    exact FunctionalInequalities.Analysis.mul_eLpNorm_inv_top_le_of_moment_product _ _ _ hμ23 s hs hp0 hR hCinv.le hc2.le (by norm_num) hpos hneg hprod hinv
  refine ⟨hlogm, hlogB, hlin, hlogE, ⟨H, dH, hHl, hHb, hHd, hHe, hdHe, hJN⟩, hsmall, hbridge,
    fun hFR p hp hpg => ?_, hmor⟩
  -- every 0 < p < n/(n-2): the GENERIC endpoint on the exported linear data and energies, times the SAME inverse norm
  obtain ⟨Clog, -, hlogb⟩ := hlogB
  have hF : 0 ≤ F := mul_nonneg hM0 hB
  have hspec := (Classical.choose_spec
    (FunctionalInequalities.Analysis.positive_norm_bound_of_cutoff_power_energy h3 hα hβ.le hp0 hp hpg)).2
    x0 R hR s a F δ hF hδ hFR hsδ hlogm ⟨Clog, hlogb⟩ (fun χ hχ hχc hχS r hr0 hr12 => by
      obtain ⟨⟨hgl, hgc, -, ⟨Cη, -, hgb⟩, -, hk⟩, hen⟩ := hlin χ hχ hχc hχS r
      exact ⟨hgl, hgc, ⟨Cη, hgb⟩, fun k => ⟨(hk k).1, (hk k).2.1, (hk k).2.2.2⟩, (hen hr12).2.2.2⟩)
  rw [← hCpos p hp hpg] at hspec
  calc
    _ ≤ (ENNReal.ofReal (Cpos p) * ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
          eLpNorm s (ENNReal.ofReal p0)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R))))) *
          eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) := by
      gcongr
    _ = ENNReal.ofReal (Cpos p) * (((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
          eLpNorm s (ENNReal.ofReal p0)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R)))) *
          eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R))) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal (Cpos p) * ENNReal.ofReal Cweak := by
      gcongr
      exact hbridge hFR
    _ = ENNReal.ofReal (Cpos p * Cweak) := (ENNReal.ofReal_mul (le_of_lt (by
      rw [hCpos p hp hpg]
      exact (Classical.choose_spec
        (FunctionalInequalities.Analysis.positive_norm_bound_of_cutoff_power_energy h3 hα hβ.le hp0 hp hpg)).1))).symm

theorem actual_full_exponent_harnack_product_two_fixed_compact_same_witness (h2 : n = 2) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        let p0 := (2 * ((n : ℝ) - 1) * Real.exp 1)⁻¹ * (n : ℝ) /
          ((32 : ℝ)^n * (3 + (4 * β / α) * (n : ℝ) * D^2))
        0 < p0 ∧
        ∃ Cinv : ℝ, 0 < Cinv ∧
        ∃ Cweak : ℝ, 0 < Cweak ∧
        ∃ Cfull : ℝ → ℝ,
          (∀ p : ℝ, 0 < p → 0 < Cfull p) ∧
        ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → Metric.closedBall x0 (4 * R) ⊆ S →
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          ∀ δ : ℝ, 0 < δ →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := M * B
          let s := fun x => δ + max (w x) 0
          let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
          AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∃ Clog : ℝ, 0 ≤ Clog ∧ ∀ x, ‖Real.log (s x)‖ ≤ Clog) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) → ∀ r : ℝ,
            let g := fun x => χ x * s x ^ r
            let dg := fun (k : Fin n) x =>
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
              χ x * (r * s x ^ (r - 1)) * a k x
            (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport g ∧ Function.support g ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖g x‖ ≤ Cη) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
      ∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧
        MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧ (r < 1 / 2 →
    Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => s x ^ (2 * r) * ∑ k : Fin n,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
        (∫ x, s x ^ (2 * r) * ∑ k : Fin n,
          (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
      (4 * r ^ 2 * F / ((1 - 2 * r) * α)) *
        (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) →
            Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2)
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∫ x, χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / α) *
                (∫ x, ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
          (∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∃ BH : ℝ, 0 ≤ BH ∧ ∀ x, ‖H x‖ ≤ BH) ∧
            (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
                MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            (H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))]
              (fun x => Real.log (s x))) ∧
            (∀ k : Fin n, dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (Metric.closedBall x0 (4 * R))] b k) ∧
            (F * R^2 ≤ α * δ →
              Integrable (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              (∫ x in Metric.ball x0 (3 * R),
                Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|)) ≤
                2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                  (1 + 4 * ((n : ℝ) - 1)^2)) * (6 * R)^(n : ℝ) ∧
              Integrable (fun x => (s x)^p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              Integrable (fun x => (s x)^(-p0))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              (∫ x in Metric.ball x0 (3 * R), (s x)^p0) * (∫ x in Metric.ball x0 (3 * R), (s x)^(-p0)) ≤
                (2 * (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) * (n : ℝ) / ((n : ℝ) - 1)) *
                  (1 + 4 * ((n : ℝ) - 1)^2)) * (6 * R)^(n : ℝ))^2 ∧
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
                ENNReal.ofReal Cinv * ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
                  eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0)
                    ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R)))))) ∧
          (F*R^2 ≤ α*δ →
            ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
              eLpNorm s (ENNReal.ofReal p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R)))) *
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
              ENNReal.ofReal Cweak) ∧
          (F*R^2 ≤ α*δ →
            ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
              eLpNorm s (ENNReal.ofReal p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R)))) *
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
              ENNReal.ofReal Cweak) ∧
          (F*R^2 ≤ α*δ → ∀ p : ℝ, 0 < p →
            ((ENNReal.ofReal R)^(-(n : ℝ)/p) *
              eLpNorm s (ENNReal.ofReal p)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R)))) *
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
              ENNReal.ofReal (Cfull p)) ∧
          ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
            (∫⁻ x in Metric.ball x0 (3 * R) ∩ Metric.ball c r,
              ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2))) ≤
              ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
                (16 : ℝ) ^ n * (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2) *
                r ^ ((n : ℝ) - 1)) := by
  subst h2
  -- ONE call of the joint JN/moment producer of `Letwin.Caccioppoli` (2 ≤ 2)
  obtain ⟨u,T,hnorm,hmap,D,hD,hS⟩ :=
    LetwinCaccioppoliAudit.actual_joint_jn_moments_fixed_compact_same_witness
      hn hκ hK hKc hKint hW hstrong μ hμ hiso (le_refl 2)
  refine ⟨u,T,hnorm,hmap,D,hD,fun S hSc => ?_⟩
  obtain ⟨α,β,B,hα,hβ,hB,hρB,hcb,hball⟩ := hS S hSc
  refine ⟨α,β,B,hα,hβ,hB,hρB,hcb,?_⟩
  intro p0
  obtain ⟨hp0,hball⟩ := hball
  -- the inverse constant from the NEW two-dimensional generic inverse, before every center/radius/cap/δ
  obtain ⟨Cinv,hCinv,hinverse⟩ :=
    FunctionalInequalities.Analysis.inverse_essential_bound_two_of_cutoff_power_energy hα hβ.le hp0
  have hvB : 0 < (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin 2))) 0 one_pos).ne'
      measure_ball_lt_top.ne
  have hc2 : 0 < 2 * (((volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) * ((2 : ℕ) : ℝ) /
      (((2 : ℕ) : ℝ) - 1)) * (1 + 4 * (((2 : ℕ) : ℝ) - 1) ^ 2)) := by
    have : 0 < ((2 : ℕ) : ℝ) - 1 := by norm_num
    positivity
  have hc6 : 0 < 2 * (((volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) * ((2 : ℕ) : ℝ) /
      (((2 : ℕ) : ℝ) - 1)) * (1 + 4 * (((2 : ℕ) : ℝ) - 1) ^ 2)) * (6 : ℝ) ^ ((2 : ℕ) : ℝ) :=
    mul_pos hc2 (Real.rpow_pos_of_pos (by norm_num) _)
  -- Cweak = Cinv (c2(2) 6²)^(2/p0), constructed here
  let Cweak : ℝ := Cinv * (2 * (((volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) *
      ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1)) * (1 + 4 * (((2 : ℕ) : ℝ) - 1) ^ 2)) * (6 : ℝ) ^ ((2 : ℕ) : ℝ)) ^ (2 / p0)
  have hCweak : 0 < Cweak := mul_pos hCinv (Real.rpow_pos_of_pos hc6 _)
  -- the positive constants of the NEW two-dimensional generic endpoint, every finite p > 0, default 1
  let Cpos : ℝ → ℝ := fun p => if h : 0 < p then
    Classical.choose (FunctionalInequalities.Analysis.positive_norm_bound_two_of_cutoff_power_energy hα hβ.le hp0 h)
    else 1
  have hCpos (p : ℝ) (hp : 0 < p) : Cpos p = Classical.choose
      (FunctionalInequalities.Analysis.positive_norm_bound_two_of_cutoff_power_energy hα hβ.le hp0 hp) := dif_pos hp
  refine ⟨hp0, Cinv, hCinv, Cweak, hCweak, fun p => Cpos p * Cweak, fun p hp => ?_,
    fun x0 R hR hBS v M hM0 hcap δ hδ => ?_⟩
  · show 0 < Cpos p * Cweak
    rw [hCpos p hp]
    exact mul_pos (Classical.choose_spec
      (FunctionalInequalities.Analysis.positive_norm_bound_two_of_cutoff_power_energy hα hβ.le hp0 hp)).1 hCweak
  intro w a F s b
  obtain ⟨hlogm,hlogB,hlin,hlogE,⟨H,dH,hHl,hHb,hHd,hHe,hdHe,hJN⟩,hmor⟩ :=
    hball x0 R hR hBS v M hM0 hcap δ hδ
  have hF : 0 ≤ F := mul_nonneg hM0 hB
  have hsδ : ∀ x, δ ≤ s x := fun x => by
    change δ ≤ δ + max (w x) 0
    linarith [le_max_right (w x) 0]
  have hs : ∀ x, 0 < s x := fun x => hδ.trans_le (hsδ x)
  obtain ⟨Clog,hClog0,hlogb⟩ := hlogB
  have hc2R : ((2 : ℕ) : ℝ) = 2 := by norm_num
  -- the inverse endpoint on B̄(x0,2R), restricted into the open B(x0,3R)
  have hinvB : F*R^2 ≤ α*δ →
      eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
        ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 R)) ≤
        ENNReal.ofReal Cinv * ((ENNReal.ofReal R)^(-((2 : ℕ) : ℝ)/p0) *
          eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0)
            ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 (3*R)))) := fun hFR => by
    have hi := hinverse x0 R hR s a F δ hF hδ hFR hsδ hlogm ⟨Clog,hlogb⟩ (by
      intro χ hχ hχc hχs r hr
      obtain ⟨⟨hgl,hgc,-,⟨Cg,-,hgb⟩,-,hgd⟩,he⟩ := hlin χ hχ hχc hχs r
      exact ⟨hgl,hgc,⟨Cg,hgb⟩,(fun k => ⟨(hgd k).1,(hgd k).2.1,(hgd k).2.2.1,(hgd k).2.2.2⟩),
        (he (by linarith : r < 1/2)).2.2.2⟩)
    have hμ23 : (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.closedBall x0 (2*R)) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 (3*R)) :=
      Measure.restrict_mono (Metric.closedBall_subset_ball (by linarith)) le_rfl
    have hnormle := eLpNorm_mono_measure (fun x => s x ^ (-1 : ℝ)) hμ23 (p := ENNReal.ofReal p0)
    have H := hi.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnormle zero_le) zero_le)
    rw [hc2R]
    exact H
  -- the SAME-H small-p0 product on B(x0,3R): the bridge
  have hbridge : F*R^2 ≤ α*δ →
      ((ENNReal.ofReal R)^(-((2 : ℕ) : ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0)
          ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 (3*R)))) *
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 R)) ≤
        ENNReal.ofReal Cweak := fun hFR => by
    obtain ⟨-, -, hpos, hneg, hprod⟩ := hJN hFR
    exact FunctionalInequalities.Analysis.mul_eLpNorm_inv_top_le_of_moment_product _ _ _ le_rfl s hs hp0 hR hCinv.le hc2.le (by norm_num) hpos hneg hprod (hinvB hFR)
  -- the same product on B(x0,2R), by restriction
  have hsmall : F*R^2 ≤ α*δ →
      ((ENNReal.ofReal R)^(-((2 : ℕ) : ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0)
          ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 (2*R)))) *
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 R)) ≤
        ENNReal.ofReal Cweak := fun hFR => by
    obtain ⟨-, -, hpos, hneg, hprod⟩ := hJN hFR
    have hμ23 : (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 (2 * R)) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 (3 * R)) :=
      Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl
    exact FunctionalInequalities.Analysis.mul_eLpNorm_inv_top_le_of_moment_product _ _ _ hμ23 s hs hp0 hR hCinv.le hc2.le (by norm_num) hpos hneg hprod (hinvB hFR)
  refine ⟨hlogm, ⟨Clog,hClog0,hlogb⟩, hlin, hlogE, ⟨H, dH, hHl, hHb, hHd, hHe, hdHe, fun hFR => ?_⟩,
    hsmall, hbridge, fun hFR p hp => ?_, hmor⟩
  · obtain ⟨hexp, hbound, hpos, hneg, hprod⟩ := hJN hFR
    exact ⟨hexp, hbound, hpos, hneg, hprod, hinvB hFR⟩
  -- every finite p > 0: the generic positive endpoint on the exported linear data, times the SAME inverse norm
  have hspec := (Classical.choose_spec
    (FunctionalInequalities.Analysis.positive_norm_bound_two_of_cutoff_power_energy hα hβ.le hp0 hp)).2
    x0 R hR s a F δ hF hδ hFR hsδ hlogm ⟨Clog, hlogb⟩ (fun χ hχ hχc hχS r hr0 hr12 => by
      obtain ⟨⟨hgl, hgc, -, ⟨Cη, -, hgb⟩, -, hk⟩, hen⟩ := hlin χ hχ hχc hχS r
      exact ⟨hgl, hgc, ⟨Cη, hgb⟩, fun k => ⟨(hk k).1, (hk k).2.1, (hk k).2.2.1, (hk k).2.2.2⟩,
        (hen hr12).2.2.2⟩)
  rw [← hCpos p hp] at hspec
  have hspec' : (ENNReal.ofReal R)^(-((2 : ℕ) : ℝ)/p) *
      eLpNorm s (ENNReal.ofReal p) ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 (2*R))) ≤
      ENNReal.ofReal (Cpos p) * ((ENNReal.ofReal R)^(-((2 : ℕ) : ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0) ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 (3*R)))) := by
    rw [hc2R]
    exact hspec
  calc
    _ ≤ (ENNReal.ofReal (Cpos p) * ((ENNReal.ofReal R)^(-((2 : ℕ) : ℝ)/p0) *
          eLpNorm s (ENNReal.ofReal p0)
            ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 (3*R))))) *
          eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
            ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 R)) := by
      gcongr
    _ = ENNReal.ofReal (Cpos p) * (((ENNReal.ofReal R)^(-((2 : ℕ) : ℝ)/p0) *
          eLpNorm s (ENNReal.ofReal p0)
            ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 (3*R)))) *
          eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
            ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball x0 R))) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal (Cpos p) * ENNReal.ofReal Cweak := by
      gcongr
      exact hbridge hFR
    _ = ENNReal.ofReal (Cpos p * Cweak) := (ENNReal.ofReal_mul (le_of_lt (by
      rw [hCpos p hp]
      exact (Classical.choose_spec
        (FunctionalInequalities.Analysis.positive_norm_bound_two_of_cutoff_power_energy hα hβ.le hp0 hp)).1))).symm

theorem actual_full_exponent_harnack_product_one_fixed_compact_same_witness (h1 : n = 1) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        let p0 := (32 * (3 + (4*β/α)*(n : ℝ)*D^2))⁻¹
        0 < p0 ∧
        ∃ Cinv : ℝ, 0 < Cinv ∧
        ∃ Cweak : ℝ, 0 < Cweak ∧
        ∃ Cfull : ℝ → ℝ,
          (∀ p : ℝ, 0 < p → 0 < Cfull p) ∧
        ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → Metric.closedBall x0 (4 * R) ⊆ S →
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          ∀ δ : ℝ, 0 < δ →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
          let F := M * B
          let s := fun x => δ + max (w x) 0
          let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
          AEStronglyMeasurable (fun x => Real.log (s x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∃ Clog : ℝ, 0 ≤ Clog ∧ ∀ x, ‖Real.log (s x)‖ ≤ Clog) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) → ∀ r : ℝ,
            let g := fun x => χ x * s x ^ r
            let dg := fun (k : Fin n) x =>
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
              χ x * (r * s x ^ (r - 1)) * a k x
            (LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport g ∧ Function.support g ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖g x‖ ≤ Cη) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ g x) ∧
      ∀ k : Fin n, HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dg k) ∧ Function.support (dg k) ⊆ tsupport χ ∧
        MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧ (r < 1 / 2 →
    Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => s x ^ (2 * r) * ∑ k : Fin n,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
        (∫ x, s x ^ (2 * r) * ∑ k : Fin n,
          (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
      (4 * r ^ 2 * F / ((1 - 2 * r) * α)) *
        (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧
          (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
            tsupport χ ⊆ Metric.closedBall x0 (4 * R) →
            Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2)
              (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∫ x, χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / α) *
                (∫ x, ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
                  ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) ∧
          (∃ (H : EuclideanSpace ℝ (Fin n) → ℝ) (dH : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
            LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∃ BH : ℝ, 0 ≤ BH ∧ ∀ x, ‖H x‖ ≤ BH) ∧
            (∀ k : Fin n, HasWeakDerivAlong H (dH k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
              ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
                MemLp (dH k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
            (H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))]
              (fun x => Real.log (s x))) ∧
            (∀ k : Fin n, dH k =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              (Metric.closedBall x0 (4 * R))] b k) ∧
            (F * R^2 ≤ α * δ →
              Integrable (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              (∫ x in Metric.ball x0 (3 * R),
                Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|)) ≤
                (Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) / 2) * (6 * R)^(n : ℝ) ∧
              Integrable (fun x => (s x)^p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              Integrable (fun x => (s x)^(-p0))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3 * R))) ∧
              (∫ x in Metric.ball x0 (3 * R), (s x)^p0) * (∫ x in Metric.ball x0 (3 * R), (s x)^(-p0)) ≤
                ((Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) / 2) * (6 * R)^(n : ℝ))^2 ∧
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
                ENNReal.ofReal Cinv * ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
                  eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0)
                    ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R)))))) ∧
          (F*R^2 ≤ α*δ →
            ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
              eLpNorm s (ENNReal.ofReal p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R)))) *
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
              ENNReal.ofReal Cweak) ∧
          (F*R^2 ≤ α*δ →
            ((ENNReal.ofReal R)^(-(n : ℝ)/p0) *
              eLpNorm s (ENNReal.ofReal p0)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (3*R)))) *
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
              ENNReal.ofReal Cweak) ∧
          (F*R^2 ≤ α*δ → ∀ p : ℝ, 0 < p →
            ((ENNReal.ofReal R)^(-(n : ℝ)/p) *
              eLpNorm s (ENNReal.ofReal p)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R)))) *
              eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) ≤
              ENNReal.ofReal (Cfull p)) ∧
          ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
            (∫⁻ x in Metric.ball x0 (3 * R) ∩ Metric.ball c r,
              ENNReal.ofReal (Real.sqrt (∑ k : Fin n, (b k x) ^ 2))) ≤
              ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
                (16 : ℝ) ^ n * (1 + (4 * β / α) * (n : ℝ) * D ^ 2 + (2 * F / (α * δ)) * R ^ 2) *
                r ^ ((n : ℝ) - 1)) := by
  subst h1
  -- ONE call of the actual local-inputs producer of `Letwin.Caccioppoli` (all n > 0)
  obtain ⟨u,T,hnorm,hmap,D,hD,hS⟩ :=
    LetwinCaccioppoliAudit.actual_local_inputs_fixed_compact_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u,T,hnorm,hmap,D,hD,fun S hSc => ?_⟩
  obtain ⟨α,β,B,hα,hβ,hB,hρB,hcb,hball⟩ := hS S hSc
  refine ⟨α,β,B,hα,hβ,hB,hρB,hcb,?_⟩
  intro p0
  have hc1R : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
  -- the uniform one-dimensional exponent p0 = (32 U)⁻¹, U = 3 + (4β/α) D², positive and < 1 before every datum
  have hp0U : p0 = (32*(3+(4*β/α)*D^2))⁻¹ := by
    show (32 * (3 + (4*β/α)*((1 : ℕ) : ℝ)*D^2))⁻¹ = _
    rw [hc1R, mul_one]
  have hQ : 0 ≤ (4*β/α)*D^2 := by positivity
  have hp0 : 0 < p0 := by rw [hp0U]; positivity
  have hp01 : p0 < 1 := by
    rw [hp0U]
    exact (inv_lt_one₀ (by positivity)).2 (by linarith)
  -- the direct generic constants, before every center/radius/cap/δ
  obtain ⟨Cinv,hCinv,hinverse⟩ :=
    FunctionalInequalities.Analysis.inverse_essential_bound_one_of_cutoff_power_energy hα hβ.le hp0
  obtain ⟨Cpos,hCpos,hpositive⟩ :=
    FunctionalInequalities.Analysis.positive_essential_bound_one_of_cutoff_power_energy hα hβ.le hp0 hp01
  have hω : 0 < (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin 1))) 0 one_pos).ne'
      measure_ball_lt_top.ne
  have hcE : 0 < Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) / 2 := by
    positivity
  -- Cweak = Cinv ((e ω₁ / 2) 6)^(2/p0) = Cinv (e ω₁ 3)^(2/p0)
  let Cweak : ℝ := Cinv * ((Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) / 2) *
    (6 : ℝ) ^ ((1 : ℕ) : ℝ)) ^ (2 / p0)
  have hCweak : 0 < Cweak := mul_pos hCinv (Real.rpow_pos_of_pos (mul_pos hcE (by positivity)) _)
  let Cstrong : ℝ := Cpos * Cweak
  have hCstrong : 0 < Cstrong := mul_pos hCpos hCweak
  refine ⟨hp0, Cinv, hCinv, Cweak, hCweak,
    fun p => Cstrong * ((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 2) ^ (1/p),
    fun p _ => mul_pos hCstrong (Real.rpow_pos_of_pos (by positivity) _),
    fun x0 R hR hBS v M hM0 hcap δ hδ => ?_⟩
  intro w a F s b
  obtain ⟨hlogm,hlogB,hlin,hlogE,⟨H,dH,hHl,hHb,hHd,hHe,hdHe⟩,hmor⟩ :=
    hball x0 R hR hBS v M hM0 hcap δ hδ
  have hF : 0 ≤ F := mul_nonneg hM0 hB
  have hsδ : ∀ x, δ ≤ s x := fun x => by
    change δ ≤ δ + max (w x) 0
    linarith [le_max_right (w x) 0]
  have hs : ∀ x, 0 < s x := fun x => hδ.trans_le (hsδ x)
  obtain ⟨Clog,hClog0,hlogb⟩ := hlogB
  obtain ⟨BH,hBH0,hBH⟩ := hHb
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  -- the direct inverse endpoint on B̄(x0,2R), restricted into the open B(x0,3R)
  have hinvB : F*R^2 ≤ α*δ →
      eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 R)) ≤
        ENNReal.ofReal Cinv * ((ENNReal.ofReal R)^(-((1 : ℕ) : ℝ)/p0) *
          eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0)
            ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3*R)))) := fun hFR => by
    have hi := hinverse x0 R hR s a F δ hF hδ hFR hsδ hlogm ⟨Clog,hlogb⟩ (by
      intro χ hχ hχc hχs r hr
      obtain ⟨⟨hgl,hgc,-,⟨Cg,-,hgb⟩,-,hgd⟩,he⟩ := hlin χ hχ hχc hχs r
      exact ⟨hgl,hgc,⟨Cg,hgb⟩,(fun k => ⟨(hgd k).1,(hgd k).2.1,(hgd k).2.2.1,(hgd k).2.2.2⟩),
        (he (by linarith : r < 1/2)).2.2.2⟩)
    have hμ23 : (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.closedBall x0 (2*R)) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3*R)) :=
      Measure.restrict_mono (Metric.closedBall_subset_ball (by linarith)) le_rfl
    have hnormle := eLpNorm_mono_measure (fun x => s x ^ (-1 : ℝ)) hμ23 (p := ENNReal.ofReal p0)
    have Hc := hi.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnormle zero_le) zero_le)
    rw [hc1R]
    exact Hc
  -- the one-dimensional replacement for John–Nirenberg on Ω = B(x0,3R), diameter 6R
  have hmom : F*R^2 ≤ α*δ →
      Integrable (fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|))
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3 * R))) ∧
      (∫ x in Metric.ball x0 (3 * R),
        Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|)) ≤
        (Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) / 2) *
          (6 * R)^((1 : ℕ) : ℝ) ∧
      Integrable (fun x => (s x)^p0)
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3 * R))) ∧
      Integrable (fun x => (s x)^(-p0))
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3 * R))) ∧
      (∫ x in Metric.ball x0 (3 * R), (s x)^p0) * (∫ x in Metric.ball x0 (3 * R), (s x)^(-p0)) ≤
        ((Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) / 2) *
          (6 * R)^((1 : ℕ) : ℝ))^2 := fun hFR => by
    have hΩsub : Metric.ball x0 (3*R) ⊆ Metric.closedBall x0 (4*R) :=
      Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
    have hdiam : ∀ y ∈ Metric.ball x0 (3*R), ∀ z ∈ Metric.ball x0 (3*R), dist y z ≤ 6*R := by
      intro y hy z hz
      have := dist_triangle_right y z x0
      rw [Metric.mem_ball] at hy hz
      linarith
    -- density mass from the SAME-witness Morrey field at c = x0, r = 3R (exponent n − 1 = 0)
    obtain ⟨-, -, hKpos, hpK⟩ := uniform_one_dimensional_exponent
      («ω» := (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1)) (D := D)
      hω hα hβ.le hF hδ hR hFR
    have hmassb : (∫⁻ z in Metric.ball x0 (3*R), ENNReal.ofReal (Real.sqrt (∑ i : Fin 1, (b i z)^2))) ≤
        ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 16 *
          (1+(4*β/α)*D^2+(2*F/(α*δ))*R^2)) := by
      have Hm := hmor x0 (3*R) (by positivity)
      rw [Set.inter_self, hc1R, sub_self, Real.rpow_zero, mul_one, pow_one, mul_one] at Hm
      exact Hm
    have hall : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3*R))),
        ∀ k, dH k x = b k x :=
      ae_all_iff.2 fun k => ae_restrict_of_ae_restrict_of_subset hΩsub (hdHe k)
    have hmass : (∫⁻ z in Metric.ball x0 (3*R), ENNReal.ofReal (Real.sqrt (∑ i : Fin 1, (dH i z)^2))) ≤
        ENNReal.ofReal ((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 16 *
          (1+(4*β/α)*D^2+(2*F/(α*δ))*R^2)) := by
      refine le_of_eq_of_le (lintegral_congr_ae ?_) hmassb
      filter_upwards [hall] with x hx
      simp only [hx]
    have htK : p0 * (6*R) * ((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 16 *
          (1+(4*β/α)*D^2+(2*F/(α*δ))*R^2)) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball x0 (3*R)) := by
      rw [hp0U, volume_ball_three_one x0 hR]
      exact hpK
    obtain ⟨-, hint, hbound⟩ := FunctionalInequalities.Analysis.integrable_exp_abs_sub_average_one_of_density_mass
      Metric.isOpen_ball (convex_ball x0 (3*R)) ⟨x0, Metric.mem_ball_self (by positivity)⟩
      (by positivity : (0 : ℝ) < 6*R) hKpos hp0.le hdiam hHl hBH (fun i => (hHd i).1) (fun i S hS => (hHd i).2 S hS)
      hmass htK
    -- transfer from H to log s on Ω (same H, same average)
    have hHΩ : H =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3*R))]
        fun x => Real.log (s x) := ae_restrict_of_ae_restrict_of_subset hΩsub hHe
    have havg : (⨍ y in Metric.ball x0 (3*R), H y) = ⨍ y in Metric.ball x0 (3*R), Real.log (s y) :=
      average_congr hHΩ
    have hexpEq : (fun x => Real.exp (p0 * |H x - ⨍ y in Metric.ball x0 (3*R), H y|)) =ᵐ[
        (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3*R))]
        fun x => Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3*R), Real.log (s y)|) := by
      filter_upwards [hHΩ] with x hx
      rw [hx, havg]
    have hExpInt := hint.congr hexpEq
    have hExpB : (∫ x in Metric.ball x0 (3 * R),
        Real.exp (p0 * |Real.log (s x) - ⨍ y in Metric.ball x0 (3 * R), Real.log (s y)|)) ≤
        (Real.exp 1 * (volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) / 2) *
          (6 * R)^((1 : ℕ) : ℝ) := by
      rw [← integral_congr_ae hexpEq]
      calc
        _ ≤ _ := hbound
        _ = _ := by
          rw [volume_ball_three_one x0 hR, hc1R, Real.rpow_one]
          ring
    have hlogΩ : AEStronglyMeasurable (fun x => Real.log (s x))
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3*R))) := hlogm.restrict
    obtain ⟨hpos, hneg, hprod⟩ := FunctionalInequalities.Probability.integral_rpow_mul_integral_rpow_neg_le_of_log_exp
      hp0.le (ae_of_all _ hs) hlogΩ hExpInt hExpB
    exact ⟨hExpInt, hExpB, hpos, hneg, hprod⟩
  -- the SAME-H small-p0 product on B(x0,3R): the bridge
  have hbridge : F*R^2 ≤ α*δ →
      ((ENNReal.ofReal R)^(-((1 : ℕ) : ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0)
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3*R)))) *
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 R)) ≤
        ENNReal.ofReal Cweak := fun hFR => by
    obtain ⟨-, -, hpos, hneg, hprod⟩ := hmom hFR
    exact FunctionalInequalities.Analysis.mul_eLpNorm_inv_top_le_of_moment_product _ _ _ le_rfl s hs hp0 hR hCinv.le hcE.le (by norm_num) hpos hneg hprod (hinvB hFR)
  -- the same product on B(x0,2R), by restriction
  have hsmall : F*R^2 ≤ α*δ →
      ((ENNReal.ofReal R)^(-((1 : ℕ) : ℝ)/p0) *
        eLpNorm s (ENNReal.ofReal p0)
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2*R)))) *
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 R)) ≤
        ENNReal.ofReal Cweak := fun hFR => by
    obtain ⟨-, -, hpos, hneg, hprod⟩ := hmom hFR
    have hμ23 : (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2 * R)) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3 * R)) :=
      Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl
    exact FunctionalInequalities.Analysis.mul_eLpNorm_inv_top_le_of_moment_product _ _ _ hμ23 s hs hp0 hR hCinv.le hcE.le (by norm_num) hpos hneg hprod (hinvB hFR)
  -- the strong product: the direct positive endpoint times the SAME inverse norm
  have hstrongP : F*R^2 ≤ α*δ →
      eLpNorm s ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (2*R))) *
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
          ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 R)) ≤
        ENNReal.ofReal Cstrong := fun hFR => by
    have hp := hpositive x0 R hR s a F δ hF hδ hFR hsδ hlogm ⟨Clog, hlogb⟩ (fun χ hχ hχc hχS r hr0 hr12 => by
      obtain ⟨⟨hgl, hgc, -, ⟨Cη, -, hgb⟩, -, hk⟩, hen⟩ := hlin χ hχ hχc hχS r
      exact ⟨hgl, hgc, ⟨Cη, hgb⟩, fun k => ⟨(hk k).1, (hk k).2.1, (hk k).2.2.1, (hk k).2.2.2⟩,
        (hen hr12).2.2.2⟩)
    have hbr := hbridge hFR
    rw [hc1R] at hbr
    calc
      _ ≤ (ENNReal.ofReal Cpos * ((ENNReal.ofReal R)^(-(1 : ℝ)/p0) *
            eLpNorm s (ENNReal.ofReal p0)
              ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3*R))))) *
            eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
              ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 R)) := by
        gcongr
      _ = ENNReal.ofReal Cpos * (((ENNReal.ofReal R)^(-(1 : ℝ)/p0) *
            eLpNorm s (ENNReal.ofReal p0)
              ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 (3*R)))) *
            eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞
              ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict (Metric.ball x0 R))) := mul_assoc _ _ _
      _ ≤ ENNReal.ofReal Cpos * ENNReal.ofReal Cweak := by gcongr
      _ = ENNReal.ofReal Cstrong := (ENNReal.ofReal_mul hCpos.le).symm
  refine ⟨hlogm, ⟨Clog,hClog0,hlogb⟩, hlin, hlogE, ⟨H, dH, hHl, ⟨BH,hBH0,hBH⟩, hHd, hHe, hdHe, fun hFR => ?_⟩,
    hsmall, hbridge, fun hFR p hp => ?_, hmor⟩
  · obtain ⟨hexp, hbound, hpos, hneg, hprod⟩ := hmom hFR
    exact ⟨hexp, hbound, hpos, hneg, hprod, hinvB hFR⟩
  -- every finite p > 0: ‖s‖_p(B2R) ≤ ‖s‖∞(B2R) · vol(B2R)^(1/p), vol(B2R) = ω₁ · 2R; the radius cancels exactly
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
  rw [hc1R]
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
      exact hstrongP hFR
    _ = ENNReal.ofReal (Cstrong * ((volume : Measure (EuclideanSpace ℝ (Fin 1))).real (Metric.ball 0 1) * 2) ^ (1/p)) :=
      (ENNReal.ofReal_mul hCstrong.le).symm

/-- **Bounded actual weak Harnack inequality, essential-infimum form, every dimension `n > 0`** (Gilbarg–Trudinger 2001,
Theorem 8.18, bounded data; Letwin 2607.24164v1, Lemmas 2.2/2.7). There is one transport potential `u` (normalized, pushing
`e^{-u}` forward to `μ` by `∇u`), and on each compact `S` coefficients `α, β, B` and ONE constant family `C`, fixed before
every center, radius, direction and cap, such that the deficit `w = M − vᵀ(∇²u)v` satisfies
`R^{−n/p} ‖w‖_{p, B(x0,2R)} ≤ C(p) (essinf_{B(x0,R)} w + M B R²/α)` for every `0 < p` with `n ≤ 2` or `p < n/(n−2)`.
The three cases use the full-exponent same-witness products (`n = 1`, `n = 2`, `n > 2`) and the generic shift removal; this is an
essential infimum (a.e.), not a pointwise infimum or a regular representative. -/
theorem actual_essential_harnack_fixed_compact_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∃ C : ℝ → ℝ,
          (∀ p : ℝ, 0 < p → (n ≤ 2 ∨ p < (n : ℝ)/((n : ℝ)-2)) → 0 < C p) ∧
        ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → Metric.closedBall x0 (4 * R) ⊆ S →
        ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
          (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          ∀ p : ℝ, 0 < p → (n ≤ 2 ∨ p < (n : ℝ)/((n : ℝ)-2)) →
            (ENNReal.ofReal R)^(-(n : ℝ)/p) *
              eLpNorm w (ENNReal.ofReal p)
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2*R))) ≤
              ENNReal.ofReal (C p) *
                (essInf (fun x => ENNReal.ofReal (w x))
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) +
                 ENNReal.ofReal (M * B * R^2 / α)) := by
  have hw4 (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ) (v : Fin n → ℝ) (M : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (hcap : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
        ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
        0 ≤ M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j := by
    filter_upwards [hcap] with x hx
    exact sub_nonneg.mpr hx
  obtain h1 | h2 | h3 : n = 1 ∨ n = 2 ∨ 2 < n := by omega
  · -- n = 1: the full-exponent direct one-dimensional product (kernel 1, exponential envelope e ω₁ 3R, every finite p > 0)
    obtain ⟨u, _T, hnorm, hmap, _D, _hD, hS⟩ := actual_full_exponent_harnack_product_one_fixed_compact_same_witness
      hn hκ hK hKc hKint hW hstrong μ hμ hiso h1
    refine ⟨u, hnorm, hmap, fun S hSc => ?_⟩
    obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hrest⟩ := hS S hSc
    obtain ⟨-, _, -, _, -, Cfull, hCfull, hball⟩ := hrest
    -- the constant family is the uniform Cfull, fixed before every center, radius, cap and shift
    refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, Cfull, fun p hp _ => hCfull p hp, fun x0 R hR hBS v M hM0 hcap => ?_⟩
    intro w p hp _
    have h4 := hw4 x0 R v M u hcap
    have h1 : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)), 0 ≤ w x :=
      ae_restrict_of_ae_restrict_of_subset
        (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) h4
    have h2 : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2 * R))), 0 ≤ w x :=
      ae_restrict_of_ae_restrict_of_subset
        (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) h4
    have : NeZero ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) :=
      ⟨by rw [Ne, Measure.restrict_eq_zero]; exact (Metric.measure_ball_pos _ x0 hR).ne'⟩
    have hk : 0 ≤ M * B * R ^ 2 / α := by positivity
    refine FunctionalInequalities.Analysis.unshifted_bound_of_shifted_inverse_norm_products
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2 * R))) w h1 h2 hk
      ((ENNReal.ofReal R) ^ (-(n : ℝ) / p)) (ENNReal.ofReal (Cfull p)) ENNReal.ofReal_ne_top (ENNReal.ofReal p)
      (fun δ hkδ => ?_) (fun δ hkδ => ?_)
    -- every shift δ > k = M B R²/α is an admissible source shift: δ > 0 and F R² ≤ α δ
    · obtain ⟨hlogm, -⟩ := hball x0 R hR hBS v M hM0 hcap δ (hk.trans_lt hkδ)
      exact hlogm.restrict
    · have hFR : M * B * R ^ 2 ≤ α * δ := by
        have h := (div_lt_iff₀ hα).1 hkδ
        rw [mul_comm α δ]
        exact h.le
      obtain ⟨-, -, -, -, -, -, -, hfull, -⟩ := hball x0 R hR hBS v M hM0 hcap δ (hk.trans_lt hkδ)
      exact hfull hFR p hp
  · -- n = 2: the full-exponent two-dimensional product (physical exponent 2 − 2/g, every finite p > 0)
    obtain ⟨u, _T, hnorm, hmap, _D, _hD, hS⟩ := actual_full_exponent_harnack_product_two_fixed_compact_same_witness
      hn hκ hK hKc hKint hW hstrong μ hμ hiso h2
    refine ⟨u, hnorm, hmap, fun S hSc => ?_⟩
    obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hrest⟩ := hS S hSc
    obtain ⟨-, _, -, _, -, Cfull, hCfull, hball⟩ := hrest
    -- the constant family is the uniform Cfull, fixed before every center, radius, cap and shift
    refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, Cfull, fun p hp _ => hCfull p hp, fun x0 R hR hBS v M hM0 hcap => ?_⟩
    intro w p hp _
    have h4 := hw4 x0 R v M u hcap
    have h1 : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)), 0 ≤ w x :=
      ae_restrict_of_ae_restrict_of_subset
        (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) h4
    have h2 : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2 * R))), 0 ≤ w x :=
      ae_restrict_of_ae_restrict_of_subset
        (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) h4
    have : NeZero ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) :=
      ⟨by rw [Ne, Measure.restrict_eq_zero]; exact (Metric.measure_ball_pos _ x0 hR).ne'⟩
    have hk : 0 ≤ M * B * R ^ 2 / α := by positivity
    refine FunctionalInequalities.Analysis.unshifted_bound_of_shifted_inverse_norm_products
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2 * R))) w h1 h2 hk
      ((ENNReal.ofReal R) ^ (-(n : ℝ) / p)) (ENNReal.ofReal (Cfull p)) ENNReal.ofReal_ne_top (ENNReal.ofReal p)
      (fun δ hkδ => ?_) (fun δ hkδ => ?_)
    -- every shift δ > k = M B R²/α is an admissible source shift: δ > 0 and F R² ≤ α δ
    · obtain ⟨hlogm, -⟩ := hball x0 R hR hBS v M hM0 hcap δ (hk.trans_lt hkδ)
      exact hlogm.restrict
    · have hFR : M * B * R ^ 2 ≤ α * δ := by
        have h := (div_lt_iff₀ hα).1 hkδ
        rw [mul_comm α δ]
        exact h.le
      obtain ⟨-, -, -, -, -, -, -, hfull, -⟩ := hball x0 R hR hBS v M hM0 hcap δ (hk.trans_lt hkδ)
      exact hfull hFR p hp
  · -- n > 2: the full-exponent critical-range product, 0 < p < n/(n−2) (the alternative n ≤ 2 is impossible)
    obtain ⟨u, _T, hnorm, hmap, _D, _hD, hS⟩ := actual_full_exponent_harnack_product_fixed_compact_same_witness
      hn hκ hK hKc hKint hW hstrong μ hμ hiso h3
    refine ⟨u, hnorm, hmap, fun S hSc => ?_⟩
    obtain ⟨α, β, B, hα, hβ, hB, hρB, hcb, hrest⟩ := hS S hSc
    obtain ⟨-, _, -, _, -, Cfull, hCfull, hball⟩ := hrest
    -- the constant family is the uniform Cfull, fixed before every center, radius, cap and shift
    refine ⟨α, β, B, hα, hβ, hB, hρB, hcb, Cfull, fun p hp hcl => hCfull p hp (hcl.resolve_left (by omega)), fun x0 R hR hBS v M hM0 hcap => ?_⟩
    intro w p hp hcl
    have h4 := hw4 x0 R v M u hcap
    have h1 : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)), 0 ≤ w x :=
      ae_restrict_of_ae_restrict_of_subset
        (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) h4
    have h2 : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2 * R))), 0 ≤ w x :=
      ae_restrict_of_ae_restrict_of_subset
        (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))) h4
    have : NeZero ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R)) :=
      ⟨by rw [Ne, Measure.restrict_eq_zero]; exact (Metric.measure_ball_pos _ x0 hR).ne'⟩
    have hk : 0 ≤ M * B * R ^ 2 / α := by positivity
    refine FunctionalInequalities.Analysis.unshifted_bound_of_shifted_inverse_norm_products
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 R))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x0 (2 * R))) w h1 h2 hk
      ((ENNReal.ofReal R) ^ (-(n : ℝ) / p)) (ENNReal.ofReal (Cfull p)) ENNReal.ofReal_ne_top (ENNReal.ofReal p)
      (fun δ hkδ => ?_) (fun δ hkδ => ?_)
    -- every shift δ > k = M B R²/α is an admissible source shift: δ > 0 and F R² ≤ α δ
    · obtain ⟨hlogm, -⟩ := hball x0 R hR hBS v M hM0 hcap δ (hk.trans_lt hkδ)
      exact hlogm.restrict
    · have hFR : M * B * R ^ 2 ≤ α * δ := by
        have h := (div_lt_iff₀ hα).1 hkδ
        rw [mul_comm α δ]
        exact h.le
      obtain ⟨-, -, -, -, -, -, -, hfull, -⟩ := hball x0 R hR hBS v M hM0 hcap δ (hk.trans_lt hkδ)
      exact hfull hFR p hp (hcl.resolve_left (by omega))

end HarnackWitness

#print axioms FunctionalInequalities.Analysis.geometric_exponential_recurrence_bound
#print axioms FunctionalInequalities.Analysis.eLpNorm_top_le_of_shrinking_norm_steps
#print axioms FunctionalInequalities.Analysis.finite_normalized_eLpNorm_sequence_bound
#print axioms FunctionalInequalities.Analysis.unshifted_bound_of_shifted_inverse_norm_products
#print axioms FunctionalInequalities.Analysis.mul_eLpNorm_inv_top_le_of_moment_product
#print axioms FunctionalInequalities.Analysis.scaled_weak_cutoff_sobolev_gain_two_of_bounded_log
#print axioms FunctionalInequalities.Analysis.weak_cutoff_sobolev_gain_of_energy_one_of_support_of_bounded_log
#print axioms FunctionalInequalities.Analysis.integrable_exp_abs_sub_average_one_of_density_mass
#print axioms FunctionalInequalities.Analysis.inverse_essential_bound_of_cutoff_power_energy
#print axioms FunctionalInequalities.Analysis.positive_norm_bound_of_cutoff_power_energy
#print axioms FunctionalInequalities.Analysis.inverse_essential_bound_two_of_cutoff_power_energy
#print axioms FunctionalInequalities.Analysis.positive_norm_bound_two_of_cutoff_power_energy
#print axioms FunctionalInequalities.Analysis.inverse_essential_bound_one_of_cutoff_power_energy
#print axioms FunctionalInequalities.Analysis.positive_essential_bound_one_of_cutoff_power_energy
#print axioms LetwinHarnackAudit.actual_full_exponent_harnack_product_fixed_compact_same_witness
#print axioms LetwinHarnackAudit.actual_full_exponent_harnack_product_two_fixed_compact_same_witness
#print axioms LetwinHarnackAudit.actual_full_exponent_harnack_product_one_fixed_compact_same_witness
#print axioms LetwinHarnackAudit.actual_essential_harnack_fixed_compact_same_witness

end LetwinHarnackAudit

noncomputable section
open MeasureTheory Set Metric Matrix
open scoped ContDiff ENNReal

namespace LetwinHarnackAudit
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
section JointRegularWitness
variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- **Weak Harnack for the directional deficits at ONE regular moment potential** (Letwin, arXiv:2607.24164v1,
Lemmas 2.2/2.7 smooth route, via Gilbarg–Trudinger 2001, Theorem 8.18). One potential `u` with all its regular-class
data (convexity, Lipschitz, normalization and pushforward, `C¹` with `16/κ`-Lipschitz gradient, Lipschitz right side,
a.e. positive definite Hessian with log-determinant identity and cap, weak Hessian tensor), and for every compact `S`
coefficients `α, β, B` and a family `C(p)`, chosen before every center, radius, direction and cap, such that every
deficit `M − vᵀ∇²u v` capped a.e. on `B̄(x0,4R)` satisfies the essential weak Harnack inequality with forcing
`M B R²/α`. Strong regular class only; not oscillation decay, `C^{2,α}` or the merely convex source class. -/
theorem harnack_joint_regular_potential :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∃ C : ℝ → ℝ,
          (∀ p : ℝ, 0 < p → (n ≤ 2 ∨ p < (n:ℝ)/((n:ℝ)-2)) → 0 < C p) ∧
          ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → closedBall x0 (4*R) ⊆ S →
          ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
            (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall x0 (4*R))),
              ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          ∀ p : ℝ, 0 < p → (n ≤ 2 ∨ p < (n:ℝ)/((n:ℝ)-2)) →
            (ENNReal.ofReal R)^(-(n:ℝ)/p) * eLpNorm w (ENNReal.ofReal p)
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (2*R))) ≤
            ENNReal.ofReal (C p) *
              (essInf (fun x => ENNReal.ofReal (w x))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) +
              ENNReal.ofReal (M*B*R^2/α)) := by
  obtain ⟨u, L, LF, T, hold, -, hcoef⟩ :=
    exists_regular_moment_directional_hessian_subsolution hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨hconv, hl, hnorm, hmap, hC1, hG, hF, -, hd, hT, -, hfirst, hInv, -⟩ := hold
  have hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
    filter_upwards [hd] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]
  have hVc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he : (fun y => W y - κ / 2 * ‖y‖ ^ 2) + (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  have hρc : Continuous fun x => Real.exp (-u x) := Real.continuous_exp.comp hC1.continuous.neg
  have hAm (i j : Fin n) : AEStronglyMeasurable (fun x => (Real.exp (-u x) • (hessianMatrix u x)⁻¹) i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hLoc : LocallyIntegrable (fun x => (hessianMatrix u x)⁻¹ i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply locallyIntegrable_iff.mpr
      intro S hS
      let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
        isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
      exact ((hInv i i j).2.2 S hS).integrable (by simp)
    change AEStronglyMeasurable (fun x => Real.exp (-u x) * (hessianMatrix u x)⁻¹ i j) volume
    exact hρc.aestronglyMeasurable.mul hLoc.aestronglyMeasurable
  refine ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,fun S hSc => ?_⟩
  -- one choice of `α, β` and of the density bound `B` on `B_4R`
  obtain ⟨c0, c1, hc0, hc1, hcb⟩ := hcoef S hSc
  obtain ⟨Cρ, hCρ⟩ := hSc.exists_bound_of_continuousOn hρc.continuousOn
  have hρB (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) :
      Real.exp (-u x) ≤ max Cρ 0 := by
    have h := hCρ x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    exact h.trans (le_max_left _ _)
  obtain ⟨C,hC,hH⟩ := FunctionalInequalities.Analysis.bounded_weak_harnack_of_given_data hn hc0 hc1
  refine ⟨c0,c1,max Cρ 0,hc0,hc1,le_max_right _ _,hρB,hcb,C,hC,?_⟩
  intro x0 R hR hBallS v M hM0 hcap w p hp hcl
  let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
  let F := M * max Cρ 0
  have hSm : MeasurableSet (Metric.closedBall x0 (4 * R)) := Metric.isClosed_closedBall.measurableSet
  classical
  set hv := fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j with hhvdef
  -- `0 ≤ h_v` everywhere a.e. (positive Hessian); `h_v ≤ M` only on `B_4R`
  have hv0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ hv x := by
    filter_upwards [hd] with x hx
    have h0 := hx.1.posSemidef.dotProduct_mulVec_nonneg v
    simp only [star_trivial] at h0
    have hquad : dotProduct v ((hessianMatrix u x).mulVec v) =
        ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hquad] at h0
    exact h0
  have hcap' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ Metric.closedBall x0 (4 * R) → hv x ≤ M :=
    (ae_restrict_iff' hSm).1 hcap
  have hw0S : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
      0 ≤ w x := hcap.mono fun x hx => by simp only [w]; linarith
  -- weak data of `w` from the weak Hessian tensor
  have hsum (k : Fin n) := hasWeakDerivAlong_finsetSum_mul (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v p.1 * v p.2) (f := fun p x => hessianMatrix u x p.1 p.2) (df := fun p x => T x k p.1 p.2)
    (v := EuclideanSpace.basisFun (Fin n) ℝ k) (fun p _ => (hT k p.1 p.2).1) (fun p _ => (hT k p.1 p.2).2)
  have hhv (k : Fin n) : HasWeakDerivAlong hv (fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    (hsum k).1.congr_ae (ae_of_all _ fun x => by simp only [hv, Fintype.sum_prod_type])
      (ae_of_all _ fun x => by simp only [Fintype.sum_prod_type])
  have htv2 (k : Fin n) : ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
      MemLp (fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') := by
    intro S' hS'
    have h := (hsum k).2 S' hS'
    simpa only [Fintype.sum_prod_type] using h
  have hwweak (k : Fin n) : HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    ((hhv k).const_add_mul M (-1)).congr_ae
      (ae_of_all _ fun x => by simp only [w, hv]; ring) (ae_of_all _ fun x => by simp only [a]; ring)
  have ha2 (k : Fin n) : ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') :=
    fun S' hS' => (htv2 k S' hS').neg
  -- the global Hessian cap bounds `w` everywhere, also where it is negative
  set Hb : ℝ := ∑ i : Fin n, ∑ j : Fin n, ‖v i * v j‖ * ((Real.toNNReal (16 / κ) : NNReal) : ℝ)
  have hvb (x : EuclideanSpace ℝ (Fin n)) : ‖hv x‖ ≤ Hb := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j) (norm_nonneg _)
  have hwb (x : EuclideanSpace ℝ (Fin n)) : ‖w x‖ ≤ ‖M‖ + Hb :=
    (norm_sub_le _ _).trans (by linarith [hvb x])
  have hwl : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))) := (hwweak ⟨0, hn⟩).1
  have hF0 : 0 ≤ F := mul_nonneg hM0 (le_max_right _ _)
  -- the weak supersolution inequality with the LOCAL forcing `F = M B`, for every cutoff in `B_4R`
  have hsub
      (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
      (hηl : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (hηb : ∃ Bη : ℝ, 0 ≤ Bη ∧ ∀ x, ‖η x‖ ≤ Bη) (hηc : HasCompactSupport η)
      (hηs : Function.support η ⊆ Metric.closedBall x0 (4 * R)) (hη0 : ∀ x, 0 ≤ η x)
      (hηd : ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ Metric.closedBall x0 (4 * R) ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, dotProduct (fun k => a k x) (((fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹) x).mulVec
          (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨Bη, -, hBη⟩ := hηb
    obtain ⟨h1, h2, h3⟩ := integral_directional_hessian_flux_le_of_bounded_weak_test hC1 hl hG
      (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet T hT hInv (fun i => (hfirst i).2.2.2.2) hVc
      (hd.mono fun x hx => hx.1) v hηl hBη hηc (fun k => (hηd k).1) (fun k => (hηd k).2.1) (fun k => (hηd k).2.2.2)
      (ae_of_all _ hη0)
    have hηint : Integrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (integrableOn_iff_integrable_of_support_subset (subset_tsupport η)).1 (hηl.integrableOn_isCompact hηc)
    have hL : (fun x => dotProduct (fun k => a k x)
        (((fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹) x).mulVec (fun k => dη k x))) =
        fun x => -(Real.exp (-u x) * (∑ k : Fin n,
          (∑ b : Fin n, (hessianMatrix u x)⁻¹ b k *
            (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) * dη k x)) := by
      funext x
      simp only [dotProduct, Matrix.mulVec, a, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
        neg_mul, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hL, integral_neg]
    have hR' : (∫ x, Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) * η x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ ∫ x, (M * max Cρ 0) * η x ∂volume := by
      refine integral_mono_ae h2 (hηint.const_mul _) ?_
      filter_upwards [hv0, hcap'] with x hx0 hxc
      by_cases hxs : x ∈ Metric.closedBall x0 (4 * R)
      · have hh : Real.exp (-u x) * hv x ≤ M * max Cρ 0 := by
          calc Real.exp (-u x) * hv x ≤ max Cρ 0 * M :=
                mul_le_mul (hρB x (hBallS hxs)) (hxc hxs) hx0 (le_max_right _ _)
            _ = M * max Cρ 0 := mul_comm _ _
        exact mul_le_mul_of_nonneg_right hh (hη0 x)
      · have h0 : η x = 0 := by
          by_contra h; exact hxs (hηs h)
        simp only [h0, mul_zero, le_refl]
    rw [integral_const_mul] at hR'
    change -(M * max Cρ 0) * _ ≤ _
    linarith
  have hCb : 0 ≤ ‖M‖ + Hb := (norm_nonneg (w 0)).trans (hwb 0)
  exact hH x0 R hR (fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹) w a F
    hwl ⟨_,hCb,hwb⟩ hwweak ha2 hAm hw0S
    (ae_restrict_of_ae_restrict_of_subset hBallS hcb) hF0 hsub p hp hcl
end JointRegularWitness
end LetwinHarnackAudit

#print axioms LetwinHarnackAudit.harnack_joint_regular_potential
#print axioms FunctionalInequalities.Analysis.bounded_weak_harnack_of_given_data
