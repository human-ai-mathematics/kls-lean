module

public import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian

/-!
# Audit client of rough nonlinear testing at the regular-class witness

One witness `u, L, LF, T` of `exists_regular_moment_directional_hessian_subsolution` is selected
once. At the same
`b = χ · vᵀ∇²u v` and derivative data `ab` from `directional_cutoff_data`, the client proves:

* the rough square test `(χ h_v)²` with the directional weak subsolution inequality;
* `b ≥ 0` a.e., from the a.e. positive definite Hessian and `χ ≥ 0`;
* the weak shifted logarithm and the weak shifted real powers of `b`, for every real `q`;
* the weak `sin` chain of `b`.

It also checks an actual bump cutoff with `q = -1/2` and `q = 0`, the scalar profile at both
endpoints of `[0, B]`, the
chain rule in dimension zero, and the old-producer prefix.

None of this is the positive outer-cutoff power test, Caccioppoli, Moser iteration or Harnack.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace LetwinRoughTestingAudit

open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

/--
The shifted real power profile at both endpoints of the physical interval, for a negative
non-integer exponent. -/
theorem rpow_profile_endpoints {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ Φ : ℝ → ℝ,
      Φ 0 = 0 ∧
        Φ B = (δ + B) ^ (-1 / 2 : ℝ) - δ ^ (-1 / 2 : ℝ) ∧
          deriv Φ 0 = (-1 / 2 : ℝ) * (δ + 0) ^ ((-1 / 2 : ℝ) - 1) := by
  obtain ⟨Φ, D, -, -, -, h0, he⟩ := exists_smooth_compact_rpow_shift_extension hδ hB (-1 / 2)
  exact ⟨Φ, h0, (he B ⟨hB, le_rfl⟩).1, (he 0 ⟨le_rfl, hB⟩).2⟩

/-- The compact bounded weak chain rule in dimension zero. -/
theorem chain_zero {η : EuclideanSpace ℝ (Fin 0) → ℝ} {a : Fin 0 → EuclideanSpace ℝ (Fin 0) → ℝ}
    {C : ℝ} (hη : LocallyIntegrable η volume) (hb : ∀ x, ‖η x‖ ≤ C) (hc : HasCompactSupport η)
    {Φ : ℝ → ℝ} {D : NNReal} (hΦ : ContDiff ℝ 1 Φ) (hL : LipschitzWith D Φ) (h0 : Φ 0 = 0) :
    HasCompactSupport (fun x => Φ (η x)) :=
  (hasWeakDerivAlong_comp_of_compact_bounded (a := a) hη hb hc
      (fun i => absurd i.2 (Nat.not_lt_zero _)) (fun i => absurd i.2 (Nat.not_lt_zero _))
      (fun i => absurd i.2 (Nat.not_lt_zero _)) hΦ hL h0).1

section SameWitness

variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
  {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
  (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ :
    (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/--
One selected witness: normalized moment potential with the actual pushforward, and at the same `b,
ab, T` the rough
square inequality, `b ≥ 0` a.e., the weak shifted logarithm, the weak shifted powers for every real
`q` and the weak `sin`
chain. -/
theorem rough_tests_same_witness (v : Fin n → ℝ) {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (hχn : ∀ x, 0 ≤ χ x) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T :
      EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
            (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
          let b := fun x => χ x * ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          let ab := fun (k : Fin n) x =>
            χ x * (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j) +
              fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) *
                ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          (∀ k : Fin n,
              HasWeakDerivAlong (fun x => b x * b x) (fun x => ab k x * b x + b x * ab k x)
                (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
            (∫ x,
                  Real.exp (-u x) *
                    (∑ k : Fin n,
                      (∑ c : Fin n,
                          (hessianMatrix u x)⁻¹ c k *
                            (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x c i j)) *
                        (ab k x * b x +
                          b x * ab k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                (∫ x,
                  Real.exp (-u x) *
                      (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) *
                    (b x * b x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
              (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ b x) ∧
                (∀ k : Fin n,
                    HasWeakDerivAlong (fun x => Real.log (δ + b x) - Real.log δ)
                      (fun x => (δ + b x)⁻¹ * ab k x) (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
                  (∀ q : ℝ,
                      ∀ k : Fin n,
                        HasWeakDerivAlong (fun x => (δ + b x) ^ q - δ ^ q)
                            (fun x => (q * (δ + b x) ^ (q - 1)) * ab k x)
                            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                          MemLp (fun x => (q * (δ + b x) ^ (q - 1)) * ab k x) 2
                            (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
                    (∀ k : Fin n,
                      HasWeakDerivAlong (fun x => Real.sin (b x))
                        (fun x => Real.cos (b x) * ab k x)
                        (EuclideanSpace.basisFun (Fin n) ℝ k)) := by
  obtain ⟨u, L, LF, T, hold, -, -⟩ :=
    exists_regular_moment_directional_hessian_subsolution hn hκ hK hKc hKint hW hstrong μ hμ
      hiso
  obtain ⟨-, hl, hnorm, hmap, hC1, hG, hF, -, hd, hT, -, hfirst, hInv, -⟩ := hold
  have hdet :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
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
  refine ⟨u, T, hnorm, hmap, ?_⟩
  intro b ab
  obtain ⟨hsq, -, -, -, -, -, hineq⟩ :=
    rough_square_test_of_weak_data hC1 hl hG (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet
      T hT hInv (fun i => (hfirst i).2.2.2.2) hVc (hd.mono fun x hx => hx.1) v hχ hχc
  obtain ⟨hbm, hbc, ⟨B, -, hbb⟩, hbd⟩ := directional_cutoff_data hG T hT v hχ hχc
  have hb0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ b x := by
    filter_upwards [hd] with x hx
    have h := hx.1.posSemidef.dotProduct_mulVec_nonneg v
    have he :
      dotProduct (star v) ((hessianMatrix u x).mulVec v) =
        ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [he] at h
    exact mul_nonneg (hχn x) h
  have hloc : LocallyIntegrable b (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact
      (memLp_top_of_bound hbm.aestronglyMeasurable.restrict B (ae_of_all _ hbb)).integrable
        le_top
  have hlog :=
    hasWeakDerivAlong_log_shift_of_ae_nonneg_compact_bounded hloc hbb hbc (fun k => (hbd k).1)
      (fun k => (hbd k).2.1) (fun k => (hbd k).2.2) hb0 hδ
  have hpow (q : ℝ) :=
    hasWeakDerivAlong_rpow_shift_of_ae_nonneg_compact_bounded hloc hbb hbc (fun k => (hbd k).1)
      (fun k => (hbd k).2.1) (fun k => (hbd k).2.2) hb0 hδ q
  have hsin :=
    hasWeakDerivAlong_comp_of_compact_bounded hloc hbb hbc (fun k => (hbd k).1)
      (fun k => (hbd k).2.1) (fun k => (hbd k).2.2) (Φ := Real.sin)
      (Real.contDiff_sin.of_le (WithTop.coe_le_coe.mpr le_top)) Real.lipschitzWith_sin
      Real.sin_zero
  simp only [Real.deriv_sin] at hsin
  exact
    ⟨fun k => (hsq k).1, hineq, hb0, fun k => (hlog.2 k).1, fun q k =>
      ⟨((hpow q).2 k).1, ((hpow q).2 k).2.2⟩, fun k => (hsin.2 k).1⟩

/--
The canonical producer's first component elaborates as
`exists_regular_moment_weak_hessian_evolution` at the
selected `u, L, LF, T`. -/
example : True := by
  obtain ⟨u, L, LF, T, hold, -⟩ :=
    exists_regular_moment_directional_hessian_subsolution hn hκ hK hKc hKint hW hstrong μ hμ
      hiso
  have _ :
    type_of%
      (exists_regular_moment_weak_hessian_evolution hn hκ hK hKc hKint hW hstrong μ hμ hiso) :=
    ⟨u, L, LF, T, hold⟩
  trivial

/-- An actual nonnegative bump cutoff with `q = -1/2` and `q = 0`. -/
theorem bump_instances (v : Fin n → ℝ) (f : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (T :
      EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      let b := fun x => f x * ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
      let ab := fun (k : Fin n) x =>
        f x * (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j) +
          fderiv ℝ (fun y => f y) x (EuclideanSpace.basisFun (Fin n) ℝ k) *
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
      HasWeakDerivAlong (fun x => (1 + b x) ^ (-1 / 2 : ℝ) - 1 ^ (-1 / 2 : ℝ))
          (fun x => ((-1 / 2 : ℝ) * (1 + b x) ^ ((-1 / 2 : ℝ) - 1)) * ab ⟨0, hn⟩ x)
          (EuclideanSpace.basisFun (Fin n) ℝ ⟨0, hn⟩) ∧
        HasWeakDerivAlong (fun x => (1 + b x) ^ (0 : ℝ) - 1 ^ (0 : ℝ))
          (fun x => ((0 : ℝ) * (1 + b x) ^ ((0 : ℝ) - 1)) * ab ⟨0, hn⟩ x)
          (EuclideanSpace.basisFun (Fin n) ℝ ⟨0, hn⟩) := by
  obtain ⟨u, T, -, -, -, -, -, -, hpow, -⟩ :=
    rough_tests_same_witness hn hκ hK hKc hKint hW hstrong μ hμ hiso v (χ := fun x => f x)
      (f.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) f.hasCompactSupport (fun _ => f.nonneg)
      one_pos
  exact ⟨u, T, (hpow (-1 / 2) ⟨0, hn⟩).1, (hpow 0 ⟨0, hn⟩).1⟩

end SameWitness

end LetwinRoughTestingAudit

#print axioms LetwinRoughTestingAudit.rpow_profile_endpoints
#print axioms LetwinRoughTestingAudit.chain_zero
#print axioms LetwinRoughTestingAudit.rough_tests_same_witness
#print axioms LetwinRoughTestingAudit.bump_instances
#print axioms
  FunctionalInequalities.Analysis.exists_smooth_compact_extension_on_nonnegative_interval
#print axioms FunctionalInequalities.Analysis.exists_smooth_compact_log_shift_extension
#print axioms FunctionalInequalities.Analysis.exists_smooth_compact_rpow_shift_extension
#print axioms FunctionalInequalities.Analysis.compact_bounded_test_domination
#print axioms FunctionalInequalities.Analysis.hasWeakDerivAlong_comp_of_compact_bounded
#print axioms
  FunctionalInequalities.Analysis.hasWeakDerivAlong_log_shift_of_ae_nonneg_compact_bounded
#print axioms
  FunctionalInequalities.Analysis.hasWeakDerivAlong_rpow_shift_of_ae_nonneg_compact_bounded
#print axioms FunctionalInequalities.Analysis.directional_cutoff_data
#print axioms
  FunctionalInequalities.Analysis.integral_directional_hessian_flux_le_of_bounded_weak_test
#print axioms FunctionalInequalities.Analysis.rough_square_test_of_weak_data
#print axioms FunctionalInequalities.Analysis.posSemidef_quadratic_young
