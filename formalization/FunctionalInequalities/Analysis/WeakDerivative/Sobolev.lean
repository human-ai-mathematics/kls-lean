import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import FunctionalInequalities.Analysis.WeakDerivative.Approximation
import FunctionalInequalities.L2.Components
import FunctionalInequalities.Analysis.LpExponent
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Weak Sobolev embeddings for bounded compact weak `H¹` functions

Three dimension regimes for a bounded, compactly supported `η` on `EuclideanSpace ℝ (Fin n)` with coordinate weak
derivatives `a i` in global `L²`. Each passes to the limit from the smooth approximation of
`WeakDerivative/Approximation.lean`, using lower semicontinuity of `eLpNorm` along the a.e. convergent sequence:

* `eLpNorm_le_sum_eLpNorm_weak_deriv_of_compact_bounded` (`n > 2`): the critical Gagliardo–Nirenberg–Sobolev
  inequality `‖η‖_q ≤ C_GNS(2) Σᵢ ‖a i‖₂` for `1/q = 1/2 - 1/n`, with the exact pinned Mathlib constant.
* `eLpNorm_finite_le_sum_eLpNorm_weak_deriv_of_support_subset_two` (`n = 2`): every finite `q ≥ 2`,
  `‖η‖_q ≤ C_GNS(2q/(q+2)) · volume(cthickening ε K)^(1/q) Σᵢ ‖a i‖₂` for supports in a compact `K`, every `ε > 0`;
  `eLpNorm_six_le_sum_eLpNorm_weak_deriv_of_support_subset_two` is its `q = 6` case.
* `eLpNorm_top_le_eLpNorm_weak_deriv_of_support_subset_one` (`n = 1`): the essential bound
  `‖η‖_∞ ≤ volume(cthickening ε K)^(1/2) ‖a 0‖₂`, through the normalized singleton-basis isometry
  `ℝ ≃ EuclideanSpace ℝ (Fin 1)` and the compact fundamental theorem of calculus.
* `weak_cutoff_sobolev_gain_of_energy` and `weak_cutoff_sobolev_gain_of_energy_of_bounded_log` (`n > 2`): one critical
  gain `‖s^r‖²_{L^q(V)} ≤ C_GNS² n (γ n L² + f/δ) ∫_U s^{2r}` from a GIVEN cutoff power energy of `χ s^r`, with the weighted
  integrabilities derived (from a bounded actual `log s` in the second form).

These are supporting `H¹` tools for Gilbarg–Trudinger (2001) (8.48)–(8.49) and Letwin arXiv:2607.24164v1 Lemma 2.2.
The two-dimensional bounds carry an explicit support-measure factor. The one-dimensional statement is an essential
bound, not a pointwise one. None of them is Moser iteration or a Harnack inequality.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal NNReal

namespace FunctionalInequalities.Analysis

/-- The dual norm on `EuclideanSpace ℝ (Fin n)` is at most the sum of the absolute values on the standard basis. -/
private theorem norm_dual_le_sum_coordinates {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i : Fin n, ‖L (EuclideanSpace.basisFun (Fin n) ℝ i)‖ := by
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i : Fin n => ‖L (EuclideanSpace.basisFun (Fin n) ℝ i)‖)
    (fun i _ => norm_nonneg _)
  have hsq' : ‖L‖ ^ 2 ≤ (∑ i : Fin n, ‖L (EuclideanSpace.basisFun (Fin n) ℝ i)‖) ^ 2 := by
    rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_dual L]
    simpa only [Real.norm_eq_abs, sq_abs] using hsq
  have hpos : 0 ≤ ∑ i : Fin n, ‖L (EuclideanSpace.basisFun (Fin n) ℝ i)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  nlinarith [norm_nonneg L]

/-- The `L^p` norm (`p ≥ 1`) of the derivative of a `C¹` function is at most the sum of the coordinate `L^p` norms. -/
private theorem eLpNorm_fderiv_le_sum_coordinates {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) {p : ENNReal} (hp : 1 ≤ p) :
    eLpNorm (fderiv ℝ f) p (volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
      ∑ i : Fin n, eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)) p
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hc (i : Fin n) : Continuous (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  calc
    _ ≤ eLpNorm (fun x => ∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)‖) p volume := by
      apply eLpNorm_mono_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
      exact norm_dual_le_sum_coordinates (fderiv ℝ f x)
    _ ≤ _ := by
      have h := eLpNorm_sum_le (s := Finset.univ)
        (f := fun (i : Fin n) x => ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)‖)
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (p := p)
        (fun i _ => (hc i).norm.aestronglyMeasurable) hp
      have hs : (∑ i : Fin n, fun x => ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)‖) =
          (fun x => ∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)‖) := by
        ext x
        simp only [Finset.sum_apply]
      rw [hs] at h
      simpa only [eLpNorm_norm] using h

/-- **Weak Gagliardo–Nirenberg–Sobolev, `n > 2`.** A bounded compactly supported weak `H¹` function with compactly
supported, globally `L²` coordinate weak derivatives satisfies `‖η‖_q ≤ C_GNS(2) Σᵢ ‖a i‖₂` for `1/q = 1/2 - 1/n`,
with the exact Mathlib constant `SNormLESNormFDerivOfEqConst`. -/
theorem eLpNorm_le_sum_eLpNorm_weak_deriv_of_compact_bounded {n : ℕ} (hn : 2 < n)
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {q : NNReal} (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    eLpNorm η q (volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) *
        ∑ i : Fin n, eLpNorm (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨S, -, -, -, θ, hθ, hconv, hae⟩ :=
    exists_contDiff_compact_bounded_all_weak_deriv_approximation hη hbound hηc hweak hac ha2
  have hθ1 (m : ℕ) : ContDiff ℝ 1 (θ m) := (hθ m).1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hnorm (m : ℕ) : eLpNorm (θ m) q volume ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) *
        ∑ i : Fin n, eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i)) 2 volume := by
    have hd : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      rw [finrank_euclideanSpace_fin]
      omega
    have hq' : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ)⁻¹ := by
      simpa only [finrank_euclideanSpace_fin] using hq
    have h := eLpNorm_le_eLpNorm_fderiv_of_eq volume (hθ1 m) (hθ m).2.1 (p := 2) (p' := q)
      (by norm_num) hd hq'
    have h' : eLpNorm (θ m) q volume ≤
        (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) *
          eLpNorm (fderiv ℝ (θ m)) 2 volume := by simpa using h
    apply h'.trans
    gcongr
    exact eLpNorm_fderiv_le_sum_coordinates (hθ1 m) one_le_two
  have ht (i : Fin n) : Tendsto
      (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i)) 2 volume)
      atTop (nhds (eLpNorm (a i) 2 volume)) := by
    have hd (m : ℕ) := ((hθ m).2.2.2.2 i).2
    have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hd (a i) (ha2 i)).2 (hconv i)
    simpa only [Lp.enorm_toLp] using hLp.enorm
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => ht i)
  have htotal := ENNReal.Tendsto.const_mul hsum
    (a := (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal))
    (Or.inr ENNReal.coe_ne_top)
  calc
    _ ≤ atTop.liminf (fun m => eLpNorm (θ m) q volume) :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm (fun m => (hθ m).1.continuous.aestronglyMeasurable) η hae
    _ ≤ atTop.liminf (fun m =>
        (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) *
          ∑ i : Fin n, eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i)) 2 volume) :=
      liminf_le_liminf (Eventually.of_forall hnorm)
    _ = _ := htotal.liminf_eq

/-- The general two-dimensional bound for `1 ≤ p ≤ 2`, `1/q = 1/p − 1/2`. Proof-local parameterization: its `p = 2`
endpoint forces the degenerate `q = 0`; the public entry is the `q ≥ 2` form below. -/
private theorem eLpNorm_le_sum_eLpNorm_weak_deriv_of_support_subset_two
    {η : EuclideanSpace ℝ (Fin 2) → ℝ}
    {a : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    (hηK : Function.support η ⊆ K) (haK : ∀ i : Fin 2, Function.support (a i) ⊆ K)
    (hweak : ∀ i : Fin 2, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (ha2 : ∀ i : Fin 2, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    {ε : ℝ} (hε : 0 < ε) {p q : NNReal} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (2 : ℝ)⁻¹) :
    eLpNorm η q (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) p : ENNReal) *
        (volume (cthickening ε K)) ^ ((q : ℝ)⁻¹) *
          ∑ i : Fin 2, eLpNorm (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
  obtain ⟨S, -, hSK, -, -, θ, hθ, hconv, hae⟩ :=
    exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset
      hη hbound hK hηK haK hε hweak ha2
  let T := cthickening ε K
  have hT : IsCompact T := hK.cthickening
  let B : ENNReal := (volume T) ^ ((q : ℝ)⁻¹)
  let A : ENNReal := (SNormLESNormFDerivOfEqConst ℝ
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) p : ENNReal) * B
  have hB : B ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hT.measure_lt_top.ne
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hB
  have hpE : (1 : ENNReal) ≤ p := by exact_mod_cast hp
  have hpLeE : (p : ENNReal) ≤ 2 := by exact_mod_cast hp2
  have hθ1 (m : ℕ) : ContDiff ℝ 1 (θ m) := (hθ m).1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdS (m : ℕ) (i : Fin 2) :
      Function.support (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 2) ℝ i)) ⊆ T :=
    ((hθ m).2.2.2.2 i).1.trans hSK
  have hcompare (m : ℕ) (i : Fin 2) :
      eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 2) ℝ i)) (p : ENNReal) volume ≤
        eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 volume * B := by
    let f := fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 2) ℝ i)
    have hf : AEStronglyMeasurable f ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict T) :=
      (((hθ m).2.2.2.2 i).2.1).restrict
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (p : ENNReal)) (q := 2)
      hpLeE hf
    rw [eLpNorm_restrict_eq_of_support_subset (hdS m i),
      eLpNorm_restrict_eq_of_support_subset (hdS m i)] at h
    simpa only [Measure.restrict_apply_univ, ENNReal.coe_toReal, ENNReal.toReal_ofNat,
      B, T, one_div, ← hq] using h
  have hnorm (m : ℕ) : eLpNorm (θ m) q volume ≤
      A * ∑ i : Fin 2, eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 volume := by
    have hd : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by simp
    have hq' : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ -
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ)⁻¹ := by
      simpa only [finrank_euclideanSpace_fin, Nat.cast_ofNat] using hq
    have h0 := eLpNorm_le_eLpNorm_fderiv_of_eq volume (hθ1 m) (hθ m).2.1
      (p := p) (p' := q) hp hd hq'
    have h0' : eLpNorm (θ m) q volume ≤
        (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) p : ENNReal) *
          eLpNorm (fderiv ℝ (θ m)) (p : ENNReal) volume := by simpa using h0
    apply h0'.trans
    calc
      _ ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) p : ENNReal) *
          ∑ i : Fin 2, eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 2) ℝ i)) (p : ENNReal) volume := by
        gcongr
        exact eLpNorm_fderiv_le_sum_coordinates (hθ1 m) (p := (p : ENNReal)) hpE
      _ ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) p : ENNReal) *
          ∑ i : Fin 2, (eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 volume * B) := by
        gcongr with i
        exact hcompare m i
      _ = _ := by rw [← Finset.sum_mul]; simp only [A]; ring
  have ht (i : Fin 2) : Tendsto
      (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 volume)
      atTop (nhds (eLpNorm (a i) 2 volume)) := by
    have hd (m : ℕ) := ((hθ m).2.2.2.2 i).2
    have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hd (a i) (ha2 i)).2 (hconv i)
    simpa only [Lp.enorm_toLp] using hLp.enorm
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => ht i)
  have htotal := ENNReal.Tendsto.const_mul hsum (a := A) (Or.inr hA)
  calc
    _ ≤ atTop.liminf (fun m => eLpNorm (θ m) q volume) :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm (fun m => (hθ m).1.continuous.aestronglyMeasurable) η hae
    _ ≤ atTop.liminf (fun m => A * ∑ i : Fin 2,
        eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 volume) :=
      liminf_le_liminf (Eventually.of_forall hnorm)
    _ = _ := htotal.liminf_eq

/-- **Weak Sobolev, `n = 2`, every finite exponent `q ≥ 2`.** For supports of `η` and of each `a i` in a compact `K` and
every `ε > 0`, `‖η‖_q ≤ C_GNS(2q/(q+2)) · volume(cthickening ε K)^(1/q) Σᵢ ‖a i‖₂` (`p = 2q/(q+2) ∈ [1, 2)`; `q = 2` is
`p = 1`). The measure factor is kept explicitly for scale control. -/
theorem eLpNorm_finite_le_sum_eLpNorm_weak_deriv_of_support_subset_two
    {η : EuclideanSpace ℝ (Fin 2) → ℝ}
    {a : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    (hηK : Function.support η ⊆ K) (haK : ∀ i : Fin 2, Function.support (a i) ⊆ K)
    (hweak : ∀ i : Fin 2, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (ha2 : ∀ i : Fin 2, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    {ε : ℝ} (hε : 0 < ε) {q : NNReal} (hq : 2 ≤ q) :
    eLpNorm η q (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (2 * q / (q + 2)) : ENNReal) *
        (volume (cthickening ε K)) ^ ((q : ℝ)⁻¹) *
          ∑ i : Fin 2, eLpNorm (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
  let p : NNReal := 2 * q / (q + 2)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (0 : ℝ) < q + 2 := by positivity
  have hp : (1 : NNReal) ≤ p := by
    change (1 : NNReal) ≤ 2 * q / (q + 2)
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_one, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add]
    exact (le_div_iff₀ hden).mpr (by linarith)
  have hp2 : p ≤ 2 := by
    apply NNReal.coe_le_coe.mp
    simp only [p, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add]
    exact (div_le_iff₀ hden).mpr (by linarith)
  have hrel : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (2 : ℝ)⁻¹ := by
    simp only [p, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add]
    field_simp
    ring
  exact eLpNorm_le_sum_eLpNorm_weak_deriv_of_support_subset_two hη hbound hK hηK haK
    hweak ha2 hε hp hp2 hrel

/-- **Weak Sobolev, `n = 2`, fixed exponent six**: the `q = 6` case (`p = 3/2`) of the finite-exponent bound. -/
theorem eLpNorm_six_le_sum_eLpNorm_weak_deriv_of_support_subset_two
    {η : EuclideanSpace ℝ (Fin 2) → ℝ}
    {a : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    (hηK : Function.support η ⊆ K) (haK : ∀ i : Fin 2, Function.support (a i) ⊆ K)
    (hweak : ∀ i : Fin 2, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (ha2 : ∀ i : Fin 2, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    {ε : ℝ} (hε : 0 < ε) :
    eLpNorm η 6 (volume : Measure (EuclideanSpace ℝ (Fin 2))) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (3 / 2) : ENNReal) *
        (volume (cthickening ε K)) ^ (1 / 6 : ℝ) *
          ∑ i : Fin 2, eLpNorm (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
  convert eLpNorm_finite_le_sum_eLpNorm_weak_deriv_of_support_subset_two hη hbound hK hηK haK hweak ha2 hε
    (q := (6 : NNReal)) (by norm_num) using 3 <;> norm_num

/-- The one-dimensional `C¹` compact inequality `‖f‖_∞ ≤ ‖∂f‖₁` in the Euclidean coordinate normalization,
transported along the volume-preserving singleton-basis isometry. -/
private theorem eLpNorm_top_le_eLpNorm_coordinate_one
    {f : EuclideanSpace ℝ (Fin 1) → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    eLpNorm f ⊤ (volume : Measure (EuclideanSpace ℝ (Fin 1))) ≤
      eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin 1) ℝ 0)) 1
        (volume : Measure (EuclideanSpace ℝ (Fin 1))) := by
  let I : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  have hIone : I 1 = EuclideanSpace.basisFun (Fin 1) ℝ 0 := by
    ext i
    fin_cases i
    simp [I, EuclideanSpace.basisFun_apply]
    change (OrthonormalBasis.singleton (Fin 1) ℝ).repr 1 (0 : Fin 1) = 1
    exact OrthonormalBasis.singleton_repr 1 (0 : Fin 1)
  let g : ℝ → ℝ := f ∘ I
  have hg : ContDiff ℝ 1 g := hf.comp I.toContinuousLinearEquiv.contDiff
  have hgc : HasCompactSupport g := hfc.comp_homeomorph I.toHomeomorph
  let D := fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin 1) ℝ 0)
  have hD : Continuous D := (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hderiv : deriv g = D ∘ I := by
    funext y
    have hI : HasDerivAt (fun t : ℝ => I t) (I 1) y := I.toContinuousLinearMap.hasFDerivAt.hasDerivAt
    have h := ((hf.differentiable one_ne_zero (I y)).hasFDerivAt.comp_hasDerivAt y hI).deriv
    simpa only [g, D, Function.comp_def, hIone] using h
  have hpoint (x : EuclideanSpace ℝ (Fin 1)) : ‖f x‖ₑ ≤ eLpNorm D 1 volume := by
    calc
      ‖f x‖ₑ = ‖g (I.symm x)‖ₑ := by simp only [g, Function.comp_def, I.apply_symm_apply]
      _ ≤ ∫⁻ y in Iic (I.symm x), ‖deriv g y‖ₑ :=
        HasCompactSupport.enorm_le_lintegral_Ici_deriv hg hgc (I.symm x)
      _ ≤ ∫⁻ y, ‖deriv g y‖ₑ := lintegral_mono' Measure.restrict_le_self le_rfl
      _ = eLpNorm D 1 volume := by
        rw [← eLpNorm_one_eq_lintegral_enorm, hderiv]
        exact eLpNorm_comp_measurePreserving hD.aestronglyMeasurable I.measurePreserving
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ hpoint)

/-- **Weak Sobolev, `n = 1`, essential `L^∞`.** For supports in a compact `K` and every `ε > 0`,
`‖η‖_∞ ≤ volume(cthickening ε K)^(1/2) ‖a 0‖₂`. An essential, not pointwise, bound. -/
theorem eLpNorm_top_le_eLpNorm_weak_deriv_of_support_subset_one
    {η : EuclideanSpace ℝ (Fin 1) → ℝ}
    {a : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    {K : Set (EuclideanSpace ℝ (Fin 1))} (hK : IsCompact K)
    (hηK : Function.support η ⊆ K) (haK : ∀ i : Fin 1, Function.support (a i) ⊆ K)
    (hweak : ∀ i : Fin 1, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin 1) ℝ i))
    (ha2 : ∀ i : Fin 1, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    {ε : ℝ} (hε : 0 < ε) :
    eLpNorm η ⊤ (volume : Measure (EuclideanSpace ℝ (Fin 1))) ≤
      (volume (cthickening ε K)) ^ (1 / 2 : ℝ) *
        eLpNorm (a 0) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1))) := by
  obtain ⟨S, -, hSK, -, -, θ, hθ, hconv, hae⟩ :=
    exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset
      hη hbound hK hηK haK hε hweak ha2
  let T := cthickening ε K
  have hT : IsCompact T := hK.cthickening
  let B : ENNReal := (volume T) ^ (1 / 2 : ℝ)
  have hB : B ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hT.measure_lt_top.ne
  have hθ1 (m : ℕ) : ContDiff ℝ 1 (θ m) := (hθ m).1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdS (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 1) ℝ 0)) ⊆ T :=
    ((hθ m).2.2.2.2 0).1.trans hSK
  have hcompare (m : ℕ) :
      eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 1) ℝ 0)) 1 volume ≤
        eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 1) ℝ 0)) 2 volume * B := by
    let f := fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 1) ℝ 0)
    have hf : AEStronglyMeasurable f ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict T) :=
      (((hθ m).2.2.2.2 0).2.1).restrict
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hf
    rw [eLpNorm_restrict_eq_of_support_subset (hdS m), eLpNorm_restrict_eq_of_support_subset (hdS m)] at h
    norm_num [B, f, Measure.restrict_apply_univ] at h ⊢
    exact h
  have hnorm (m : ℕ) : eLpNorm (θ m) ⊤ volume ≤
      B * eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 1) ℝ 0)) 2 volume := by
    exact (eLpNorm_top_le_eLpNorm_coordinate_one (hθ1 m) (hθ m).2.1).trans
      ((hcompare m).trans_eq (mul_comm _ _))
  have ht : Tendsto
      (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 1) ℝ 0)) 2 volume)
      atTop (nhds (eLpNorm (a 0) 2 volume)) := by
    have hd (m : ℕ) := ((hθ m).2.2.2.2 0).2
    have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hd (a 0) (ha2 0)).2 (hconv 0)
    simpa only [Lp.enorm_toLp] using hLp.enorm
  have htotal := ENNReal.Tendsto.const_mul ht (a := B) (Or.inr hB)
  calc
    _ ≤ atTop.liminf (fun m => eLpNorm (θ m) ⊤ volume) :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm (fun m => (hθ m).1.continuous.aestronglyMeasurable) η hae
    _ ≤ atTop.liminf (fun m => B *
        eLpNorm (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin 1) ℝ 0)) 2 volume) :=
      liminf_le_liminf (Eventually.of_forall hnorm)
    _ = _ := htotal.liminf_eq

/-! ### One-step critical gains from a given cutoff power energy

For `n > 2` and an energy variable `g = χ s^r` with exact weak data, a given power-energy bound
`∫ Σ dg² ≤ γ ∫ s^{2r} Σ (∂χ)² + f ∫ χ² s^{2r-1}` becomes the critical Sobolev gain on the set `V` where `χ = 1`. The weighted
integrabilities are derived by domination from the outer moment of `s^{2r}`, and that moment and the measurability from
a bounded actual `log s`. One step of a Moser-type iteration (Gilbarg–Trudinger (2001) (8.48)–(8.49)); not the iteration. -/

/-- The two weighted cutoff integrands are dominated by `H 1_U s^{2r}` and `δ⁻¹ 1_U s^{2r}`. -/
private theorem weighted_cutoff_power_integrable_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    {s χ : X → ℝ} {dχ : Fin n → X → ℝ} {U : Set X} {δ r H : ℝ}
    (hU : MeasurableSet U) (hδ : 0 < δ) (hs : ∀ x, δ ≤ s x)
    (hχ : ∀ x, |χ x| ≤ 1) (hχU : Function.support χ ⊆ U)
    (hdχU : ∀ i : Fin n, Function.support (dχ i) ⊆ U)
    (hD : ∀ x, ∑ i : Fin n, (dχ i x) ^ 2 ≤ H)
    (hI : IntegrableOn (fun x => s x ^ (2 * r)) U μ)
    (hKm : AEStronglyMeasurable (fun x => s x ^ (2 * r) * ∑ i : Fin n, (dχ i x) ^ 2) μ)
    (hJm : AEStronglyMeasurable (fun x => χ x ^ 2 * s x ^ (2 * r - 1)) μ) :
    Integrable (fun x => s x ^ (2 * r) * ∑ i : Fin n, (dχ i x) ^ 2) μ ∧
    Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1)) μ ∧
    (∫ x, s x ^ (2 * r) * ∑ i : Fin n, (dχ i x) ^ 2 ∂μ) ≤
        H * (∫ x in U, s x ^ (2 * r) ∂μ) ∧
    (∫ x, χ x ^ 2 * s x ^ (2 * r - 1) ∂μ) ≤
        δ⁻¹ * (∫ x in U, s x ^ (2 * r) ∂μ) := by
  classical
  let f := U.indicator (fun x => s x ^ (2 * r))
  have hfi : Integrable f μ := (integrable_indicator_iff hU).mpr hI
  have hfn : ∫ x, f x ∂μ = ∫ x in U, s x ^ (2 * r) ∂μ := integral_indicator hU
  have hsp (x : X) : 0 < s x := hδ.trans_le (hs x)
  have hpK (x : X) : s x ^ (2 * r) * ∑ i : Fin n, (dχ i x) ^ 2 ≤ H * f x := by
    by_cases hx : x ∈ U
    · rw [show f x = s x ^ (2 * r) from indicator_of_mem hx _]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hD x)
        (Real.rpow_nonneg (hsp x).le (2 * r))
    · have hdz (i : Fin n) : dχ i x = 0 := by
        by_contra h
        exact hx (hdχU i h)
      simp only [hdz, zero_pow two_ne_zero, Finset.sum_const_zero, mul_zero,
        show f x = 0 from indicator_of_notMem hx _, le_refl]
  have hpJ (x : X) : χ x ^ 2 * s x ^ (2 * r - 1) ≤ δ⁻¹ * f x := by
    by_cases hx : x ∈ U
    · rw [show f x = s x ^ (2 * r) from indicator_of_mem hx _]
      have hχ2 : χ x ^ 2 ≤ 1 := by nlinarith [sq_abs (χ x), hχ x, abs_nonneg (χ x)]
      have hi : (s x)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (hs x)
      rw [Real.rpow_sub (hsp x), Real.rpow_one, div_eq_mul_inv]
      calc
        _ ≤ 1 * (s x ^ (2 * r) * δ⁻¹) :=
          mul_le_mul hχ2 (mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (hsp x).le (2 * r)))
            (mul_nonneg (Real.rpow_nonneg (hsp x).le (2 * r)) (inv_nonneg.mpr (hsp x).le)) zero_le_one
        _ = _ := by ring
    · have hzero : χ x = 0 := by
        by_contra h
        exact hx (hχU h)
      simp only [hzero, zero_pow two_ne_zero, zero_mul,
        show f x = 0 from indicator_of_notMem hx _, mul_zero, le_refl]
  have hK : Integrable (fun x => s x ^ (2 * r) * ∑ i : Fin n, (dχ i x) ^ 2) μ := by
    apply (hfi.const_mul H).mono' hKm
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hsp x).le _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
    exact hpK x
  have hJ : Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1)) μ := by
    apply (hfi.const_mul δ⁻¹).mono' hJm
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsp x).le _))]
    exact hpJ x
  refine ⟨hK, hJ, ?_, ?_⟩
  · simpa only [integral_const_mul, hfn] using
      integral_mono hK (hfi.const_mul (H)) hpK
  · simpa only [integral_const_mul, hfn] using
      integral_mono hJ (hfi.const_mul δ⁻¹) hpJ

/-- **Critical one-step gain from a given power energy** (`n > 2`, `1/q = 1/2 − 1/n`): with `χ = 1` on `V`, `|χ| ≤ 1`,
`tsupport χ ⊆ U` compact, `‖Dχ‖ ≤ L` and `s ≥ δ > 0`, `‖s^r‖²_{L^q(V)} ≤ C_GNS² n (γ n L² + f/δ) ∫_U s^{2r}`. -/
theorem weak_cutoff_sobolev_gain_of_energy {n : ℕ} (hn : 2 < n)
    {s χ : EuclideanSpace ℝ (Fin n) → ℝ}
    {dg : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ r γ fcoef L : ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsCompact U) (hV : MeasurableSet V)
    (hδ : 0 < δ) (hs : ∀ x, δ ≤ s x)
    (hχU : tsupport χ ⊆ U) (hχV : ∀ x ∈ V, χ x = 1) (hχone : ∀ x, |χ x| ≤ 1)
    (hχD : ∀ x, ‖fderiv ℝ χ x‖ ≤ L)
    (hgl : LocallyIntegrable (fun x => χ x * s x ^ r) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hgb : ∀ x, ‖χ x * s x ^ r‖ ≤ C) (hgc : HasCompactSupport (fun x => χ x * s x ^ r))
    (hgd : ∀ k : Fin n, HasWeakDerivAlong (fun x => χ x * s x ^ r) (dg k)
      (EuclideanSpace.basisFun (Fin n) ℝ k) ∧ HasCompactSupport (dg k) ∧
      MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hI : IntegrableOn (fun x => s x ^ (2 * r)) U (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hKm : AEStronglyMeasurable (fun x => s x ^ (2 * r) * ∑ i : Fin n,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) volume)
    (hJm : AEStronglyMeasurable (fun x => χ x ^ 2 * s x ^ (2 * r - 1)) volume)
    (hγ : 0 ≤ γ) (hforce : 0 ≤ fcoef)
    (he : (∫ x, ∑ i : Fin n, (dg i x) ^ 2) ≤
      γ * (∫ x, s x ^ (2 * r) * ∑ i : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) +
      fcoef * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)))
    {q : NNReal} (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    (eLpNorm (fun x => s x ^ r) q ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict V)) ^ (2 : ℕ) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) ^ (2 : ℕ) *
      (n : ENNReal) * ENNReal.ofReal
        ((γ * ((n : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r))) := by
  classical
  let g := fun x => χ x * s x ^ r
  have hL : 0 ≤ L := (norm_nonneg (fderiv ℝ χ 0)).trans (hχD 0)
  have hDsum (x : EuclideanSpace ℝ (Fin n)) :
      ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 ≤ (n : ℝ) * L ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin n, L ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hb : |fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)| ≤ L := by
          have h := (fderiv ℝ χ x).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ k)
          rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one k, mul_one] at h
          have h' : |fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)| ≤ ‖fderiv ℝ χ x‖ := by
            simpa only [Real.norm_eq_abs] using h
          exact h'.trans (hχD x)
        nlinarith [sq_abs (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)),
          abs_nonneg (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k))]
      _ = _ := by simp
  have hdU (k : Fin n) : Function.support
      (fun x => fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ⊆ U := by
    intro x hx
    by_contra hnot
    have hnt : x ∉ tsupport χ := fun hx' => hnot (hχU hx')
    have hz := fderiv_of_notMem_tsupport ℝ hnt
    exact hx (by change fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) = 0; rw [hz]; rfl)
  have hW := weighted_cutoff_power_integrable_bounds (volume : Measure (EuclideanSpace ℝ (Fin n)))
    hU.measurableSet hδ hs hχone ((subset_tsupport χ).trans hχU) hdU hDsum hI hKm hJm
  have hE : (∫ x, ∑ k : Fin n, (dg k x) ^ 2) ≤
      (γ * ((n : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r)) := by
    calc
      _ ≤ _ := he
      _ ≤ γ * (((n : ℝ) * L ^ 2) * (∫ x in U, s x ^ (2 * r))) +
          fcoef * (δ⁻¹ * (∫ x in U, s x ^ (2 * r))) :=
        add_le_add (mul_le_mul_of_nonneg_left hW.2.2.1 hγ)
          (mul_le_mul_of_nonneg_left hW.2.2.2 hforce)
      _ = _ := by ring
  have hsob := eLpNorm_le_sum_eLpNorm_weak_deriv_of_compact_bounded hn hgl hgb hgc
    (fun k => (hgd k).1) (fun k => (hgd k).2.1) (fun k => (hgd k).2.2) hq
  have hcoord := FunctionalInequalities.L2.sq_sum_eLpNorm_le_dim_mul_integral_sum_sq
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (fun k => (hgd k).2.2)
  have heq : (fun x => s x ^ r) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict V] g := by
    filter_upwards [ae_restrict_mem hV] with x hx
    dsimp only [g]
    rw [hχV x hx, one_mul]
  have hnorm : eLpNorm (fun x => s x ^ r) q ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict V) ≤
      eLpNorm g q (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_restrict_le _ _ _ _
  calc
    _ ≤ ((SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) *
        ∑ k : Fin n, eLpNorm (dg k) 2 volume) ^ (2 : ℕ) := by
      gcongr
      exact hnorm.trans hsob
    _ = _ := mul_pow _ _ 2
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) ^ (2 : ℕ) *
        ((n : ENNReal) * ENNReal.ofReal (∫ x, ∑ k : Fin n, (dg k x) ^ 2)) := by
      gcongr
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) ^ (2 : ℕ) *
        ((n : ENNReal) * ENNReal.ofReal
          ((γ * ((n : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r)))) := by
      gcongr
    _ = _ := (mul_assoc _ _ _).symm

/-- **Critical one-step gain from a bounded actual logarithm.** The same gain, with the outer moment and the measurability
side conditions derived from a measurable bounded `log s` and the `C¹` cutoff. -/
theorem weak_cutoff_sobolev_gain_of_energy_of_bounded_log {n : ℕ} (hn : 2 < n)
    {s χ : EuclideanSpace ℝ (Fin n) → ℝ}
    {dg : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ r γ fcoef L : ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsCompact U) (hV : MeasurableSet V)
    (hδ : 0 < δ) (hs : ∀ x, δ ≤ s x)
    (hχU : tsupport χ ⊆ U) (hχV : ∀ x ∈ V, χ x = 1) (hχone : ∀ x, |χ x| ≤ 1)
    (hχD : ∀ x, ‖fderiv ℝ χ x‖ ≤ L)
    (hgl : LocallyIntegrable (fun x => χ x * s x ^ r) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hgb : ∀ x, ‖χ x * s x ^ r‖ ≤ C) (hgc : HasCompactSupport (fun x => χ x * s x ^ r))
    (hgd : ∀ k : Fin n, HasWeakDerivAlong (fun x => χ x * s x ^ r) (dg k)
      (EuclideanSpace.basisFun (Fin n) ℝ k) ∧ HasCompactSupport (dg k) ∧
      MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hχ : ContDiff ℝ 1 χ) {Clog : ℝ}
    (hlogm : AEStronglyMeasurable (fun x => Real.log (s x)) volume)
    (hlogb : ∀ x, ‖Real.log (s x)‖ ≤ Clog)
    (hγ : 0 ≤ γ) (hforce : 0 ≤ fcoef)
    (he : (∫ x, ∑ i : Fin n, (dg i x) ^ 2) ≤
      γ * (∫ x, s x ^ (2 * r) * ∑ i : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) +
      fcoef * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)))
    {q : NNReal} (hq : (q : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹) :
    (eLpNorm (fun x => s x ^ r) q ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict V)) ^ (2 : ℕ) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin n))) 2 : ENNReal) ^ (2 : ℕ) *
      (n : ENNReal) * ENNReal.ofReal
        ((γ * ((n : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r))) := by
  classical
  have hsp (x : EuclideanSpace ℝ (Fin n)) : 0 < s x := hδ.trans_le (hs x)
  have hI : IntegrableOn (fun x => s x ^ (2 * r)) U volume := by
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict U) :=
      isFiniteMeasure_restrict.mpr hU.measure_lt_top.ne
    exact MemLp.integrable le_rfl (memLp_rpow_of_bounded_log
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict U) hsp hlogm.restrict hlogb
      (q := 2 * r) (p := 1))
  have hsmeas : AEStronglyMeasurable s (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have H := Real.continuous_exp.comp_aestronglyMeasurable hlogm
    have heq : (fun x => Real.exp (Real.log (s x))) = s := funext fun x => Real.exp_log (hsp x)
    rw [heq] at H
    exact H
  have hdcont (k : Fin n) : Continuous (fun x => fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdmeas : AEStronglyMeasurable (fun x => ∑ k : Fin n,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun k _ =>
      ((hdcont k).measurable.pow_const (2 : ℕ)).aestronglyMeasurable
  have hKm : AEStronglyMeasurable (fun x => s x ^ (2 * r) * ∑ i : Fin n,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) volume :=
    ((hsmeas.aemeasurable.pow_const (2 * r)).aestronglyMeasurable).mul hdmeas
  have hJm : AEStronglyMeasurable (fun x => χ x ^ 2 * s x ^ (2 * r - 1)) volume :=
    ((hχ.continuous.measurable.pow_const (2 : ℕ)).aestronglyMeasurable).mul
      ((hsmeas.aemeasurable.pow_const (2 * r - 1)).aestronglyMeasurable)
  exact weak_cutoff_sobolev_gain_of_energy hn hU hV hδ hs hχU hχV hχone hχD hgl hgb hgc hgd
    hI hKm hJm hγ hforce he hq


/-! ## Low-dimensional energy gains

One-step gains for the Moser iterations in dimensions two and one (Gilbarg–Trudinger 2001, Theorem 8.18, `n ≤ 2`), from
actual weak linear data whose derivative representatives are supported in `U` and a given power energy. In dimension two
the finite-`q` embedding keeps the exact support factor `vol(cthickening ε U)^{2/q}` and the source GNS constant at
`2q/(q+2)`; the scaled form separates the radius power `R^{4/q}` for supports in `B̄(x0,5R/2)` with `ε = R/4`. In dimension
one the essential-supremum embedding keeps `vol(cthickening ε U)`. -/

section LowDimensionalGain


/-- Two-dimensional finite-q Sobolev gain from actual weak linear data with coordinate supports in U and a given power energy.
No raw PDE/source fields are needed. Weighted integrabilities are derived from domination. -/
theorem weak_cutoff_sobolev_gain_of_energy_two_of_support
    {s χ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {dg : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ} {C δ r γ fcoef L : ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsCompact U) (hV : MeasurableSet V)
    (hδ : 0 < δ) (hs : ∀ x, δ ≤ s x)
    (hχU : tsupport χ ⊆ U) (hχV : ∀ x ∈ V, χ x = 1) (hχone : ∀ x, |χ x| ≤ 1)
    (hχD : ∀ x, ‖fderiv ℝ χ x‖ ≤ L)
    (hgl : LocallyIntegrable (fun x => χ x * s x ^ r) (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hgb : ∀ x, ‖χ x * s x ^ r‖ ≤ C)
    (hgd : ∀ k : Fin 2, HasWeakDerivAlong (fun x => χ x * s x ^ r) (dg k)
      (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧ Function.support (dg k) ⊆ U ∧
      MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hI : IntegrableOn (fun x => s x ^ (2 * r)) U (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hKm : AEStronglyMeasurable (fun x => s x ^ (2 * r) * ∑ i : Fin 2,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ i)) ^ 2) volume)
    (hJm : AEStronglyMeasurable (fun x => χ x ^ 2 * s x ^ (2 * r - 1)) volume)
    (hγ : 0 ≤ γ) (hforce : 0 ≤ fcoef)
    (he : (∫ x, ∑ i : Fin 2, (dg i x) ^ 2) ≤
      γ * (∫ x, s x ^ (2 * r) * ∑ i : Fin 2, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ i)) ^ 2) +
      fcoef * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)))
    {ε : ℝ} (hε : 0 < ε) {q : NNReal} (hq : 2 ≤ q) :
    (eLpNorm (fun x => s x ^ r) q ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict V)) ^ (2 : ℕ) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (2*q/(q+2)) : ENNReal) ^ (2 : ℕ) *
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))) (cthickening ε U)) ^ (2/(q : ℝ)) *
      (2 : ENNReal) * ENNReal.ofReal
        ((γ * ((2 : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r))) := by
  classical
  let g := fun x => χ x * s x ^ r
  have hL : 0 ≤ L := (norm_nonneg (fderiv ℝ χ 0)).trans (hχD 0)
  have hDsum (x : EuclideanSpace ℝ (Fin 2)) :
      ∑ k : Fin 2, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2 ≤ (2 : ℝ) * L ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin 2, L ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hb : |fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k)| ≤ L := by
          have h := (fderiv ℝ χ x).le_opNorm (EuclideanSpace.basisFun (Fin 2) ℝ k)
          rw [(EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one k, mul_one] at h
          have h' : |fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k)| ≤ ‖fderiv ℝ χ x‖ := by
            simpa only [Real.norm_eq_abs] using h
          exact h'.trans (hχD x)
        nlinarith [sq_abs (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k)),
          abs_nonneg (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k))]
      _ = _ := by simp
  have hdU (k : Fin 2) : Function.support
      (fun x => fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ⊆ U := by
    intro x hx
    by_contra hnot
    have hnt : x ∉ tsupport χ := fun hx' => hnot (hχU hx')
    have hz := fderiv_of_notMem_tsupport ℝ hnt
    exact hx (by change fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k) = 0; rw [hz]; rfl)
  have hW := weighted_cutoff_power_integrable_bounds (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    hU.measurableSet hδ hs hχone ((subset_tsupport χ).trans hχU) hdU hDsum hI hKm hJm
  have hE : (∫ x, ∑ k : Fin 2, (dg k x) ^ 2) ≤
      (γ * ((2 : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r)) := by
    calc
      _ ≤ _ := he
      _ ≤ γ * (((2 : ℝ) * L ^ 2) * (∫ x in U, s x ^ (2 * r))) +
          fcoef * (δ⁻¹ * (∫ x in U, s x ^ (2 * r))) :=
        add_le_add (mul_le_mul_of_nonneg_left hW.2.2.1 hγ)
          (mul_le_mul_of_nonneg_left hW.2.2.2 hforce)
      _ = _ := by ring
  have hgU : Function.support g ⊆ U := by
    intro x hx
    apply hχU
    apply subset_tsupport χ
    intro hz
    exact hx (by dsimp only [g]; rw [hz,zero_mul])
  let A : ENNReal := (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (2*q/(q+2)) : ENNReal) *
    ((volume : Measure (EuclideanSpace ℝ (Fin 2))) (cthickening ε U)) ^ ((q : ℝ)⁻¹)
  have hsob := eLpNorm_finite_le_sum_eLpNorm_weak_deriv_of_support_subset_two hgl hgb hU hgU
    (fun k => (hgd k).2.1) (fun k => (hgd k).1) (fun k => (hgd k).2.2) hε hq
  have hcoord := FunctionalInequalities.L2.sq_sum_eLpNorm_le_dim_mul_integral_sum_sq
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) (fun k => (hgd k).2.2)
  have heq : (fun x => s x ^ r) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict V] g := by
    filter_upwards [ae_restrict_mem hV] with x hx
    dsimp only [g]
    rw [hχV x hx, one_mul]
  have hnorm : eLpNorm (fun x => s x ^ r) q ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict V) ≤
      eLpNorm g q (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_restrict_le _ _ _ _
  calc
    _ ≤ (A *
        ∑ k : Fin 2, eLpNorm (dg k) 2 volume) ^ (2 : ℕ) := by
      gcongr
      exact hnorm.trans hsob
    _ = _ := mul_pow _ _ 2
    _ ≤ A ^ (2 : ℕ) *
        ((2 : ENNReal) * ENNReal.ofReal (∫ x, ∑ k : Fin 2, (dg k x) ^ 2)) := by
      gcongr
      simpa only [Nat.cast_ofNat] using hcoord
    _ ≤ A ^ (2 : ℕ) *
        ((2 : ENNReal) * ENNReal.ofReal
          ((γ * ((2 : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r)))) := by
      gcongr
    _ = _ := by
      dsimp only [A]
      rw [mul_pow,← ENNReal.rpow_mul_natCast]
      have heq : (q : ℝ)⁻¹*(2 : ℕ) = 2/(q : ℝ) := by push_cast; ring
      rw [heq]
      ac_rfl

/-- Finite-q n2 gain with the actual power integrabilities derived from a bounded measurable actual log.
Derivative representatives retain explicit support in U; all q>=2 and epsilon>0 support factors stay exact. -/
theorem weak_cutoff_sobolev_gain_of_energy_two_of_support_of_bounded_log
    {s χ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {dg : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ} {C δ r γ fcoef L : ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsCompact U) (hV : MeasurableSet V)
    (hδ : 0 < δ) (hs : ∀ x, δ ≤ s x)
    (hχU : tsupport χ ⊆ U) (hχV : ∀ x ∈ V, χ x = 1) (hχone : ∀ x, |χ x| ≤ 1)
    (hχD : ∀ x, ‖fderiv ℝ χ x‖ ≤ L)
    (hgl : LocallyIntegrable (fun x => χ x * s x ^ r) (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hgb : ∀ x, ‖χ x * s x ^ r‖ ≤ C)
    (hgd : ∀ k : Fin 2, HasWeakDerivAlong (fun x => χ x * s x ^ r) (dg k)
      (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧ Function.support (dg k) ⊆ U ∧
      MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hχ : ContDiff ℝ 1 χ) {Clog : ℝ}
    (hlogm : AEStronglyMeasurable (fun x => Real.log (s x)) volume)
    (hlogb : ∀ x, ‖Real.log (s x)‖ ≤ Clog)
    (hγ : 0 ≤ γ) (hforce : 0 ≤ fcoef)
    (he : (∫ x, ∑ i : Fin 2, (dg i x) ^ 2) ≤
      γ * (∫ x, s x ^ (2 * r) * ∑ i : Fin 2, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ i)) ^ 2) +
      fcoef * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)))
    {ε : ℝ} (hε : 0 < ε) {q : NNReal} (hq : 2 ≤ q) :
    (eLpNorm (fun x => s x ^ r) q ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict V)) ^ (2 : ℕ) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (2*q/(q+2)) : ENNReal) ^ (2 : ℕ) *
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))) (cthickening ε U)) ^ (2/(q : ℝ)) *
      (2 : ENNReal) * ENNReal.ofReal
        ((γ * ((2 : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r))) := by
  classical
  have hsp (x : EuclideanSpace ℝ (Fin 2)) : 0 < s x := hδ.trans_le (hs x)
  have hI : IntegrableOn (fun x => s x ^ (2 * r)) U volume := by
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict U) :=
      isFiniteMeasure_restrict.mpr hU.measure_lt_top.ne
    exact MemLp.integrable le_rfl (memLp_rpow_of_bounded_log
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict U) hsp hlogm.restrict hlogb
      (q := 2 * r) (p := 1))
  have hsmeas : AEStronglyMeasurable s (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
    have H := Real.continuous_exp.comp_aestronglyMeasurable hlogm
    have heq : (fun x => Real.exp (Real.log (s x))) = s := funext fun x => Real.exp_log (hsp x)
    rw [heq] at H
    exact H
  have hdcont (k : Fin 2) : Continuous (fun x => fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k)) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdmeas : AEStronglyMeasurable (fun x => ∑ k : Fin 2,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin 2))) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun k _ =>
      ((hdcont k).measurable.pow_const (2 : ℕ)).aestronglyMeasurable
  have hKm : AEStronglyMeasurable (fun x => s x ^ (2 * r) * ∑ i : Fin 2,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ i)) ^ 2) volume :=
    ((hsmeas.aemeasurable.pow_const (2 * r)).aestronglyMeasurable).mul hdmeas
  have hJm : AEStronglyMeasurable (fun x => χ x ^ 2 * s x ^ (2 * r - 1)) volume :=
    ((hχ.continuous.measurable.pow_const (2 : ℕ)).aestronglyMeasurable).mul
      ((hsmeas.aemeasurable.pow_const (2 * r - 1)).aestronglyMeasurable)
  exact weak_cutoff_sobolev_gain_of_energy_two_of_support hU hV hδ hs hχU hχV hχone hχD hgl hgb hgd
    hI hKm hJm hγ hforce he hε hq

/-- A fixed support envelope gives an exact dimensionless thickened-volume bound, for all R>0. -/
theorem volume_cthickening_le_of_subset_closedBall
    {n : ℕ} (x0 : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : U ⊆ closedBall x0 (5/2*R)) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (cthickening (R/4) U) ≤
      ((volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) * ENNReal.ofReal ((3 : ℝ)^n)) *
        (ENNReal.ofReal R)^(n : ℝ) := by
  have hsub : cthickening (R/4) U ⊆ ball x0 (3*R) := by
    refine (cthickening_subset_of_subset (R/4) hU).trans ?_
    rw [cthickening_closedBall (by positivity : 0 ≤ R/4) (by positivity : 0 ≤ 5/2*R)]
    exact closedBall_subset_ball (by linarith)
  calc
    _ ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x0 (3*R)) := measure_mono hsub
    _ = _ := by
      rw [Measure.addHaar_ball_of_pos _ _ (by positivity : (0 : ℝ) < 3*R),
        finrank_euclideanSpace_fin,ENNReal.rpow_natCast,mul_pow,
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow hR.le]
      ring

/-- Keep the exact support-volume power under its dimensionless radius bound. -/
private theorem rpow_le_of_volume_radius_bound {V M : ℝ≥0∞} {R N e : ℝ}
    (he : 0 ≤ e) (hV : V ≤ M * (ENNReal.ofReal R)^N) :
    V^e ≤ M^e * (ENNReal.ofReal R)^(N*e) := by
  have H := ENNReal.rpow_le_rpow hV he
  rwa [ENNReal.mul_rpow_of_nonneg _ _ he,← ENNReal.rpow_mul] at H

/-- Finite-q weak gain with its physical radius gain separated from the dimensionless constant. -/
theorem scaled_weak_cutoff_sobolev_gain_two_of_bounded_log
    {s χ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {dg : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ} {C δ r γ fcoef L : ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsCompact U) (hV : MeasurableSet V)
    (hδ : 0 < δ) (hs : ∀ x, δ ≤ s x)
    (hχU : tsupport χ ⊆ U) (hχV : ∀ x ∈ V, χ x = 1) (hχone : ∀ x, |χ x| ≤ 1)
    (hχD : ∀ x, ‖fderiv ℝ χ x‖ ≤ L)
    (hgl : LocallyIntegrable (fun x => χ x * s x ^ r) (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hgb : ∀ x, ‖χ x * s x ^ r‖ ≤ C)
    (hgd : ∀ k : Fin 2, HasWeakDerivAlong (fun x => χ x * s x ^ r) (dg k)
      (EuclideanSpace.basisFun (Fin 2) ℝ k) ∧ Function.support (dg k) ⊆ U ∧
      MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (hχ : ContDiff ℝ 1 χ) {Clog : ℝ}
    (hlogm : AEStronglyMeasurable (fun x => Real.log (s x)) volume)
    (hlogb : ∀ x, ‖Real.log (s x)‖ ≤ Clog)
    (hγ : 0 ≤ γ) (hforce : 0 ≤ fcoef)
    (he : (∫ x, ∑ i : Fin 2, (dg i x) ^ 2) ≤
      γ * (∫ x, s x ^ (2 * r) * ∑ i : Fin 2, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 2) ℝ i)) ^ 2) +
      fcoef * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)))
    {q : NNReal} (hq : 2 ≤ q) (x0 : EuclideanSpace ℝ (Fin 2)) {R : ℝ} (hR : 0 < R)
    (hUs : U ⊆ closedBall x0 (5/2*R)) :
    let G := SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin 2))) (2*q/(q+2))
    let M : ENNReal := (volume : Measure (EuclideanSpace ℝ (Fin 2))) (ball 0 1) * ENNReal.ofReal (9 : ℝ)
    (eLpNorm (fun x => s x ^ r) q ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict V)) ^ (2 : ℕ) ≤
      ((G : ENNReal)^2 * M^(2/(q : ℝ)) * 2) * (ENNReal.ofReal R)^(4/(q : ℝ)) *
        ENNReal.ofReal ((γ * ((2 : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r))) := by
  intro G M
  have hraw := weak_cutoff_sobolev_gain_of_energy_two_of_support_of_bounded_log
    hU hV hδ hs hχU hχV hχone hχD hgl hgb hgd hχ hlogm hlogb hγ hforce he
    (by positivity : 0 < R/4) hq
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : NNReal)<2) hq)
  have hvol := rpow_le_of_volume_radius_bound
    (by positivity : 0 ≤ 2/(q : ℝ)) (volume_cthickening_le_of_subset_closedBall x0 hR hUs)
  have heq : (2 : ℝ)*(2/(q : ℝ)) = 4/(q : ℝ) := by ring
  have hvol' : ((volume : Measure (EuclideanSpace ℝ (Fin 2))) (cthickening (R/4) U))^(2/(q : ℝ)) ≤
      M^(2/(q : ℝ)) * (ENNReal.ofReal R)^(4/(q : ℝ)) := by
    simpa only [Nat.cast_ofNat,show (3 : ℝ)^2=9 by norm_num,heq] using hvol
  calc
    _ ≤ (G : ENNReal)^2 * ((volume : Measure (EuclideanSpace ℝ (Fin 2))) (cthickening (R/4) U))^(2/(q : ℝ)) *
        2 * ENNReal.ofReal ((γ * (2*L^2)+fcoef/δ)*(∫ x in U,s x^(2*r))) := hraw
    _ ≤ (G : ENNReal)^2 * (M^(2/(q : ℝ))*(ENNReal.ofReal R)^(4/(q : ℝ))) *
        2 * ENNReal.ofReal ((γ * (2*L^2)+fcoef/δ)*(∫ x in U,s x^(2*r))) := by gcongr
    _ = _ := by ring

/-- Two-dimensional finite-q Sobolev gain from actual weak linear data with coordinate supports in U and a given power energy.
No raw PDE/source fields are needed. Weighted integrabilities are derived from domination. -/
theorem weak_cutoff_sobolev_gain_of_energy_one_of_support
    {s χ : EuclideanSpace ℝ (Fin 1) → ℝ}
    {dg : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ} {C δ r γ fcoef L : ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin 1))} (hU : IsCompact U) (hV : MeasurableSet V)
    (hδ : 0 < δ) (hs : ∀ x, δ ≤ s x)
    (hχU : tsupport χ ⊆ U) (hχV : ∀ x ∈ V, χ x = 1) (hχone : ∀ x, |χ x| ≤ 1)
    (hχD : ∀ x, ‖fderiv ℝ χ x‖ ≤ L)
    (hgl : LocallyIntegrable (fun x => χ x * s x ^ r) (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (hgb : ∀ x, ‖χ x * s x ^ r‖ ≤ C)
    (hgd : ∀ k : Fin 1, HasWeakDerivAlong (fun x => χ x * s x ^ r) (dg k)
      (EuclideanSpace.basisFun (Fin 1) ℝ k) ∧ Function.support (dg k) ⊆ U ∧
      MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (hI : IntegrableOn (fun x => s x ^ (2 * r)) U (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (hKm : AEStronglyMeasurable (fun x => s x ^ (2 * r) * ∑ i : Fin 1,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ i)) ^ 2) volume)
    (hJm : AEStronglyMeasurable (fun x => χ x ^ 2 * s x ^ (2 * r - 1)) volume)
    (hγ : 0 ≤ γ) (hforce : 0 ≤ fcoef)
    (he : (∫ x, ∑ i : Fin 1, (dg i x) ^ 2) ≤
      γ * (∫ x, s x ^ (2 * r) * ∑ i : Fin 1, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ i)) ^ 2) +
      fcoef * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)))
    {ε : ℝ} (hε : 0 < ε) :
    (eLpNorm (fun x => s x ^ r) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict V)) ^ (2 : ℕ) ≤
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))) (cthickening ε U)) * ENNReal.ofReal
        ((γ * ((1 : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r))) := by
  classical
  let g := fun x => χ x * s x ^ r
  have hL : 0 ≤ L := (norm_nonneg (fderiv ℝ χ 0)).trans (hχD 0)
  have hDsum (x : EuclideanSpace ℝ (Fin 1)) :
      ∑ k : Fin 1, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k)) ^ 2 ≤ (1 : ℝ) * L ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin 1, L ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hb : |fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k)| ≤ L := by
          have h := (fderiv ℝ χ x).le_opNorm (EuclideanSpace.basisFun (Fin 1) ℝ k)
          rw [(EuclideanSpace.basisFun (Fin 1) ℝ).norm_eq_one k, mul_one] at h
          have h' : |fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k)| ≤ ‖fderiv ℝ χ x‖ := by
            simpa only [Real.norm_eq_abs] using h
          exact h'.trans (hχD x)
        nlinarith [sq_abs (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k)),
          abs_nonneg (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k))]
      _ = _ := by simp
  have hdU (k : Fin 1) : Function.support
      (fun x => fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k)) ⊆ U := by
    intro x hx
    by_contra hnot
    have hnt : x ∉ tsupport χ := fun hx' => hnot (hχU hx')
    have hz := fderiv_of_notMem_tsupport ℝ hnt
    exact hx (by change fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k) = 0; rw [hz]; rfl)
  have hW := weighted_cutoff_power_integrable_bounds (volume : Measure (EuclideanSpace ℝ (Fin 1)))
    hU.measurableSet hδ hs hχone ((subset_tsupport χ).trans hχU) hdU hDsum hI hKm hJm
  have hE : (∫ x, ∑ k : Fin 1, (dg k x) ^ 2) ≤
      (γ * ((1 : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r)) := by
    calc
      _ ≤ _ := he
      _ ≤ γ * (((1 : ℝ) * L ^ 2) * (∫ x in U, s x ^ (2 * r))) +
          fcoef * (δ⁻¹ * (∫ x in U, s x ^ (2 * r))) :=
        add_le_add (mul_le_mul_of_nonneg_left hW.2.2.1 hγ)
          (mul_le_mul_of_nonneg_left hW.2.2.2 hforce)
      _ = _ := by ring
  have hgU : Function.support g ⊆ U := by
    intro x hx
    apply hχU
    apply subset_tsupport χ
    intro hz
    exact hx (by dsimp only [g]; rw [hz,zero_mul])
  let A : ENNReal := ((volume : Measure (EuclideanSpace ℝ (Fin 1))) (cthickening ε U))^(1/2 : ℝ)
  have hsob := eLpNorm_top_le_eLpNorm_weak_deriv_of_support_subset_one hgl hgb hU hgU
    (fun k => (hgd k).2.1) (fun k => (hgd k).1) (fun k => (hgd k).2.2) hε
  have hcoord := FunctionalInequalities.L2.sq_sum_eLpNorm_le_dim_mul_integral_sum_sq
    (volume : Measure (EuclideanSpace ℝ (Fin 1))) (fun k => (hgd k).2.2)
  have hcoord1 : (eLpNorm (dg 0) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1))))^2 ≤
      ENNReal.ofReal (∫ x,∑ k : Fin 1,(dg k x)^2) := by
    simpa only [Fin.sum_univ_one,Nat.cast_one,one_mul] using hcoord
  have heq : (fun x => s x ^ r) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict V] g := by
    filter_upwards [ae_restrict_mem hV] with x hx
    dsimp only [g]
    rw [hχV x hx,one_mul]
  have hnorm : eLpNorm (fun x => s x ^ r) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict V) ≤
      eLpNorm g ∞ (volume : Measure (EuclideanSpace ℝ (Fin 1))) := by
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_restrict_le _ _ _ _
  calc
    _ ≤ (A*eLpNorm (dg 0) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1)) ))^2 := by
      gcongr
      exact hnorm.trans hsob
    _ = A^2*(eLpNorm (dg 0) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1))))^2 := mul_pow _ _ 2
    _ ≤ A^2*ENNReal.ofReal (∫ x,∑ k : Fin 1,(dg k x)^2) := by gcongr
    _ ≤ A^2*ENNReal.ofReal ((γ*(1*L^2)+fcoef/δ)*(∫ x in U,s x^(2*r))) := by gcongr
    _ = _ := by
      dsimp only [A]
      rw [← ENNReal.rpow_mul_natCast]
      norm_num

/-- Finite-q n2 gain with the actual power integrabilities derived from a bounded measurable actual log.
Derivative representatives retain explicit support in U; all q>=2 and epsilon>0 support factors stay exact. -/
theorem weak_cutoff_sobolev_gain_of_energy_one_of_support_of_bounded_log
    {s χ : EuclideanSpace ℝ (Fin 1) → ℝ}
    {dg : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ} {C δ r γ fcoef L : ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin 1))} (hU : IsCompact U) (hV : MeasurableSet V)
    (hδ : 0 < δ) (hs : ∀ x, δ ≤ s x)
    (hχU : tsupport χ ⊆ U) (hχV : ∀ x ∈ V, χ x = 1) (hχone : ∀ x, |χ x| ≤ 1)
    (hχD : ∀ x, ‖fderiv ℝ χ x‖ ≤ L)
    (hgl : LocallyIntegrable (fun x => χ x * s x ^ r) (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (hgb : ∀ x, ‖χ x * s x ^ r‖ ≤ C)
    (hgd : ∀ k : Fin 1, HasWeakDerivAlong (fun x => χ x * s x ^ r) (dg k)
      (EuclideanSpace.basisFun (Fin 1) ℝ k) ∧ Function.support (dg k) ⊆ U ∧
      MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 1))))
    (hχ : ContDiff ℝ 1 χ) {Clog : ℝ}
    (hlogm : AEStronglyMeasurable (fun x => Real.log (s x)) volume)
    (hlogb : ∀ x, ‖Real.log (s x)‖ ≤ Clog)
    (hγ : 0 ≤ γ) (hforce : 0 ≤ fcoef)
    (he : (∫ x, ∑ i : Fin 1, (dg i x) ^ 2) ≤
      γ * (∫ x, s x ^ (2 * r) * ∑ i : Fin 1, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ i)) ^ 2) +
      fcoef * (∫ x, χ x ^ 2 * s x ^ (2 * r - 1)))
    {ε : ℝ} (hε : 0 < ε) :
    (eLpNorm (fun x => s x ^ r) ∞ ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict V)) ^ (2 : ℕ) ≤
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))) (cthickening ε U)) * ENNReal.ofReal
        ((γ * ((1 : ℝ) * L ^ 2) + fcoef / δ) * (∫ x in U, s x ^ (2 * r))) := by
  classical
  have hsp (x : EuclideanSpace ℝ (Fin 1)) : 0 < s x := hδ.trans_le (hs x)
  have hI : IntegrableOn (fun x => s x ^ (2 * r)) U volume := by
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict U) :=
      isFiniteMeasure_restrict.mpr hU.measure_lt_top.ne
    exact MemLp.integrable le_rfl (memLp_rpow_of_bounded_log
      ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict U) hsp hlogm.restrict hlogb
      (q := 2 * r) (p := 1))
  have hsmeas : AEStronglyMeasurable s (volume : Measure (EuclideanSpace ℝ (Fin 1))) := by
    have H := Real.continuous_exp.comp_aestronglyMeasurable hlogm
    have heq : (fun x => Real.exp (Real.log (s x))) = s := funext fun x => Real.exp_log (hsp x)
    rw [heq] at H
    exact H
  have hdcont (k : Fin 1) : Continuous (fun x => fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k)) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdmeas : AEStronglyMeasurable (fun x => ∑ k : Fin 1,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun k _ =>
      ((hdcont k).measurable.pow_const (2 : ℕ)).aestronglyMeasurable
  have hKm : AEStronglyMeasurable (fun x => s x ^ (2 * r) * ∑ i : Fin 1,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin 1) ℝ i)) ^ 2) volume :=
    ((hsmeas.aemeasurable.pow_const (2 * r)).aestronglyMeasurable).mul hdmeas
  have hJm : AEStronglyMeasurable (fun x => χ x ^ 2 * s x ^ (2 * r - 1)) volume :=
    ((hχ.continuous.measurable.pow_const (2 : ℕ)).aestronglyMeasurable).mul
      ((hsmeas.aemeasurable.pow_const (2 * r - 1)).aestronglyMeasurable)
  exact weak_cutoff_sobolev_gain_of_energy_one_of_support hU hV hδ hs hχU hχV hχone hχD hgl hgb hgd
    hI hKm hJm hγ hforce he hε

end LowDimensionalGain

end FunctionalInequalities.Analysis
