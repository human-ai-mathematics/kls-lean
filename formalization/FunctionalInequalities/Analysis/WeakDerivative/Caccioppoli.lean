module

public import FunctionalInequalities.Analysis.WeakDerivative.ChainRule
public import FunctionalInequalities.Analysis.WeakDerivative.PowerTests
public import FunctionalInequalities.Analysis.Matrix.Positivity

/-!
# Caccioppoli inequality for bounded weak supersolutions

For a bounded weak `H¹_loc` function `w` on `EuclideanSpace ℝ (Fin n)` (every `n`), nonnegative a.e.
on the support of a
`C¹` compactly supported cutoff `χ`, a.e. measurable coefficients `A` that are elliptic between `α`
and `β` a.e. on
`tsupport χ`, and the weak supersolution inequality `-F ∫ η ≤ ∫ aᵀ A ∇η` against every bounded
nonnegative test supported
in `tsupport χ`, the energy of the negative power `s^(-p-1)` (`s = δ + max w 0`, `δ, p > 0`) is
controlled:
`∫ χ² s^(-p-1) |a|² ≤ (4β/(p²α)) ∫ s^(1-p) |∇χ|² + (2F/(pα)) ∫ χ² s^(-p)`, with all three integrals
integrable
(`local_weak_supersolution_caccioppoli`).

The proof tests with the square cutoff test `χ² s^(-p)` of `WeakDerivative/PowerTests.lean` and
absorbs the cross term with
`rpow_cutoff_quadratic_young`. This is a supporting `H¹` energy estimate for Gilbarg–Trudinger
(2001) (8.48)–(8.49) and
Letwin arXiv:2607.24164v1 Lemma 2.2. It is not Moser iteration, John–Nirenberg or a Harnack
inequality.

The Moser energy inputs, with nonnegativity only on the cutoff support:
* `local_weak_supersolution_log_energy`, the logarithmic energy (`p = 1`) of `b = s⁻¹ a`, without
  any weak derivative of
  `log (δ + max w 0)`;
* `local_weak_supersolution_power_energy`, the power energy of `χ s^r` for every real `r < 1/2`.

For `w ≥ 0` a.e. on the whole space, `bounded_weak_supersolution_caccioppoli`,
`bounded_weak_supersolution_power_energy` and
`bounded_weak_supersolution_log_caccioppoli` are their consumers; the last also gives the weak
derivatives of
`log (δ + max w 0)`.
-/

@[expose] public section

section

open MeasureTheory Set Matrix
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/--
**Caccioppoli inequality, local nonnegativity.** For bounded `w` with weak derivatives `a` in
`L²_loc`, nonnegative
only a.e. on `tsupport χ`, elliptic measurable coefficients between `α` and `β` on `tsupport χ` and
the weak
supersolution inequality against nonnegative tests supported in `tsupport χ`: with `s = δ + max w 0`
and `δ, p > 0`,
`∫ χ² s^(-p-1) Σ_k a_k² ≤ (4β/(p²α)) ∫ s^(1-p) Σ_k (∂_k χ)² + (2F/(pα)) ∫ χ² s^(-p)`, all integrands
integrable. -/
theorem local_weak_supersolution_caccioppoli {n : ℕ} {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C α β F δ p : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 :
      ∀ k : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hAm :
      ∀ i j : Fin n,
        AEStronglyMeasurable (fun x => A x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hnonneg :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)), 0 ≤ w x)
    (hα : 0 < α) (hβ : 0 < β) (hF : 0 ≤ F)
    (hcoeff :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)),
        (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (hsub :
      ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
        LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
          (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) →
            HasCompactSupport η →
              Function.support η ⊆ tsupport χ →
                (∀ x, 0 ≤ η x) →
                  (∀ k : Fin n,
                      HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                        HasCompactSupport (dη k) ∧
                          Function.support (dη k) ⊆ tsupport χ ∧
                            MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
                    -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                      ∫ x,
                        dotProduct (fun k => a k x)
                          ((A x).mulVec
                            (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hδ : 0 < δ) (hp : 0 < p) :
    let s := fun x => δ + max (w x) 0
    Integrable (fun x => χ x ^ 2 * s x ^ (-p - 1) * ∑ k : Fin n, (a k x) ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable
          (fun x =>
            s x ^ (1 - p) *
              ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => χ x ^ 2 * s x ^ (-p))
            (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∫ x,
              χ x ^ 2 * s x ^ (-p - 1) *
                ∑ k : Fin n, (a k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            (4 * β / (p ^ 2 * α)) *
                (∫ x,
                  s x ^ (1 - p) *
                    ∑ k : Fin n,
                      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^
                        2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (p * α)) *
                (∫ x, χ x ^ 2 * s x ^ (-p) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  -- Regularize the positive part and prepare the power test.
  intro s
  classical
  -- `0 < β` and `0 ≤ F` belong to the elliptic/forcing setting; the estimate itself does not use
  -- them

  have _hβ := hβ
  have _hF := hF
  have hStm : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hSt : IsCompact (tsupport χ) := hχc
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  have hs_lo (x : EuclideanSpace ℝ (Fin n)) : δ ≤ s x := by
    simp only [s];
    linarith [le_max_right (w x) 0]
  have hs_pos (x : EuclideanSpace ℝ (Fin n)) : 0 < s x := lt_of_lt_of_le hδ (hs_lo x)
  have hs_hi (x : EuclideanSpace ℝ (Fin n)) : s x ≤ δ + C := by
    have h1 : w x ≤ C :=
      (le_abs_self (w x)).trans (by simpa only [Real.norm_eq_abs] using hbound x)
    simp only [s];
    linarith [max_le h1 hC]
  -- bounded real powers of s

  have hpow (r : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, 0 ≤ s x ^ r ∧ s x ^ r ≤ B := by
    obtain ⟨B, hB⟩ :=
      (isCompact_Icc : IsCompact (Icc δ (δ + C))).exists_bound_of_continuousOn (f :=
        fun t : ℝ => t ^ r)
        (ContinuousOn.rpow_const continuousOn_id fun t ht =>
          Or.inl (ne_of_gt (lt_of_lt_of_le hδ ht.1)))
    refine
      ⟨B, (norm_nonneg _).trans (hB δ ⟨le_rfl, by linarith⟩), fun x =>
        ⟨Real.rpow_nonneg (hs_pos x).le r, ?_⟩⟩
    have h := hB (s x) ⟨hs_lo x, hs_hi x⟩
    rwa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hs_pos x).le r)] at h
  have hspm (r : ℝ) :
    AEStronglyMeasurable (fun x => s x ^ r) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hg : Continuous fun t : ℝ => (δ + max t 0) ^ r :=
      Continuous.rpow_const (f := fun t : ℝ => δ + max t 0) (by fun_prop) fun t =>
        Or.inl (show δ + max t 0 ≠ 0 from ne_of_gt (by linarith [le_max_right t 0]))
    exact hg.comp_aestronglyMeasurable hw.aestronglyMeasurable
  have ham (k : Fin n) :
    AEStronglyMeasurable (a k) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hweak k).2.1.aestronglyMeasurable
  have hdχc (k : Fin n) :
    Continuous (fun x => fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsqc {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => f x ^ 2) :=
    hf.mono' fun x hx =>
      subset_tsupport f
        (fun h =>
          hx (by simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]))
  have hzero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport χ) :
    χ x = 0 ∧ fderiv ℝ χ x = 0 := by
    have hev := notMem_tsupport_iff_eventuallyEq.mp hx
    refine ⟨hev.eq_of_nhds, ?_⟩
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  obtain ⟨Cχ, hCχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hχ2 (x : EuclideanSpace ℝ (Fin n)) : χ x ^ 2 ≤ Cχ ^ 2 := by
    have h := hCχ x
    rw [Real.norm_eq_abs] at h
    nlinarith [abs_nonneg (χ x), sq_abs (χ x)]
  -- the vectors and the bilinear forms

  have hbil (u v : EuclideanSpace ℝ (Fin n) → Fin n → ℝ)
    (hu :
      ∀ k, AEStronglyMeasurable (fun x => u x k) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hv :
      ∀ k,
        AEStronglyMeasurable (fun x => v x k) (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    AEStronglyMeasurable (fun x => dotProduct (u x) ((A x).mulVec (v x)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simp only [dotProduct, Matrix.mulVec]
    exact
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (hu i).mul (Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hAm i j).mul (hv j))
  set aV : EuclideanSpace ℝ (Fin n) → Fin n → ℝ := fun x k => a k x with haV

  -- Write its weak derivative and the pointwise coercive estimate.
  set dV : EuclideanSpace ℝ (Fin n) → Fin n → ℝ := fun x k =>
    fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) with hdV
  set EA : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    χ x ^ 2 * s x ^ (-p - 1) * dotProduct (aV x) ((A x).mulVec (aV x))
  set X : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    2 * χ x * s x ^ (-p) * dotProduct (aV x) ((A x).mulVec (dV x))
  set KA : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    s x ^ (1 - p) * dotProduct (dV x) ((A x).mulVec (dV x))
  set E : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    χ x ^ 2 * s x ^ (-p - 1) * ∑ k : Fin n, (a k x) ^ 2
  set Kc : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    s x ^ (1 - p) * ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
  set J : EuclideanSpace ℝ (Fin n) → ℝ := fun x => χ x ^ 2 * s x ^ (-p)
  have hself (v : Fin n → ℝ) : dotProduct v v = ∑ k : Fin n, v k ^ 2 := by
    simp only [dotProduct, sq]
  -- pointwise a.e. facts: ellipticity and the weighted Young inequality on tsupport χ, zero
  -- elsewhere

  have hcoeff' :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ tsupport χ →
        (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef :=
    (ae_restrict_iff' hStm).1 hcoeff
  have hpt :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      0 ≤ EA x ∧
        α * E x ≤ EA x ∧
          EA x ≤ β * E x ∧
            0 ≤ KA x ∧
              KA x ≤ β * Kc x ∧
                X x ≤ (p / 2) * EA x + (2 / p) * KA x ∧
                  -X x ≤ (p / 2) * EA x + (2 / p) * KA x := by
    filter_upwards [hcoeff'] with x hx
    by_cases hxs : x ∈ tsupport χ
    · obtain ⟨hlo, hup⟩ := hx hxs
      have hA : (A x).PosSemidef := by
        have h :=
          hlo.add
            ((Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef).smul hα.le)
        simpa only [sub_add_cancel] using h
      have hq (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef) (v : Fin n → ℝ) :
        0 ≤ dotProduct v (B.mulVec v) := by
        simpa only [star_trivial] using hB.dotProduct_mulVec_nonneg v
      have hlo' (v : Fin n → ℝ) : α * dotProduct v v ≤ dotProduct v ((A x).mulVec v) := by
        have h := hq _ hlo v
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
          dotProduct_smul, smul_eq_mul] at h
        linarith
      have hup' (v : Fin n → ℝ) : dotProduct v ((A x).mulVec v) ≤ β * dotProduct v v := by
        have h := hq _ hup v
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
          dotProduct_smul, smul_eq_mul] at h
        linarith
      have hf1 : 0 ≤ χ x ^ 2 * s x ^ (-p - 1) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hs_pos x).le _)
      have hf2 : 0 ≤ s x ^ (1 - p) := Real.rpow_nonneg (hs_pos x).le _
      have hy1 := rpow_cutoff_quadratic_young (A x) hA (aV x) (dV x) (hs_pos x) hp (χ x)
      have hy2 := rpow_cutoff_quadratic_young (A x) hA (aV x) (dV x) (hs_pos x) hp (-χ x)
      have haa := hlo' (aV x)
      have hau := hup' (aV x)
      have hdd := hup' (dV x)
      have hd0 := hq _ hA (dV x)
      have ha0 := hq _ hA (aV x)
      rw [hself] at haa hau hdd
      refine ⟨mul_nonneg hf1 ha0, ?_, ?_, mul_nonneg hf2 hd0, ?_, ?_, ?_⟩
      · have h := mul_le_mul_of_nonneg_left haa hf1
        simp only [E, EA]; nlinarith [h]
      · have h := mul_le_mul_of_nonneg_left hau hf1
        simp only [E, EA]; nlinarith [h]
      · have h := mul_le_mul_of_nonneg_left hdd hf2
        simp only [Kc, KA, dV] at h ⊢; nlinarith [h]
      · simp only [X, EA, KA]; nlinarith [hy1]
      · simp only [X, EA, KA]
        have e2 : (-χ x) ^ 2 = χ x ^ 2 := neg_sq _
        rw [e2] at hy2
        nlinarith [hy2]
    · obtain ⟨h0, h1⟩ := hzero x hxs
      have hdv0 : dV x = 0 := by funext k; simp only [dV, h1, _root_.zero_apply, Pi.zero_apply]
      simp only [EA, E, KA, Kc, X, h0, hdv0, h1, Matrix.mulVec_zero, dotProduct_zero]
      simp
  -- integrability by domination

  obtain ⟨B1, hB10, hB1⟩ := hpow (-p - 1)
  obtain ⟨B2, hB20, hB2⟩ := hpow (1 - p)
  obtain ⟨B3, hB30, hB3⟩ := hpow (-p)
  have hχsq : Continuous (fun x => χ x ^ 2) := hχ.continuous.pow 2
  have hχsqi : Integrable (fun x => χ x ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχsq.integrable_of_hasCompactSupport (hsqc hχc)
  have hJm : AEStronglyMeasurable J (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχsq.aestronglyMeasurable.mul (hspm _)
  have hJ : Integrable J (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    refine (hχsqi.const_mul B3).mono' hJm (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hB3 x).1)]
    nlinarith [(hB3 x).2, sq_nonneg (χ x)]
  have hdsum :
    Integrable (fun x => ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum _ fun k _ =>
      ((hdχc k).pow 2).integrable_of_hasCompactSupport
        (hsqc (hχc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ k)))
  have hdsum0 (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hKcm : AEStronglyMeasurable Kc (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hspm _).mul
      (Finset.aestronglyMeasurable_fun_sum _ fun k _ => ((hdχc k).pow 2).aestronglyMeasurable)
  have hKc : Integrable Kc (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    refine (hdsum.const_mul B2).mono' hKcm (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hB2 x).1 (hdsum0 x))]
    exact mul_le_mul_of_nonneg_right (hB2 x).2 (hdsum0 x)
  have hasq : IntegrableOn (fun x => ∑ k : Fin n, (a k x) ^ 2) (tsupport χ) volume :=
    integrable_finsetSum _ fun k _ => (ha2 k _ hSt).integrable_sq
  have hasq0 (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ ∑ k : Fin n, (a k x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEm : AEStronglyMeasurable E (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hχsq.aestronglyMeasurable.mul (hspm _)).mul
      (Finset.aestronglyMeasurable_fun_sum _ fun k _ => (ham k).pow 2)

  -- Check integrability and integrate the energy inequality.
  have hE : Integrable E (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    refine
      (((integrable_indicator_iff hStm).2 hasq).const_mul (Cχ ^ 2 * B1)).mono' hEm
        (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hB1 x).1) (hasq0 x))]
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
      exact
        mul_le_mul_of_nonneg_right (mul_le_mul (hχ2 x) (hB1 x).2 (hB1 x).1 (sq_nonneg _))
          (hasq0 x)
    · rw [Set.indicator_of_notMem hx, (hzero x hx).1]; simp
  have haVm (k : Fin n) :
    AEStronglyMeasurable (fun x => aV x k) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ham k
  have hdVm (k : Fin n) :
    AEStronglyMeasurable (fun x => dV x k) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hdχc k).aestronglyMeasurable
  have hEAm : AEStronglyMeasurable EA (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hχsq.aestronglyMeasurable.mul (hspm _)).mul (hbil aV aV haVm haVm)
  have hKAm : AEStronglyMeasurable KA (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hspm _).mul (hbil dV dV hdVm hdVm)
  have hXm : AEStronglyMeasurable X (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ((hχ.continuous.aestronglyMeasurable.const_mul 2).mul (hspm _)).mul (hbil aV dV haVm hdVm)
  have hEA : Integrable EA (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hE.const_mul β).mono' hEAm
      (hpt.mono fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2.2.1)
  have hKA : Integrable KA (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hKc.const_mul β).mono' hKAm
      (hpt.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg hx.2.2.2.1];
        exact hx.2.2.2.2.1)
  have hY :
    Integrable (fun x => (p / 2) * EA x + (2 / p) * KA x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hEA.const_mul _).add (hKA.const_mul _)
  have hX : Integrable X (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hY.mono' hXm
      (hpt.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_le];
        constructor <;> linarith [hx.2.2.2.2.2.1, hx.2.2.2.2.2.2])
  -- the weak supersolution tested with η = χ² s^(-p): the only use of nonnegativity, now
  -- local on tsupport χ

  obtain ⟨hηloc, hηc, hηsupp, hηb, hη0, hηd⟩ :=
    local_rpow_cutoff_weak_test hw hbound hweak ha2 hχ hχc hnonneg hδ (-p)
  have hmain := hsub _ _ hηloc hηb hηc hηsupp hη0 hηd
  have hident :
    (fun x =>
        dotProduct (fun k => a k x)
          ((A x).mulVec
            (fun k =>
              2 * χ x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) *
                  (δ + max (w x) 0) ^ (-p) +
                χ x ^ 2 * ((-p) * (δ + max (w x) 0) ^ (-p - 1)) * a k x))) =
      fun x => X x - p * EA x := by
    funext x
    have hv :
      (fun k =>
          2 * χ x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) *
              (δ + max (w x) 0) ^ (-p) +
            χ x ^ 2 * ((-p) * (δ + max (w x) 0) ^ (-p - 1)) * a k x) =
        (2 * χ x * s x ^ (-p)) • dV x + (χ x ^ 2 * (-p) * s x ^ (-p - 1)) • aV x := by
      funext k; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dV, aV, s]; ring
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    simp only [X, EA]
    ring
  rw [hident, integral_sub hX (hEA.const_mul p), integral_const_mul] at hmain
  change -F * (∫ x, J x) ≤ (∫ x, X x) - p * ∫ x, EA x at hmain
  have h2 : (∫ x, X x) ≤ (p / 2) * (∫ x, EA x) + (2 / p) * ∫ x, KA x := by
    rw [← integral_const_mul, ← integral_const_mul, ←
      integral_add (hEA.const_mul _) (hKA.const_mul _)]
    exact integral_mono_ae hX hY (hpt.mono fun x hx => hx.2.2.2.2.2.1)
  have h3 : α * (∫ x, E x) ≤ ∫ x, EA x := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hE.const_mul α) hEA (hpt.mono fun x hx => hx.2.1)
  have h4 : (∫ x, KA x) ≤ β * ∫ x, Kc x := by
    rw [← integral_const_mul]
    exact integral_mono_ae hKA (hKc.const_mul β) (hpt.mono fun x hx => hx.2.2.2.2.1)
  refine ⟨hE, hKc, hJ, ?_⟩
  change (∫ x, E x) ≤ (4 * β / (p ^ 2 * α)) * (∫ x, Kc x) + (2 * F / (p * α)) * ∫ x, J x
  have hJ0 : 0 ≤ ∫ x, J x :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hs_pos x).le _)
  have hkey : (p / 2) * (∫ x, EA x) ≤ (2 / p) * (∫ x, KA x) + F * ∫ x, J x := by linarith
  have hEA' : (∫ x, EA x) ≤ (4 / p ^ 2) * (∫ x, KA x) + (2 * F / p) * ∫ x, J x := by
    have h := mul_le_mul_of_nonneg_left hkey (show 0 ≤ 2 / p by positivity)
    have e1 : 2 / p * (p / 2 * ∫ x, EA x) = ∫ x, EA x := by field_simp
    have e2 :
      2 / p * (2 / p * (∫ x, KA x) + F * ∫ x, J x) =
        (4 / p ^ 2) * (∫ x, KA x) + (2 * F / p) * ∫ x, J x := by
      field_simp; ring
    linarith
  have hfin : α * (∫ x, E x) ≤ (4 / p ^ 2) * (β * ∫ x, Kc x) + (2 * F / p) * ∫ x, J x :=
    h3.trans (hEA'.trans (by gcongr))
  rw [← mul_le_mul_iff_of_pos_left hα]
  have e3 :
    α * ((4 * β / (p ^ 2 * α)) * (∫ x, Kc x) + (2 * F / (p * α)) * ∫ x, J x) =
      (4 / p ^ 2) * (β * ∫ x, Kc x) + (2 * F / p) * ∫ x, J x := by
    field_simp
  rw [e3]; exact hfin

/--
**Caccioppoli inequality for bounded weak supersolutions** with the negative real power `s^(-p-1)`,
`s = δ + max w 0`: the three energy integrands are integrable and
`∫ χ² s^(-p-1) Σ_k a_k² ≤ (4β/(p²α)) ∫ s^(1-p) Σ_k (∂_k χ)² + (2F/(pα)) ∫ χ² s^(-p)`. -/
theorem bounded_weak_supersolution_caccioppoli {n : ℕ} {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C α β F δ p : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 :
      ∀ k : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x)
    (hAm :
      ∀ i j : Fin n,
        AEStronglyMeasurable (fun x => A x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hα : 0 < α) (hβ : 0 < β) (hF : 0 ≤ F)
    (hcoeff :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)),
        (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (hsub :
      ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
        LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
          (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) →
            HasCompactSupport η →
              Function.support η ⊆ tsupport χ →
                (∀ x, 0 ≤ η x) →
                  (∀ k : Fin n,
                      HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                        HasCompactSupport (dη k) ∧
                          Function.support (dη k) ⊆ tsupport χ ∧
                            MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
                    -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                      ∫ x,
                        dotProduct (fun k => a k x)
                          ((A x).mulVec
                            (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hδ : 0 < δ) (hp : 0 < p) :
    let s := fun x => δ + max (w x) 0
    Integrable (fun x => χ x ^ 2 * s x ^ (-p - 1) * ∑ k : Fin n, (a k x) ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable
          (fun x =>
            s x ^ (1 - p) *
              ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => χ x ^ 2 * s x ^ (-p))
            (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∫ x,
              χ x ^ 2 * s x ^ (-p - 1) *
                ∑ k : Fin n, (a k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            (4 * β / (p ^ 2 * α)) *
                (∫ x,
                  s x ^ (1 - p) *
                    ∑ k : Fin n,
                      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^
                        2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (p * α)) *
                (∫ x, χ x ^ 2 * s x ^ (-p) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  exact
    local_weak_supersolution_caccioppoli hw hbound hweak ha2 hAm hχ hχc
      (ae_restrict_of_ae hnonneg) hα hβ hF hcoeff hsub hδ hp

/--
**Logarithmic energy, local nonnegativity** (`p = 1`): with `b k = s⁻¹ a k`, the integrability of
the three
integrands and `∫ χ² Σ_k b_k² ≤ (4β/α) ∫ Σ_k (∂_k χ)² + (2F/(αδ)) ∫ χ²`, nonnegativity only a.e. on
`tsupport χ`. It
asserts no weak derivative of `log (δ + max w 0)`; see `exists_bounded_weak_log_extension` for a
weak extension. -/
theorem local_weak_supersolution_log_energy {n : ℕ} {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C α β F δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 :
      ∀ k : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hAm :
      ∀ i j : Fin n,
        AEStronglyMeasurable (fun x => A x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hnonneg :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)), 0 ≤ w x)
    (hα : 0 < α) (hβ : 0 < β) (hF : 0 ≤ F)
    (hcoeff :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)),
        (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (hsub :
      ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
        LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
          (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) →
            HasCompactSupport η →
              Function.support η ⊆ tsupport χ →
                (∀ x, 0 ≤ η x) →
                  (∀ k : Fin n,
                      HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                        HasCompactSupport (dη k) ∧
                          Function.support (dη k) ⊆ tsupport χ ∧
                            MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
                    -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                      ∫ x,
                        dotProduct (fun k => a k x)
                          ((A x).mulVec
                            (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hδ : 0 < δ) :
    let s := fun x => δ + max (w x) 0
    let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
    Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable
          (fun x => ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => χ x ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∫ x,
              χ x ^ 2 *
                ∑ k : Fin n, (b k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            (4 * β / α) *
                (∫ x,
                  ∑ k : Fin n,
                    (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^
                      2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (2 * F / (α * δ)) *
                (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  intro s b
  have hc :=
    local_weak_supersolution_caccioppoli hw hbound hweak ha2 hAm hχ hχc hnonneg hα hβ hF hcoeff
      hsub hδ (p := 1) zero_lt_one
  dsimp only at hc
  have hp1 : -(1 : ℝ) - 1 = -2 := by norm_num
  simp only [hp1, sub_self, Real.rpow_zero, one_mul, one_pow, Real.rpow_neg_one] at hc
  have hsame (x : EuclideanSpace ℝ (Fin n)) :
    χ x ^ 2 * (δ + max (w x) 0) ^ (-2 : ℝ) * ∑ k : Fin n, (a k x) ^ 2 =
      χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2 := by
    have hs : 0 ≤ s x := (lt_of_lt_of_le hδ (le_add_of_nonneg_right (le_max_right _ _))).le
    have hpow : s x ^ (-2 : ℝ) = (s x)⁻¹ ^ (2 : ℕ) := by
      rw [Real.rpow_neg hs, Real.rpow_two, inv_pow]
    change χ x ^ 2 * s x ^ (-2 : ℝ) * _ = _
    rw [hpow, mul_assoc, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by simp only [b, mul_pow]
  have hleft :
    (fun x => χ x ^ 2 * (δ + max (w x) 0) ^ (-2 : ℝ) * ∑ k : Fin n, (a k x) ^ 2) =
      (fun x => χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2) :=
    funext hsame
  rw [hleft] at hc
  have hχ2c : HasCompactSupport (fun x => χ x ^ 2) :=
    hχc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hχ2i : Integrable (fun x => χ x ^ 2) volume :=
    (hχ.continuous.pow 2).integrable_of_hasCompactSupport hχ2c
  have hj :
    (∫ x, χ x ^ 2 * (s x)⁻¹ ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      δ⁻¹ * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    rw [← integral_const_mul]
    apply integral_mono hc.2.2.1 (hχ2i.const_mul δ⁻¹)
    intro x
    have hslo : δ ≤ s x := le_add_of_nonneg_right (le_max_right _ _)
    have hi : (s x)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hslo
    calc
      χ x ^ 2 * (s x)⁻¹ ≤ χ x ^ 2 * δ⁻¹ := mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = δ⁻¹ * χ x ^ 2 :=
        mul_comm _
          _
  -- no weak derivative of `log (δ + max w 0)` is asserted: only the energy and its
  -- integrability

  refine ⟨hc.1, hc.2.1, hχ2i, ?_⟩
  calc
    _ ≤
        (4 * β / α) *
            (∫ x, ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2) +
          (2 * F / α) * (∫ x, χ x ^ 2 * (s x)⁻¹) :=
      hc.2.2.2
    _ ≤
        (4 * β / α) *
            (∫ x, ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2) +
          (2 * F / α) * (δ⁻¹ * ∫ x, χ x ^ 2) := by
      gcongr
    _ = _ := by ring

/--
**Logarithmic energy** (Caccioppoli at `p = 1`): with `s = δ + max w 0` and `b k = s⁻¹ a k`, the
actual weak
derivatives of `log s` together with `∫ χ² Σ_k b_k² ≤ (4β/α) ∫ Σ_k (∂_k χ)² + (2F/(αδ)) ∫ χ²`, all
integrands integrable. -/
theorem bounded_weak_supersolution_log_caccioppoli {n : ℕ} {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C α β F δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 :
      ∀ k : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x)
    (hAm :
      ∀ i j : Fin n,
        AEStronglyMeasurable (fun x => A x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hα : 0 < α) (hβ : 0 < β) (hF : 0 ≤ F)
    (hcoeff :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)),
        (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (hsub :
      ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
        LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
          (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) →
            HasCompactSupport η →
              Function.support η ⊆ tsupport χ →
                (∀ x, 0 ≤ η x) →
                  (∀ k : Fin n,
                      HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                        HasCompactSupport (dη k) ∧
                          Function.support (dη k) ⊆ tsupport χ ∧
                            MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
                    -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                      ∫ x,
                        dotProduct (fun k => a k x)
                          ((A x).mulVec
                            (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hδ : 0 < δ) :
    let s := fun x => δ + max (w x) 0
    let b := fun (k : Fin n) x => (s x)⁻¹ * a k x
    (∀ k : Fin n,
        HasWeakDerivAlong (fun x => Real.log (s x)) (b k)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)),
            IsCompact S →
              MemLp (b k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, (b k x) ^ 2)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable
            (fun x => ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
            (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          Integrable (fun x => χ x ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
            (∫ x,
                χ x ^ 2 *
                  ∑ k : Fin n, (b k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
              (4 * β / α) *
                  (∫ x,
                    ∑ k : Fin n,
                      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^
                        2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
                (2 * F / (α * δ)) *
                  (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  intro s b
  exact
    ⟨(hasWeakDerivAlong_log_max_shift_of_ae_nonneg_bounded hw hbound hweak ha2 hnonneg hδ).2.2,
      local_weak_supersolution_log_energy hw hbound hweak ha2 hAm hχ hχc
        (ae_restrict_of_ae hnonneg) hα hβ hF hcoeff hsub hδ⟩

/--
**Power energy, local nonnegativity**, for `g = χ s^r`, every real `r < 1/2` (`p = 1 − 2r > 0`),
with the exact
weak derivative `dg`: `∫ Σ_k dg_k² ≤ (2 + 8r²β/(p²α)) ∫ s^{2r} Σ_k (∂_k χ)² + (4r²F/(pα)) ∫ χ²
s^{2r−1}`, all integrands
integrable, nonnegativity only a.e. on `tsupport χ`. -/
theorem local_weak_supersolution_power_energy {n : ℕ} {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C α β F δ r : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 :
      ∀ k : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hAm :
      ∀ i j : Fin n,
        AEStronglyMeasurable (fun x => A x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hnonneg :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)), 0 ≤ w x)
    (hα : 0 < α) (hβ : 0 < β) (hF : 0 ≤ F)
    (hcoeff :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)),
        (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (hsub :
      ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
        LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
          (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) →
            HasCompactSupport η →
              Function.support η ⊆ tsupport χ →
                (∀ x, 0 ≤ η x) →
                  (∀ k : Fin n,
                      HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                        HasCompactSupport (dη k) ∧
                          Function.support (dη k) ⊆ tsupport χ ∧
                            MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
                    -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                      ∫ x,
                        dotProduct (fun k => a k x)
                          ((A x).mulVec
                            (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hδ : 0 < δ) (hr : r < 1 / 2) :
    let s := fun x => δ + max (w x) 0
    let dg := fun (k : Fin n) x =>
      fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
        χ x * (r * s x ^ (r - 1)) * a k x
    Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable
          (fun x =>
            s x ^ (2 * r) *
              ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1))
            (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                (∫ x,
                  s x ^ (2 * r) *
                    ∑ k : Fin n,
                      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^
                        2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (4 * r ^ 2 * F / ((1 - 2 * r) * α)) *
                (∫ x,
                  χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  intro s dg
  classical
  have hp : 0 < 1 - 2 * r := by linarith
  have hc :=
    local_weak_supersolution_caccioppoli hw hbound hweak ha2 hAm hχ hχc hnonneg hα hβ hF hcoeff
      hsub hδ hp
  dsimp only at hc
  have he : 2 * r - 1 - 1 = 2 * r - 2 := by ring
  have hk : 1 - (1 - 2 * r) = 2 * r := by ring
  have hj : -(1 - 2 * r) = 2 * r - 1 := by ring
  simp only [hk, hj, he] at hc
  let E := fun x => χ x ^ 2 * s x ^ (2 * r - 2) * ∑ k : Fin n, (a k x) ^ 2
  let K := fun x =>
    s x ^ (2 * r) * ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
  let J := fun x => χ x ^ 2 * s x ^ (2 * r - 1)
  have hEi : Integrable E volume := hc.1
  have hKi : Integrable K volume := hc.2.1
  have hJi : Integrable J volume :=
    hc.2.2.1
  -- the linear energy variable `χ s^r` from the LOCAL cutoff power data

  have hd := local_rpow_cutoff_weak_data hw hbound hweak ha2 hχ hχc hnonneg hδ r
  dsimp only at hd
  have hdi : Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2) volume :=
    integrable_finsetSum Finset.univ fun k _ => ((hd.2.2.2.2.2 k).2.2.2).integrable_sq
  have hsq (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : (s x ^ t) ^ (2 : ℕ) = s x ^ (2 * t) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (by dsimp only [s]; positivity : 0 ≤ s x)]
    congr 1
    ring
  have hadd (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
    ∑ k : Fin n, (dg k x) ^ 2 ≤ 2 * K x + 2 * r ^ 2 * E x := by
    have hterm (k : Fin n) :
      (dg k x) ^ 2 ≤
        (2 * s x ^ (2 * r)) * (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 +
          (2 * r ^ 2 * χ x ^ 2 * s x ^ (2 * r - 2)) * (a k x) ^ 2 := by
      have h :=
        hadd (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r)
          (χ x * (r * s x ^ (r - 1)) * a k x)
      simp only [mul_pow, hsq] at h
      have hx : 2 * (r - 1) = 2 * r - 2 := by ring
      rw [hx] at h
      convert h using 1
      ring
    calc
      _ ≤
          ∑ k : Fin n,
            ((2 * s x ^ (2 * r)) * (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 +
              (2 * r ^ 2 * χ x ^ 2 * s x ^ (2 * r - 2)) * (a k x) ^ 2) :=
        Finset.sum_le_sum fun k _ => hterm k
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, K, E]; ring
  have hint :
    (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      2 * (∫ x, K x) + 2 * r ^ 2 * (∫ x, E x) := by
    calc
      _ ≤ ∫ x, (2 * K x + 2 * r ^ 2 * E x) :=
        integral_mono hdi ((hKi.const_mul 2).add (hEi.const_mul (2 * r ^ 2))) hpoint
      _ = _ := by
        rw [integral_add (hKi.const_mul 2) (hEi.const_mul (2 * r ^ 2)), integral_const_mul,
          integral_const_mul]
  refine ⟨hdi, hKi, hJi, ?_⟩
  calc
    _ ≤ 2 * (∫ x, K x) + 2 * r ^ 2 * (∫ x, E x) := hint
    _ ≤
        2 * (∫ x, K x) +
          2 * r ^ 2 *
            ((4 * β / ((1 - 2 * r) ^ 2 * α)) * (∫ x, K x) +
              (2 * F / ((1 - 2 * r) * α)) * (∫ x, J x)) := by
      gcongr
      exact hc.2.2.2
    _ = _ := by dsimp only [K, J]; ring

/--
**Power energy** for the energy variables `g = χ s^r`, `r < 1/2` (`p = 1 − 2r > 0`), with the exact
weak derivative
`dg`: `∫ Σ_k dg_k² ≤ (2 + 8r²β/(p²α)) ∫ s^{2r} Σ_k (∂_k χ)² + (4r²F/(pα)) ∫ χ² s^{2r−1}`, all
integrands integrable.
Every real `r < 1/2`, zero and negative included. An energy input, not the Moser iteration. -/
theorem bounded_weak_supersolution_power_energy {n : ℕ} {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C α β F δ r : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 :
      ∀ k : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x)
    (hAm :
      ∀ i j : Fin n,
        AEStronglyMeasurable (fun x => A x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hα : 0 < α) (hβ : 0 < β) (hF : 0 ≤ F)
    (hcoeff :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)),
        (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (hsub :
      ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
        LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
          (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) →
            HasCompactSupport η →
              Function.support η ⊆ tsupport χ →
                (∀ x, 0 ≤ η x) →
                  (∀ k : Fin n,
                      HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                        HasCompactSupport (dη k) ∧
                          Function.support (dη k) ⊆ tsupport χ ∧
                            MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
                    -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                      ∫ x,
                        dotProduct (fun k => a k x)
                          ((A x).mulVec
                            (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hδ : 0 < δ) (hr : r < 1 / 2) :
    let s := fun x => δ + max (w x) 0
    let dg := fun (k : Fin n) x =>
      fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
        χ x * (r * s x ^ (r - 1)) * a k x
    Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable
          (fun x =>
            s x ^ (2 * r) *
              ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1))
            (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          (∫ x, ∑ k : Fin n, (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                (∫ x,
                  s x ^ (2 * r) *
                    ∑ k : Fin n,
                      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^
                        2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
              (4 * r ^ 2 * F / ((1 - 2 * r) * α)) *
                (∫ x,
                  χ x ^ 2 * s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  exact
    local_weak_supersolution_power_energy hw hbound hweak ha2 hAm hχ hχc
      (ae_restrict_of_ae hnonneg) hα hβ hF hcoeff hsub hδ hr

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

section GivenDataCutoffPower
open MeasureTheory Matrix Set FunctionalInequalities.Analysis
open scoped ContDiff
/--
**Cutoff power data from the weak supersolution inequality on a set.** If `w` is globally bounded
with weak
derivatives in `L²_loc`, `w ≥ 0` and `α ≤ A ≤ β` a.e. on `S`, and the weak supersolution inequality
holds for every
bounded nonnegative test supported in `S`, then for every `C¹` cutoff with `tsupport χ ⊆ S` and `r <
1/2` the variable
`χ (δ + max w 0)^r` has exact weak data (derivatives supported in `tsupport χ`) and the power energy
bound of
Gilbarg–Trudinger (2001), (8.48)–(8.49). -/
theorem cutoff_power_data_of_weak_supersolution_on_set {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C α β F δ r : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 :
      ∀ k : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hAm :
      ∀ i j : Fin n,
        AEStronglyMeasurable (fun x => A x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {S : Set (EuclideanSpace ℝ (Fin n))} {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (hχS : tsupport χ ⊆ S)
    (hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)), 0 ≤ w x)
    (hα : 0 < α) (hβ : 0 < β) (hF : 0 ≤ F)
    (hcoeff :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)),
        (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (hsub :
      ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
        LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) →
          (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖η x‖ ≤ B) →
            HasCompactSupport η →
              Function.support η ⊆ S →
                (∀ x, 0 ≤ η x) →
                  (∀ k : Fin n,
                      HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                        HasCompactSupport (dη k) ∧
                          Function.support (dη k) ⊆ S ∧
                            MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
                    -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                      ∫ x,
                        dotProduct (fun k => a k x)
                          ((A x).mulVec
                            (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hδ : 0 < δ) (hr : r < 1 / 2) :
    let s := fun x => δ + max (w x) 0
    let g := fun x => χ x * s x ^ r
    let dg := fun (k : Fin n) x =>
      fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * s x ^ r +
        χ x * (r * s x ^ (r - 1)) * a k x
    LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport g ∧
        (∃ Cg : ℝ, ∀ x, ‖g x‖ ≤ Cg) ∧
          (∀ k : Fin n,
              HasWeakDerivAlong g (dg k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
                HasCompactSupport (dg k) ∧
                  Function.support (dg k) ⊆ tsupport χ ∧
                    MemLp (dg k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
            Integrable (fun x => ∑ k : Fin n, (dg k x) ^ 2)
                (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
              Integrable
                  (fun x =>
                    s x ^ (2 * r) *
                      ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
                  (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
                Integrable (fun x => χ x ^ 2 * s x ^ (2 * r - 1))
                    (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
                  (∫ x,
                      ∑ k : Fin n,
                        (dg k x) ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
                    (2 + 8 * r ^ 2 * β / ((1 - 2 * r) ^ 2 * α)) *
                        (∫ x,
                          s x ^ (2 * r) *
                            ∑ k : Fin n,
                              (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^
                                2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
                      (4 * r ^ 2 * F / ((1 - 2 * r) * α)) *
                        (∫ x,
                          χ x ^ 2 *
                            s x ^ (2 * r - 1) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  intro s g dg
  have hwχ := ae_restrict_of_ae_restrict_of_subset hχS hnonneg
  have hcoeffχ := ae_restrict_of_ae_restrict_of_subset hχS hcoeff
  obtain ⟨hl, hc, -, ⟨Cg, -, hCg⟩, -, hd⟩ :=
    local_rpow_cutoff_weak_data hw hbound hweak ha2 hχ hχc hwχ hδ r
  refine ⟨hl, hc, ⟨Cg, hCg⟩, hd, ?_⟩
  refine
    local_weak_supersolution_power_energy hw hbound hweak ha2 hAm hχ hχc hwχ hα hβ hF hcoeffχ ?_
      hδ hr
  intro η dη hηl hηb hηc hηs hηn hdη
  exact
    hsub η dη hηl hηb hηc (hηs.trans hχS) hηn
      (fun k => ⟨(hdη k).1, (hdη k).2.1, (hdη k).2.2.1.trans hχS, (hdη k).2.2.2⟩)
end GivenDataCutoffPower

section GivenDataLogEnergy
open MeasureTheory Matrix Set FunctionalInequalities.Analysis
open scoped ContDiff
/-- **Weak logarithm with energy on a set.** Under the hypotheses of
`cutoff_power_data_of_weak_supersolution_on_set`
there is ONE globally bounded weak `H` with derivatives in `L²_loc`, equal a.e. on `S` to `log (δ +
max w 0)` with
derivative `(δ + max w 0)⁻¹ a`, and with the logarithmic energy bound of Gilbarg–Trudinger (2001),
(8.49), for every
cutoff in `S`. No weak derivative of `log (δ + max w 0)` off `S` is claimed. -/
theorem exists_weak_log_extension_with_energy_on_set {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {C α β F δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hAm : ∀ i j : Fin n, AEStronglyMeasurable (fun x => A x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S)
    (hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)), 0 ≤ w x)
    (hα : 0 < α) (hβ : 0 < β) (hF : 0 ≤ F)
    (hcoeff : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S)),
      (A x - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A x).PosSemidef)
    (hsub : ∀ (η : EuclideanSpace ℝ (Fin n) → ℝ)
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
    (hδ : 0 < δ) :
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
      ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ → tsupport χ ⊆ S →
    Integrable (fun x => χ x ^ 2 * ∑ k : Fin n, (dH k x) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => ∑ k : Fin n,
      (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => χ x ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, χ x ^ 2 * ∑ k : Fin n, (dH k x) ^ 2
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      (4 * β / α) *
        (∫ x, ∑ k : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
      (2 * F / (α * δ)) * (∫ x, χ x ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    obtain ⟨H, dH, hl, hb, hd, hEq⟩ :=
      exists_bounded_weak_log_extension hw hbound hweak ha2 hδ
    obtain ⟨hHe, hde⟩ := hEq S hSm hnonneg
    refine ⟨H, dH, hl, hb, hd, hHe, hde, fun χ hχ hχc hχS => ?_⟩
    have hwχ := ae_restrict_of_ae_restrict_of_subset hχS hnonneg
    have hcoeffχ := ae_restrict_of_ae_restrict_of_subset hχS hcoeff
    have hc :=
      local_weak_supersolution_log_energy hw hbound hweak ha2 hAm hχ hχc hwχ hα hβ hF
        hcoeffχ
        (fun η dη hηl hηb hηc hηs hηn hdη =>
          hsub η dη hηl hηb hηc (hηs.trans hχS) hηn
            (fun k => ⟨(hdη k).1, (hdη k).2.1, (hdη k).2.2.1.trans hχS, (hdη k).2.2.2⟩))
        hδ
    dsimp only at hc
    have he :
      (fun x =>
          χ x ^ 2 *
            ∑ k : Fin n, (dH k x) ^ 2) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
        (fun x => χ x ^ 2 * ∑ k : Fin n, ((δ + max (w x) 0)⁻¹ * a k x) ^ 2) := by
      have hda := (ae_restrict_iff' hSm).mp (ae_all_iff.mpr hde)
      filter_upwards [hda] with x hx
      by_cases hxs : x ∈ S
      · simp only [hx hxs]
      · have hχ0 : χ x = 0 := by
          by_contra h
          exact hxs (hχS (subset_tsupport χ h))
        simp only [hχ0, zero_pow (by decide : 2 ≠ 0), zero_mul]
    refine ⟨hc.1.congr he.symm, hc.2.1, hc.2.2.1, ?_⟩
    rw [integral_congr_ae he]
    exact hc.2.2.2
end GivenDataLogEnergy

end FunctionalInequalities.Analysis
