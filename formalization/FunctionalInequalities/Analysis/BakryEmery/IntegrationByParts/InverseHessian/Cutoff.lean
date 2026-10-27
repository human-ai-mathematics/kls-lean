import FunctionalInequalities.Analysis.Cutoff.Profile
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
import FunctionalInequalities.Analysis.Convex.Coercivity

/-!
# Letwin Lemma A.4: the cutoff family (source construction)

Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17), for a given potential in the source class: smooth convex `φ` with gradient
image in a bounded `K`, `V` smooth on an open `U ⊇ closure K`, the pointwise Monge–Ampère equation, positive definite
Hessian and `∫ e^{−φ} dm = 1`, in any finite dimension and for any additive Haar measure `m`.
`exists_scaled_cutoffs_hessianInverseOperator` constructs, for every real `R ≥ 1`, `χ_R = η((φ − c)/R)` with
`c = min φ − 1` and `η = smoothTransition (2 − ·)`: smooth, compactly supported, `[0,1]`-valued, monotone in `R` on
`[1, ∞)`, tending to `1`, with `Lχ_R ∈ L¹(ν)` and one constructed `C ≥ 0` such that `∫ |Lχ_R| dν ≤ C/R`, so the defect
tends to `0`. The minimum of `φ` and its compact sublevel sets (from convexity and the normalization), the
self-generator bound, the profile bounds, the weighted energy estimate and the integrability of `Lχ_R` are derived in
the proof, never assumed. The natural-index corollary `exists_cutoffs_hessianInverseOperator` takes `χ_n = χ_{n+1}`, with
the same `C` and the bound `C/(n+1)`; its conclusions are the cutoff premises of Lemma A.5
(`integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs`). The moment map itself is not constructed: the
source-class properties are hypotheses.

Private local supports: compact support through a compact sublevel set, the shifted tail primitive, the source-form
pointwise defect bound and one scalar monotonicity step. Proof bodies: the fixed source construction (Codex) with the
independently verified Codex API helper and unit proofs (`letwin-a4-support-compact/shifted/defect-astra-v1`,
`letwin-a4-support-add-monotonicity-astra-v1` after scalar `add_comm` normalization) and, for the natural-index
corollary, the independently verified Codex API proof (`letwin-a4-natural-from-actual-astra-v1`), verbatim; placement:
Claude.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis.BakryEmery

private theorem abs_hessianInverseOperator_profile_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {φ V : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    {B D : ℝ} {w : ℝ → ℝ} (hB : ∀ t, |deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t| ≤ B)
    (hw : ∀ t, |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ w t)
    (hD : ∀ x, |hessianInverseOperator φ V φ x| ≤ D) (c : ℝ) {R : ℝ} (hR : 0 < R) (x : E) :
    |hessianInverseOperator φ V (fun y => Real.smoothTransition (2 - (φ y - c) / R)) x| ≤
      R⁻¹ * B * D + (R ^ 2)⁻¹ * w ((φ x - c) / R) *
        ∑ i, ∑ j, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
          fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) * fderiv ℝ φ x (stdOrthonormalBasis ℝ E j) := by
    have hη : ContDiff ℝ 2 (fun s : ℝ => Real.smoothTransition (2 - s)) :=
      FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff.1.of_le
        (WithTop.coe_le_coe.mpr le_top)
    have hΓ :
        0 ≤ ∑ i, ∑ j, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
          fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ φ x (stdOrthonormalBasis ℝ E j) :=
      sum_inverseHessianEntry_mul_mul_nonneg (stdOrthonormalBasis ℝ E)
        hφ x (hPD x) (fun i => fderiv ℝ φ x (stdOrthonormalBasis ℝ E i))
    have hRi : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ((φ x - c) / R))
    have hfirst :
        |R⁻¹ * deriv (fun s : ℝ => Real.smoothTransition (2 - s))
            ((φ x - c) / R)| ≤ R⁻¹ * B := by
      rw [abs_mul, abs_of_nonneg hRi]
      exact mul_le_mul_of_nonneg_left (hB _) hRi
    have hbound := abs_hessianInverseOperator_comp_sub_div_le
      (V := V) hφ hη c R x
    rw [abs_of_nonneg hΓ] at hbound
    apply hbound.trans
    apply add_le_add
    · exact mul_le_mul hfirst (hD x) (abs_nonneg _)
        (mul_nonneg hRi hB0)
    · have hsecond :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hw ((φ x - c) / R))
            (sq_nonneg R⁻¹)) hΓ
      simpa only [inv_pow] using hsecond

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis.BakryEmery

private theorem add_const_left_le_of_le (A a b : ℝ) (hab : a ≤ b) : A + a ≤ A + b := by
  simpa only [add_comm] using add_le_add_left hab A

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Letwin Lemma A.4, real parameter** (p. 17). For a potential in the source class there are cutoffs `χ R` and one
constant `C ≥ 0` such that, for every real `R ≥ 1`, `χ R` is smooth, compactly supported and `[0,1]`-valued, `R ↦ χ R x`
is monotone on `[1, ∞)` with limit `1`, `L (χ R)` is integrable for `ν = m.tilted (−φ)` and `∫ |L (χ R)| dν ≤ C / R`;
in particular the defect tends to `0`. -/
theorem exists_scaled_cutoffs_hessianInverseOperator (m : Measure E) [m.IsAddHaarMeasure] {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hconv : ConvexOn ℝ Set.univ φ)
    {K U : Set E} (hK : Bornology.IsBounded K) (hRange : Set.range (gradient φ) ⊆ K)
    (hU : IsOpen U) (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    ∃ (chi : ℝ → E → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ ∞ (chi R)) ∧ (∀ R : ℝ, 1 ≤ R → HasCompactSupport (chi R)) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ x, 0 ≤ chi R x ∧ chi R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => chi R x) (Set.Ici 1)) ∧
      (∀ x, Filter.Tendsto (fun R => chi R x) Filter.atTop (nhds 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (hessianInverseOperator φ V (chi R)) (m.tilted (-φ))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |hessianInverseOperator φ V (chi R) x| ∂(m.tilted (-φ))) ≤ C / R) ∧
      Filter.Tendsto (fun R => ∫ x, |hessianInverseOperator φ V (chi R) x| ∂(m.tilted (-φ)))
        Filter.atTop (nhds 0) := by
    have hφ2 : ContDiff ℝ 2 φ :=
      hφ.of_le (WithTop.coe_le_coe.mpr le_top)
    have hV1 : ContDiffOn ℝ 1 V U :=
      hV.of_le (WithTop.coe_le_coe.mpr le_top)
    have hRangeU : Set.range (gradient φ) ⊆ U :=
      fun x hx => hKU (subset_closure (hRange hx))
    let : IsProbabilityMeasure (m.tilted (-φ)) :=
      isProbabilityMeasure_tilted_neg_of_integral_eq_one m φ hnorm
    obtain ⟨⟨y₀, hy₀⟩, hsub⟩ :=
      exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
        m hconv (integrable_exp_neg_of_integral_eq_one m φ hnorm)
    let c : ℝ := φ y₀ - 1
    have hshift : ∀ x, 1 ≤ φ x - c := by
      intro x
      dsimp [c]
      linarith [hy₀ x]
    obtain ⟨D, hD0, hDbound⟩ :=
      bounded_hessianInverseOperator_self hφ2 hPD hK hRange hU hKU hV1
    obtain ⟨hη, hηanti, hηbounds, hηone, hηzero, hηderiv,
        hηsupp, hηsupp₂, B, hB0, hB⟩ :=
      smoothTransition_two_sub_cutoff
    obtain ⟨w, hw, hwsupp, hw0, hws, hwmajor⟩ :=
      exists_majorant_abs_deriv_deriv_smoothTransition_two_sub
    let Wint : ℝ := ∫ t in (0 : ℝ)..3, w t
    have hW0 : 0 ≤ Wint := by
      simpa [Wint] using
        (inv_mul_intervalIntegral_div_three_cutoff hw hw0 hws
          (R := 1) (by norm_num)).2.2.1 0
    let C : ℝ := B * D + D * Wint
    have hC : 0 ≤ C :=
      add_nonneg (mul_nonneg hB0 hD0) (mul_nonneg hD0 hW0)
    let chi : ℝ → E → ℝ :=
      fun R x => Real.smoothTransition (2 - (φ x - c) / R)
    have hchiSmooth (R : ℝ) : ContDiff ℝ ∞ (chi R) :=
      hη.comp ((hφ.sub contDiff_const).div_const R)
    have hchiSupport (R : ℝ) (hR : 1 ≤ R) :
        HasCompactSupport (chi R) := by
      have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
      change HasCompactSupport
        (fun x => Real.smoothTransition (2 - (φ x - c) / R))
      apply hasCompactSupport_comp_of_isCompact_sublevel
        (g := fun s : ℝ => Real.smoothTransition (2 - (s - c) / R))
        hφ.continuous (hsub (c + 2 * R))
      intro s hs
      apply hηzero
      apply (le_div_iff₀ hRp).2
      linarith
    let Γ : E → ℝ := fun x =>
      ∑ i, ∑ j, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
        fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
        fderiv ℝ φ x (stdOrthonormalBasis ℝ E j)
    have hest : ∀ R : ℝ, 1 ≤ R →
        Integrable (hessianInverseOperator φ V (chi R)) (m.tilted (-φ)) ∧
          (∫ x, |hessianInverseOperator φ V (chi R) x| ∂(m.tilted (-φ))) ≤
            C / R := by
      intro R hR
      have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
      let h : ℝ → ℝ := fun s =>
        R⁻¹ * ∫ t in (s - c) / R..3, w t
      obtain ⟨hh, hhd, hhbound, hhzero⟩ :=
        shifted_inv_mul_intervalIntegral_div_three_cutoff hw hw0 hws hRp c
      have hhsupp : HasCompactSupport (fun x => h (φ x)) :=
        hasCompactSupport_comp_of_isCompact_sublevel
          hφ.continuous (hsub (c + 3 * R)) hhzero
      obtain ⟨heint, heineq⟩ :=
        integrable_and_neg_integral_deriv_comp_mul_le
          m hφ hh hhsupp hU hV hRangeU hMA hPD hnorm hDbound hhbound
      let e : E → ℝ := fun x => -(deriv h (φ x) * Γ x)
      have hei : Integrable e (m.tilted (-φ)) := heint.neg
      have heI : (∫ x, e x ∂(m.tilted (-φ))) ≤ D * (R⁻¹ * Wint) := by
        calc
          (∫ x, e x ∂(m.tilted (-φ))) =
              -(∫ x, deriv h (φ x) * Γ x ∂(m.tilted (-φ))) :=
            integral_neg _
          _ ≤ D * (R⁻¹ * Wint) := heineq
      have heeq (x : E) :
          e x = (R ^ 2)⁻¹ * w ((φ x - c) / R) * Γ x := by
        change -(deriv h (φ x) * Γ x) = _
        rw [show deriv h (φ x) =
          -((R ^ 2)⁻¹ * w ((φ x - c) / R)) from hhd (φ x)]
        ring
      have hpoint (x : E) :
          |hessianInverseOperator φ V (chi R) x| ≤ R⁻¹ * B * D + e x := by
        rw [heeq]
        exact abs_hessianInverseOperator_profile_le
          hφ2 hPD (fun t => (hB t).1) hwmajor hDbound c hRp x
      have hg : Integrable (fun x => R⁻¹ * B * D + e x) (m.tilted (-φ)) :=
        (integrable_const _).add hei
      have hcont : Continuous (hessianInverseOperator φ V (chi R)) :=
        continuous_hessianInverseOperator hφ hPD hU hV1 hRangeU
          ((hchiSmooth R).of_le (WithTop.coe_le_coe.mpr le_top))
      have hLi : Integrable (hessianInverseOperator φ V (chi R))
          (m.tilted (-φ)) := by
        apply hg.mono' hcont.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using hpoint x
      refine ⟨hLi, ?_⟩
      calc
        (∫ x, |hessianInverseOperator φ V (chi R) x| ∂(m.tilted (-φ))) ≤
            ∫ x, R⁻¹ * B * D + e x ∂(m.tilted (-φ)) :=
          integral_mono hLi.abs hg hpoint
        _ = R⁻¹ * B * D + ∫ x, e x ∂(m.tilted (-φ)) := by
          rw [integral_add (integrable_const _) hei]
          simp only [integral_const, probReal_univ, one_smul]
        _ ≤ R⁻¹ * B * D + D * (R⁻¹ * Wint) :=
          add_const_left_le_of_le _ _ _ heI
        _ = C / R := by
          dsimp [C]
          rw [div_eq_mul_inv]
          ring
    refine ⟨chi, C, hC, (fun R _ => hchiSmooth R), hchiSupport,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro R hR x
      exact hηbounds ((φ x - c) / R)
    · intro x
      exact (monotoneOn_and_tendsto_smoothTransition_two_sub_div (φ x - c)).1.mono
        (fun R hR => show (0 : ℝ) < R from lt_of_lt_of_le zero_lt_one hR)
    · intro x
      exact (monotoneOn_and_tendsto_smoothTransition_two_sub_div (φ x - c)).2
    · intro R hR
      exact (hest R hR).1
    · intro R hR
      exact (hest R hR).2
    · have hlim : Filter.Tendsto (fun R : ℝ => C / R)
          Filter.atTop (nhds 0) := by
        simpa only [div_eq_mul_inv, mul_zero] using
          (tendsto_inv_atTop_zero :
            Filter.Tendsto (fun R : ℝ => R⁻¹) Filter.atTop (nhds 0)).const_mul C
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hlim
      · exact Filter.Eventually.of_forall fun R =>
          integral_nonneg (fun x => abs_nonneg _)
      · exact Filter.eventually_atTop.mpr ⟨1, fun R hR => (hest R hR).2⟩

/-- **Letwin Lemma A.4, natural index**: under the same hypotheses, cutoffs `χ n` indexed by `ℕ` (`χ n = χ_{n+1}` of
`exists_scaled_cutoffs_hessianInverseOperator`) that are smooth, compactly supported, `[0,1]`-valued, monotone in `n`
with limit `1`, with `L (χ n)` integrable, `∫ |L (χ n)| dν ≤ C / (n + 1)` and defect tending to `0`. These are the
cutoff premises of `integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs`. -/
theorem exists_cutoffs_hessianInverseOperator (m : Measure E) [m.IsAddHaarMeasure] {φ V : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hconv : ConvexOn ℝ Set.univ φ)
    {K U : Set E} (hK : Bornology.IsBounded K) (hRange : Set.range (gradient φ) ⊆ K)
    (hU : IsOpen U) (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    ∃ (chi : ℕ → E → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ n, ContDiff ℝ ∞ (chi n)) ∧ (∀ n, HasCompactSupport (chi n)) ∧
      (∀ n x, 0 ≤ chi n x ∧ chi n x ≤ 1) ∧
      (∀ x, Monotone (fun n => chi n x)) ∧
      (∀ x, Filter.Tendsto (fun n => chi n x) Filter.atTop (nhds 1)) ∧
      (∀ n, Integrable (hessianInverseOperator φ V (chi n)) (m.tilted (-φ))) ∧
      (∀ n, (∫ x, |hessianInverseOperator φ V (chi n) x| ∂(m.tilted (-φ))) ≤
        C / ((n : ℝ) + 1)) ∧
      Filter.Tendsto (fun n => ∫ x, |hessianInverseOperator φ V (chi n) x| ∂(m.tilted (-φ)))
        Filter.atTop (nhds 0) := by
  obtain ⟨chi, C, hC, hs, hcs, hb, hmono, hlim, hint, hbd, hdec⟩ :=
    exists_scaled_cutoffs_hessianInverseOperator m hφ hconv hK hRange hU hKU
      hV hMA hPD hnorm
  have h1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := by
    intro n
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hT : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  refine ⟨fun n => chi ((n : ℝ) + 1), C, hC,
    fun n => hs _ (h1 n),
    fun n => hcs _ (h1 n),
    fun n => hb _ (h1 n),
    ?_, fun x => (hlim x).comp hT,
    fun n => hint _ (h1 n),
    fun n => hbd _ (h1 n),
    hdec.comp hT⟩
  intro x a b hab
  apply hmono x (Set.mem_Ici.mpr (h1 a)) (Set.mem_Ici.mpr (h1 b))
  have hab' : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
  linarith

end FunctionalInequalities.Analysis.BakryEmery
