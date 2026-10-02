import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Quantiles and the Paley–Zygmund inequality

E. Milman, *On the role of convexity in isoperimetry, spectral gap and concentration*
(arXiv:0712.4092v5), §4: for a Borel function `f` on a probability space and `δ ∈ [0, 1]`,
`Q_δ(f) = inf {q ∈ ℝ : μ{f ≤ q} ≥ δ}`, and Lemma 4.1 (Paley–Zygmund): if
`‖f‖₂ ≤ D ‖f‖₁ < ∞` then `Q_{1-ε}(|f|) ≥ θ ‖f‖₁` for `θ ∈ (0, 1)` and `ε = (1 - θ)² / D²`.

`lowerQuantile` uses the real `sInf`, so an empty or unbounded-below set has quantile `0`. The
paper's quantile is `-∞` in the degenerate case `f = 0` with `1 - ε < 0`, where its literal
inequality fails; the real convention gives `0`, and the Lean statement keeps the paper's
hypotheses unchanged.
-/

open MeasureTheory

namespace FunctionalInequalities.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `δ`-quantile `Q_δ(g) = inf {q : δ ≤ μ{g ≤ q}}` of E. Milman (2009), §4. -/
noncomputable def lowerQuantile (μ : Measure Ω) (g : Ω → ℝ) (δ : ℝ) : ℝ :=
  sInf {q : ℝ | ENNReal.ofReal δ ≤ μ {x | g x ≤ q}}

/-- A lower bound for the quantile: if every level below `a` has sub-level mass below `δ < 1`,
then `a ≤ Q_δ(g)`. -/
theorem le_lowerQuantile (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ} {δ a : ℝ}
    (hδ : δ < 1) (h : ∀ q < a, μ {x | g x ≤ q} < ENNReal.ofReal δ) :
    a ≤ lowerQuantile μ g δ := by
  let s : ℕ → Set Ω := fun n => {x | g x ≤ (n : ℝ)}
  let S : Set ℝ := {q : ℝ | ENNReal.ofReal δ ≤ μ {x | g x ≤ q}}

  have hsmono : Monotone s := by
    intro m n hmn x hxm
    change g x ≤ (m : ℝ) at hxm
    change g x ≤ (n : ℝ)
    exact hxm.trans (by exact_mod_cast hmn)

  have hunion : (⋃ n : ℕ, s n) = Set.univ := by
    ext x
    simp only [s, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge (g x)
    exact ⟨n, hn⟩

  have ht :
      Filter.Tendsto (fun n : ℕ => μ (s n)) Filter.atTop
        (nhds (μ Set.univ)) := by
    rw [← hunion]
    exact MeasureTheory.tendsto_measure_iUnion_atTop hsmono

  have hδlt : ENNReal.ofReal δ < 1 :=
    ENNReal.ofReal_lt_one.mpr hδ

  have hlim : ENNReal.ofReal δ < μ Set.univ := by
    rw [measure_univ]
    exact hδlt

  have hev :
      ∀ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal δ < μ (s n) :=
    (tendsto_order.1 ht).1 _ hlim

  have hS : S.Nonempty := by
    rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
    refine ⟨(N : ℝ), ?_⟩
    change ENNReal.ofReal δ ≤ μ (s N)
    exact (hN N le_rfl).le

  have hbound : ∀ b ∈ S, a ≤ b := by
    intro b hb
    change ENNReal.ofReal δ ≤ μ {x | g x ≤ b} at hb
    by_contra hba
    have hlt : b < a := lt_of_not_ge hba
    exact (not_lt_of_ge hb) (h b hlt)

  change a ≤ sInf S
  exact le_csInf hS hbound

/-- Cauchy–Schwarz on a set: `(∫_A g)² ≤ (∫ g²) · μ(A)`. -/
theorem sq_setIntegral_le (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : MemLp g 2 μ) (A : Set Ω) :
    (∫ x in A, g x ∂μ) ^ 2 ≤ (∫ x, g x ^ 2 ∂μ) * μ.real A := by
  let ν : Measure Ω := μ.restrict A

  have hgν : MemLp g 2 ν := by
    simpa [ν] using hg.restrict A

  have hngν : MemLp (fun x => ‖g x‖) 2 ν := hgν.norm

  have honeν : MemLp (fun _ : Ω => (1 : ℝ)) 2 ν := by
    apply memLp_const

  have hngν' :
      MemLp (fun x => ‖g x‖) (ENNReal.ofReal (2 : ℝ)) ν := by
    norm_num
    exact hngν

  have honeν' :
      MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) ν := by
    norm_num
    exact honeν

  have hcs :
      ∫ x, ‖g x‖ * (1 : ℝ) ∂ν ≤
        (∫ x, ‖g x‖ ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2) *
          (∫ x, (1 : ℝ) ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2) := by
    exact integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := ν) (p := (2 : ℝ)) (q := (2 : ℝ))
      Real.HolderConjugate.two_two
      (ae_of_all ν fun x => norm_nonneg (g x))
      (ae_of_all ν fun _ => zero_le_one)
      hngν' honeν'

  have hcs₁ :
      ∫ x, ‖g x‖ ∂ν ≤
        (∫ x, ‖g x‖ ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2) *
          (ν.real Set.univ) ^ ((1 : ℝ) / 2) := by
    simpa [MeasureTheory.integral_const, smul_eq_mul] using hcs

  let X : ℝ :=
    (∫ x, ‖g x‖ ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2)
  let Y : ℝ := (ν.real Set.univ) ^ ((1 : ℝ) / 2)
  let M : ℝ := ∫ x, ‖g x‖ ∂ν

  have hMY : M ≤ X * Y := by
    simpa [X, Y, M] using hcs₁

  have hsqXY : M ^ 2 ≤ (X * Y) ^ 2 := by
    have h₁ : 0 ≤ X * Y - M := sub_nonneg.mpr hMY
    have h₂ : 0 ≤ X * Y + M := by
      dsimp [X, Y, M]
      positivity
    have h₃ : 0 ≤ (X * Y - M) * (X * Y + M) :=
      mul_nonneg h₁ h₂
    nlinarith

  have hsqX :
      X ^ 2 = ∫ x, ‖g x‖ ^ (2 : ℝ) ∂ν := by
    dsimp [X]
    have hnonneg :
        0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) ∂ν :=
      integral_nonneg fun x => by positivity
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hnonneg

  have hsqY :
      Y ^ 2 = ν.real Set.univ := by
    dsimp [Y]
    have hnonneg : 0 ≤ ν.real Set.univ :=
      measureReal_nonneg
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hnonneg

  have hsqν :
      (∫ x, ‖g x‖ ∂ν) ^ 2 ≤
        (∫ x, ‖g x‖ ^ (2 : ℝ) ∂ν) * ν.real Set.univ := by
    calc
      (∫ x, ‖g x‖ ∂ν) ^ 2 = M ^ 2 := by rfl
      _ ≤ (X * Y) ^ 2 := hsqXY
      _ = X ^ 2 * Y ^ 2 := by ring
      _ = (∫ x, ‖g x‖ ^ (2 : ℝ) ∂ν) * ν.real Set.univ := by
        rw [hsqX, hsqY]

  have hsqA :
      (∫ x in A, ‖g x‖ ∂μ) ^ 2 ≤
        (∫ x in A, g x ^ 2 ∂μ) * μ.real A := by
    simpa [ν, Real.norm_eq_abs, sq_abs] using hsqν

  have hnorm :
      |∫ x in A, g x ∂μ| ≤ ∫ x in A, ‖g x‖ ∂μ := by
    exact norm_integral_le_integral_norm g

  have habs_sq :
      |∫ x in A, g x ∂μ| ^ 2 ≤
        (∫ x in A, ‖g x‖ ∂μ) ^ 2 := by
    have hdiff :
        0 ≤ ∫ x in A, ‖g x‖ ∂μ - |∫ x in A, g x ∂μ| :=
      sub_nonneg.mpr hnorm
    have hsum :
        0 ≤ ∫ x in A, ‖g x‖ ∂μ + |∫ x in A, g x ∂μ| := by
      positivity
    have hprod :
        0 ≤
          (∫ x in A, ‖g x‖ ∂μ - |∫ x in A, g x ∂μ|) *
            (∫ x in A, ‖g x‖ ∂μ + |∫ x in A, g x ∂μ|) :=
      mul_nonneg hdiff hsum
    nlinarith

  have hset :
      (∫ x in A, g x ^ 2 ∂μ) ≤ ∫ x, g x ^ 2 ∂μ := by
    exact setIntegral_le_integral hg.integrable_sq
      (ae_of_all μ fun x => sq_nonneg (g x))

  have hset_mul :
      (∫ x in A, g x ^ 2 ∂μ) * μ.real A ≤
        (∫ x, g x ^ 2 ∂μ) * μ.real A :=
    mul_le_mul_of_nonneg_right hset measureReal_nonneg

  have hfinal :
      |∫ x in A, g x ∂μ| ^ 2 ≤
        (∫ x, g x ^ 2 ∂μ) * μ.real A :=
    habs_sq.trans (hsqA.trans hset_mul)

  simpa [sq_abs] using hfinal

/-- Strict Paley–Zygmund inequality: for a nonnegative measurable square-integrable `g` with
positive mean and `θ ∈ (0, 1)`, `(1 - θ)² (∫ g)² < (∫ g²) · μ{g > θ ∫ g}`. -/
theorem sq_mul_sq_integral_lt (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg : MemLp g 2 μ) (hpos : 0 < ∫ x, g x ∂μ) {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    (1 - θ) ^ 2 * (∫ x, g x ∂μ) ^ 2 <
      (∫ x, g x ^ 2 ∂μ) * μ.real {x | θ * ∫ y, g y ∂μ < g x} := by
  let E : ℝ := ∫ x, g x ∂μ
  let A : Set Ω := {x | θ * E < g x}

  have hEpos : 0 < E := by
    simpa [E] using hpos

  have hgi : Integrable g μ := hg.integrable (by norm_num)

  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt measurable_const hgm

  have hB : MeasurableSet Aᶜ := hA.compl

  have hcomp : μ.real Aᶜ = 1 - μ.real A := by
    rw [measureReal_compl hA]
    simp

  have hIB :
      (∫ x in Aᶜ, g x ∂μ) ≤ θ * E * μ.real Aᶜ := by
    calc
      (∫ x in Aᶜ, g x ∂μ) ≤
          ∫ x in Aᶜ, (θ * E : ℝ) ∂μ := by
        apply setIntegral_mono_on hgi.integrableOn integrableOn_const hB
        intro x hx
        have hx' : ¬θ * E < g x := by
          simpa [A] using hx
        exact le_of_not_gt hx'
      _ = θ * E * μ.real Aᶜ := by
        rw [setIntegral_const]
        simp [smul_eq_mul, mul_comm, mul_assoc]

  have hdecomp :
      (∫ x in A, g x ∂μ) + (∫ x in Aᶜ, g x ∂μ) = E := by
    simpa [E] using integral_add_compl hA hgi

  have hIA :
      (1 - θ) * E + θ * E * μ.real A ≤ ∫ x in A, g x ∂μ := by
    rw [hcomp] at hIB
    linarith

  have hsq :
      (∫ x in A, g x ∂μ) ^ 2 ≤
        (∫ x, g x ^ 2 ∂μ) * μ.real A := by
    exact sq_setIntegral_le μ hg A

  have hApos : 0 < μ.real A := by
    by_contra hA'
    have hAzero : μ.real A = 0 := by
      exact le_antisymm (le_of_not_gt hA') measureReal_nonneg

    have hIAzero : ∫ x in A, g x ∂μ = 0 := by
      have hsq' : (∫ x in A, g x ∂μ) ^ 2 ≤ 0 := by
        simpa [hAzero] using hsq
      have hnonneg : 0 ≤ ∫ x in A, g x ∂μ := by
        exact integral_nonneg fun x => hg0 x
      nlinarith

    have hbasepos : 0 < (1 - θ) * E := by
      exact mul_pos (sub_pos.mpr hθ1) hEpos

    rw [hAzero, hIAzero] at hIA
    linarith

  have hbasepos : 0 < (1 - θ) * E := by
    exact mul_pos (sub_pos.mpr hθ1) hEpos

  have hIAstrict :
      (1 - θ) * E < ∫ x in A, g x ∂μ := by
    have hterm : 0 < θ * E * μ.real A := by
      exact mul_pos (mul_pos hθ hEpos) hApos
    linarith

  have hsquares :
      ((1 - θ) * E) ^ 2 < (∫ x in A, g x ∂μ) ^ 2 := by
    nlinarith

  calc
    (1 - θ) ^ 2 * (∫ x, g x ∂μ) ^ 2 = ((1 - θ) * E) ^ 2 := by
      simp [E]
      ring
    _ < (∫ x in A, g x ∂μ) ^ 2 := hsquares
    _ ≤ (∫ x, g x ^ 2 ∂μ) * μ.real A := hsq
    _ = (∫ x, g x ^ 2 ∂μ) *
        μ.real {x | θ * ∫ y, g y ∂μ < g x} := by
      simp [A, E]

/-- The quantile of a nonnegative function is nonnegative (with the real `sInf` convention). -/
theorem lowerQuantile_nonneg (μ : Measure Ω) [IsFiniteMeasure μ] {g : Ω → ℝ}
    (hg0 : ∀ x, 0 ≤ g x) (δ : ℝ) :
    0 ≤ lowerQuantile μ g δ := by
  let S : Set ℝ := {q : ℝ | ENNReal.ofReal δ ≤ μ {x | g x ≤ q}}
  change 0 ≤ sInf S

  by_cases hδ : δ ≤ 0
  · have hS : S = Set.univ := by
      ext q
      simp [S, ENNReal.ofReal_of_nonpos hδ]

    have hnb : ¬BddBelow S := by
      rw [hS]
      intro hb
      rcases hb with ⟨a, ha⟩
      have ha' : a ≤ a - 1 := by
        apply ha
        simp
      linarith

    rw [Real.sInf_of_not_bddBelow hnb]

  · have hδpos : 0 < δ := lt_of_not_ge hδ
    have hOR : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδpos

    by_cases hbound : BddBelow S
    · by_cases hnonempty : S.Nonempty
      · have hzero : ∀ q ∈ S, 0 ≤ q := by
          intro q hq
          by_contra hqneg
          have hq_lt : q < 0 := lt_of_not_ge hqneg

          have hempty : {x : Ω | g x ≤ q} = ∅ := by
            ext x
            constructor
            · intro hx
              change g x ≤ q at hx
              linarith [hg0 x]
            · intro hx
              exact False.elim (by simp at hx)

          have hq' : ENNReal.ofReal δ ≤ 0 := by
            change ENNReal.ofReal δ ≤ μ {x : Ω | g x ≤ q} at hq
            rw [hempty] at hq
            simpa using hq

          exact (not_lt_of_ge hq') hOR

        exact le_csInf hnonempty hzero
      · have hSempty : S = ∅ := by
          ext q
          constructor
          · intro hq
            exact (hnonempty ⟨q, hq⟩).elim
          · intro hq
            simp at hq

        rw [hSempty, Real.sInf_empty]
    · rw [Real.sInf_of_not_bddBelow hbound]

/-- `‖f‖₁ = ∫ |f|` for a measurable real function. -/
theorem toReal_eLpNorm_one_eq_integral_abs (μ : Measure Ω) {f : Ω → ℝ} (hf : Measurable f) :
    (eLpNorm f 1 μ).toReal = ∫ x, |f x| ∂μ := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  symm
  simpa [Real.norm_eq_abs] using
    (integral_norm_eq_lintegral_enorm (μ := μ) hf.aestronglyMeasurable)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `L²` hypothesis of Lemma 4.1 in integral form: `f ∈ L²` and `∫ f² ≤ D² ‖f‖₁²`. -/
theorem integral_sq_le_of_eLpNorm_two_le (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 < D) (hL1 : eLpNorm f 1 μ < ⊤)
    (hL2 : eLpNorm f 2 μ ≤ ENNReal.ofReal D * eLpNorm f 1 μ) :
    MemLp f 2 μ ∧ ∫ x, f x ^ 2 ∂μ ≤ D ^ 2 * (eLpNorm f 1 μ).toReal ^ 2 := by
  have hf2 : MemLp f 2 μ := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    exact
      lt_of_le_of_lt hL2
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL1)

  have heq :
      eLpNorm f 2 μ =
        ENNReal.ofReal
          ((∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹)) := by
    simpa using
      (MemLp.eLpNorm_eq_integral_rpow_norm
        (f := f) (μ := μ) (p := (2 : ENNReal))
        (by norm_num) (by norm_num) hf2)

  have htop : ENNReal.ofReal D * eLpNorm f 1 μ ≠ ⊤ := by
    exact
      ENNReal.mul_ne_top
        (ne_of_lt ENNReal.ofReal_lt_top) (ne_of_lt hL1)

  have hto := ENNReal.toReal_mono htop hL2
  rw [heq] at hto

  have hnonneg :
      0 ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
    positivity

  rw [ENNReal.toReal_ofReal hnonneg] at hto
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le] at hto

  have hI : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
    exact integral_nonneg fun x => by positivity

  have hroot :
      ((∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹)) ^ 2 =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
    have hinv : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by
      norm_num
    rw [hinv, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hI

  have hsq :
      ((∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹)) ^ 2 ≤
        (D * (eLpNorm f 1 μ).toReal) ^ 2 := by
    have hright : 0 ≤ D * (eLpNorm f 1 μ).toReal := by
      exact mul_nonneg hD.le ENNReal.toReal_nonneg
    nlinarith

  have hnorm :
      (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) = ∫ x, f x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [Real.norm_eq_abs, sq_abs]

  refine ⟨hf2, ?_⟩
  calc
    ∫ x, f x ^ 2 ∂μ =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := hnorm.symm
    _ = ((∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹)) ^ 2 := hroot.symm
    _ ≤ (D * (eLpNorm f 1 μ).toReal) ^ 2 := hsq
    _ = D ^ 2 * (eLpNorm f 1 μ).toReal ^ 2 := by
      ring

/-- The sub-level bound in Lemma 4.1: below `θ ‖f‖₁` the mass of `{|f| ≤ q}` is less than
`1 - (1 - θ)² / D²`. -/
theorem measureReal_abs_le_lt (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 < D) (hL1 : eLpNorm f 1 μ < ⊤)
    (hL2 : eLpNorm f 2 μ ≤ ENNReal.ofReal D * eLpNorm f 1 μ)
    (hpos : 0 < (eLpNorm f 1 μ).toReal) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) {q : ℝ}
    (hq : q < θ * (eLpNorm f 1 μ).toReal) :
    μ.real {x | |f x| ≤ q} < 1 - (1 - θ) ^ 2 / D ^ 2 := by
  let E : ℝ := (eLpNorm f 1 μ).toReal
  let A : Set Ω := {x | θ * E < |f x|}

  have hE : E = ∫ x, |f x| ∂μ := by
    dsimp [E]
    exact toReal_eLpNorm_one_eq_integral_abs μ hf

  have hEpos : 0 < E := by
    dsimp [E]
    exact hpos

  have hmeanpos : 0 < ∫ x, |f x| ∂μ := by
    rw [← hE]
    exact hEpos

  obtain ⟨hf2, hI⟩ :=
    integral_sq_le_of_eLpNorm_two_le μ hf hD hL1 hL2

  have hg2 : MemLp (fun x => |f x|) 2 μ := by
    simpa [Real.norm_eq_abs] using hf2.norm

  have hgm : Measurable (fun x => |f x|) :=
    continuous_abs.measurable.comp hf

  have hs :=
    sq_mul_sq_integral_lt μ hgm (fun x => abs_nonneg (f x)) hg2
      hmeanpos hθ hθ1

  have hs' :
      (1 - θ) ^ 2 * E ^ 2 <
        (∫ x, |f x| ^ 2 ∂μ) * μ.real A := by
    rw [← hE] at hs
    simpa [A] using hs

  have hsq_integral :
      (∫ x, |f x| ^ 2 ∂μ) = ∫ x, f x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [sq_abs]

  rw [hsq_integral] at hs'

  have hprod :
      E ^ 2 * (1 - θ) ^ 2 <
        E ^ 2 * (D ^ 2 * μ.real A) := by
    calc
      E ^ 2 * (1 - θ) ^ 2 = (1 - θ) ^ 2 * E ^ 2 := by ring
      _ < (D ^ 2 * E ^ 2) * μ.real A := by
        exact lt_of_lt_of_le hs'
          (mul_le_mul_of_nonneg_right hI measureReal_nonneg)
      _ = E ^ 2 * (D ^ 2 * μ.real A) := by ring

  have hE2 : 0 < E ^ 2 := sq_pos_of_pos hEpos

  have hcancel :
      (1 - θ) ^ 2 < D ^ 2 * μ.real A := by
    nlinarith

  have hratio :
      (1 - θ) ^ 2 / D ^ 2 < μ.real A := by
    apply (div_lt_iff₀ (sq_pos_of_pos hD)).2
    simpa [mul_comm] using hcancel

  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt measurable_const hgm

  have hqE : q < θ * E := by
    simpa [E] using hq

  have hsub :
      {x | |f x| ≤ q} ⊆ Aᶜ := by
    intro x hx hxA
    change |f x| ≤ q at hx
    change θ * E < |f x| at hxA
    have hlt : θ * E < q := lt_of_lt_of_le hxA hx
    exact (lt_irrefl q) (lt_trans hqE hlt)

  have hmass :
      μ.real {x | |f x| ≤ q} ≤ 1 - μ.real A := by
    calc
      μ.real {x | |f x| ≤ q} ≤ μ.real Aᶜ :=
        measureReal_mono hsub
      _ = 1 - μ.real A := by
        rw [measureReal_compl hA]
        simp

  linarith

/-- E. Milman (2009), Lemma 4.1 (Paley–Zygmund): if `‖f‖₂ ≤ D ‖f‖₁ < ∞` with `D > 0`, then for
every `θ ∈ (0, 1)` and `ε = (1 - θ)² / D²`, `Q_{1-ε}(|f|) ≥ θ ‖f‖₁`. -/
theorem mul_eLpNorm_one_le_lowerQuantile (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 < D) (hL1 : eLpNorm f 1 μ < ⊤)
    (hL2 : eLpNorm f 2 μ ≤ ENNReal.ofReal D * eLpNorm f 1 μ) {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) :
    θ * (eLpNorm f 1 μ).toReal ≤
      lowerQuantile μ (fun x => |f x|) (1 - (1 - θ) ^ 2 / D ^ 2) := by
  let E : ℝ := (eLpNorm f 1 μ).toReal

  by_cases hE : E = 0
  · have hnonneg :
        0 ≤ lowerQuantile μ (fun x => |f x|)
          (1 - (1 - θ) ^ 2 / D ^ 2) :=
      lowerQuantile_nonneg μ (fun x => abs_nonneg (f x))
        (1 - (1 - θ) ^ 2 / D ^ 2)
    simpa [E, hE] using hnonneg

  have hEpos : 0 < E :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hE)

  have hmono :
      eLpNorm f 1 μ ≤ eLpNorm f 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le
      (μ := μ) (f := f) (p := (1 : ENNReal)) (q := (2 : ENNReal))
      (by norm_num) hf.aestronglyMeasurable

  have htop :
      ENNReal.ofReal D * eLpNorm f 1 μ ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ne_of_lt ENNReal.ofReal_lt_top) (ne_of_lt hL1)

  have hnorm :
      E ≤ D * E := by
    have ht := ENNReal.toReal_mono htop (hmono.trans hL2)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le] at ht
    simpa [E] using ht

  have hD1 : 1 ≤ D := by
    nlinarith

  have hratio_pos :
      0 < (1 - θ) ^ 2 / D ^ 2 :=
    div_pos (sq_pos_of_pos (sub_pos.mpr hθ1)) (sq_pos_of_pos hD)

  have hratio_lt :
      (1 - θ) ^ 2 / D ^ 2 < 1 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hD)).2
    have hsub : 0 < 1 - θ := sub_pos.mpr hθ1
    nlinarith [sq_nonneg (D - (1 - θ))]

  have hδpos :
      0 < 1 - (1 - θ) ^ 2 / D ^ 2 := by
    linarith

  have hδlt :
      1 - (1 - θ) ^ 2 / D ^ 2 < 1 := by
    linarith [hratio_pos]

  have hgm : Measurable (fun x => |f x|) :=
    continuous_abs.measurable.comp hf

  refine le_lowerQuantile μ
    (δ := 1 - (1 - θ) ^ 2 / D ^ 2)
    (a := θ * E) hδlt ?_

  intro q hq

  have hq' : q < θ * (eLpNorm f 1 μ).toReal := by
    simpa [E] using hq

  have hreal :=
    measureReal_abs_le_lt μ hf hD hL1 hL2 hEpos hθ hθ1 hq'

  let S : Set Ω := {x | |f x| ≤ q}

  have hmeasure : ENNReal.ofReal (μ.real S) = μ S := by
    change ENNReal.ofReal (μ S).toReal = μ S
    exact ENNReal.ofReal_toReal (measure_ne_top μ S)

  have hof :
      ENNReal.ofReal (μ.real S) <
        ENNReal.ofReal (1 - (1 - θ) ^ 2 / D ^ 2) :=
    (ENNReal.ofReal_lt_ofReal_iff hδpos).2 hreal

  rw [hmeasure] at hof
  simpa [S] using hof

end FunctionalInequalities.Probability
