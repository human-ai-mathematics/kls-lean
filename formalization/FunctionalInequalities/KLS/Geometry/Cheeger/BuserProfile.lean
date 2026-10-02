import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Explicit Buser profiles of De Ponti–Mondino

De Ponti–Mondino, *Sharp Cheeger–Buser type inequalities in RCD(K, ∞) spaces*
(arXiv:1902.03835v2), Lemmas 3.2 and 3.3. For a fixed `T > 0`,

* `f₁(x) = √x / arctan (√(e^{Tx} − 1))` is strictly increasing on `(0, ∞)` and `f₁ ≥ 1/√T`;
* `f₂(x) = √x / log (e^{Tx} + √(e^{2Tx} − 1))` is strictly decreasing on `(0, ∞)`.

The paper states "increasing" and "decreasing"; the strict forms imply them. These functions
enter the explicit Buser bounds for `K > 0` and `K < 0` (Corollary 1.2 and Remark 3.4).
-/

open Real Set

namespace FunctionalInequalities.KLS.Isoperimetry

/-- The function `f₁` of De Ponti–Mondino Lemma 3.2. -/
noncomputable def buserRatioPos (T x : ℝ) : ℝ :=
  Real.sqrt x / Real.arctan (Real.sqrt (Real.exp (T * x) - 1))

/-- The function `f₂` of De Ponti–Mondino Lemma 3.3. -/
noncomputable def buserRatioNeg (T x : ℝ) : ℝ :=
  Real.sqrt x / Real.log (Real.exp (T * x) + Real.sqrt (Real.exp (2 * T * x) - 1))

/-- `sin s · cos s < s` for `s > 0`. -/
theorem sin_mul_cos_lt_self {s : ℝ} (hs : 0 < s) : Real.sin s * Real.cos s < s := by
  have h : Real.sin (2 * s) < 2 * s := Real.sin_lt (by positivity)
  rw [Real.sin_two_mul] at h
  linarith

/-- `s < sinh s · cosh s` for `s > 0`. -/
theorem self_lt_sinh_mul_cosh {s : ℝ} (hs : 0 < s) :
    s < Real.sinh s * Real.cosh s := by
  have h : 2 * s < Real.sinh (2 * s) :=
    Real.self_lt_sinh_iff.mpr (by positivity)
  rw [Real.sinh_two_mul] at h
  linarith

/-- `s² / 2 < -log (cos s)` on `(0,π/2)`. -/
theorem sq_div_two_lt_neg_log_cos {s : ℝ} (hs : 0 < s) (hs' : s < π / 2) :
    s ^ 2 / 2 < -Real.log (Real.cos s) := by
  let φ : ℝ → ℝ := fun t => -Real.log (Real.cos t) - t ^ 2 / 2
  have hcos : ∀ t ∈ Ico (0 : ℝ) (π / 2), Real.cos t ≠ 0 := by
    intro t ht
    apply (Real.cos_pos_of_mem_Ioo ?_).ne'
    constructor
    · linarith [Real.pi_pos, ht.1]
    · exact ht.2
  have hcont : ContinuousOn φ (Ico (0 : ℝ) (π / 2)) := by
    have hlog : ContinuousOn (fun t : ℝ => Real.log (Real.cos t))
        (Ico (0 : ℝ) (π / 2)) :=
      Real.continuous_cos.continuousOn.log (fun t ht => hcos t ht)
    dsimp [φ]
    exact hlog.neg.sub ((continuousOn_id.pow 2).div_const 2)
  have hderiv :
      ∀ x ∈ interior (Ico (0 : ℝ) (π / 2)), 0 < deriv φ x := by
    intro x hx
    rw [interior_Ico] at hx
    have hcx : Real.cos x ≠ 0 := hcos x ⟨le_of_lt hx.1, hx.2⟩
    have hlog :
        HasDerivAt (fun y : ℝ => Real.log (Real.cos y))
          (-Real.sin x / Real.cos x) x :=
      (Real.hasDerivAt_cos x).log hcx
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    have hφ : HasDerivAt φ (-(-Real.sin x / Real.cos x) - x) x := by
      dsimp [φ]
      exact hlog.neg.sub hpow
    have htan : x < Real.sin x / Real.cos x := by
      rw [← Real.tan_eq_sin_div_cos x]
      exact Real.lt_tan hx.1 hx.2
    have hrewrite :
        -(-Real.sin x / Real.cos x) - x =
          Real.sin x / Real.cos x - x := by
      ring
    rw [hφ.deriv, hrewrite]
    linarith
  have hmono : StrictMonoOn φ (Ico (0 : ℝ) (π / 2)) :=
    strictMonoOn_of_deriv_pos (convex_Ico 0 (π / 2)) hcont hderiv
  have hφ : φ 0 < φ s := by
    apply hmono
    · exact ⟨le_rfl, by positivity⟩
    · exact ⟨le_of_lt hs, hs'⟩
    · exact hs
  have hzero : φ 0 = 0 := by
    simp [φ]
  rw [hzero] at hφ
  dsimp [φ] at hφ
  linarith

/-- `2 (-log (cos s)) < s tan s` on `(0,π/2)`. -/
theorem two_mul_neg_log_cos_lt_mul_tan {s : ℝ} (hs : 0 < s) (hs' : s < π / 2) :
    2 * -Real.log (Real.cos s) < s * Real.tan s := by
  let k : ℝ → ℝ :=
    (id * Real.tan) + (fun t : ℝ => 2 * Real.log (Real.cos t))
  have hcos : ∀ t ∈ Ico (0 : ℝ) (π / 2), Real.cos t ≠ 0 := by
    intro t ht
    apply (Real.cos_pos_of_mem_Ioo ?_).ne'
    constructor
    · linarith [Real.pi_pos, ht.1]
    · exact ht.2
  have hcont : ContinuousOn k (Ico (0 : ℝ) (π / 2)) := by
    dsimp [k]
    apply ContinuousOn.add
    · exact continuousOn_id.mul <|
        Real.continuousOn_tan_Ioo.mono (by
          intro t ht
          constructor
          · linarith [Real.pi_pos, ht.1]
          · exact ht.2)
    · have hlog :
          ContinuousOn (fun t : ℝ => Real.log (Real.cos t))
            (Ico (0 : ℝ) (π / 2)) :=
        Real.continuous_cos.continuousOn.log (fun t ht => hcos t ht)
      exact continuousOn_const.mul hlog
  have hderiv :
      ∀ x ∈ interior (Ico (0 : ℝ) (π / 2)), 0 < deriv k x := by
    intro x hx
    rw [interior_Ico] at hx
    have hcx : Real.cos x ≠ 0 := hcos x ⟨le_of_lt hx.1, hx.2⟩
    have hlog :
        HasDerivAt (fun y : ℝ => Real.log (Real.cos y))
          (-Real.sin x / Real.cos x) x :=
      (Real.hasDerivAt_cos x).log hcx
    have hk :
        HasDerivAt k
          (1 * Real.tan x + x * (1 / Real.cos x ^ 2) +
            2 * (-Real.sin x / Real.cos x)) x := by
      dsimp [k]
      exact
        ((hasDerivAt_id x).mul (Real.hasDerivAt_tan hcx)).add
          (HasDerivAt.const_mul 2 hlog)
    have heq :
        1 * Real.tan x + x * (1 / Real.cos x ^ 2) +
            2 * (-Real.sin x / Real.cos x) =
          (x - Real.sin x * Real.cos x) / Real.cos x ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp [hcx]; ring
    have hnum : 0 < x - Real.sin x * Real.cos x := by
      linarith [sin_mul_cos_lt_self hx.1]
    have hden : 0 < Real.cos x ^ 2 := sq_pos_of_ne_zero hcx
    rw [hk.deriv, heq]
    exact div_pos hnum hden
  have hmono : StrictMonoOn k (Ico (0 : ℝ) (π / 2)) :=
    strictMonoOn_of_deriv_pos (convex_Ico 0 (π / 2)) hcont hderiv
  have hks : k 0 < k s := by
    apply hmono
    · exact ⟨le_rfl, by positivity⟩
    · exact ⟨le_of_lt hs, hs'⟩
    · exact hs
  have hkzero : k 0 = 0 := by
    simp [k]
  rw [hkzero] at hks
  have hpos : 0 < s * Real.tan s + 2 * Real.log (Real.cos s) := by
    simpa [k] using hks
  linarith

/-- `s tanh s < 2 log (cosh s)` for `s > 0`. -/
theorem mul_tanh_lt_two_mul_log_cosh {s : ℝ} (hs : 0 < s) :
    s * Real.tanh s < 2 * Real.log (Real.cosh s) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  let m : ℝ → ℝ :=
    (id * (fun t : ℝ => Real.sinh t / Real.cosh t)) -
      (fun t : ℝ => 2 * Real.log (Real.cosh t))
  have hquot :
      ContinuousOn (fun t : ℝ => Real.sinh t / Real.cosh t)
        (Ici (0 : ℝ)) :=
    Real.continuous_sinh.continuousOn.div
      (Real.continuous_cosh.continuousOn : ContinuousOn Real.cosh (Ici 0))
      (fun t _ => (Real.cosh_pos t).ne')
  have hlog :
      ContinuousOn (fun t : ℝ => Real.log (Real.cosh t))
        (Ici (0 : ℝ)) :=
    Real.continuous_cosh.continuousOn.log
      (fun t _ => (Real.cosh_pos t).ne')
  have hcont : ContinuousOn m (Ici (0 : ℝ)) := by
    dsimp [m]
    exact (continuousOn_id.mul hquot).sub (continuousOn_const.mul hlog)
  have hderiv :
      ∀ x ∈ interior (Ici (0 : ℝ)), deriv m x < 0 := by
    intro x hx
    rw [interior_Ici] at hx
    have hcx : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
    have hquot' :
        HasDerivAt
          (fun y : ℝ => Real.sinh y / Real.cosh y)
          ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) /
            Real.cosh x ^ 2) x :=
      (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hcx
    have hlog' :
        HasDerivAt (fun y : ℝ => Real.log (Real.cosh y))
          (Real.sinh x / Real.cosh x) x :=
      (Real.hasDerivAt_cosh x).log hcx
    have hm :
        HasDerivAt m
          (1 * (Real.sinh x / Real.cosh x) +
              x * ((Real.cosh x * Real.cosh x -
                Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) -
              2 * (Real.sinh x / Real.cosh x)) x := by
      change HasDerivAt
        ((id * (fun t : ℝ => Real.sinh t / Real.cosh t)) -
          (fun t : ℝ => 2 * Real.log (Real.cosh t)))
        _ x
      exact
        ((hasDerivAt_id x).mul hquot').sub
          (HasDerivAt.const_mul 2 hlog')
    have hsq :
        Real.cosh x * Real.cosh x -
            Real.sinh x * Real.sinh x = 1 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
    have heq :
        1 * (Real.sinh x / Real.cosh x) +
              x * ((Real.cosh x * Real.cosh x -
                Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) -
              2 * (Real.sinh x / Real.cosh x) =
          (x - Real.sinh x * Real.cosh x) / Real.cosh x ^ 2 := by
      rw [hsq]
      field_simp [hcx]
      ring
    have hnum : x - Real.sinh x * Real.cosh x < 0 := by
      linarith [self_lt_sinh_mul_cosh hx]
    have hden : 0 < Real.cosh x ^ 2 := sq_pos_of_ne_zero hcx
    rw [hm.deriv, heq]
    exact div_neg_of_neg_of_pos hnum hden
  have hmono : StrictAntiOn m (Ici (0 : ℝ)) :=
    strictAntiOn_of_deriv_neg (convex_Ici 0) hcont hderiv
  have hms : m s < m 0 := by
    apply hmono
    · exact (show (0 : ℝ) ≤ 0 from le_rfl)
    · exact le_of_lt hs
    · exact hs
  have hmzero : m 0 = 0 := by
    simp [m]
  rw [hmzero] at hms
  simpa [m] using hms

/-- `-log (cos s) / s²` is strictly increasing on `(0,π/2)`. -/
theorem strictMonoOn_neg_log_cos_div_sq :
    StrictMonoOn (fun s : ℝ => -Real.log (Real.cos s) / s ^ 2) (Ioo 0 (π / 2)) := by
  have hcos : ∀ t ∈ Ioo (0 : ℝ) (π / 2), Real.cos t ≠ 0 := by
    intro t ht
    apply (Real.cos_pos_of_mem_Ioo ?_).ne'
    constructor
    · linarith [Real.pi_pos, ht.1]
    · exact ht.2
  have hcont :
      ContinuousOn (fun s : ℝ => -Real.log (Real.cos s) / s ^ 2)
        (Ioo (0 : ℝ) (π / 2)) := by
    have hlog :
        ContinuousOn (fun s : ℝ => Real.log (Real.cos s))
          (Ioo (0 : ℝ) (π / 2)) :=
      Real.continuous_cos.continuousOn.log (fun t ht => hcos t ht)
    exact hlog.neg.div (continuousOn_id.pow 2) (fun t ht =>
      pow_ne_zero 2 ht.1.ne')
  have hderiv :
      ∀ x ∈ interior (Ioo (0 : ℝ) (π / 2)),
        0 < deriv (fun s : ℝ => -Real.log (Real.cos s) / s ^ 2) x := by
    intro x hx
    rw [interior_Ioo] at hx
    have hcx : Real.cos x ≠ 0 := hcos x ⟨hx.1, hx.2⟩
    have hlog :
        HasDerivAt (fun y : ℝ => Real.log (Real.cos y))
          (-Real.sin x / Real.cos x) x :=
      (Real.hasDerivAt_cos x).log hcx
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have hq :
        HasDerivAt
          (fun y : ℝ => -Real.log (Real.cos y) / y ^ 2)
          ((-(-Real.sin x / Real.cos x) * x ^ 2 -
              (-Real.log (Real.cos x)) * (2 * x)) /
            (x ^ 2) ^ 2) x := by
      exact hlog.neg.div hpow (pow_ne_zero 2 hx.1.ne')
    have hineq :
        2 * -Real.log (Real.cos x) <
          x * (Real.sin x / Real.cos x) := by
      simpa [Real.tan_eq_sin_div_cos] using
        (two_mul_neg_log_cos_lt_mul_tan hx.1 hx.2)
    have hmul :
        (2 * -Real.log (Real.cos x)) * x <
          (x * (Real.sin x / Real.cos x)) * x :=
      mul_lt_mul_of_pos_right hineq hx.1
    have heq :
        -(-Real.sin x / Real.cos x) * x ^ 2 -
              (-Real.log (Real.cos x)) * (2 * x) =
          (x * (Real.sin x / Real.cos x)) * x -
            (2 * -Real.log (Real.cos x)) * x := by
      ring
    have hnum :
        0 <
          -(-Real.sin x / Real.cos x) * x ^ 2 -
            (-Real.log (Real.cos x)) * (2 * x) := by
      rw [heq]
      exact sub_pos.mpr hmul
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx.1.ne'
    have hden : 0 < (x ^ 2) ^ 2 := sq_pos_of_ne_zero hx2
    rw [hq.deriv]
    exact div_pos hnum hden
  exact strictMonoOn_of_deriv_pos (convex_Ioo 0 (π / 2)) hcont hderiv

/-- `log (cosh s) / s²` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_log_cosh_div_sq :
    StrictAntiOn (fun s : ℝ => Real.log (Real.cosh s) / s ^ 2) (Ioi 0) := by
  have hcont :
      ContinuousOn (fun s : ℝ => Real.log (Real.cosh s) / s ^ 2)
        (Ioi (0 : ℝ)) := by
    have hlog :
        ContinuousOn (fun s : ℝ => Real.log (Real.cosh s)) (Ioi (0 : ℝ)) :=
      Real.continuous_cosh.continuousOn.log
        (fun t _ => (Real.cosh_pos t).ne')
    exact hlog.div (continuousOn_id.pow 2) (fun t ht =>
      pow_ne_zero 2 ht.ne')
  have hderiv :
      ∀ x ∈ interior (Ioi (0 : ℝ)),
        deriv (fun s : ℝ => Real.log (Real.cosh s) / s ^ 2) x < 0 := by
    intro x hx
    rw [interior_Ioi] at hx
    have hcx : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
    have hlog :
        HasDerivAt (fun y : ℝ => Real.log (Real.cosh y))
          (Real.sinh x / Real.cosh x) x :=
      (Real.hasDerivAt_cosh x).log hcx
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have hq :
        HasDerivAt
          (fun y : ℝ => Real.log (Real.cosh y) / y ^ 2)
          (((Real.sinh x / Real.cosh x) * x ^ 2 -
              Real.log (Real.cosh x) * (2 * x)) /
            (x ^ 2) ^ 2) x := by
      exact hlog.div hpow (pow_ne_zero 2 hx.ne')
    have hineq :
        x * (Real.sinh x / Real.cosh x) <
          2 * Real.log (Real.cosh x) := by
      simpa [Real.tanh_eq_sinh_div_cosh] using
        (mul_tanh_lt_two_mul_log_cosh hx)
    have hinner :
        x * (x * (Real.sinh x / Real.cosh x) -
            2 * Real.log (Real.cosh x)) < 0 :=
      mul_neg_of_pos_of_neg hx (sub_neg.mpr hineq)
    have hfactor :
        (Real.sinh x / Real.cosh x) * x ^ 2 -
            Real.log (Real.cosh x) * (2 * x) =
          x * (x * (Real.sinh x / Real.cosh x) -
            2 * Real.log (Real.cosh x)) := by
      ring
    have hnum :
        (Real.sinh x / Real.cosh x) * x ^ 2 -
            Real.log (Real.cosh x) * (2 * x) < 0 := by
      rw [hfactor]
      exact hinner
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx.ne'
    have hden : 0 < (x ^ 2) ^ 2 := sq_pos_of_ne_zero hx2
    rw [hq.deriv]
    exact div_neg_of_neg_of_pos hnum hden
  exact strictAntiOn_of_deriv_neg (convex_Ioi 0) hcont hderiv

/-- The `arctan` substitution of Lemma 3.2 lands in `(0,π/2)` for `x > 0`. -/
theorem arctan_sqrt_exp_sub_one_mem {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    Real.arctan (Real.sqrt (Real.exp (T * x) - 1)) ∈ Ioo 0 (π / 2) := by
  have hTx : 0 < T * x := mul_pos hT hx
  have hexp : 1 < Real.exp (T * x) := by
    have h := Real.add_one_le_exp (T * x)
    linarith
  have hsub : 0 < Real.exp (T * x) - 1 := sub_pos.mpr hexp
  have hsqrt : 0 < Real.sqrt (Real.exp (T * x) - 1) :=
    Real.sqrt_pos.mpr hsub
  constructor
  · exact Real.arctan_pos.mpr hsqrt
  · exact Real.arctan_lt_pi_div_two _

/-- The `arctan` substitution is strictly increasing in `x > 0`. -/
theorem strictMonoOn_arctan_sqrt_exp_sub_one {T : ℝ} (hT : 0 < T) :
    StrictMonoOn (fun x : ℝ => Real.arctan (Real.sqrt (Real.exp (T * x) - 1))) (Ioi 0) := by
  intro x hx y hy hxy
  have hTxy : T * x < T * y :=
    mul_lt_mul_of_pos_left hxy hT
  have hexp : Real.exp (T * x) < Real.exp (T * y) :=
    Real.exp_lt_exp.mpr hTxy
  have hnonneg : 0 ≤ Real.exp (T * x) - 1 := by
    have hTx : 0 ≤ T * x := le_of_lt (mul_pos hT hx)
    have h₁ : 1 ≤ Real.exp (T * x) := by
      have h := Real.add_one_le_exp (T * x)
      linarith
    exact sub_nonneg.mpr h₁
  have harg :
      Real.exp (T * x) - 1 < Real.exp (T * y) - 1 := by
    linarith
  have hsqrt :
      Real.sqrt (Real.exp (T * x) - 1) <
        Real.sqrt (Real.exp (T * y) - 1) :=
    Real.sqrt_lt_sqrt hnonneg harg
  exact Real.arctan_strictMono hsqrt

/-- Inverting the `arctan` substitution: `-log (cos s) = T x / 2`. -/
theorem neg_log_cos_arctan_sqrt_exp_sub_one {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    -Real.log (Real.cos (Real.arctan (Real.sqrt (Real.exp (T * x) - 1)))) = T * x / 2 := by
  have hTx : 0 < T * x := mul_pos hT hx
  have hexp : 1 ≤ Real.exp (T * x) := by
    have h := Real.add_one_le_exp (T * x)
    linarith
  have hnonneg : 0 ≤ Real.exp (T * x) - 1 :=
    sub_nonneg.mpr hexp
  have hsquare :
      Real.sqrt (Real.exp (T * x) - 1) ^ 2 =
        Real.exp (T * x) - 1 :=
    Real.sq_sqrt hnonneg
  have hinside :
      1 + Real.sqrt (Real.exp (T * x) - 1) ^ 2 =
        Real.exp (T * x) := by
    rw [hsquare]
    ring
  have hcos :
      Real.cos (Real.arctan (Real.sqrt (Real.exp (T * x) - 1))) =
        1 / Real.sqrt (Real.exp (T * x)) := by
    rw [Real.cos_arctan, hinside]
  have hexppos : 0 < Real.exp (T * x) := Real.exp_pos _
  calc
    -Real.log (Real.cos (Real.arctan (Real.sqrt (Real.exp (T * x) - 1)))) =
        -Real.log ((Real.sqrt (Real.exp (T * x)))⁻¹) := by
          rw [hcos, one_div]
    _ = Real.log (Real.sqrt (Real.exp (T * x))) := by
      rw [Real.log_inv]
      ring
    _ = Real.log (Real.exp (T * x)) / 2 :=
      Real.log_sqrt (le_of_lt hexppos)
    _ = T * x / 2 := by
      rw [Real.log_exp]

/-- The logarithm in Lemma 3.3 is `arcosh (e^{Tx})`. -/
theorem log_exp_add_sqrt_eq_arcosh (T x : ℝ) :
    Real.log (Real.exp (T * x) + Real.sqrt (Real.exp (2 * T * x) - 1)) =
      Real.arcosh (Real.exp (T * x)) := by
  unfold Real.arcosh
  have h :
      Real.exp (2 * T * x) = Real.exp (T * x) ^ 2 := by
    rw [show 2 * T * x = T * x + T * x by ring, Real.exp_add]
    ring
  rw [h]

/-- Inverting the `arcosh` substitution: `log (cosh s) = T x`. -/
theorem log_cosh_arcosh_exp (T x : ℝ) (h : 0 ≤ T * x) :
    Real.log (Real.cosh (Real.arcosh (Real.exp (T * x)))) = T * x := by
  have hexp : 1 ≤ Real.exp (T * x) := by
    exact Real.one_le_exp h
  rw [Real.cosh_arcosh hexp, Real.log_exp]

/-- `f₁` through the `arctan` substitution of Lemma 3.2. -/
theorem buserRatioPos_eq {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    buserRatioPos T x =
      Real.sqrt (2 / T * (-Real.log (Real.cos (Real.arctan (Real.sqrt (Real.exp (T * x) - 1)))) /
        Real.arctan (Real.sqrt (Real.exp (T * x) - 1)) ^ 2)) := by
  let s : ℝ := Real.arctan (Real.sqrt (Real.exp (T * x) - 1))
  have hs_mem : s ∈ Ioo (0 : ℝ) (π / 2) := by
    simpa [s] using arctan_sqrt_exp_sub_one_mem hT hx
  have hs : 0 < s := hs_mem.1
  have hlog : -Real.log (Real.cos s) = T * x / 2 := by
    simpa [s] using neg_log_cos_arctan_sqrt_exp_sub_one hT hx
  have hinside :
      2 / T * (-Real.log (Real.cos s) / s ^ 2) = x / s ^ 2 := by
    rw [hlog]
    field_simp [ne_of_gt hT, ne_of_gt hs]
  have hquot : 0 ≤ x / s ^ 2 := by
    exact div_nonneg (le_of_lt hx) (sq_nonneg s)
  have ha_sq :
      (Real.sqrt (x / s ^ 2)) ^ 2 = x / s ^ 2 :=
    Real.sq_sqrt hquot
  have hb_nonneg : 0 ≤ Real.sqrt x / s := by
    exact div_nonneg (Real.sqrt_nonneg x) (le_of_lt hs)
  have hb_sq :
      (Real.sqrt x / s) ^ 2 = x / s ^ 2 := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hx)]
  have hsqrt :
      Real.sqrt (x / s ^ 2) = Real.sqrt x / s := by
    have hprod :
        (Real.sqrt (x / s ^ 2) - Real.sqrt x / s) *
          (Real.sqrt (x / s ^ 2) + Real.sqrt x / s) = 0 := by
      nlinarith [ha_sq, hb_sq]
    rcases mul_eq_zero.mp hprod with hdiff | hsum
    · linarith
    · linarith [Real.sqrt_nonneg (x / s ^ 2), Real.sqrt_nonneg x]
  unfold buserRatioPos
  change Real.sqrt x / s =
    Real.sqrt (2 / T * (-Real.log (Real.cos s) / s ^ 2))
  rw [hinside, hsqrt]

/-- `f₂` through the `arcosh` substitution of Lemma 3.3. -/
theorem buserRatioNeg_eq {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    buserRatioNeg T x =
      Real.sqrt (1 / T * (Real.log (Real.cosh (Real.arcosh (Real.exp (T * x)))) /
        Real.arcosh (Real.exp (T * x)) ^ 2)) := by
  let s : ℝ := Real.arcosh (Real.exp (T * x))
  have hTx : 0 < T * x := mul_pos hT hx
  have hexp : 1 < Real.exp (T * x) := by
    have h := Real.add_one_le_exp (T * x)
    linarith
  have hs : 0 < s := by
    dsimp [s]
    exact Real.arcosh_pos hexp
  have hlog : Real.log (Real.cosh s) = T * x := by
    simpa [s] using
      (log_cosh_arcosh_exp T x (le_of_lt hTx))
  have hinside :
      1 / T * (Real.log (Real.cosh s) / s ^ 2) = x / s ^ 2 := by
    rw [hlog]
    field_simp [ne_of_gt hT, ne_of_gt hs]
  have hquot : 0 ≤ x / s ^ 2 := by
    exact div_nonneg (le_of_lt hx) (sq_nonneg s)
  have ha_sq :
      (Real.sqrt (x / s ^ 2)) ^ 2 = x / s ^ 2 :=
    Real.sq_sqrt hquot
  have hb_nonneg : 0 ≤ Real.sqrt x / s := by
    exact div_nonneg (Real.sqrt_nonneg x) (le_of_lt hs)
  have hb_sq :
      (Real.sqrt x / s) ^ 2 = x / s ^ 2 := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hx)]
  have hsqrt :
      Real.sqrt (x / s ^ 2) = Real.sqrt x / s := by
    have hprod :
        (Real.sqrt (x / s ^ 2) - Real.sqrt x / s) *
          (Real.sqrt (x / s ^ 2) + Real.sqrt x / s) = 0 := by
      nlinarith [ha_sq, hb_sq]
    rcases mul_eq_zero.mp hprod with hdiff | hsum
    · linarith
    · linarith [Real.sqrt_nonneg (x / s ^ 2), Real.sqrt_nonneg x]
  unfold buserRatioNeg
  rw [log_exp_add_sqrt_eq_arcosh T x]
  change Real.sqrt x / s =
    Real.sqrt (1 / T * (Real.log (Real.cosh s) / s ^ 2))
  rw [hinside, hsqrt]

/-- De Ponti–Mondino Lemma 3.2, monotonicity: `f₁` is strictly increasing on `(0, ∞)`. -/
theorem strictMonoOn_buserRatioPos {T : ℝ} (hT : 0 < T) :
    StrictMonoOn (buserRatioPos T) (Ioi 0) := by
  intro x hx y hy hxy
  let sx : ℝ :=
    Real.arctan (Real.sqrt (Real.exp (T * x) - 1))
  let sy : ℝ :=
    Real.arctan (Real.sqrt (Real.exp (T * y) - 1))
  have hsx_mem : sx ∈ Ioo (0 : ℝ) (π / 2) := by
    dsimp [sx]
    exact arctan_sqrt_exp_sub_one_mem hT hx
  have hsy_mem : sy ∈ Ioo (0 : ℝ) (π / 2) := by
    dsimp [sy]
    exact arctan_sqrt_exp_sub_one_mem hT hy
  have hsxy : sx < sy := by
    dsimp [sx, sy]
    exact strictMonoOn_arctan_sqrt_exp_sub_one hT hx hy hxy
  have hg :
      -Real.log (Real.cos sx) / sx ^ 2 <
        -Real.log (Real.cos sy) / sy ^ 2 :=
    strictMonoOn_neg_log_cos_div_sq hsx_mem hsy_mem hsxy
  have hscale : 0 < 2 / T := by
    exact div_pos (by norm_num) hT
  have hscaled :
      2 / T * (-Real.log (Real.cos sx) / sx ^ 2) <
        2 / T * (-Real.log (Real.cos sy) / sy ^ 2) :=
    mul_lt_mul_of_pos_left hg hscale
  have hnum : 0 < -Real.log (Real.cos sx) := by
    have hbound :
        sx ^ 2 / 2 < -Real.log (Real.cos sx) :=
      sq_div_two_lt_neg_log_cos hsx_mem.1 hsx_mem.2
    have hsq : 0 < sx ^ 2 / 2 :=
      div_pos (sq_pos_of_pos hsx_mem.1) (by norm_num)
    linarith
  have hnonneg :
      0 ≤ 2 / T * (-Real.log (Real.cos sx) / sx ^ 2) := by
    have hquot : 0 < -Real.log (Real.cos sx) / sx ^ 2 :=
      div_pos hnum (sq_pos_of_pos hsx_mem.1)
    exact le_of_lt (mul_pos hscale hquot)
  have hsqrt :
      Real.sqrt (2 / T * (-Real.log (Real.cos sx) / sx ^ 2)) <
        Real.sqrt (2 / T * (-Real.log (Real.cos sy) / sy ^ 2)) :=
    Real.sqrt_lt_sqrt hnonneg hscaled
  rw [buserRatioPos_eq hT hx, buserRatioPos_eq hT hy]
  simpa [sx, sy] using hsqrt

/-- De Ponti–Mondino Lemma 3.2, lower bound: `f₁(x) ≥ 1/√T` for `x > 0`. -/
theorem one_div_sqrt_le_buserRatioPos {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    1 / Real.sqrt T ≤ buserRatioPos T x := by
  rw [buserRatioPos_eq hT hx]
  let s : ℝ :=
    Real.arctan (Real.sqrt (Real.exp (T * x) - 1))
  have hs_mem : s ∈ Ioo (0 : ℝ) (π / 2) := by
    simpa [s] using arctan_sqrt_exp_sub_one_mem hT hx
  have hs : 0 < s := hs_mem.1
  change
    1 / Real.sqrt T ≤
      Real.sqrt (2 / T * (-Real.log (Real.cos s) / s ^ 2))
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hbound :
      s ^ 2 / 2 < -Real.log (Real.cos s) :=
    sq_div_two_lt_neg_log_cos hs_mem.1 hs_mem.2
  have hq :
      (1 : ℝ) / 2 <
        -Real.log (Real.cos s) / s ^ 2 := by
    apply (lt_div_iff₀ hs2).2
    nlinarith [hbound]
  have hscale : 0 < 2 / T := by
    exact div_pos (by norm_num) hT
  have hscaled :
      (2 / T) * (1 / 2) <
        2 / T * (-Real.log (Real.cos s) / s ^ 2) :=
    mul_lt_mul_of_pos_left hq hscale
  have hfactor : (2 / T) * (1 / 2) = 1 / T := by
    ring
  rw [hfactor] at hscaled
  have hA :
      1 / T ≤ 2 / T * (-Real.log (Real.cos s) / s ^ 2) :=
    le_of_lt hscaled
  have hA_nonneg :
      0 ≤ 2 / T * (-Real.log (Real.cos s) / s ^ 2) :=
    le_trans (by positivity) hA
  have hTroot : 0 < Real.sqrt T :=
    Real.sqrt_pos.mpr hT
  have hu_sq : (1 / Real.sqrt T) ^ 2 = 1 / T := by
    calc
      (1 / Real.sqrt T) ^ 2 = 1 / (Real.sqrt T) ^ 2 := by
        rw [div_pow]
        norm_num
      _ = 1 / T := by
        rw [Real.sq_sqrt (le_of_lt hT)]
  have hv_sq :
      (Real.sqrt (2 / T * (-Real.log (Real.cos s) / s ^ 2))) ^ 2 =
        2 / T * (-Real.log (Real.cos s) / s ^ 2) :=
    Real.sq_sqrt hA_nonneg
  have hu : 0 ≤ 1 / Real.sqrt T := by
    positivity
  have hv :
      0 ≤ Real.sqrt (2 / T * (-Real.log (Real.cos s) / s ^ 2)) :=
    Real.sqrt_nonneg _
  nlinarith [hA, hu_sq, hv_sq]

/-- De Ponti–Mondino Lemma 3.3: `f₂` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_buserRatioNeg {T : ℝ} (hT : 0 < T) :
    StrictAntiOn (buserRatioNeg T) (Ioi 0) := by
  intro x hx y hy hxy
  let sx : ℝ := Real.arcosh (Real.exp (T * x))
  let sy : ℝ := Real.arcosh (Real.exp (T * y))
  have hTx : 0 < T * x := mul_pos hT hx
  have hTy : 0 < T * y := mul_pos hT hy
  have hexpx : 1 < Real.exp (T * x) := by
    have h := Real.add_one_le_exp (T * x)
    linarith
  have hexpy : 1 < Real.exp (T * y) := by
    have h := Real.add_one_le_exp (T * y)
    linarith
  have hsx : 0 < sx := by
    dsimp [sx]
    exact Real.arcosh_pos hexpx
  have hsy : 0 < sy := by
    dsimp [sy]
    exact Real.arcosh_pos hexpy
  have hsx_mem : sx ∈ Ioi (0 : ℝ) := hsx
  have hsy_mem : sy ∈ Ioi (0 : ℝ) := hsy
  have hTxy : T * x < T * y :=
    mul_lt_mul_of_pos_left hxy hT
  have hexp_xy : Real.exp (T * x) < Real.exp (T * y) :=
    Real.exp_lt_exp.mpr hTxy
  have hsxy : sx < sy := by
    dsimp [sx, sy]
    exact Real.strictMonoOn_arcosh (Real.exp_pos _) (Real.exp_pos _) hexp_xy
  have hq :
      Real.log (Real.cosh sy) / sy ^ 2 <
        Real.log (Real.cosh sx) / sx ^ 2 :=
    strictAntiOn_log_cosh_div_sq hsx_mem hsy_mem hsxy
  have hlogy : 0 ≤ Real.log (Real.cosh sy) := by
    apply Real.log_nonneg
    exact le_of_lt ((Real.one_lt_cosh).mpr (ne_of_gt hsy))
  have hqy : 0 ≤ Real.log (Real.cosh sy) / sy ^ 2 :=
    div_nonneg hlogy (sq_nonneg sy)
  have hscale : 0 < 1 / T := div_pos (by norm_num) hT
  have hscaled :
      (1 / T) * (Real.log (Real.cosh sy) / sy ^ 2) <
        (1 / T) * (Real.log (Real.cosh sx) / sx ^ 2) :=
    mul_lt_mul_of_pos_left hq hscale
  have hnonneg :
      0 ≤ (1 / T) * (Real.log (Real.cosh sy) / sy ^ 2) :=
    mul_nonneg (le_of_lt hscale) hqy
  have hsqrt :
      Real.sqrt (1 / T * (Real.log (Real.cosh sy) / sy ^ 2)) <
        Real.sqrt (1 / T * (Real.log (Real.cosh sx) / sx ^ 2)) :=
    Real.sqrt_lt_sqrt hnonneg hscaled
  rw [buserRatioNeg_eq hT hx, buserRatioNeg_eq hT hy]
  simpa [sx, sy] using hsqrt

end FunctionalInequalities.KLS.Isoperimetry
