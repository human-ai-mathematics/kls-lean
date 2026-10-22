import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar oscillation moduli

The iteration lemma of Gilbarg–Trudinger (2001), Lemma 8.23 (pp. 201–202): if nondecreasing nonnegative `ω, σ` on `(0, R₀]`
satisfy `ω(τ r) ≤ γ ω(r) + σ(r)` with `0 < γ, τ < 1`, then `ω(R) ≤ C ((R/R₀)^α ω(R₀) + σ(R^μ R₀^{1−μ}))` with
`C = max(γ⁻¹, (1−γ)⁻¹)` chosen before `μ ∈ (0,1)` and `α = (1−μ) log γ / log τ` chosen before `ω, σ, R₀`. This is a scalar
lemma; it is not an oscillation estimate for any equation.
-/

namespace FunctionalInequalities.Analysis

section Modulus
open Set

private theorem geometric_iterate
    {ω σ : ℝ → ℝ} {γ τ R₀ R₁ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hR₁ : 0 < R₁) (hR₁₀ : R₁ ≤ R₀)
    (hω : MonotoneOn ω (Ioc 0 R₀)) (hσ : MonotoneOn σ (Ioc 0 R₀))
    (hrec : ∀ r ∈ Ioc 0 R₀, ω (τ*r) ≤ γ*ω r + σ r) (k : ℕ) :
    ω (τ^k * R₁) ≤ γ^k * ω R₀ + σ R₁ / (1-γ) * (1-γ^k) := by
  have hd : 1-γ ≠ 0 := ne_of_gt (sub_pos.mpr hγ1)
  have hr (j : ℕ) : τ^j * R₁ ∈ Ioc 0 R₀ := by
    refine ⟨mul_pos (pow_pos hτ _) hR₁, ?_⟩
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.le hτ1.le) hR₁.le).trans (by simpa using hR₁₀)
  induction k with
  | zero => simpa using hω ⟨hR₁,hR₁₀⟩ ⟨hR₁.trans_le hR₁₀,le_rfl⟩ hR₁₀
  | succ k ih =>
    have hs := hσ (hr k) ⟨hR₁,hR₁₀⟩
      (by simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.le hτ1.le) hR₁.le)
    have hc := hrec (τ^k*R₁) (hr k)
    have hi := mul_le_mul_of_nonneg_left ih hγ.le
    calc
      ω (τ^(k+1)*R₁) = ω (τ*(τ^k*R₁)) := by rw [pow_succ',mul_assoc]
      _ ≤ γ*(γ^k*ω R₀ + σ R₁/(1-γ)*(1-γ^k)) + σ R₁ := by linarith
      _ = γ^(k+1)*ω R₀ + σ R₁/(1-γ)*(1-γ^(k+1)) := by
        rw [pow_succ]
        field_simp
        ring

/-- The two-scale estimate in the proof of Gilbarg–Trudinger (2001), Lemma 8.23, pp. 201–202.
Both functions are contextual nonnegative moduli; no PDE conclusion is assumed. -/
theorem two_scale_modulus_bound
    {ω σ : ℝ → ℝ} {γ τ R₀ R₁ R : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hR : 0 < R) (hRR₁ : R ≤ R₁) (hR₁₀ : R₁ ≤ R₀)
    (hω₀ : 0 ≤ ω R₀) (hσ₁ : 0 ≤ σ R₁)
    (hω : MonotoneOn ω (Ioc 0 R₀)) (hσ : MonotoneOn σ (Ioc 0 R₀))
    (hrec : ∀ r ∈ Ioc 0 R₀, ω (τ*r) ≤ γ*ω r + σ r) :
    ω R ≤ γ⁻¹ * (R/R₁) ^ (Real.log γ / Real.log τ) * ω R₀ + σ R₁ / (1-γ) := by
  have hR₁ : 0 < R₁ := hR.trans_le hRR₁
  have hx : 0 < R/R₁ := div_pos hR hR₁
  have hx1 : R/R₁ ≤ 1 := (div_le_one hR₁).2 hRR₁
  obtain ⟨k,hklo,hkhi⟩ := exists_nat_pow_near_of_lt_one hx hx1 hτ hτ1
  have ha : 0 < Real.log γ / Real.log τ := div_pos_of_neg_of_neg
    (Real.log_neg hγ hγ1) (Real.log_neg hτ hτ1)
  have hτlog : Real.log τ ≠ 0 := ne_of_lt (Real.log_neg hτ hτ1)
  have heq : τ ^ (Real.log γ / Real.log τ) = γ := by
    rw [Real.rpow_def_of_pos hτ]
    convert Real.exp_log hγ using 1
    field_simp
  have hpow : γ^(k+1) ≤ (R/R₁) ^ (Real.log γ / Real.log τ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hτ.le (k+1)) hklo.le ha.le
    rw [← Real.rpow_natCast_mul hτ.le, mul_comm, Real.rpow_mul hτ.le,
      heq,Real.rpow_natCast] at hh
    exact hh
  have hgp : γ^k ≤ γ⁻¹ * (R/R₁) ^ (Real.log γ / Real.log τ) := by
    have hm := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hγ.le)
    simpa [pow_succ',← mul_assoc,ne_of_gt hγ] using hm
  have hr : τ^k*R₁ ∈ Ioc 0 R₀ := by
    refine ⟨mul_pos (pow_pos hτ _) hR₁,?_⟩
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.le hτ1.le) hR₁.le).trans (by simpa using hR₁₀)
  have hmon := hω ⟨hR,hRR₁.trans hR₁₀⟩ hr ((div_le_iff₀ hR₁).mp hkhi)
  have hi := geometric_iterate hγ hγ1 hτ hτ1 hR₁ hR₁₀ hω hσ hrec k
  have hE : 0 ≤ σ R₁ / (1-γ) := div_nonneg hσ₁ (sub_pos.mpr hγ1).le
  calc
    ω R ≤ γ^k * ω R₀ + σ R₁/(1-γ)*(1-γ^k) := hmon.trans hi
    _ ≤ γ^k * ω R₀ + σ R₁/(1-γ) := by nlinarith [pow_nonneg hγ.le k]
    _ ≤ γ⁻¹ * (R/R₁) ^ (Real.log γ / Real.log τ) * ω R₀ + σ R₁/(1-γ) := by gcongr

/-- Gilbarg–Trudinger (2001), Lemma 8.23, (8.67), with the explicit admissible choice
`C=max(1/γ,1/(1-γ))` and `α=(1-μ) log γ/log τ`.
Nonnegativity spells out the contextual oscillation/error-modulus convention. -/
theorem modulus_bound_of_scale_contraction
    {ω σ : ℝ → ℝ} {γ τ R₀ R μ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hR : 0 < R) (hRR₀ : R ≤ R₀) (hμ : 0 < μ) (hμ1 : μ < 1)
    (hω₀ : 0 ≤ ω R₀) (hσ₀ : ∀ r ∈ Ioc 0 R₀, 0 ≤ σ r)
    (hω : MonotoneOn ω (Ioc 0 R₀)) (hσ : MonotoneOn σ (Ioc 0 R₀))
    (hrec : ∀ r ∈ Ioc 0 R₀, ω (τ*r) ≤ γ*ω r + σ r) :
    ω R ≤ max γ⁻¹ (1-γ)⁻¹ *
      ((R/R₀) ^ ((1-μ)*(Real.log γ / Real.log τ))*ω R₀ +
        σ (R^μ * R₀^(1-μ))) := by
  have hR₀ : 0 < R₀ := hR.trans_le hRR₀
  let x := R/R₀
  have hx : 0 < x := div_pos hR hR₀
  have hx1 : x ≤ 1 := (div_le_one hR₀).2 hRR₀
  let t := R₀*x^μ
  have ht : 0 < t := mul_pos hR₀ (Real.rpow_pos_of_pos hx _)
  have ht₀ : t ≤ R₀ := by
    dsimp [t]
    simpa using mul_le_mul_of_nonneg_left (Real.rpow_le_one hx.le hx1 hμ.le) hR₀.le
  have hxt : x ≤ x^μ := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hx hx1 hμ1.le
  have hRt : R ≤ t := by
    have hh := mul_le_mul_of_nonneg_left hxt hR₀.le
    dsimp [x,t] at *
    field_simp at hh ⊢
    nlinarith
  have htsource : R^μ*R₀^(1-μ) = t := by
    dsimp [t,x]
    rw [Real.div_rpow hR.le hR₀.le,Real.rpow_sub hR₀,Real.rpow_one]
    ring
  have hratio : R/t = x^(1-μ) := by
    rw [Real.rpow_sub hx,Real.rpow_one]
    dsimp [t,x]
    field_simp
  have he : (R/t) ^ (Real.log γ / Real.log τ) =
      x ^ ((1-μ)*(Real.log γ / Real.log τ)) := by
    rw [hratio,← Real.rpow_mul hx.le]
  have hb := two_scale_modulus_bound hγ hγ1 hτ hτ1 hR hRt ht₀ hω₀ (hσ₀ t ⟨ht,ht₀⟩) hω hσ hrec
  rw [he,← htsource] at hb
  have hA : 0 ≤ x ^ ((1-μ)*(Real.log γ/Real.log τ))*ω R₀ := mul_nonneg (Real.rpow_nonneg hx.le _) hω₀
  have hB : 0 ≤ σ (R^μ*R₀^(1-μ)) := by rw [htsource]; exact hσ₀ t ⟨ht,ht₀⟩
  calc
    ω R ≤ γ⁻¹ * (x ^ ((1-μ)*(Real.log γ/Real.log τ))*ω R₀) +
        (1-γ)⁻¹ * σ (R^μ*R₀^(1-μ)) := by simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hb
    _ ≤ max γ⁻¹ (1-γ)⁻¹ * (x ^ ((1-μ)*(Real.log γ/Real.log τ))*ω R₀) +
        max γ⁻¹ (1-γ)⁻¹ * σ (R^μ*R₀^(1-μ)) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hA)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)
    _ = _ := by rw [mul_add]

/-- Uniform constants in Gilbarg–Trudinger (2001), Lemma 8.23: `C` precedes `μ`,
and α precedes the particular moduli and radii. -/
theorem exists_modulus_bound_of_scale_contraction
    {γ τ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) (hτ : 0 < τ) (hτ1 : τ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ ∈ Ioo (0:ℝ) 1, ∃ α : ℝ, 0 < α ∧
      ∀ (ω σ : ℝ → ℝ) (R₀ : ℝ), 0 ≤ ω R₀ →
      (∀ r ∈ Ioc 0 R₀, 0 ≤ σ r) →
      MonotoneOn ω (Ioc 0 R₀) → MonotoneOn σ (Ioc 0 R₀) →
      (∀ r ∈ Ioc 0 R₀, ω (τ*r) ≤ γ*ω r + σ r) →
      ∀ R ∈ Ioc 0 R₀,
        ω R ≤ C*((R/R₀)^α*ω R₀ + σ (R^μ*R₀^(1-μ))) := by
  refine ⟨max γ⁻¹ (1-γ)⁻¹, lt_of_lt_of_le (inv_pos.mpr hγ) (le_max_left _ _), ?_⟩
  intro μ hμ
  refine ⟨(1-μ)*(Real.log γ/Real.log τ),
    mul_pos (sub_pos.mpr hμ.2) (div_pos_of_neg_of_neg
      (Real.log_neg hγ hγ1) (Real.log_neg hτ hτ1)), ?_⟩
  intro ω σ R₀ hω₀ hσ₀ hω hσ hrec R hR
  exact modulus_bound_of_scale_contraction hγ hγ1 hτ hτ1 hR.1 hR.2 hμ.1 hμ.2 hω₀ hσ₀ hω hσ hrec
end Modulus

end FunctionalInequalities.Analysis

/-! ## Scalar width absorption and the quarter-scale power modulus -/

noncomputable section WidthContraction

open Finset Set

namespace FunctionalInequalities.Analysis

/-- Scalar gap absorption: if `gap ≤ v − w` and `w ≤ C·gap + E` with `C > 0`, then `w ≤ (C/(1+C)) v + E/(1+C)`, with
`0 < C/(1+C) < 1`. -/
theorem contraction_of_gap_bound {w v gap C E : ℝ} (hC : 0 < C)
    (hgap : gap ≤ v-w) (h : w ≤ C*gap+E) :
    0 < C/(1+C) ∧ C/(1+C) < 1 ∧ w ≤ (C/(1+C))*v+E/(1+C) := by
  have hd : 0 < 1+C := by linarith
  refine ⟨div_pos hC hd,(div_lt_one hd).2 (by linarith),?_⟩
  have hmain : w*(1+C) ≤ C*v+E := by nlinarith
  have heq : C/(1+C)*v+E/(1+C) = (C*v+E)/(1+C) := by ring
  rw [heq]
  exact (le_div_iff₀ hd).2 hmain

/-- Finite width contraction: nested intervals `[m_k, M_k] ⊆ [m′_k, M′_k]` with every inner width bounded by
`D ∑_j (M′_j − M_j) + E` satisfy `∑ (M_k − m_k) ≤ θ ∑ (M′_k − m′_k) + N E/(1+C)` with `C = 1 + N D` and `θ = C/(1+C) < 1`. -/
theorem finite_sum_width_contraction {N : ℕ} {D E : ℝ} (hD : 0 ≤ D)
    (outerM outerm innerM innerm : Fin N → ℝ)
    (horder : ∀ k, outerm k ≤ innerm k ∧ innerm k ≤ innerM k ∧ innerM k ≤ outerM k)
    (hwidth : ∀ k, innerM k-innerm k ≤ D*(∑ j, (outerM j-innerM j))+E) :
    let C := 1+(N:ℝ)*D
    0 < C/(1+C) ∧ C/(1+C) < 1 ∧
      (∑ k, (innerM k-innerm k)) ≤ (C/(1+C))*(∑ k, (outerM k-outerm k))+(N:ℝ)*E/(1+C) := by
  intro C
  have hC : 0 < C := by dsimp only [C]; positivity
  have hg0 : 0 ≤ ∑ j, (outerM j-innerM j) :=
    Finset.sum_nonneg fun j _ => sub_nonneg.mpr (horder j).2.2
  have hgap : (∑ j, (outerM j-innerM j)) ≤
      (∑ j, (outerM j-outerm j))-(∑ j, (innerM j-innerm j)) := by
    have hh : (∑ j, (outerM j-innerM j)) ≤ ∑ j, ((outerM j-outerm j)-(innerM j-innerm j)) :=
      Finset.sum_le_sum fun j _ => by linarith [(horder j).1]
    simpa only [Finset.sum_sub_distrib] using hh
  have hs : (∑ k, (innerM k-innerm k)) ≤ (N:ℝ)*(D*(∑ j, (outerM j-innerM j))+E) := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun k _ => hwidth k)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hcontrol : (∑ k, (innerM k-innerm k)) ≤ C*(∑ j, (outerM j-innerM j))+(N:ℝ)*E := by
    calc
      _ ≤ (N:ℝ)*(D*(∑ j, (outerM j-innerM j))+E) := hs
      _ ≤ _ := by dsimp only [C]; nlinarith
  exact contraction_of_gap_bound hC hgap hcontrol

/-- Gilbarg–Trudinger (2001), Lemma 8.23 at `τ = 1/4`, `μ = 1/2`: for `0 < θ < 1`, `W ≥ 0`, `E > 0` there are `0 < η < 1`
and `Q > 0`, chosen before `ω`, such that every monotone `ω` on `(0,1]` with `0 ≤ ω 1 ≤ W` and
`ω(r/4) ≤ θ ω(r) + E (r + r²)` satisfies `ω r ≤ Q r^η` on `(0,1]`. -/
theorem power_modulus_of_quarter_scale_contraction {θ W E : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hW : 0 ≤ W) (hE : 0 < E) :
    ∃ η Q : ℝ, 0 < η ∧ η < 1 ∧ 0 < Q ∧
      ∀ ω : ℝ → ℝ, MonotoneOn ω (Ioc 0 1) → 0 ≤ ω 1 → ω 1 ≤ W →
        (∀ r ∈ Ioc (0:ℝ) 1, ω ((1/4)*r) ≤ θ*ω r+E*(r+r^2)) →
        ∀ r ∈ Ioc (0:ℝ) 1, ω r ≤ Q*r^η := by
  obtain ⟨C,hC,hmod⟩ := exists_modulus_bound_of_scale_contraction
    hθ hθ1 (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) < 1)
  obtain ⟨a,ha,hA⟩ := hmod (1/2) (by constructor <;> norm_num)
  let η := min a (1/2:ℝ)
  have hη : 0 < η := lt_min ha (by norm_num)
  have hη1 : η < 1 := lt_of_le_of_lt (min_le_right a (1/2:ℝ)) (by norm_num)
  let Q := C*(W+2*E)
  have hQ : 0 < Q := mul_pos hC (by linarith)
  refine ⟨η,Q,hη,hη1,hQ,fun ω hω hω0 hωW hrec r hr => ?_⟩
  let σ := fun s : ℝ => E*(s+s^2)
  have hσ0 : ∀ s ∈ Ioc (0:ℝ) 1, 0 ≤ σ s := fun s hs => mul_nonneg hE.le (add_nonneg hs.1.le (sq_nonneg s))
  have hσ : MonotoneOn σ (Ioc (0:ℝ) 1) := by
    intro s hs t ht hst
    dsimp only [σ]
    apply mul_le_mul_of_nonneg_left _ hE.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hst) (add_nonneg hs.1.le ht.1.le)]
  have H := hA ω σ 1 hω0 hσ0 hω hσ hrec r hr
  simp only [div_one,Real.one_rpow,mul_one] at H
  have hra : r^a ≤ r^η := Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2 (min_le_left a (1/2:ℝ))
  have hrh : r^(1/2:ℝ) ≤ r^η := Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2 (min_le_right a (1/2:ℝ))
  have hs0 : 0 ≤ r^(1/2:ℝ) := Real.rpow_nonneg hr.1.le _
  have hs1 : r^(1/2:ℝ) ≤ 1 := Real.rpow_le_one hr.1.le hr.2 (by norm_num)
  have hσr : σ (r^(1/2:ℝ)) ≤ 2*E*r^η := by
    dsimp only [σ]
    have hsq : (r^(1/2:ℝ))^2 ≤ r^(1/2:ℝ) := by nlinarith
    have htwo : E*(r^(1/2:ℝ)+(r^(1/2:ℝ))^2) ≤ 2*E*r^(1/2:ℝ) := by nlinarith
    exact htwo.trans (mul_le_mul_of_nonneg_left hrh (by positivity))
  calc
    _ ≤ C*(r^a*ω 1+σ (r^(1/2:ℝ))) := H
    _ ≤ C*(r^η*W+2*E*r^η) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul hra hωW hω0 (Real.rpow_nonneg hr.1.le η)) hσr) hC.le
    _ = Q*r^η := by dsimp only [Q]; ring

end FunctionalInequalities.Analysis

end WidthContraction
