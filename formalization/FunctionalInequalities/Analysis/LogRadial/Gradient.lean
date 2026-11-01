module

public import FunctionalInequalities.Analysis.LogRadial.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# First derivative bound of the CNS barrier profile (CNS1984 Lemma 5.1, p. 386; drift support)

For the barrier profile `Φ = (√S + (p - β) - ε q log S) / 2` with `S = (p - β)² + q²`, real
continuous linear
functionals `p`, `q` of norm at most `1` on an arbitrary real normed space, `ε ≥ 0` and `0 < q x`:
`‖DΦ(x)‖ ≤ 2 + ε (|log S(x)| + 2)`. The constant `2` is a conservative derived support constant.

Proof: by the first-derivative producer `hasFDerivAt_log_radial_barrier`,
`DΦ = ½ (R' + p + ε L')` with `R' = (2r)⁻¹ S'` and `L' = -q S⁻¹ S' - log S · q`, where `S' = 2(p -
β) p + 2 q q`
and `r = √S`. Since `|p - β|, |q| ≤ r`, we get `‖R'‖ ≤ 2` and `‖L'‖ ≤ 4 + |log S|`.

* `fderiv_log_radial_profile_norm_le`: the generic bound.
* `tangent_normal_log_radial_profile_fderiv_norm_le`: in `ℝ^{m+1}` with `p = ⟨ζ, ·⟩` (`‖ζ‖ ≤ 1`) and
  `q` the last
  coordinate; no tangency or orthogonality is needed.
-/

@[expose] public section

section
open Filter
open scoped Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

theorem fderiv_log_radial_profile_norm_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p q : G →L[ℝ] ℝ) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (β ε : ℝ) (hε : 0 ≤ ε) {x : G}
    (hx : 0 < q x) :
    ‖fderiv ℝ
          (fun y : G =>
            (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) -
                ε * q y * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) /
              2)
          x‖ ≤
      2 + ε * (|Real.log ((p x - β) ^ 2 + (q x) ^ 2)| + 2) := by
  -- the shared profile first-derivative producer at `x`

  rw [(hasFDerivAt_log_radial_profile_of_pos p q β ε
        (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hx 2))).fderiv]
  -- scalar data at `x`

  set s := p x - β with hs
  set t := q x with ht
  have hS : 0 < s ^ 2 + t ^ 2 := by positivity
  set r := Real.sqrt (s ^ 2 + t ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hS
  have hr2 : r ^ 2 = s ^ 2 + t ^ 2 := Real.sq_sqrt hS.le
  have hsr : |s| ≤ r := Real.abs_le_sqrt (by nlinarith)
  have htr : |t| ≤ r :=
    Real.abs_le_sqrt
      (by nlinarith)
  -- `‖S'‖ ≤ 2 |s| + 2 |t|`

  have hS' : ‖(2 * s) • p + (2 * t) • q‖ ≤ 2 * |s| + 2 * |t| := by
    calc
      ‖(2 * s) • p + (2 * t) • q‖ ≤ ‖(2 * s) • p‖ + ‖(2 * t) • q‖ := norm_add_le _ _
      _ = |2 * s| * ‖p‖ + |2 * t| * ‖q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |2 * s| * 1 + |2 * t| * 1 := by gcongr
      _ = 2 * |s| + 2 * |t| := by
        rw [abs_mul, abs_mul, abs_two];
        ring
  -- radial: `‖R'‖ ≤ 2`

  have hRn : ‖(1 / (2 * r)) • ((2 * s) • p + (2 * t) • q)‖ ≤ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      1 / (2 * r) * ‖(2 * s) • p + (2 * t) • q‖ ≤ 1 / (2 * r) * (2 * |s| + 2 * |t|) :=
        mul_le_mul_of_nonneg_left hS' (by positivity)
      _ ≤ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  -- logarithmic: `‖L'‖ ≤ 4 + |log S|`

  have hLn :
    ‖(-t) • ((s ^ 2 + t ^ 2)⁻¹ • ((2 * s) • p + (2 * t) • q)) +
          Real.log (s ^ 2 + t ^ 2) • (-q)‖ ≤
      4 + |Real.log (s ^ 2 + t ^ 2)| := by
    have h1 : ‖(-t) • ((s ^ 2 + t ^ 2)⁻¹ • ((2 * s) • p + (2 * t) • q))‖ ≤ 4 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
        abs_of_pos (inv_pos.mpr hS)]
      calc
        |t| * ((s ^ 2 + t ^ 2)⁻¹ * ‖(2 * s) • p + (2 * t) • q‖) ≤
            |t| * ((s ^ 2 + t ^ 2)⁻¹ * (2 * |s| + 2 * |t|)) := by
          gcongr
        _ = (|t| * (2 * |s| + 2 * |t|)) / (s ^ 2 + t ^ 2) := by field_simp
        _ ≤ 4 := by
          rw [div_le_iff₀ hS, ← hr2]
          nlinarith [abs_nonneg s, abs_nonneg t]
    have h2 : ‖Real.log (s ^ 2 + t ^ 2) • (-q)‖ ≤ |Real.log (s ^ 2 + t ^ 2)| := by
      rw [norm_smul, norm_neg, Real.norm_eq_abs]
      calc
        |Real.log (s ^ 2 + t ^ 2)| * ‖q‖ ≤ |Real.log (s ^ 2 + t ^ 2)| * 1 := by gcongr
        _ = |Real.log (s ^ 2 + t ^ 2)| := mul_one _
    linarith [norm_add_le ((-t) • ((s ^ 2 + t ^ 2)⁻¹ • ((2 * s) • p + (2 * t) • q)))
        (Real.log (s ^ 2 + t ^ 2) • (-q))]
  -- assemble `‖½ (R' + p + ε L')‖`

  have hlog0 : 0 ≤ |Real.log (s ^ 2 + t ^ 2)| := abs_nonneg _
  calc
    ‖(2⁻¹ : ℝ) •
            ((1 / (2 * r)) • ((2 * s) • p + (2 * t) • q) + p +
              ε •
                ((-t) • ((s ^ 2 + t ^ 2)⁻¹ • ((2 * s) • p + (2 * t) • q)) +
                  Real.log (s ^ 2 + t ^ 2) • (-q)))‖ ≤
        2⁻¹ *
          (‖(1 / (2 * r)) • ((2 * s) • p + (2 * t) • q)‖ + ‖p‖ +
            ε *
              ‖(-t) • ((s ^ 2 + t ^ 2)⁻¹ • ((2 * s) • p + (2 * t) • q)) +
                  Real.log (s ^ 2 + t ^ 2) • (-q)‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
      gcongr
      refine (norm_add_le _ _).trans ?_
      gcongr
      · exact norm_add_le _ _
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
    _ ≤ 2⁻¹ * (2 + 1 + ε * (4 + |Real.log (s ^ 2 + t ^ 2)|)) := by gcongr
    _ ≤ 2 + ε * (|Real.log (s ^ 2 + t ^ 2)| + 2) := by nlinarith [mul_nonneg hε hlog0]

theorem tangent_normal_log_radial_profile_fderiv_norm_le {m : ℕ}
    (zeta : EuclideanSpace ℝ (Fin (m + 1))) (hz : ‖zeta‖ ≤ 1)
    (β ε : ℝ) (hε : 0 ≤ ε) {x : EuclideanSpace ℝ (Fin (m + 1))}
    (hx : 0 < x (Fin.last m)) :
    ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (Real.sqrt (((∑ i, zeta i * y i) - β) ^ 2 + (y (Fin.last m)) ^ 2) +
        ((∑ i, zeta i * y i) - β) - ε * y (Fin.last m) *
          Real.log (((∑ i, zeta i * y i) - β) ^ 2 + (y (Fin.last m)) ^ 2)) / 2) x‖ ≤
      2 + ε * (|Real.log (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last m)) ^ 2)| + 2) := by
  set p : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ := innerSL ℝ zeta with hpdef
  set q : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last m) with hqdef
  have hp : ‖p‖ ≤ 1 := by rw [hpdef, innerSL_apply_norm]; exact hz
  have hq : ‖q‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    rw [one_mul, hqdef]
    exact PiLp.norm_apply_le y (Fin.last m)
  have hpy : ∀ y, p y = ∑ i, zeta i * y i := fun y => by
    simp [hpdef, PiLp.inner_apply, mul_comm]
  have hqy : ∀ y, q y = y (Fin.last m) := fun _ => rfl
  have h := fderiv_log_radial_profile_norm_le p q hp hq β ε hε (x := x) hx
  simp only [hpy, hqy] at h
  exact h

end FunctionalInequalities.Analysis

end
