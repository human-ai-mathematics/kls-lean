module

public import FunctionalInequalities.Analysis.Matrix.LogDet.Inequalities
public import FunctionalInequalities.Analysis.Matrix.RankOneFrame
public import FunctionalInequalities.Analysis.MeasureGrowth
public import FunctionalInequalities.Analysis.EssentialExtrema.Basic
public import FunctionalInequalities.Analysis.EssentialExtrema.Oscillation
public import FunctionalInequalities.Analysis.MeasureAverage
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Frame oscillation of a log-determinant matrix field

For a matrix field `P` with `P ≻ 0`, `P ≤ K·I` and `log det P = V` a.e. (`V` Lipschitz), and
coefficient matrix `ρ P⁻¹`
in `[α, β]` decomposing in one fixed unit rank-one frame: the pairwise essential deficit comparison,
the averaged deficit bound
from an essential weak Harnack law at `p = 1`, and the resulting essential oscillation decay of the
frame directions. This is
the rough-divergence form of Gilbarg–Trudinger (2001), Lemma 17.14 with the frame of Lemma 17.13.
The frame and the Harnack
law are explicit premises; no PDE module is imported. It is not the classical `C⁴` Lemma 17.14.
-/

@[expose] public section

/-! ## Pairwise comparison, averaged deficits and oscillation decay -/

section FrameOscillation

open MeasureTheory Matrix Set Metric Filter Finset

namespace FunctionalInequalities.Analysis

private theorem quadratic_eq {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    dotProduct v (P.mulVec v) = ∑ i, ∑ j, v i * v j * P i j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/--
Pairwise essential deficit comparison for a matrix field `P` with `P ≻ 0`, `P ≤ K·I` and `log det P
= V` a.e. (`V`
Lipschitz), and coefficient matrix `ρ P⁻¹ ∈ [α, β]` a.e. on `S` (`0 ≤ ρ ≤ B` on `S`), whose matrices
decompose in one fixed
unit frame with coefficients in `[lc, uc]`. For `B̄(x0, 4R) ⊆ S` and the caps `M_k =
essSup_{B(x0,4R)} γ_kᵀ P γ_k`: a.e.
`y ∈ B(x0,R)`, a.e. `x ∈ B(x0,2R)`, `lc (M_k − q_k y) ≤ uc ∑_j (M_j − q_j x) + 3 B L R`. -/
theorem pairwise_essential_deficit_comparison_of_fixed_frame {n N : ℕ}
    (P : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (V ρ : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    {K α β B lc uc : ℝ} (hα : 0 < α) (hB : 0 ≤ B) (hlc : 0 ≤ lc) (hρ : ∀ x, 0 ≤ ρ x)
    (hρB : ∀ x ∈ S, ρ x ≤ B) (hV : LipschitzWith L V)
    (hP :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (P x).PosDef ∧
          (K • (1 : Matrix (Fin n) (Fin n) ℝ) - P x).PosSemidef ∧ Real.log (P x).det = V x)
    (hA :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
        (ρ x • (P x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - ρ x • (P x)⁻¹).PosSemidef)
    (γ : Fin N → Fin n → ℝ) (hγ : ∀ k, ∑ i, (γ k i) ^ 2 = 1)
    (hframe :
      ∀ A : Matrix (Fin n) (Fin n) ℝ,
        A.PosDef →
          (A - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef →
            (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef →
              ∃ b : Fin N → ℝ,
                (∀ k, lc ≤ b k ∧ b k ≤ uc) ∧ A = ∑ k, b k • vecMulVec (γ k) (γ k))
    (x0 : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) (hBS : closedBall x0 (4 * R) ⊆ S) :
    let q := fun k x => ∑ i : Fin n, ∑ j : Fin n, γ k i * γ k j * P x i j
    let M := fun k =>
      essSup (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (4 * R)))
    ∀ k,
      ∀ᵐ y ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)),
        ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (2 * R))),
          lc * (M k - q k y) ≤ uc * (∑ j, (M j - q j x)) + 3 * B * (L : ℝ) * R := by
  intro q M k
  let μ4 := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (4 * R))
  let μ2 := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (2 * R))
  let μ1 := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)
  have hqK (j : Fin N) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ q j x ∧ q j x ≤ K := by
    filter_upwards [hP] with x hx
    have h0 := hx.1.posSemidef.dotProduct_mulVec_nonneg (γ j)
    have h1 := hx.2.1.dotProduct_mulVec_nonneg (γ j)
    have hunit : dotProduct (γ j) (γ j) = 1 := by simpa only [dotProduct, ← pow_two] using hγ j
    simp only [star_trivial] at h0 h1
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, hunit, mul_one, quadratic_eq] at h1
    rw [quadratic_eq] at h0
    exact ⟨h0, by dsimp only [q]; linarith⟩
  have hcap4 : ∀ᵐ x ∂μ4, ∀ j, q j x ≤ M j := by
    apply ae_all_iff.mpr
    intro j
    exact ae_le_essSup ⟨K, (ae_restrict_of_ae (hqK j)).mono fun _ h => h.2⟩
  have hμ24 : μ2 ≤ μ4 := Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl
  have hμ14 : μ1 ≤ μ4 := Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl
  have hxS : ball x0 (2 * R) ⊆ S :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hBS
  have hA2 := ae_restrict_of_ae_restrict_of_subset hxS hA
  have hP2 :
    ∀ᵐ x ∂μ2,
      (P x).PosDef ∧
        (K • (1 : Matrix (Fin n) (Fin n) ℝ) - P x).PosSemidef ∧ Real.log (P x).det = V x :=
    ae_restrict_of_ae hP
  have hP1 :
    ∀ᵐ x ∂μ1,
      (P x).PosDef ∧
        (K • (1 : Matrix (Fin n) (Fin n) ℝ) - P x).PosSemidef ∧ Real.log (P x).det = V x :=
    ae_restrict_of_ae hP
  filter_upwards [hP1, (Measure.absolutelyContinuous_of_le hμ14).ae_le hcap4,
    ae_restrict_mem measurableSet_ball] with y hy hMy hym
  filter_upwards [hP2, hA2, (Measure.absolutelyContinuous_of_le hμ24).ae_le hcap4,
    ae_restrict_mem measurableSet_ball] with x hx hAx hMx hxm
  have hApd : (ρ x • (P x)⁻¹).PosDef := by
    have h := (Matrix.PosDef.one.smul hα).add_posSemidef hAx.1
    simpa only [add_sub_cancel] using h
  obtain ⟨b, hb, hdecomp⟩ := hframe _ hApd hAx.1 hAx.2
  have hdist : dist x y ≤ 3 * R := by
    have ht := dist_triangle x x0 y
    have hxx := Metric.mem_ball.mp hxm
    have hyy := Metric.mem_ball.mp hym
    rw [dist_comm x0 y] at ht
    linarith
  have hVabs : |V x - V y| ≤ (L : ℝ) * (3 * R) := by
    have hv := hV.dist_le_mul x y
    rw [Real.dist_eq] at hv
    exact hv.trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
  have hE : ρ x * (Real.log (P x).det - Real.log (P y).det) ≤ 3 * B * (L : ℝ) * R := by
    rw [hx.2.2, hy.2.2]
    calc
      _ ≤ ρ x * |V x - V y| := mul_le_mul_of_nonneg_left (le_abs_self _) (hρ x)
      _ ≤ B * ((L : ℝ) * (3 * R)) := mul_le_mul (hρB x (hxS hxm)) hVabs (abs_nonneg _) hB
      _ = _ := by ring
  exact
    directional_deficit_le_sum_of_logdet (P x) (P y) γ b M hx.1 hy.1 hx.2.1 hy.2.1 (hρ x) hlc hb
      hdecomp hMx hMy hE k

/--
From a weak Harnack law at `p = 1` for the deficits `M − q_k` (closed-ball cap, forcing `M B R²/α`),
the averaged
deficits on `B(x0, 2R)` are bounded by `(C_h/m) (essSup_{B4R} q_k − essSup_{BR} q_k) + (C_h/m) (K
B/α) R²` with
`m = |B(0,1)| · 2ⁿ`. The closed-ball cap comes from the open-ball essential supremum through the
null sphere. -/
theorem averaged_deficit_bound_of_essential_harnack {n N : ℕ}
    (q : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (S : Set (EuclideanSpace ℝ (Fin n)))
    {K B α Ch : ℝ} (hB : 0 ≤ B) (hα : 0 < α) (hCh : 0 ≤ Ch)
    (hql : ∀ k, LocallyIntegrable (q k) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hq0 : ∀ k, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ q k x)
    (hqK : ∀ k, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), q k x ≤ K)
    (hH :
      ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ),
        0 < R →
          closedBall x0 (4 * R) ⊆ S →
            ∀ (k : Fin N) (M : ℝ),
              0 ≤ M →
                (∀ᵐ
                    x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
                      (closedBall x0 (4 * R))),
                    q k x ≤ M) →
                  (ENNReal.ofReal R) ^ (-(n : ℝ)) *
                      eLpNorm (fun x => M - q k x) 1
                        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
                          (ball x0 (2 * R))) ≤
                    ENNReal.ofReal Ch *
                      (essInf (fun x => ENNReal.ofReal (M - q k x))
                          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) +
                        ENNReal.ofReal (M * B * R ^ 2 / α))) :
    let m := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (2 : ℝ) ^ n
    ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ),
      0 < R →
        closedBall x0 (4 * R) ⊆ S →
          let μ4 := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (4 * R))
          let μ2 := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (2 * R))
          let μ1 := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)
          ∀ k : Fin N,
            (∫ x, (essSup (q k) μ4 - q k x) ∂μ2) / μ2.real Set.univ ≤
              (Ch / m) * (essSup (q k) μ4 - essSup (q k) μ1) + (Ch / m) * (K * B / α) * R ^ 2 := by
  intro m x0 R hR hBS μ4 μ2 μ1 k
  let : NeZero μ4 := ⟨restricted_ball_ne_zero x0 (by linarith : 0 < 4 * R)⟩
  let : NeZero μ1 := ⟨restricted_ball_ne_zero x0 hR⟩
  let : IsFiniteMeasure μ2 := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let M := essSup (q k) μ4
  have h0out : ∀ᵐ x ∂μ4, 0 ≤ q k x := ae_restrict_of_ae (hq0 k)
  have hKout : ∀ᵐ x ∂μ4, q k x ≤ K := ae_restrict_of_ae (hqK k)
  have hext := real_essential_bounds μ4 (q k) h0out hKout
  have hM0 : 0 ≤ M := hext.1.trans hext.2.1
  have hMK : M ≤ K := hext.2.2.1
  have hcap4 : ∀ᵐ x ∂μ4, q k x ≤ M := hext.2.2.2.mono fun _ hx => hx.2
  have hcapclosed :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall x0 (4 * R))),
      q k x ≤ M := by
    rw [restrict_closedBall_eq_ball x0 (by linarith : 0 < 4 * R)]
    exact hcap4
  have h14 : μ1 ≤ μ4 := Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl
  have h24 : μ2 ≤ μ4 := Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl
  have h0in : ∀ᵐ x ∂μ1, 0 ≤ q k x := ae_restrict_of_ae (hq0 k)
  have hcapin : ∀ᵐ x ∂μ1, q k x ≤ M := (Measure.absolutelyContinuous_of_le h14).ae_le hcap4
  have hgap : 0 ≤ M - essSup (q k) μ1 := by
    apply sub_nonneg.mpr
    exact (real_essential_bounds_mono_measure μ4 μ1 h14 (q k) h0out hKout).2
  have hforce : 0 ≤ M * B * R ^ 2 / α := by positivity
  have HH := hH x0 R hR hBS k M hM0 hcapclosed
  rw [essInf_ofReal_deficit_eq_sub_essSup μ1 (q k) M h0in hcapin, ←
    ENNReal.ofReal_add hgap hforce] at HH
  have hqi : Integrable (q k) μ2 :=
    ((hql k).integrableOn_isCompact (isCompact_closedBall x0 (2 * R))).mono_set
      Metric.ball_subset_closedBall
  have hdint : Integrable (fun x => M - q k x) μ2 := (integrable_const _).sub hqi
  have hcap2 : ∀ᵐ x ∂μ2, q k x ≤ M := (Measure.absolutelyContinuous_of_le h24).ae_le hcap4
  have hd0 : ∀ᵐ x ∂μ2, 0 ≤ M - q k x := hcap2.mono fun _ hx => sub_nonneg.mpr hx
  have hv : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ 0 one_pos).ne' measure_ball_lt_top.ne
  have hm : 0 < m := mul_pos hv (pow_pos (by norm_num) n)
  have hmass : μ2.real Set.univ = m * R ^ (n : ℝ) :=
    restricted_ball_real_mass x0 (by norm_num) hR
  have ha :=
    average_le_of_normalized_eLpNorm_one μ2 (fun x => M - q k x) hdint hd0 hR hCh
      (add_nonneg hgap hforce) hm hmass HH
  have hcoef : 0 ≤ Ch / m := div_nonneg hCh hm.le
  calc
    _ ≤ Ch * ((M - essSup (q k) μ1) + M * B * R ^ 2 / α) / m := ha
    _ = (Ch / m) * ((M - essSup (q k) μ1) + M * B * R ^ 2 / α) := by ring
    _ ≤ (Ch / m) * ((M - essSup (q k) μ1) + K * B * R ^ 2 / α) := by gcongr
    _ = _ := by ring

/--
Essential oscillation decay of the frame directions of a log-determinant matrix field (the
rough-divergence form of
Gilbarg–Trudinger (2001), Lemma 17.14, with the frame of Lemma 17.13). With a fixed unit frame for
the coefficient range
`[α, β]` and an essential weak Harnack law for its directional deficits as explicit premises, there
are `0 < θ < 1` and
`C > 0`, chosen before every ball, such that the summed essential widths on `B(x0,R)` are at most
`θ` times those on
`B(x0,4R)` plus `C (R + R²)` whenever `B̄(x0,4R) ⊆ S`. -/
theorem oscillation_of_fixed_frame_and_essential_harnack {n N : ℕ}
    (P : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (V ρ : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    {K α β B lc uc Ch : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hB : 0 ≤ B) (hlc : 0 < lc) (huc : 0 ≤ uc)
    (hCh : 0 ≤ Ch)
    (hPl :
      ∀ i j, LocallyIntegrable (fun x => P x i j) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hρ : ∀ x, 0 ≤ ρ x) (hρB : ∀ x ∈ S, ρ x ≤ B) (hV : LipschitzWith L V)
    (hP :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (P x).PosDef ∧
          (K • (1 : Matrix (Fin n) (Fin n) ℝ) - P x).PosSemidef ∧ Real.log (P x).det = V x)
    (hA :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
        (ρ x • (P x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - ρ x • (P x)⁻¹).PosSemidef)
    (γ : Fin N → Fin n → ℝ) (hγ : ∀ k, ∑ i, (γ k i) ^ 2 = 1)
    (hframe :
      ∀ A : Matrix (Fin n) (Fin n) ℝ,
        A.PosDef →
          (A - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef →
            (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef →
              ∃ b : Fin N → ℝ,
                (∀ k, lc ≤ b k ∧ b k ≤ uc) ∧ A = ∑ k, b k • vecMulVec (γ k) (γ k))
    (hH :
      ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ),
        0 < R →
          closedBall x0 (4 * R) ⊆ S →
            ∀ (k : Fin N) (M : ℝ),
              0 ≤ M →
                (∀ᵐ
                    x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
                      (closedBall x0 (4 * R))),
                    (∑ i, ∑ j, γ k i * γ k j * P x i j) ≤ M) →
                  (ENNReal.ofReal R) ^ (-(n : ℝ)) *
                      eLpNorm (fun x => M - ∑ i, ∑ j, γ k i * γ k j * P x i j) 1
                        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
                          (ball x0 (2 * R))) ≤
                    ENNReal.ofReal Ch *
                      (essInf (fun x => ENNReal.ofReal (M - ∑ i, ∑ j, γ k i * γ k j * P x i j))
                          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) +
                        ENNReal.ofReal (M * B * R ^ 2 / α))) :
    let q := fun k x => ∑ i : Fin n, ∑ j : Fin n, γ k i * γ k j * P x i j
    ∃ θ C : ℝ,
      0 < θ ∧
        θ < 1 ∧
          0 < C ∧
            ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ),
              0 < R →
                closedBall x0 (4 * R) ⊆ S →
                  (∑ k,
                      (essSup (q k)
                          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) -
                        essInf (q k)
                          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
                            (ball x0 R)))) ≤
                    θ *
                        (∑ k,
                          (essSup (q k)
                              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
                                (ball x0 (4 * R))) -
                            essInf (q k)
                              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
                                (ball x0 (4 * R))))) +
                      C * (R + R ^ 2) := by
  intro q
  have hqb (k : Fin N) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ q k x ∧ q k x ≤ K := by
    filter_upwards [hP] with x hx
    exact unit_quadratic_bounds (P x) (γ k) hx.1.posSemidef hx.2.1 (hγ k)
  have hql (k : Fin N) :
    LocallyIntegrable (q k) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro A hAc
    exact
      integrable_finsetSum _
        (fun i _ =>
          integrable_finsetSum _
            (fun j _ => ((hPl i j).integrableOn_isCompact hAc).const_mul (γ k i * γ k j)))
  let m := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (2 : ℝ) ^ n
  have hv : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ 0 one_pos).ne' measure_ball_lt_top.ne
  have hm : 0 < m := mul_pos hv (pow_pos (by norm_num) n)
  let Hc := Ch / m
  have hHc : 0 ≤ Hc := div_nonneg hCh hm.le
  let C0 : ℝ := 1 + (N : ℝ) * (uc / lc * Hc)
  have hC0 : 0 < C0 := by dsimp only [C0]; positivity
  have hden : 0 < 1 + C0 := by linarith
  let θ := C0 / (1 + C0)
  have hθ0 : 0 < θ := div_pos hC0 hden
  have hθ1 : θ < 1 := (div_lt_one hden).2 (by linarith)
  let Ca : ℝ := (N : ℝ) * ((uc / lc) * (N : ℝ) * Hc * (K * B / α)) / (1 + C0)
  let Cb : ℝ := (N : ℝ) * (3 * B * (L : ℝ) / lc) / (1 + C0)
  have hCa : 0 ≤ Ca := by dsimp only [Ca]; positivity
  have hCb : 0 ≤ Cb := by dsimp only [Cb]; positivity
  refine ⟨θ, 1 + Ca + Cb, hθ0, hθ1, by positivity, fun x0 R hR hBS => ?_⟩
  let μ4 := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (4 * R))
  let μ2 := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (2 * R))
  let μ1 := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)
  let : NeZero μ4 := ⟨restricted_ball_ne_zero x0 (by linarith : 0 < 4 * R)⟩
  let : NeZero μ2 := ⟨restricted_ball_ne_zero x0 (by linarith : 0 < 2 * R)⟩
  let : NeZero μ1 := ⟨restricted_ball_ne_zero x0 hR⟩
  let : IsFiniteMeasure μ2 := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have h24 : μ2 ≤ μ4 := Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl
  have h12 : μ1 ≤ μ2 := Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl
  have hqi (k : Fin N) : Integrable (q k) μ2 :=
    ((hql k).integrableOn_isCompact (isCompact_closedBall x0 (2 * R))).mono_set
      Metric.ball_subset_closedBall
  have hp :=
    pairwise_essential_deficit_comparison_of_fixed_frame P V ρ L S hα hB hlc.le hρ hρB hV hP hA
      γ hγ hframe x0 hR hBS
  have ha :=
    averaged_deficit_bound_of_essential_harnack q S hB hα hCh hql
      (fun k => (hqb k).mono fun _ hx => hx.1) (fun k => (hqb k).mono fun _ hx => hx.2) hH x0 R
      hR hBS
  have hc :=
    finite_essential_width_contraction μ4 μ2 μ1 h24 h12 q hlc huc hHc hqi
      (fun k => ae_restrict_of_ae ((hqb k).mono fun _ hx => hx.1))
      (fun k => ae_restrict_of_ae ((hqb k).mono fun _ hx => hx.2)) hp ha
  change
    0 < θ ∧
      θ < 1 ∧
        (∑ k, (essSup (q k) μ1 - essInf (q k) μ1)) ≤
          θ * (∑ k, (essSup (q k) μ4 - essInf (q k) μ4)) +
            (N : ℝ) *
                ((uc / lc) * (N : ℝ) * (Hc * (K * B / α) * R ^ 2) +
                  (3 * B * (L : ℝ) * R) / lc) /
              (1 + C0) at hc
  have he :
    (N : ℝ) * ((uc / lc) * (N : ℝ) * (Hc * (K * B / α) * R ^ 2) + (3 * B * (L : ℝ) * R) / lc) /
        (1 + C0) =
      Ca * R ^ 2 + Cb * R := by
    dsimp only [Ca, Cb]; ring
  rw [he] at hc
  have herr : Ca * R ^ 2 + Cb * R ≤ (1 + Ca + Cb) * (R + R ^ 2) := by
    nlinarith [mul_nonneg hCa hR.le, mul_nonneg hCb (sq_nonneg R), sq_nonneg R]
  exact hc.2.2.trans (add_le_add le_rfl herr)

end FunctionalInequalities.Analysis

end FrameOscillation
