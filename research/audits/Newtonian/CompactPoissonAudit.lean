module

public import FunctionalInequalities.Analysis.Newtonian.Schauder.CompactPoisson
public import FunctionalInequalities.Analysis.Holder.Cutoff

/-!
# Audit: GT Theorem 4.5 for compactly supported Poisson solutions

Real clients of `compactPoisson_GT4_5`
(`FunctionalInequalities/Analysis/Newtonian/Schauder/CompactPoisson.lean`;
Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001, Theorem
4.5,
p. 60) with `α = 3/4` and the ball `B = B_2(0)` (`R = 2`, diameter `4`):

* (a) `n = 2`: the smooth bump `u = β` with `β = 1` on `B̄_1(0)`, `planar_bump_GT4_5`;
* (b) `n = 3`: the signed function `u(y) = β(y) y₀`, which takes both signs, `spatial_signed_GT4_5`.

The solutions are actual smooth compactly supported functions; the sources are derived as `f = Δu`;
compact
support, `C²`, the source condition (uniformly `3/4`-Hölder on every compact set) and `tsupport u ⊆
B_2(0)` are
proved. The constants `C₁, C₂` are the theorem's constants (chosen there before `u`); `M, H` are
derived.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal
open FunctionalInequalities.Analysis.BakryEmery

namespace CompactPoissonAudit

open FunctionalInequalities.Analysis

/--
A `C¹` function on `ℝⁿ` is uniformly `α`-Hölder (`α ≤ 1`) on every compact set: the source condition
of pp. 51–53. -/
theorem holderOnWith_compact_of_contDiff_one {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContDiff ℝ 1 g) {α : ℝ≥0} (hα : α ≤ 1) :
    ∀ K, IsCompact K → ∃ H : ℝ≥0, HolderOnWith H α g K := by
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨L, hL⟩ :=
    hg.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 r)
      (isCompact_closedBall 0 r)
  refine
    ⟨_,
      holderOnWith_of_dist_le_mul_of_diam (d := 2 * |r|) L.coe_nonneg (by positivity) hα
        (fun x hx y hy => ?_) (fun x hx y hy => hL.dist_le_mul x (hr hx) y (hr hy))⟩
  have hx' := hr hx
  have hy' := hr hy
  rw [mem_closedBall, dist_zero_right] at hx' hy'
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le x y
    _ ≤ 2 * |r| := by linarith [le_abs_self r]

theorem three_quarters_pos : (0 : ℝ≥0) < 3 / 4 := by rw [← NNReal.coe_lt_coe]; norm_num

theorem three_quarters_lt_one : (3 / 4 : ℝ≥0) < 1 := by rw [← NNReal.coe_lt_coe]; norm_num

/-! ### (a) `n = 2`: the unit bump -/

/-- Smooth bump on `ℝ²`, equal to `1` on `B̄_1(0)` and supported in `B̄_{3/2}(0) ⊂ B_2(0)`. -/
def planarBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) := ⟨1, 3 / 2, by norm_num, by norm_num⟩

/-- The planar solution `u = β`. -/
def planarU (y : EuclideanSpace ℝ (Fin 2)) : ℝ := planarBump y

/-- The derived planar source `f = Δu`. -/
def planarF : EuclideanSpace ℝ (Fin 2) → ℝ := Laplacian.laplacian planarU

theorem planarU_zero : planarU 0 = 1 :=
  planarBump.one_of_mem_closedBall (mem_closedBall_self planarBump.rIn_pos.le)

theorem planarU_tsupport : tsupport planarU ⊆ ball 0 2 := by
  change tsupport planarBump ⊆ _
  rw [planarBump.tsupport_eq]; exact closedBall_subset_ball (show (3 / 2 : ℝ) < 2 by norm_num)

theorem planarF_localHolder : ∀ K, IsCompact K → ∃ H : ℝ≥0, HolderOnWith H (3 / 4) planarF K :=
  holderOnWith_compact_of_contDiff_one
    (contDiff_laplacian (planarBump.contDiff (n := 3)) (by norm_num)) three_quarters_lt_one.le

/-- (a) GT2001 Theorem 4.5 for the planar bump: compact source support, the representation (4.15)
(with value `1` at `0`), a
global Hölder cap of the actual Hessian, and on `B_2(0)` derived source bounds with both estimates
(4.14). -/
theorem planar_bump_GT4_5 :
    planarU 0 = 1 ∧ (HasCompactSupport planarF ∧ tsupport planarF ⊆ tsupport planarU) ∧
    (∀ x, Integrable (fun y => newtonianKernel 2 (x - y) * planarF y) volume ∧
      planarU x = ∫ y, newtonianKernel 2 (x - y) * planarF y) ∧
    (∫ y, newtonianKernel 2 (0 - y) * planarF y) = 1 ∧
    (∃ K : ℝ≥0, HolderWith K (3 / 4) (fderiv ℝ (fderiv ℝ planarU))) ∧
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧ ∃ M : ℝ, ∃ H : ℝ≥0,
      (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 2, |planarF y| ≤ M) ∧ HolderOnWith H (3 / 4)
        planarF (ball 0 2) ∧
      HolderWith (Real.toNNReal (C2 * ((2 * 2) ^ (-((3 / 4 : ℝ≥0) : ℝ)) * M + H))) (3 / 4) (fderiv
        ℝ (fderiv ℝ planarU)) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ planarU) x‖ ≤ C2 * (M + (2 * 2) ^ ((3 / 4 : ℝ≥0) : ℝ) * H)) ∧
      (∀ x z, ‖fderiv ℝ (fderiv ℝ planarU) x - fderiv ℝ (fderiv ℝ planarU) z‖ ≤
        C2 * ((2 * 2) ^ (-((3 / 4 : ℝ≥0) : ℝ)) * M + H) * ‖x - z‖ ^ ((3 / 4 : ℝ≥0) : ℝ)) ∧
      (∀ x y z, y ≠ z → ‖fderiv ℝ (fderiv ℝ planarU) x‖ + (2 * 2) ^ ((3 / 4 : ℝ≥0) : ℝ) *
        (‖fderiv ℝ (fderiv ℝ planarU) y - fderiv ℝ (fderiv ℝ planarU) z‖ / ‖y - z‖ ^ ((3 / 4 :
          ℝ≥0) : ℝ)) ≤
        C2 * (M + (2 * 2) ^ ((3 / 4 : ℝ≥0) : ℝ) * H)) ∧
      (∀ x z, |planarU x| + 2 * 2 * ‖fderiv ℝ planarU z‖ ≤ C1 * 2 ^ 2 * M) := by
    obtain ⟨C1, hC1, hQ⟩ := compactPoisson_GT4_5 (n := 2) le_rfl
    obtain ⟨C2, hC2, hE⟩ := hQ (3 / 4) three_quarters_pos three_quarters_lt_one
    obtain ⟨hsupp, hrep, hK, -, hball⟩ :=
      hE planarU planarF (planarBump.contDiff (n := 2)) planarBump.hasCompactSupport
        planarF_localHolder fun _ => rfl
    obtain ⟨⟨M, H, hM, hH⟩, hest⟩ := hball 0 2 two_pos planarU_tsupport
    obtain ⟨h1, h2, h3, h4, h5⟩ := hest M H hM hH
    have hval : (∫ y, newtonianKernel 2 (0 - y) * planarF y) = 1 := by
      rw [← (hrep 0).2, planarU_zero]
    exact
      ⟨planarU_zero, hsupp, hrep, hval, hK, C1, C2, hC1, hC2, M, H, hM, hH, h1, h2, h3,
        h4, h5⟩

/-! ### (b) `n = 3`: the signed bump `y₀ β(y)` -/

/-- Smooth bump on `ℝ³`, equal to `1` on `B̄_1(0)` and supported in `B̄_{3/2}(0) ⊂ B_2(0)`. -/
def spatialBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) :=
  ⟨1, 3 / 2, by norm_num, by norm_num⟩

/-- The signed spatial solution `u(y) = β(y) y₀`. -/
def spatialU (y : EuclideanSpace ℝ (Fin 3)) : ℝ := spatialBump y * y 0

/-- The derived spatial source `f = Δu`. -/
def spatialF : EuclideanSpace ℝ (Fin 3) → ℝ := Laplacian.laplacian spatialU

theorem spatialU_contDiff (k : ℕ) : ContDiff ℝ k spatialU :=
  spatialBump.contDiff.mul (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff

theorem spatialU_tsupport : tsupport spatialU ⊆ ball 0 2 := by
  refine
    (tsupport_mul_subset_left (f := spatialBump) (g := fun y : EuclideanSpace ℝ (Fin 3) =>
          y 0)).trans
      ?_
  rw [spatialBump.tsupport_eq]; exact closedBall_subset_ball (show (3 / 2 : ℝ) < 2 by norm_num)

theorem spatialU_hasCompactSupport : HasCompactSupport spatialU :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2).of_isClosed_subset (isClosed_tsupport _)
    (spatialU_tsupport.trans ball_subset_closedBall)

/-- `u(±e₀/2) = ±1/2`: the solution genuinely takes both signs. -/
theorem spatialU_takes_both_signs :
    spatialU ((1 / 2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 0) = 1 / 2 ∧
      spatialU ((-1 / 2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 0) = -1 / 2 := by
  have hb : ∀ t : ℝ, |t| ≤ 1 → spatialBump (t • EuclideanSpace.basisFun (Fin 3) ℝ 0) = 1 :=
    fun t ht =>
    spatialBump.one_of_mem_closedBall
      (by
        change dist (t • EuclideanSpace.basisFun (Fin 3) ℝ 0) 0 ≤ (1 : ℝ)
        rw [dist_zero_right, norm_smul,
          (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one 0, mul_one,
          Real.norm_eq_abs]
        exact ht)
  refine ⟨?_, ?_⟩
  · change spatialBump _ * _ = _
    rw [hb _ (by norm_num [abs_of_pos])]
    norm_num [EuclideanSpace.basisFun_apply]
  · change spatialBump _ * _ = _
    rw [hb _ (by norm_num [abs_of_neg])]
    norm_num [EuclideanSpace.basisFun_apply]

theorem spatialF_localHolder :
    ∀ K, IsCompact K → ∃ H : ℝ≥0, HolderOnWith H (3 / 4) spatialF K :=
  holderOnWith_compact_of_contDiff_one (contDiff_laplacian (spatialU_contDiff 3) (by norm_num))
    three_quarters_lt_one.le

/-- (b) GT2001 Theorem 4.5 for the signed spatial bump: compact source support, the representation
(4.15) (with value `1/2` at
`e₀/2`), a global Hölder cap of the actual Hessian, and on `B_2(0)` derived source bounds with both
estimates (4.14). -/
theorem spatial_signed_GT4_5 :
    (HasCompactSupport spatialF ∧ tsupport spatialF ⊆ tsupport spatialU) ∧
    (∀ x, Integrable (fun y => newtonianKernel 3 (x - y) * spatialF y) volume ∧
      spatialU x = ∫ y, newtonianKernel 3 (x - y) * spatialF y) ∧
    (∫ y, newtonianKernel 3 ((1 / 2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 0 - y) * spatialF y)
      = 1 / 2 ∧
    (∃ K : ℝ≥0, HolderWith K (3 / 4) (fderiv ℝ (fderiv ℝ spatialU))) ∧
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧ ∃ M : ℝ, ∃ H : ℝ≥0,
      (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 2, |spatialF y| ≤ M) ∧ HolderOnWith H (3 / 4)
        spatialF (ball 0 2) ∧
      HolderWith (Real.toNNReal (C2 * ((2 * 2) ^ (-((3 / 4 : ℝ≥0) : ℝ)) * M + H))) (3 / 4) (fderiv
        ℝ (fderiv ℝ spatialU)) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ spatialU) x‖ ≤ C2 * (M + (2 * 2) ^ ((3 / 4 : ℝ≥0) : ℝ) * H)) ∧
      (∀ x z, ‖fderiv ℝ (fderiv ℝ spatialU) x - fderiv ℝ (fderiv ℝ spatialU) z‖ ≤
        C2 * ((2 * 2) ^ (-((3 / 4 : ℝ≥0) : ℝ)) * M + H) * ‖x - z‖ ^ ((3 / 4 : ℝ≥0) : ℝ)) ∧
      (∀ x y z, y ≠ z → ‖fderiv ℝ (fderiv ℝ spatialU) x‖ + (2 * 2) ^ ((3 / 4 : ℝ≥0) : ℝ) *
        (‖fderiv ℝ (fderiv ℝ spatialU) y - fderiv ℝ (fderiv ℝ spatialU) z‖ / ‖y - z‖ ^ ((3 / 4 :
          ℝ≥0) : ℝ)) ≤
        C2 * (M + (2 * 2) ^ ((3 / 4 : ℝ≥0) : ℝ) * H)) ∧
      (∀ x z, |spatialU x| + 2 * 2 * ‖fderiv ℝ spatialU z‖ ≤ C1 * 2 ^ 2 * M) := by
    obtain ⟨C1, hC1, hQ⟩ := compactPoisson_GT4_5 (n := 3) (by norm_num)
    obtain ⟨C2, hC2, hE⟩ := hQ (3 / 4) three_quarters_pos three_quarters_lt_one
    obtain ⟨hsupp, hrep, hK, -, hball⟩ :=
      hE spatialU spatialF (spatialU_contDiff 2) spatialU_hasCompactSupport
        spatialF_localHolder fun _ => rfl
    obtain ⟨⟨M, H, hM, hH⟩, hest⟩ := hball 0 2 two_pos spatialU_tsupport
    obtain ⟨h1, h2, h3, h4, h5⟩ := hest M H hM hH
    have hval :
      (∫ y,
          newtonianKernel 3 ((1 / 2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 0 - y) *
            spatialF y) =
        1 / 2 := by
      rw [← (hrep _).2, spatialU_takes_both_signs.1]
    exact ⟨hsupp, hrep, hval, hK, C1, C2, hC1, hC2, M, H, hM, hH, h1, h2, h3, h4, h5⟩

end CompactPoissonAudit

#print axioms CompactPoissonAudit.holderOnWith_compact_of_contDiff_one
#print axioms CompactPoissonAudit.three_quarters_pos
#print axioms CompactPoissonAudit.three_quarters_lt_one
#print axioms CompactPoissonAudit.planarU_zero
#print axioms CompactPoissonAudit.planarU_tsupport
#print axioms CompactPoissonAudit.planarF_localHolder
#print axioms CompactPoissonAudit.planar_bump_GT4_5
#print axioms CompactPoissonAudit.spatialU_contDiff
#print axioms CompactPoissonAudit.spatialU_tsupport
#print axioms CompactPoissonAudit.spatialU_hasCompactSupport
#print axioms CompactPoissonAudit.spatialU_takes_both_signs
#print axioms CompactPoissonAudit.spatialF_localHolder
#print axioms CompactPoissonAudit.spatial_signed_GT4_5
#print axioms FunctionalInequalities.Analysis.compactPoisson_estimates
#print axioms FunctionalInequalities.Analysis.compactPoisson_hessian_estimates
#print axioms FunctionalInequalities.Analysis.compactPoisson_GT4_5
#print axioms FunctionalInequalities.Analysis.newtonianPotential_schauder
#print axioms FunctionalInequalities.Analysis.newtonianPotential_contDiffOn_two
#print axioms FunctionalInequalities.Analysis.newtonianPotential_lemma_4_2
#print axioms FunctionalInequalities.Analysis.compact_C2_newtonian_representation
