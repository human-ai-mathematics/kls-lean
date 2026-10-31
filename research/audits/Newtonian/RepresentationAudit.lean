module

public import FunctionalInequalities.Analysis.Newtonian.Potential.Representation

/-!
# Audit: the compact C² Newtonian representation (4.15)

Real clients of `compact_C2_newtonian_representation`
(`FunctionalInequalities/Analysis/Newtonian/Potential/Representation.lean`; Gilbarg–Trudinger,
*Elliptic Partial
Differential Equations of Second Order*, Classics 2001, (4.15)), with the source-normalized kernel:

* `planar_bump_representation` (`n = 2`): for the smooth bump `β` with `β = 1` on `B̄_1(0)`,
  `∫ Γ(-y) Δβ(y) dy = β(0) = 1`, with the integrand integrable;
* `spatial_signed_bump_representation` (`n = 3`): for the signed function `u(y) = β(y) y₀` and
  `q = e₀/2`, `∫ Γ(q - y) Δu(y) dy = u(q) = 1/2`.

Both values are computed from the representation theorem, not assumed.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace RepresentationAudit

def unitBump (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨1, 2, by norm_num, by norm_num⟩

theorem planar_bump_representation :
    Integrable
        (fun y : EuclideanSpace ℝ (Fin 2) =>
          FunctionalInequalities.Analysis.newtonianKernel 2 (-y) *
            Laplacian.laplacian (fun y => unitBump 2 y) y)
        volume ∧
      (∫ y : EuclideanSpace ℝ (Fin 2),
          FunctionalInequalities.Analysis.newtonianKernel 2 (-y) *
            Laplacian.laplacian (fun y => unitBump 2 y) y) =
        1 := by
  have h :=
    FunctionalInequalities.Analysis.compact_C2_newtonian_representation (n := 2) (u := fun y =>
      unitBump 2 y) (by norm_num) (unitBump 2).contDiff (unitBump 2).hasCompactSupport 0
  have h0 : unitBump 2 0 = 1 :=
    (unitBump 2).one_of_mem_closedBall
      (by change dist (0 : EuclideanSpace ℝ (Fin 2)) 0 ≤ (1 : ℝ); norm_num)
  simpa only [zero_sub, h0] using And.intro h.1 h.2.symm

def signedBump (x : EuclideanSpace ℝ (Fin 3)) : ℝ := unitBump 3 x * x 0

theorem spatial_signed_bump_representation :
    let q : EuclideanSpace ℝ (Fin 3) := (1 / 2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 0
    Integrable
        (fun y =>
          FunctionalInequalities.Analysis.newtonianKernel 3 (q - y) *
            Laplacian.laplacian signedBump y)
        volume ∧
      (∫ y,
          FunctionalInequalities.Analysis.newtonianKernel 3 (q - y) *
            Laplacian.laplacian signedBump y) =
        1 / 2 := by
  dsimp only
  let q : EuclideanSpace ℝ (Fin 3) := (1 / 2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 0
  have hproj : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin 3) => x 0) := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff
  have hu : ContDiff ℝ 2 signedBump := (unitBump 3).contDiff.mul hproj
  have hc : HasCompactSupport signedBump := (unitBump 3).hasCompactSupport.mul_right
  have h :=
    FunctionalInequalities.Analysis.compact_C2_newtonian_representation (n := 3) (by norm_num)
      hu hc q
  have hq : unitBump 3 q = 1 :=
    (unitBump 3).one_of_mem_closedBall
      (by
        change dist q 0 ≤ (1 : ℝ)
        rw [dist_zero_right]
        norm_num [q, norm_smul])
  have hval : signedBump q = 1 / 2 := by
    change unitBump 3 q * q 0 = 1 / 2
    rw [hq, one_mul]
    norm_num [q, EuclideanSpace.basisFun_apply]
  exact ⟨h.1, by simpa only [hval] using h.2.symm⟩

end RepresentationAudit

#print axioms RepresentationAudit.planar_bump_representation
#print axioms RepresentationAudit.spatial_signed_bump_representation
#print axioms FunctionalInequalities.Analysis.compact_C2_newtonian_representation
#print axioms FunctionalInequalities.Analysis.locallyIntegrable_newtonianKernel
#print axioms FunctionalInequalities.Analysis.laplacian_convolution_compact_C2
#print axioms FunctionalInequalities.Analysis.newtonianPotential_contDiffOn_two
