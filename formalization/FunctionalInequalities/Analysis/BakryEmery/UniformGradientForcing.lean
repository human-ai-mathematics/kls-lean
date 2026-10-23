import FunctionalInequalities.Analysis.GradientSegment
import FunctionalInequalities.Analysis.MeasureAverage
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Uniform bounds for segment forcing coefficients

Supporting the lower-order coefficients in Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16, pp. 463–464, whose
Hölder norms enter the interior Schauder estimate, Theorem 6.2, pp. 90–92.

`exists_uniform_segmentForcingCoefficient_bounds`: for `C²` `W : ℝⁿ → ℝ` and a field `G` that is
`G0`-Lipschitz on `closedBall c R`, there are constants `B, Cb > 0` such that for every
displacement `d` with `r + ‖d‖ ≤ R` the coefficients `segmentForcingCoefficient W G d · i` are
bounded by `B` and `α`-Hölder with constant `Cb` on `closedBall c r`, for any `α ≤ 1`. The
constants are chosen before `d`, hence before any direction or scalar step of a finite difference.

The proof bounds `∂ᵢW` and its Lipschitz constant on a compact ball containing `G (closedBall c R)`;
no third derivative of a potential, Schauder estimate or regularity gain is used. In the strong
regular class the Lipschitz gradient field is `∇u`, but this module does not specialize to it.
-/
noncomputable section
namespace FunctionalInequalities.Analysis.BakryEmery
open Set MeasureTheory Metric
open scoped BigOperators ContDiff NNReal ENNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem exists_partial_bounds {W : E → ℝ} (hW : ContDiff ℝ 2 W) (M : ℝ) :
    ∃ B D : ℝ≥0, 0 < B ∧ 0 < D ∧
      (∀ y ∈ closedBall (0 : E) M, ∀ i,
        |fderiv ℝ W y (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ B) ∧
      ∀ i, LipschitzOnWith D
        (fun y => fderiv ℝ W y (EuclideanSpace.basisFun (Fin n) ℝ i)) (closedBall 0 M) := by
  have hD1 : ContDiff ℝ 1 (fderiv ℝ W) := hW.fderiv_right (by norm_num)
  obtain ⟨U,hU⟩ := (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn
    hD1.continuous.continuousOn
  obtain ⟨K,hK⟩ := ((ContDiff.locallyLipschitz hD1).locallyLipschitzOn
    (s := closedBall (0 : E) M)).exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 M)
  let B : ℝ≥0 := ⟨|U|+1,by positivity⟩
  let D : ℝ≥0 := K+1
  have hcap (y : E) (hy : y ∈ closedBall 0 M) : ‖fderiv ℝ W y‖ ≤ B :=
    (hU y hy).trans ((le_abs_self U).trans (le_add_of_nonneg_right zero_le_one))
  have hLip : LipschitzOnWith D (fderiv ℝ W) (closedBall 0 M) :=
    hK.weaken (le_add_of_nonneg_right zero_le_one)
  have hB : 0 < B := by
    rw [← NNReal.coe_pos]
    show (0 : ℝ) < |U|+1
    positivity
  refine ⟨B,D,hB,by dsimp [D]; positivity,?_,?_⟩
  · intro y hy i
    have h := (fderiv ℝ W y).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ i)
    rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i,mul_one] at h
    have h' : |fderiv ℝ W y (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ ‖fderiv ℝ W y‖ := by
      simpa only [Real.norm_eq_abs] using h
    exact h'.trans (hcap y hy)
  · intro i
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := (fderiv ℝ W x-fderiv ℝ W y).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ i)
    rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i,mul_one] at h
    have h' : dist (fderiv ℝ W x (EuclideanSpace.basisFun (Fin n) ℝ i))
        (fderiv ℝ W y (EuclideanSpace.basisFun (Fin n) ℝ i)) ≤ ‖fderiv ℝ W x-fderiv ℝ W y‖ := by
      simpa only [dist_eq_norm,sub_apply] using h
    have hl : ‖fderiv ℝ W x-fderiv ℝ W y‖ ≤ (D : ℝ)*dist x y := by
      simpa only [dist_eq_norm] using hLip.dist_le_mul x hx y hy
    exact h'.trans hl

private theorem translated_mem {c d x : E} {r R : ℝ}
    (hd : r+‖d‖ ≤ R) (hx : x ∈ closedBall c r) : x+d ∈ closedBall c R := by
  rw [mem_closedBall] at hx ⊢
  have he : dist (x+d) x = ‖d‖ := by
    rw [dist_eq_norm]
    congr 1
    module
  calc
    dist (x+d) c ≤ dist (x+d) x+dist x c := dist_triangle _ _ _
    _ = ‖d‖+dist x c := by rw [he]
    _ ≤ ‖d‖+r := by linarith
    _ ≤ R := by linarith

/-- Uniform cap and `α`-Hölder constant for the segment forcing coefficients. `W` is only `C²` and
`G` is Lipschitz on the outer ball; the constants precede the displacement `d`, hence also every
scalar step and direction. -/
theorem exists_uniform_segmentForcingCoefficient_bounds {W : E → ℝ} (hW : ContDiff ℝ 2 W)
    (G : E → E) (G0 : ℝ≥0) (c : E) (r R : ℝ) (hrR : r ≤ R)
    (hG : LipschitzOnWith G0 G (closedBall c R)) (α : ℝ≥0) (hα : α ≤ 1) :
    ∃ B Cb : ℝ≥0, 0 < B ∧ 0 < Cb ∧ ∀ d : E, r+‖d‖ ≤ R →
      (∀ x ∈ closedBall c r, ∀ i, |segmentForcingCoefficient W G d x i| ≤ B) ∧
      ∀ i, HolderOnWith Cb α (fun x => segmentForcingCoefficient W G d x i) (closedBall c r) := by
  have hs := (isCompact_closedBall c R).image_of_continuousOn hG.continuousOn
  obtain ⟨T,hT⟩ := hs.isBounded.exists_norm_le
  let M : ℝ := |T|+1
  have himage (x : E) (hx : x ∈ closedBall c R) : G x ∈ closedBall (0 : E) M := by
    rw [mem_closedBall,dist_zero_right]
    exact (hT _ ⟨x,hx,rfl⟩).trans ((le_abs_self T).trans (le_add_of_nonneg_right zero_le_one))
  obtain ⟨B,D,hB,hD,hcap,hLip⟩ := exists_partial_bounds hW M
  obtain ⟨S,hS⟩ := (isCompact_closedBall c r).isBounded.exists_norm_le
  let diam : ℝ≥0 := ⟨2*|S|+1,by positivity⟩
  have hdiam : ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r, edist x y ≤ diam := by
    intro x hx y hy
    rw [edist_dist,← ENNReal.ofReal_coe_nnreal (p := diam)]
    apply ENNReal.ofReal_le_ofReal
    calc
      dist x y ≤ ‖x‖+‖y‖ := dist_le_norm_add_norm _ _
      _ ≤ S+S := add_le_add (hS x hx) (hS y hy)
      _ ≤ (diam : ℝ) := by show S+S ≤ 2*|S|+1; linarith [le_abs_self S]
  let Cb : ℝ≥0 := (D*G0)*diam^(1-(α : ℝ))+1
  have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  refine ⟨B,Cb,hB,by dsimp [Cb]; positivity,?_⟩
  intro d hd
  have hout {x : E} (hx : x ∈ closedBall c r) : x ∈ closedBall c R :=
    closedBall_subset_closedBall hrR hx
  have hshift {x : E} (hx : x ∈ closedBall c r) : x+d ∈ closedBall c R := translated_mem hd hx
  have hsegment (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (x : E) (hx : x ∈ closedBall c r) :
      (1-θ) • G x+θ • G (x+d) ∈ closedBall (0 : E) M :=
    (convex_closedBall 0 M) (himage x (hout hx)) (himage (x+d) (hshift hx))
      (sub_nonneg.mpr hθ.2) hθ.1 (by ring)
  have hsegdist (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1)
      (x y : E) (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
      dist ((1-θ) • G x+θ • G (x+d)) ((1-θ) • G y+θ • G (y+d)) ≤
        (G0 : ℝ)*dist x y := by
    have h0 := hG.dist_le_mul x (hout hx) y (hout hy)
    have h1 := hG.dist_le_mul (x+d) (hshift hx) (y+d) (hshift hy)
    rw [dist_add_right] at h1
    simp only [dist_eq_norm] at h0 h1 ⊢
    have he : ((1-θ) • G x+θ • G (x+d))-((1-θ) • G y+θ • G (y+d)) =
        (1-θ) • (G x-G y)+θ • (G (x+d)-G (y+d)) := by module
    rw [he]
    calc
      _ ≤ ‖(1-θ) • (G x-G y)‖+‖θ • (G (x+d)-G (y+d))‖ := norm_add_le _ _
      _ = (1-θ)*‖G x-G y‖+θ*‖G (x+d)-G (y+d)‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hθ.2),abs_of_nonneg hθ.1]
      _ ≤ (1-θ)*((G0 : ℝ)*‖x-y‖)+θ*((G0 : ℝ)*‖x-y‖) :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hθ.2))
          (mul_le_mul_of_nonneg_left h1 hθ.1)
      _ = _ := by ring
  constructor
  · intro x hx i
    have hb : ∀ θ ∈ uIoc (0 : ℝ) 1,
        ‖fderiv ℝ W ((1-θ) • G x+θ • G (x+d)) (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ≤ B := by
      intro θ hθ
      have hθ' : θ ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hθ
      simpa only [Real.norm_eq_abs] using hcap _ (hsegment θ ⟨hθ'.1.le,hθ'.2⟩ x hx) i
    simpa only [segmentForcingCoefficient,segmentMeanCoefficient,sub_zero,abs_one,one_mul,
      mul_one,Real.norm_eq_abs]
      using intervalIntegral.norm_integral_le_of_norm_le_const hb
  · intro i
    have hm : HolderWith (D*G0) 1
        (fun x : closedBall c r => segmentForcingCoefficient W G d x i) := by
      apply holderWith_unit_interval_mean
        (q := fun θ (x : closedBall c r) => fderiv ℝ W ((1-θ) • G x+θ • G (x+d))
          (EuclideanSpace.basisFun (Fin n) ℝ i)) (D*G0) 1
      · intro x
        exact intervalIntegrable_segmentMeanCoefficient hW1 (G x) (G (x+d)) i
      · intro θ hθ
        have hθ' : θ ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hθ
        apply LipschitzWith.holderWith
        apply LipschitzWith.of_dist_le_mul
        intro x y
        calc
          _ ≤ (D : ℝ)*dist ((1-θ) • G x+θ • G (x+d)) ((1-θ) • G y+θ • G (y+d)) :=
            (hLip i).dist_le_mul _ (hsegment θ ⟨hθ'.1.le,hθ'.2⟩ x x.property)
              _ (hsegment θ ⟨hθ'.1.le,hθ'.2⟩ y y.property)
          _ ≤ (D : ℝ)*((G0 : ℝ)*dist (x : E) (y : E)) :=
            mul_le_mul_of_nonneg_left
              (hsegdist θ ⟨hθ'.1.le,hθ'.2⟩ x y x.property y.property) D.coe_nonneg
          _ = _ := by simp only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq]
    have hon : HolderOnWith (D*G0) 1 (fun x => segmentForcingCoefficient W G d x i)
        (closedBall c r) :=
      HolderWith.restrict_iff.mp hm
    exact (hon.of_le hdiam hα).mono_const (le_add_of_nonneg_right zero_le_one)

end FunctionalInequalities.Analysis.BakryEmery
