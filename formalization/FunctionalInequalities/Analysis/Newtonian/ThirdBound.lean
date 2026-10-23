import FunctionalInequalities.Analysis.Newtonian.Third

/-!
# An explicit third-derivative bound for the Newtonian kernel

`norm_fderiv_newtonianKernel_entry_le`: for `n ≥ 2` and `x ≠ 0`, the derivative of each Hessian entry
`y ↦ D_ijΓ(y)` has operator norm at most `(n + 5) / ω_n · ‖x‖^(-n-1)`. Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.14) allows an
unspecified dimensional constant; this explicit one suffices for the far-field step of Lemma 4.4.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- A dimension-only third-derivative bound for the actual Hessian entries.
GT2001 (2.14) permits an unspecified dimensional constant; this explicit
(n+5)/omega_n suffices for the far step of Lemma 4.4. -/
theorem norm_fderiv_newtonianKernel_entry_le {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (i j : Fin n) :
    ‖fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x‖ ≤
      ((n:ℝ)+5)/euclideanUnitBallVolume n*‖x‖^(-(n:ℝ)-1) := by
  let N := (n:ℝ)
  let r := ‖x‖
  let S := r^(-N-2)
  let T := r^(-N-4)
  let e := r^(-N-1)
  let u := EuclideanSpace.basisFun (Fin n) ℝ i
  let v := EuclideanSpace.basisFun (Fin n) ℝ j
  have hN : 0 < N := by dsimp [N];exact_mod_cast (by omega : 0 < n)
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hw : 0 < euclideanUnitBallVolume n := euclideanUnitBallVolume_pos n
  have hS : 0 ≤ S := Real.rpow_nonneg hr.le _
  have hT : 0 ≤ T := Real.rpow_nonneg hr.le _
  have hu : ‖u‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i
  have hv : ‖v‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one j
  have hxu : |⟪x,u⟫| ≤ r := by simpa only [hu,mul_one] using abs_real_inner_le_norm x u
  have hxv : |⟪x,v⟫| ≤ r := by simpa only [hv,mul_one] using abs_real_inner_le_norm x v
  have huv : |⟪u,v⟫| ≤ 1 := by simpa only [hu,hv,mul_one] using abs_real_inner_le_norm u v
  have hSr : S*r = e := by
    change r^(-N-2)*r = r^(-N-1)
    calc
      _ = r^(-N-2)*r^(1:ℝ) := by rw [Real.rpow_one]
      _ = r^((-N-2)+1) := (Real.rpow_add hr _ _).symm
      _ = _ := by congr 1;ring
  have hTr : T*r*r*r = e := by
    calc
      _ = r^(-N-4)*r^(3:ℕ) := by dsimp only [T];ring
      _ = r^(-N-4)*r^(3:ℝ) := by norm_num [Real.rpow_ofNat]
      _ = r^((-N-4)+3) := (Real.rpow_add hr _ _).symm
      _ = _ := by dsimp only [e];congr 1;ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [Real.norm_eq_abs,fderiv_bilinear_newtonianKernel hn x u v w hx]
  let q := ‖w‖
  have hxw : |⟪x,w⟫| ≤ r*q := abs_real_inner_le_norm x w
  have hwu : |⟪w,u⟫| ≤ q := by simpa only [hu,mul_one] using abs_real_inner_le_norm w u
  have hwv : |⟪w,v⟫| ≤ q := by simpa only [hv,mul_one] using abs_real_inner_le_norm w v
  have hfirst : |(-N)*S*⟪x,w⟫*⟪u,v⟫| ≤ N*S*(r*q) := by
    simp only [abs_mul,abs_neg,abs_of_nonneg hN.le,abs_of_nonneg hS]
    calc
      _ ≤ N*S*(r*q)*1 := by gcongr
      _ = _ := by ring
  have hcoeff : |-N-2| = N+2 := by rw [abs_of_nonpos (by linarith : -N-2 ≤ 0)];ring
  have ht1 : |(-N-2)*T*⟪x,w⟫*⟪x,u⟫*⟪x,v⟫| ≤ (N+2)*T*(r*q)*r*r := by
    simp only [abs_mul,hcoeff,abs_of_nonneg hT]
    gcongr
  have ht2 : |S*(⟪w,u⟫*⟪x,v⟫+⟪x,u⟫*⟪w,v⟫)| ≤ S*(q*r+r*q) := by
    rw [abs_mul,abs_of_nonneg hS]
    apply mul_le_mul_of_nonneg_left _ hS
    calc
      _ ≤ |⟪w,u⟫| * |⟪x,v⟫| + |⟪x,u⟫| * |⟪w,v⟫| := by
        simpa only [abs_mul] using abs_add_le (⟪w,u⟫*⟪x,v⟫) (⟪x,u⟫*⟪w,v⟫)
      _ ≤ _ := by gcongr
  have hsecond : |N*((-N-2)*T*⟪x,w⟫*⟪x,u⟫*⟪x,v⟫+S*(⟪w,u⟫*⟪x,v⟫+⟪x,u⟫*⟪w,v⟫))| ≤
      N*((N+2)*T*(r*q)*r*r+S*(q*r+r*q)) := by
    rw [abs_mul,abs_of_nonneg hN.le]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ht1 ht2)) hN.le
  have halg : N*S*(r*q)+N*((N+2)*T*(r*q)*r*r+S*(q*r+r*q)) = N*(N+5)*e*q := by
    calc
      _ = N*(S*r)*q+N*(N+2)*(T*r*r*r)*q+2*N*(S*r)*q := by ring
      _ = _ := by rw [hSr,hTr];ring
  have hmodel := (abs_sub ((-N)*S*⟪x,w⟫*⟪u,v⟫)
    (N*((-N-2)*T*⟪x,w⟫*⟪x,u⟫*⟪x,v⟫+S*(⟪w,u⟫*⟪x,v⟫+⟪x,u⟫*⟪w,v⟫)))).trans
      (add_le_add hfirst hsecond)
  rw [halg] at hmodel
  change |(1/(N*euclideanUnitBallVolume n))*((-N)*S*⟪x,w⟫*⟪u,v⟫-
    N*((-N-2)*T*⟪x,w⟫*⟪x,u⟫*⟪x,v⟫+S*(⟪w,u⟫*⟪x,v⟫+⟪x,u⟫*⟪w,v⟫)))| ≤ _
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(N*euclideanUnitBallVolume n))]
  calc
    _ ≤ (1/(N*euclideanUnitBallVolume n))*(N*(N+5)*e*q) := mul_le_mul_of_nonneg_left hmodel (by positivity)
    _ = _ := by change (1/(N*euclideanUnitBallVolume n))*(N*(N+5)*e*q) = (N+5)/euclideanUnitBallVolume n*e*q;field_simp [hN.ne',hw.ne']

end FunctionalInequalities.Analysis
