import FunctionalInequalities.Probability.Stein.HessianKernel
import Mathlib.Analysis.Calculus.DerivativeTest
import FunctionalInequalities.Analysis.Convex.Alexandrov
import FunctionalInequalities.Analysis.Convex.SecondOrder
import FunctionalInequalities.Analysis.Matrix.LogDet
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Touching-test (viscosity) inequalities for convex functions

Pointwise consequences of touching a function from above or below by a `C²` test function, stated with the
coordinate Hessian `Probability.Stein.hessianMatrix` (weak Letwin route, steps N8/N12). Kept apart from
`Analysis/Convex/Alexandrov.lean`, which needs no Hessian machinery.

* `posSemidef_hessianMatrix_of_upper_touch` (task L-T12c3).
-/

noncomputable section

open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

private lemma directional_second_deriv_nonneg
    {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀)
    (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x)
    (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ bilinearIteratedFDerivTwo ℝ ψ x₀ v v := by
  let L : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x₀ + t • v
  let q : ℝ → ℝ := fun t => ψ (L t)
  let p : ℝ → ℝ := fun t => (fderiv ℝ ψ (L t)) v
  let r : ℝ → ℝ := fun t => q t + q (-t)
  have hL (t : ℝ) : HasDerivAt L v t := by
    simpa [L] using
      ((hasDerivAt_id (𝕜 := ℝ) t).smul_const v).const_add x₀
  have hLcont : Tendsto L (𝓝 0) (𝓝 x₀) := by
    simpa [L] using (hL 0).continuousAt.tendsto
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using
      (continuousAt_neg : ContinuousAt (fun t : ℝ => -t) (0 : ℝ)).tendsto
  have hψevent :
      ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 2 ψ (L t) :=
    hLcont.eventually (hψ.eventually (by norm_num))
  have hqevent : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt q (p t) t := by
    filter_upwards [hψevent] with t ht
    have h :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hL t)
    simpa only [q, p, Function.comp_def] using h
  have hrderiv : deriv r =ᶠ[𝓝 0] (fun t => p t - p (-t)) := by
    filter_upwards [hqevent, hneg.eventually hqevent] with t ht htneg
    have hn : HasDerivAt (fun s : ℝ => q (-s)) (-p (-t)) t := by
      simpa [Function.comp_def] using
        htneg.comp t (hasDerivAt_id (𝕜 := ℝ) t).neg
    simpa only [r, sub_eq_add_neg] using (ht.fun_add hn).deriv
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ ψ) x₀ :=
    hψ.fderiv_right (m := 1) (n := 2) (by norm_num)
  have hpf : HasFDerivAt (fderiv ℝ ψ)
      (fderiv ℝ (fderiv ℝ ψ) x₀) x₀ :=
    (hfd.differentiableAt (by norm_num)).hasFDerivAt
  have hp0 :
      HasDerivAt p (bilinearIteratedFDerivTwo ℝ ψ x₀ v v) 0 := by
    have hpf' : HasFDerivAt (fderiv ℝ ψ)
        (fderiv ℝ (fderiv ℝ ψ) x₀) (L 0) := by
      simpa [L] using hpf
    have hcomp := hpf'.comp_hasDerivAt 0 (hL 0)
    have happ := hcomp.clm_apply (hasDerivAt_const (x := (0 : ℝ)) v)
    simpa [p, L, bilinearIteratedFDerivTwo, Function.comp_def] using happ
  have hpneg :
      HasDerivAt (fun t => p (-t))
        (-(bilinearIteratedFDerivTwo ℝ ψ x₀ v v)) 0 := by
    have hp0' : HasDerivAt p
        (bilinearIteratedFDerivTwo ℝ ψ x₀ v v) (-(0 : ℝ)) := by
      simpa only [neg_zero] using hp0
    simpa [Function.comp_def] using
      hp0'.comp 0 (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).neg
  have hpdiff :
      HasDerivAt (fun t => p t - p (-t))
        (2 * bilinearIteratedFDerivTwo ℝ ψ x₀ v v) 0 := by
    simpa [two_mul] using hp0.fun_sub hpneg
  have hsecond :
      deriv (deriv r) 0 =
        2 * bilinearIteratedFDerivTwo ℝ ψ x₀ v v := by
    calc
      deriv (deriv r) 0 =
          deriv (fun t => p t - p (-t)) 0 := hrderiv.deriv_eq
      _ = 2 * bilinearIteratedFDerivTwo ℝ ψ x₀ v v := hpdiff.deriv
  have hq0 : HasDerivAt q ((fderiv ℝ ψ x₀) v) 0 := by
    have hψ' : HasFDerivAt ψ (fderiv ℝ ψ x₀) (L 0) := by
      simpa [L] using (hψ.differentiableAt (by norm_num)).hasFDerivAt
    simpa only [q, Function.comp_def] using hψ'.comp_hasDerivAt 0 (hL 0)
  have hqneg0 :
      HasDerivAt (fun t => q (-t)) (-((fderiv ℝ ψ x₀) v)) 0 := by
    have hq0' : HasDerivAt q ((fderiv ℝ ψ x₀) v) (-(0 : ℝ)) := by
      simpa only [neg_zero] using hq0
    simpa [Function.comp_def] using
      hq0'.comp 0 (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).neg
  have hr0 : deriv r 0 = 0 := by
    simpa [r] using (hq0.fun_add hqneg0).deriv
  have hrcont : ContinuousAt r 0 :=
    (hq0.fun_add hqneg0).continuousAt
  have hmin : IsLocalMin r 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, r 0 ≤ r t
    have hLt : ∀ᶠ t : ℝ in 𝓝 0, u (L t) ≤ ψ (L t) :=
      hLcont.eventually htouch
    filter_upwards [hLt, hneg.eventually hLt] with t ht htneg
    have hc := hconv.2 (mem_univ (L t)) (mem_univ (L (-t)))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hmid :
        (1 / 2 : ℝ) • L t + (1 / 2 : ℝ) • L (-t) = x₀ := by
      dsimp [L]
      module
    rw [hmid] at hc
    change u x₀ ≤ (1 / 2 : ℝ) * u (L t) + (1 / 2 : ℝ) * u (L (-t)) at hc
    rw [hcontact] at hc
    have hrzero : r 0 = 2 * ψ x₀ := by
      simp [r, q, L, two_mul]
    rw [hrzero]
    change 2 * ψ x₀ ≤ ψ (L t) + ψ (L (-t))
    linarith
  by_contra hA
  have hA' : bilinearIteratedFDerivTwo ℝ ψ x₀ v v < 0 :=
    lt_of_not_ge hA
  have hmax : IsLocalMax r 0 :=
    isLocalMax_of_deriv_deriv_neg (by linarith [hsecond]) hr0 hrcont
  change ∀ᶠ t : ℝ in 𝓝 0, r t ≤ r 0 at hmax
  change ∀ᶠ t : ℝ in 𝓝 0, r 0 ≤ r t at hmin
  have heq : r =ᶠ[𝓝 0] (fun _ : ℝ => r 0) := by
    filter_upwards [hmin, hmax] with t htmin htmax
    exact le_antisymm htmax htmin
  rcases _root_.mem_nhds_iff.mp heq with ⟨s, hs, hso, h0s⟩
  have hderiv : deriv r =ᶠ[𝓝 0] (fun _ : ℝ => 0) := by
    filter_upwards [hso.mem_nhds h0s] with t ht
    have hloc : r =ᶠ[𝓝 t] (fun _ : ℝ => r 0) := by
      filter_upwards [hso.mem_nhds ht] with y hy
      exact hs hy
    simpa using hloc.deriv_eq
  have hz : deriv (deriv r) 0 = 0 := by
    simpa using hderiv.deriv_eq
  linarith

/-- **A `C²` function touching a convex function from above has positive semidefinite Hessian at the
contact point** (weak Letwin route, N8 viscosity tests). -/
theorem posSemidef_hessianMatrix_of_upper_touch {n : ℕ} {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ : EuclideanSpace ℝ (Fin n)} (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    (hessianMatrix ψ x₀).PosSemidef := by
  classical
  have hs := hψ.isSymmSndFDerivAt
    (by norm_num : minSmoothness ℝ 2 ≤ 2)
  unfold Matrix.PosSemidef
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa [hessianMatrix, bilinearIteratedFDerivTwo] using
      hs (EuclideanSpace.basisFun (Fin n) ℝ j)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
  · intro z
    let v : EuclideanSpace ℝ (Fin n) :=
      z.sum (fun i zi => zi • EuclideanSpace.basisFun (Fin n) ℝ i)
    have hv := directional_second_deriv_nonneg hconv hψ hcontact htouch v
    have hquad :
        z.sum (fun i zi =>
            z.sum (fun j zj =>
              star zi * hessianMatrix ψ x₀ i j * zj)) =
          bilinearIteratedFDerivTwo ℝ ψ x₀ v v := by
      simp [v, hessianMatrix, bilinearIteratedFDerivTwo, Finsupp.sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hs (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)]
      ring
    rw [hquad]
    exact hv

end FunctionalInequalities.Analysis

section LT12C2TaylorHessianBound

open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

/-! Second-order Taylor bound with the coordinate Hessian for `C²` test functions (task L-T12c2). -/

namespace FunctionalInequalities.Analysis

private lemma matrix_quadratic_formula
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin M v⟫ =
      ∑ i, ∑ j, v.ofLp i * (M i j * v.ofLp j) := by
  rw [Matrix.toLpLin_apply 2 2, PiLp.inner_apply]
  simp [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma hessianMatrix_quadratic
    {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin (hessianMatrix ψ x) v⟫ =
      (fderiv ℝ (fderiv ℝ ψ) x) v v := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let H : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ ψ) x
  let c : Fin n → ℝ := fun i => (b.repr v).ofLp i
  have hv : ∑ i, c i • b i = v := b.sum_repr v
  have hc : ∀ i, c i = v.ofLp i := by
    intro i
    exact (EuclideanSpace.basisFun_repr (Fin n) ℝ v i).symm
  have hentry : ∀ i j, hessianMatrix ψ x i j = H (b i) (b j) := by
    intro i j
    change
      bilinearIteratedFDerivTwo ℝ ψ x (b i) (b j) =
        H (b i) (b j)
    rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
    simpa [H] using iteratedFDeriv_two_apply ψ x ![b i, b j]
  have hfirst :
      H (∑ i, c i • b i) = ∑ i, H (c i • b i) := by
    rw [map_sum]
  have hsecond :
      ∀ i, (H (c i • b i)) (∑ j, c j • b j) =
        ∑ j, (H (c i • b i)) (c j • b j) := by
    intro i
    rw [map_sum]
  have hsum :
      H (∑ i, c i • b i) (∑ j, c j • b j) =
        ∑ i, ∑ j, c i * (H (b i) (b j) * c j) := by
    calc
      H (∑ i, c i • b i) (∑ j, c j • b j) =
          (∑ i, H (c i • b i)) (∑ j, c j • b j) := by
            rw [hfirst]
      _ = ∑ i, (H (c i • b i)) (∑ j, c j • b j) := by
            rw [sum_apply]
      _ = ∑ i, ∑ j, c i * (H (b i) (b j) * c j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hsecond i]
            simp only [map_smul, smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [matrix_quadratic_formula]
  simp_rw [hentry, ← hc]
  rw [← hsum, hv]

private lemma local_taylor_two
    {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hψ : ContDiffAt ℝ 2 ψ x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ ball x₀ r,
      |ψ x - (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
        (1 / 2 : ℝ) *
          (fderiv ℝ (fderiv ℝ ψ) x₀ (x - x₀)) (x - x₀))| ≤
        ε * ‖x - x₀‖ ^ 2 := by
  classical
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ ψ) x₀
  have hsymm :
      ∀ v w : EuclideanSpace ℝ (Fin n), B v w = B w v := by
    intro v w
    exact hψ.isSymmSndFDerivAt (by norm_num) v w
  rcases hψ.contDiffOn (m := 2) le_rfl (by simp) with ⟨u, hu, hψu⟩
  rcases Metric.mem_nhds_iff.mp hu with ⟨ρ, hρ, hρu⟩
  let s : Set (EuclideanSpace ℝ (Fin n)) := ball x₀ ρ
  have hs : Convex ℝ s := convex_ball x₀ ρ
  have hx₀s : x₀ ∈ s := mem_ball_self hρ
  have hψs : ContDiffOn ℝ 2 ψ s := hψu.mono hρu
  let q : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => (1 / 2 : ℝ) * B (y - x₀) (y - x₀)
  let g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => ψ y - ψ x₀ - fderiv ℝ ψ x₀ (y - x₀) - q y
  let dg : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun y => fderiv ℝ ψ y - fderiv ℝ ψ x₀ - B (y - x₀)
  have hderiv :
      ∀ y ∈ s, HasFDerivWithinAt g (dg y) s y := by
    intro y hy
    have hy' : ContDiffAt ℝ 2 ψ y :=
      (hψs y hy).contDiffAt (Metric.isOpen_ball.mem_nhds hy)
    have hψy : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
      (hy'.differentiableAt (by norm_num)).hasFDerivAt
    have hsub : HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin n) => z - x₀)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
      (hasFDerivAt_id y).sub_const x₀
    have hlin :=
      (ContinuousLinearMap.hasFDerivAt (fderiv ℝ ψ x₀)).comp y hsub
    rw [ContinuousLinearMap.comp_id] at hlin
    have hB :=
      (ContinuousLinearMap.hasFDerivAt B).comp y hsub
    rw [ContinuousLinearMap.comp_id] at hB
    have hquad₀ := hB.clm_apply hsub
    simp only [Function.comp_apply] at hquad₀
    have hquad_eq :
        B (y - x₀) ∘SL
              (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) +
            B.flip (y - x₀) =
          2 • B (y - x₀) := by
      ext z
      simp only [ContinuousLinearMap.comp_id, add_apply,
        ContinuousLinearMap.flip_apply, smul_apply]
      rw [hsymm z (y - x₀)]
      ring
    rw [hquad_eq] at hquad₀
    have hq : HasFDerivAt q (B (y - x₀)) y := by
      convert hquad₀.const_mul (1 / 2 : ℝ) using 1 <;>
        first
        | rfl
        | (ext z; norm_num [smul_apply, smul_eq_mul]; ring)
    have hg₀ := ((hψy.sub_const (ψ x₀)).sub hlin).sub hq
    have hg : HasFDerivAt g (dg y) y := by
      convert hg₀ using 1 <;> rfl
    convert hg.hasFDerivWithinAt (s := s) using 1
  have hB₀ :
      (fun y : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ ψ y - fderiv ℝ ψ x₀ - B (y - x₀)) =o[𝓝 x₀]
        fun y => ‖y - x₀‖ := by
    have hfd : HasFDerivAt (fderiv ℝ ψ) B x₀ := by
      exact
        ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt
          (by norm_num)).hasFDerivAt
    simpa [B] using hfd.isLittleO.norm_right
  have hB₀' :
      dg =o[𝓝[s] x₀] fun y => ‖y - x₀‖ := by
    rw [Asymptotics.isLittleO_iff] at hB₀ ⊢
    intro c hc
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (hB₀ hc)
  have hB₀'' :
      dg =o[𝓝[s] x₀] fun y => ‖y - x₀‖ ^ 1 := by
    simpa using hB₀'
  have hg₀ :
      (fun y => g y - g x₀) =o[𝓝[s] x₀]
        fun y => ‖y - x₀‖ ^ (1 + 1) :=
    hs.isLittleO_pow_succ hx₀s hderiv hB₀''
  have hgzero : g x₀ = 0 := by
    simp [g, q]
  have hg₀' :
      g =o[𝓝[s] x₀] fun y => ‖y - x₀‖ ^ 2 := by
    simpa [hgzero, pow_two] using hg₀
  have hev :
      ∀ᶠ y in 𝓝[s] x₀, ‖g y‖ ≤ ε * ‖y - x₀‖ ^ 2 := by
    have h := Asymptotics.IsLittleO.bound hg₀' hε
    filter_upwards [h] with y hy
    calc
      ‖g y‖ ≤ ε * ‖‖y - x₀‖ ^ 2‖ := hy
      _ = ε * ‖y - x₀‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖y - x₀‖))]
  rcases Metric.mem_nhdsWithin_iff.mp hev with ⟨δ, hδ, hδev⟩
  refine ⟨min ρ δ, lt_min hρ hδ, ?_⟩
  intro x hx
  have hx' : dist x x₀ < min ρ δ := Metric.mem_ball.mp hx
  have hxρ : x ∈ s :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hx' (min_le_left ρ δ))
  have hxδ : x ∈ ball x₀ δ :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hx' (min_le_right ρ δ))
  have hbound : ‖g x‖ ≤ ε * ‖x - x₀‖ ^ 2 := by
    have h := hδev ⟨hxδ, hxρ⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖x - x₀‖))] using h
  have hgexpr :
      g x =
        ψ x - (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
          (1 / 2 : ℝ) *
            (fderiv ℝ (fderiv ℝ ψ) x₀ (x - x₀)) (x - x₀)) := by
    simp [g, q, sub_eq_add_neg]
    ring
  rw [hgexpr] at hbound
  simpa only [Real.norm_eq_abs] using hbound

/-- **Second-order Taylor bound with the coordinate Hessian** (weak Letwin route, N8 viscosity tests):
for `ψ` twice differentiable at `x₀` (`ContDiffAt ℝ 2`), every `ε > 0` admits `r > 0` with
`|ψ x − ψ x₀ − Dψ(x₀)(x − x₀) − ½ ⟪x − x₀, ∇²ψ(x₀)(x − x₀)⟫| ≤ ε ‖x − x₀‖²` on `ball x₀ r`. -/
theorem exists_taylor_two_hessianMatrix_bound {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)} (hψ : ContDiffAt ℝ 2 ψ x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ ball x₀ r,
      |ψ x - (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
        (1 / 2) * ⟪x - x₀, Matrix.toEuclideanLin (hessianMatrix ψ x₀) (x - x₀)⟫)| ≤
        ε * ‖x - x₀‖ ^ 2 := by
  rcases local_taylor_two hψ hε with ⟨r, hr, hrbound⟩
  refine ⟨r, hr, ?_⟩
  intro x hx
  rw [hessianMatrix_quadratic]
  exact hrbound x hx

end FunctionalInequalities.Analysis

end LT12C2TaylorHessianBound

section LT12C4ViscosityTouchingAssembly

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

/-! Viscosity inequalities for Alexandrov solutions: the determinant of the Hessian of a `C²` test touching from above (below) is bounded below (above) by the Monge–Ampère density (task L-T12c4). -/

namespace FunctionalInequalities.Analysis

private lemma touching_positive_parameter {P : ℝ → Prop}
    (hP : ∀ᶠ t in 𝓝 (0 : ℝ), P t) :
    ∃ t > 0, P t := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨r / 2, half_pos hr, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

private lemma touching_closedBall {n : ℕ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {P : EuclideanSpace ℝ (Fin n) → Prop}
    (hP : ∀ᶠ x in 𝓝 x₀, P x) :
    ∃ r > 0, ∀ x ∈ closedBall x₀ r, P x := by
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro x hx
  exact hsub (closedBall_subset_ball (by linarith : R / 2 < R) hx)

private lemma touching_posDef_perturbation {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∀ᶠ t : ℝ in 𝓝 0, (A + t • 1).PosDef := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < hA.1.eigenvalues i + t :=
    Filter.eventually_all.mpr fun i =>
      continuous_const.continuousAt.eventually_lt
        (continuous_const.add continuous_id).continuousAt
        (by simpa only [add_zero] using hA.eigenvalues_pos i)
  filter_upwards [hev] with t ht
  let e :=
    Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)
      hA.1.eigenvectorUnitary
  have he : e (Matrix.diagonal hA.1.eigenvalues) = A := by
    simpa [e] using hA.1.spectral_theorem.symm
  have hid :
      Matrix.diagonal (fun _ : Fin n => t) =
        t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    calc
      Matrix.diagonal (fun _ : Fin n => t) =
          Matrix.diagonal (t • (fun _ : Fin n => (1 : ℝ))) := by
        apply congrArg Matrix.diagonal
        funext i
        exact (mul_one t).symm
      _ = t • 1 := by
        rw [Matrix.diagonal_smul, Matrix.diagonal_one]
  have heq :
      A + t • 1 =
        e (Matrix.diagonal (fun i => hA.1.eigenvalues i + t)) := by
    rw [← Matrix.diagonal_add, hid, map_add, map_smul, map_one, he]
  rw [heq]
  change
    ((hA.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal (fun i => hA.1.eigenvalues i + t) *
      star (hA.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)).PosDef
  exact
    (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr
      (Matrix.posDef_diagonal_iff.mpr ht)

private lemma touching_quadratic_shift {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ b x : EuclideanSpace ℝ (Fin n)) (c d t : ℝ) :
    quadraticAt (A + t • 1) x₀ b c x =
      quadraticAt A x₀ b d x + (c - d) + t / 2 * ‖x - x₀‖ ^ 2 := by
  unfold quadraticAt
  have ha :
      Matrix.toEuclideanLin (A + t • 1) (x - x₀) =
        Matrix.toEuclideanLin A (x - x₀) + t • (x - x₀) := by
    change Matrix.toLpLin 2 2 (A + t • 1) (x - x₀) = _
    rw [map_add, map_smul, Matrix.toLpLin_one]
    rfl
  rw [ha, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

private lemma touching_comparison_set {n : ℕ}
    {v w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv : ConvexOn ℝ univ v) (hw : ConvexOn ℝ univ w)
    {x₀ : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hcenter : w x₀ < v x₀)
    (hsphere : ∀ x, ‖x - x₀‖ = r → v x ≤ w x) :
    ∃ G : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen G ∧ G ⊆ ball x₀ r ∧ Bornology.IsBounded G ∧ G.Nonempty ∧
        subgradientImage v G ⊆ subgradientImage w G := by
  have hvc : Continuous v :=
    continuousOn_univ.mp (hv.continuousOn isOpen_univ)
  have hwc : Continuous w :=
    continuousOn_univ.mp (hw.continuousOn isOpen_univ)
  let G : Set (EuclideanSpace ℝ (Fin n)) :=
    ball x₀ r ∩ {x | w x < v x}
  have hGo : IsOpen G := isOpen_ball.inter (isOpen_lt hwc hvc)
  have hGball : G ⊆ ball x₀ r := fun _ hx => hx.1
  have hGb : Bornology.IsBounded G := isBounded_ball.subset hGball
  have hGeq : ∀ x ∈ frontier G, w x = v x := by
    intro x hx
    have hxclG : x ∈ closure G := frontier_subset_closure hx
    have hxclB : x ∈ closedBall x₀ r :=
      closure_minimal
        (fun y hy => ball_subset_closedBall (hGball (show y ∈ G from hy)))
        isClosed_closedBall hxclG
    have hle : w x ≤ v x := by
      apply closure_minimal
        (s := G) (t := {y | w y ≤ v y}) ?_
        (isClosed_le hwc hvc) hxclG
      intro y hy
      change w y ≤ v y
      exact le_of_lt (show w y < v y from hy.2)
    have hxnotG : x ∉ G := by
      rw [hGo.frontier_eq] at hx
      exact hx.2
    by_cases hxb : x ∈ ball x₀ r
    · exact le_antisymm hle
        (le_of_not_gt fun hlt => hxnotG ⟨hxb, hlt⟩)
    · have hnle : ‖x - x₀‖ ≤ r := by
        simpa only [mem_closedBall, dist_eq_norm] using hxclB
      have hnge : r ≤ ‖x - x₀‖ := by
        apply le_of_not_gt
        intro hlt
        apply hxb
        simpa only [mem_ball, dist_eq_norm] using hlt
      exact le_antisymm hle (hsphere x (le_antisymm hnle hnge))
  refine ⟨G, hGo, hGball, hGb, ⟨x₀, mem_ball_self hr, hcenter⟩, ?_⟩
  exact subgradientImage_subset_of_le hw hv hGo hGb
    (fun x hx => le_of_lt (show w x < v x from hx.2)) hGeq

private lemma touching_cancel_volume {n : ℕ}
    {G : Set (EuclideanSpace ℝ (Fin n))}
    (hpos : 0 < volume G) (hfin : volume G < ∞)
    {a b : ℝ} (hb : 0 ≤ b)
    (h : ENNReal.ofReal a * volume G ≤ ENNReal.ofReal b * volume G) :
    a ≤ b := by
  apply (ENNReal.ofReal_le_ofReal_iff hb).mp
  exact
    (ENNReal.mul_le_mul_iff_right (ne_of_gt hpos) (ne_of_lt hfin)).mp
      (by simpa only [mul_comm] using h)

set_option maxHeartbeats 800000 in
/-- **Upper touching test for an Alexandrov solution** (weak Letwin route, N8 viscosity inequality,
T12c): if the subgradient images of the convex `u` on open subsets of `Ω` carry the density `f`
(`vol (∂u(G)) = ∫_G f`), `f` is continuous at `x₀ ∈ Ω`, and a `C²` function `ψ` touches `u` from above
at `x₀` (`u ≤ ψ` near `x₀`, `u x₀ = ψ x₀`), then `f x₀ ≤ det ∇²ψ(x₀)` (standard coordinates of
`EuclideanSpace ℝ (Fin n)`, `hessianMatrix ψ x₀ i j = D²ψ(x₀)(eᵢ, eⱼ)`). -/
theorem le_det_hessianMatrix_of_upper_touch {n : ℕ} {u f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    f x₀ ≤ (hessianMatrix ψ x₀).det := by
  classical
  apply le_of_not_gt
  intro hbad
  let A := hessianMatrix ψ x₀
  have hA : A.PosSemidef :=
    posSemidef_hessianMatrix_of_upper_touch hconv hψ hcontact htouch
  change A.det < f x₀ at hbad
  obtain ⟨a, hAa, haf⟩ := exists_between hbad
  have hdcont : Continuous (fun t : ℝ => (A + (4 * t) • 1).det) :=
    (continuous_const.add
      ((continuous_const.mul continuous_id).smul continuous_const)).matrix_det
  have hdnear : ∀ᶠ t : ℝ in 𝓝 0, (A + (4 * t) • 1).det < a :=
    hdcont.continuousAt.eventually_lt continuous_const.continuousAt
      (by simpa using hAa)
  obtain ⟨ε, hε, hdet⟩ := touching_positive_parameter hdnear
  let M : Matrix (Fin n) (Fin n) ℝ := A + (4 * ε) • 1
  have hM : M.PosDef := by
    dsimp only [M]
    simpa only [add_comm] using
      (Matrix.PosDef.one.smul (show 0 < 4 * ε by positivity)).add_posSemidef hA
  have hMdet : M.det < a := hdet
  let b : EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ ψ x₀)
  let q := quadraticAt A x₀ b (ψ x₀)
  obtain ⟨ρ, hρ, htaylor⟩ := exists_taylor_two_hessianMatrix_bound hψ hε
  have htaylor' (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball x₀ ρ) :
      |ψ x - q x| ≤ ε * ‖x - x₀‖ ^ 2 := by
    simpa only [q, A, b, quadraticAt, InnerProductSpace.toDual_symm_apply]
      using htaylor x hx
  have hfnear : ∀ᶠ x in 𝓝 x₀, a < f x :=
    continuous_const.continuousAt.eventually_lt hf haf
  have hnear : ∀ᶠ x in 𝓝 x₀,
      x ∈ Ω ∧ u x ≤ ψ x ∧ a ≤ f x ∧
        |ψ x - q x| ≤ ε * ‖x - x₀‖ ^ 2 := by
    filter_upwards [hΩ.mem_nhds hx₀, htouch, hfnear, ball_mem_nhds x₀ hρ]
      with x hxΩ hxu hxf hxt
    exact ⟨hxΩ, hxu, le_of_lt hxf, htaylor' x hxt⟩
  obtain ⟨r, hr, hlocal⟩ := touching_closedBall hnear
  let w := quadraticAt M x₀ b (ψ x₀ - ε * r ^ 2)
  have hwconv : ConvexOn ℝ univ w :=
    convexOn_quadraticAt hM.posSemidef x₀ b (ψ x₀ - ε * r ^ 2)
  have hwformula (x : EuclideanSpace ℝ (Fin n)) :
      w x = q x - ε * r ^ 2 + 2 * ε * ‖x - x₀‖ ^ 2 := by
    dsimp only [w, M, q]
    rw [touching_quadratic_shift A x₀ b x
      (ψ x₀ - ε * r ^ 2) (ψ x₀) (4 * ε)]
    ring
  have hwcenter : w x₀ = ψ x₀ - ε * r ^ 2 := by
    simp [w, quadraticAt]
  have hcenter : w x₀ < u x₀ := by
    rw [hwcenter, hcontact]
    have hpos : 0 < ε * r ^ 2 := mul_pos hε (sq_pos_of_pos hr)
    linarith
  have hsphere : ∀ x, ‖x - x₀‖ = r → u x ≤ w x := by
    intro x hxr
    have hx : x ∈ closedBall x₀ r := by
      simpa only [mem_closedBall, dist_eq_norm, hxr] using (le_refl r)
    have hloc := hlocal x hx
    have he := (abs_le.mp hloc.2.2.2).2
    rw [hxr] at he
    rw [hwformula, hxr]
    nlinarith [hloc.2.1]
  obtain ⟨G, hGo, hGball, hGb, hGne, hcomp⟩ :=
    touching_comparison_set hconv hwconv hr hcenter hsphere
  have hGΩ : G ⊆ Ω := by
    intro x hx
    exact (hlocal x (ball_subset_closedBall (hGball hx))).1
  have hGpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) G :=
    IsOpen.measure_pos volume hGo hGne
  have hGfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) G < ∞ :=
    hGb.measure_lt_top
  have hmul :
      ENNReal.ofReal a * volume G ≤ ENNReal.ofReal M.det * volume G := by
    calc
      ENNReal.ofReal a * volume G =
          ∫⁻ x in G, ENNReal.ofReal a ∂volume :=
        (setLIntegral_const G (ENNReal.ofReal a)).symm
      _ ≤ ∫⁻ x in G, ENNReal.ofReal (f x) ∂volume := by
        apply setLIntegral_mono' hGo.measurableSet
        intro x hx
        exact ENNReal.ofReal_mono
          (hlocal x (ball_subset_closedBall (hGball hx))).2.2.1
      _ = volume (subgradientImage u G) := (hMA G hGo hGΩ).symm
      _ ≤ volume (subgradientImage w G) := measure_mono hcomp
      _ = ENNReal.ofReal M.det * volume G :=
        volume_subgradientImage_quadraticAt hM x₀ b
          (ψ x₀ - ε * r ^ 2) hGo.measurableSet
  have hcoef : a ≤ M.det :=
    touching_cancel_volume hGpos hGfin hM.det_pos.le hmul
  exact (not_le_of_gt hMdet) hcoef

set_option maxHeartbeats 800000 in
/-- **Lower touching test for an Alexandrov solution** (weak Letwin route, N8, T12c): with the
same Alexandrov hypothesis, if `ψ ∈ C²` touches `u` from below at `x₀` (`ψ ≤ u` near `x₀`,
`u x₀ = ψ x₀`) and `∇²ψ(x₀)` is positive semidefinite, then `det ∇²ψ(x₀) ≤ f x₀`. -/
theorem det_hessianMatrix_le_of_lower_touch {n : ℕ} {u f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀) (hf0 : 0 ≤ f x₀)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hH : (hessianMatrix ψ x₀).PosSemidef)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, ψ x ≤ u x) :
    (hessianMatrix ψ x₀).det ≤ f x₀ := by
  classical
  apply le_of_not_gt
  intro hbad
  let A := hessianMatrix ψ x₀
  change f x₀ < A.det at hbad
  have hA : A.PosDef :=
    hH.posDef_iff_det_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt hf0 hbad))
  obtain ⟨a, hfa, haA⟩ := exists_between hbad
  have ha0 : 0 ≤ a := le_trans hf0 hfa.le
  have hdcont :
      Continuous (fun t : ℝ => (A + (-(4 * t)) • 1).det) :=
    (continuous_const.add
      ((continuous_const.mul continuous_id).neg.smul continuous_const)).matrix_det
  have hdnear : ∀ᶠ t : ℝ in 𝓝 0, a < (A + (-(4 * t)) • 1).det :=
    continuous_const.continuousAt.eventually_lt hdcont.continuousAt
      (by simpa using haA)
  have htendsto :
      Tendsto (fun t : ℝ => -(4 * t)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => -(4 * t)) :=
      (continuous_const.mul continuous_id).neg
    simpa only [mul_zero, neg_zero] using hc.tendsto 0
  have hpnear : ∀ᶠ t : ℝ in 𝓝 0, (A + (-(4 * t)) • 1).PosDef :=
    htendsto.eventually (touching_posDef_perturbation hA)
  obtain ⟨ε, hε, hdet, hpd⟩ :=
    touching_positive_parameter (hdnear.and hpnear)
  let M : Matrix (Fin n) (Fin n) ℝ := A + (-(4 * ε)) • 1
  have hM : M.PosDef := hpd
  have hMdet : a < M.det := hdet
  let b : EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ ψ x₀)
  let q := quadraticAt A x₀ b (ψ x₀)
  obtain ⟨ρ, hρ, htaylor⟩ := exists_taylor_two_hessianMatrix_bound hψ hε
  have htaylor' (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball x₀ ρ) :
      |ψ x - q x| ≤ ε * ‖x - x₀‖ ^ 2 := by
    simpa only [q, A, b, quadraticAt, InnerProductSpace.toDual_symm_apply]
      using htaylor x hx
  have hfnear : ∀ᶠ x in 𝓝 x₀, f x < a :=
    hf.eventually_lt continuous_const.continuousAt hfa
  have hnear : ∀ᶠ x in 𝓝 x₀,
      x ∈ Ω ∧ ψ x ≤ u x ∧ f x ≤ a ∧
        |ψ x - q x| ≤ ε * ‖x - x₀‖ ^ 2 := by
    filter_upwards [hΩ.mem_nhds hx₀, htouch, hfnear, ball_mem_nhds x₀ hρ]
      with x hxΩ hxu hxf hxt
    exact ⟨hxΩ, hxu, le_of_lt hxf, htaylor' x hxt⟩
  obtain ⟨r, hr, hlocal⟩ := touching_closedBall hnear
  let w := quadraticAt M x₀ b (ψ x₀ + ε * r ^ 2)
  have hwconv : ConvexOn ℝ univ w :=
    convexOn_quadraticAt hM.posSemidef x₀ b (ψ x₀ + ε * r ^ 2)
  have hwformula (x : EuclideanSpace ℝ (Fin n)) :
      w x = q x + ε * r ^ 2 - 2 * ε * ‖x - x₀‖ ^ 2 := by
    dsimp only [w, M, q]
    rw [touching_quadratic_shift A x₀ b x
      (ψ x₀ + ε * r ^ 2) (ψ x₀) (-(4 * ε))]
    ring
  have hwcenter : w x₀ = ψ x₀ + ε * r ^ 2 := by
    simp [w, quadraticAt]
  have hcenter : u x₀ < w x₀ := by
    rw [hwcenter, hcontact]
    have hpos : 0 < ε * r ^ 2 := mul_pos hε (sq_pos_of_pos hr)
    linarith
  have hsphere : ∀ x, ‖x - x₀‖ = r → w x ≤ u x := by
    intro x hxr
    have hx : x ∈ closedBall x₀ r := by
      simpa only [mem_closedBall, dist_eq_norm, hxr] using (le_refl r)
    have hloc := hlocal x hx
    have he := (abs_le.mp hloc.2.2.2).1
    rw [hxr] at he
    rw [hwformula, hxr]
    nlinarith [hloc.2.1]
  obtain ⟨G, hGo, hGball, hGb, hGne, hcomp⟩ :=
    touching_comparison_set hwconv hconv hr hcenter hsphere
  have hGΩ : G ⊆ Ω := by
    intro x hx
    exact (hlocal x (ball_subset_closedBall (hGball hx))).1
  have hGpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) G :=
    IsOpen.measure_pos volume hGo hGne
  have hGfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) G < ∞ :=
    hGb.measure_lt_top
  have hmul :
      ENNReal.ofReal M.det * volume G ≤ ENNReal.ofReal a * volume G := by
    calc
      ENNReal.ofReal M.det * volume G =
          volume (subgradientImage w G) :=
        (volume_subgradientImage_quadraticAt hM x₀ b
          (ψ x₀ + ε * r ^ 2) hGo.measurableSet).symm
      _ ≤ volume (subgradientImage u G) := measure_mono hcomp
      _ = ∫⁻ x in G, ENNReal.ofReal (f x) ∂volume := hMA G hGo hGΩ
      _ ≤ ∫⁻ x in G, ENNReal.ofReal a ∂volume := by
        apply setLIntegral_mono' hGo.measurableSet
        intro x hx
        exact ENNReal.ofReal_mono
          (hlocal x (ball_subset_closedBall (hGball hx))).2.2.1
      _ = ENNReal.ofReal a * volume G :=
        setLIntegral_const G (ENNReal.ofReal a)
  have hcoef : M.det ≤ a :=
    touching_cancel_volume hGpos hGfin ha0 hmul
  exact (not_le_of_gt hMdet) hcoef

end FunctionalInequalities.Analysis

end LT12C4ViscosityTouchingAssembly

section LT12E1AlexandrovPointEquation

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

/-! At a point of second-order expansion the Monge–Ampère equation holds pointwise with a positive definite Hessian (task L-T12e1). -/

namespace FunctionalInequalities.Analysis

/-- `quadraticAt A x₀ b c` is smooth (weak Letwin route, task T12e1). -/
theorem contDiff_quadraticAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) : ContDiff ℝ 2 (quadraticAt A x₀ b c) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  change ContDiff ℝ 2
    (fun x => c + ⟪b, x - x₀⟫ + (1 / 2 : ℝ) * ⟪x - x₀, T (x - x₀)⟫)
  exact (contDiff_const.add
    (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const))).add
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).inner ℝ
      (T.contDiff.comp (contDiff_id.sub contDiff_const))))

private lemma quadraticAt_fderiv_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (y w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (quadraticAt A x₀ b c) y w =
      ⟪b, w⟫ + (1 / 2 : ℝ) *
        (⟪y - x₀, Matrix.toEuclideanLin A w⟫ +
          ⟪w, Matrix.toEuclideanLin A (y - x₀)⟫) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hd := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x₀
  have ht := T.hasFDerivAt.comp y hd
  have hb := (hasFDerivAt_const (𝕜 := ℝ) b y).inner ℝ hd
  have hq := hd.inner ℝ ht
  have hh := (hb.const_add c).add (hq.const_mul (1 / 2 : ℝ))
  change HasFDerivAt (quadraticAt A x₀ b c) _ y at hh
  rw [hh.fderiv]
  simp [fderivInnerCLM_apply, T]

private lemma quadraticAt_second_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ w x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ
      (fun y => (1 / 2 : ℝ) *
        (⟪y - x₀, Matrix.toEuclideanLin A w⟫ +
          ⟪w, Matrix.toEuclideanLin A (y - x₀)⟫)) x v =
      (1 / 2 : ℝ) *
        (⟪v, Matrix.toEuclideanLin A w⟫ + ⟪w, Matrix.toEuclideanLin A v⟫) := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hd := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀
  have ht := T.hasFDerivAt.comp x hd
  have h₁ := hd.inner ℝ (hasFDerivAt_const (𝕜 := ℝ) (T w) x)
  have h₂ := (hasFDerivAt_const (𝕜 := ℝ) w x).inner ℝ ht
  have hh := (h₁.add h₂).const_mul (1 / 2 : ℝ)
  simpa [fderivInnerCLM_apply, T, mul_add] using
    congrArg (fun L => L v) hh.fderiv

private lemma quadraticAt_basis_entry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Matrix.toEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ = A i j := by
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, Matrix.toLpLin_apply 2 2]
  simp [Matrix.mulVec, dotProduct]

/-- The coordinate Hessian of `quadraticAt A x₀ b c` is `A` at every point when `A` is symmetric
(weak Letwin route, task T12e1). -/
theorem hessianMatrix_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (quadraticAt A x₀ b c) x = A := by
  ext i j
  change bilinearIteratedFDerivTwo ℝ (quadraticAt A x₀ b c) x
    (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j) = A i j
  rw [BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply
    (contDiff_quadraticAt A x₀ b c)]
  simp_rw [quadraticAt_fderiv_apply]
  rw [fderiv_const_add, quadraticAt_second_apply,
    quadraticAt_basis_entry, quadraticAt_basis_entry]
  have hs : A j i = A i j := by simpa using hA.apply i j
  rw [hs]
  ring

private lemma quadraticAt_shift {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    quadraticAt (A + t • 1) x₀ b c x =
      quadraticAt A x₀ b c x + t / 2 * ‖x - x₀‖ ^ 2 := by
  unfold quadraticAt
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_right, inner_smul_right]
  rw [show Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) =
    LinearMap.id by exact Matrix.toLpLin_one 2]
  simp only [LinearMap.id_apply, real_inner_self_eq_norm_sq]
  ring

private lemma quadraticAt_shift_sub {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    quadraticAt (A - t • 1) x₀ b c x =
      quadraticAt A x₀ b c x - t / 2 * ‖x - x₀‖ ^ 2 := by
  simpa only [neg_smul, sub_eq_add_neg, neg_div, neg_mul] using
    quadraticAt_shift A x₀ b c x (-t)

private lemma posSemidef_of_positive_shifts {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (hu : ∀ t : ℝ, 0 < t → (B + t • 1).PosSemidef) : B.PosSemidef := by
  have hc : Continuous (fun t : ℝ => B + t • 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hB, ?_⟩
  intro v
  have hv : Continuous (fun t : ℝ => star v ⬝ᵥ (B + t • 1).mulVec v) :=
    continuous_const.dotProduct (hc.matrix_mulVec continuous_const)
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ star v ⬝ᵥ (B + t • 1).mulVec v := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hu t ht).dotProduct_mulVec_nonneg v
  simpa using ge_of_tendsto
    (hv.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))) hh

private lemma posSemidef_sub_eventually {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) :
    ∀ᶠ t : ℝ in 𝓝 0, (B - t • 1).PosSemidef := by
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, t < hB.1.eigenvalues i :=
    eventually_all.mpr (fun i => eventually_lt_nhds (hB.eigenvalues_pos i))
  filter_upwards [he] with t ht
  let U := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)
    hB.1.eigenvectorUnitary
  have hd : (Matrix.diagonal (fun i => hB.1.eigenvalues i - t)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => le_of_lt (sub_pos.mpr (ht i)))
  have hc : Matrix.diagonal (fun _ : Fin n => t) =
      t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have heq : B - t • 1 =
      U (Matrix.diagonal (fun i => hB.1.eigenvalues i - t)) := by
    rw [← Matrix.diagonal_sub, map_sub, hc, map_smul, map_one]
    congr 1
    simpa [U, Function.comp_def] using hB.1.spectral_theorem
  rw [heq]
  exact hd.mul_mul_conjTranspose_same _

/-- **The Monge–Ampère equation at points of second-order differentiability** (weak Letwin route, N8;
task T12e1): if the subgradient images of the convex `u` on open subsets of `Ω` carry the density `f`,
`f` is continuous and positive at `x₀ ∈ Ω`, and `u` has a second-order expansion at `x₀` with a symmetric
matrix `B` (`|u x − (u x₀ + ⟪g, x − x₀⟫ + ½ ⟪x − x₀, B (x − x₀)⟫)| ≤ ε ‖x − x₀‖²` near `x₀` for every
`ε > 0`), then `B` is positive definite and `det B = f x₀`. -/
theorem posDef_and_det_eq_of_quadratic_expansion {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀) (hfpos : 0 < f x₀)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) {g : EuclideanSpace ℝ (Fin n)}
    (hexp : ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, |u x - quadraticAt B x₀ g (u x₀) x| ≤ ε * ‖x - x₀‖ ^ 2) :
    B.PosDef ∧ B.det = f x₀ := by
  have hu : ∀ t : ℝ, 0 < t →
      (B + t • 1).PosSemidef ∧ f x₀ ≤ (B + t • 1).det := by
    intro t ht
    have hs : (B + t • 1).IsHermitian :=
      hB.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t))
    have hc : u x₀ = quadraticAt (B + t • 1) x₀ g (u x₀) x₀ := by
      simp [quadraticAt]
    have htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ quadraticAt (B + t • 1) x₀ g (u x₀) x := by
      filter_upwards [hexp (t / 2) (by positivity)] with x hx
      rw [quadraticAt_shift]
      have hh := (abs_le.mp hx).2
      linarith
    have hψ : ContDiffAt ℝ 2 (quadraticAt (B + t • 1) x₀ g (u x₀)) x₀ :=
      (contDiff_quadraticAt (B + t • 1) x₀ g (u x₀)).contDiffAt
    have hp := posSemidef_hessianMatrix_of_upper_touch hconv hψ hc htouch
    have hd := le_det_hessianMatrix_of_upper_touch hconv hΩ hMA hx₀ hf hψ hc htouch
    rw [hessianMatrix_quadraticAt hs] at hp hd
    exact ⟨hp, hd⟩
  have hplus : Continuous (fun t : ℝ => B + t • 1) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hdet_lower : f x₀ ≤ B.det := by
    have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, f x₀ ≤ (B + t • 1).det := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hu t ht).2
    simpa using ge_of_tendsto
      (hplus.matrix_det.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))) hh
  have hps : B.PosSemidef :=
    posSemidef_of_positive_shifts hB (fun t ht => (hu t ht).1)
  have hpd : B.PosDef :=
    hps.posDef_iff_det_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hfpos hdet_lower))
  refine ⟨hpd, le_antisymm ?_ hdet_lower⟩
  have hlower : ∀ᶠ t : ℝ in 𝓝[>] 0, (B - t • 1).det ≤ f x₀ := by
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (B - t • 1).PosSemidef :=
      (posSemidef_sub_eventually hpd).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, he] with t ht hpt
    have hc : u x₀ = quadraticAt (B - t • 1) x₀ g (u x₀) x₀ := by
      simp [quadraticAt]
    have htouch : ∀ᶠ x in 𝓝 x₀, quadraticAt (B - t • 1) x₀ g (u x₀) x ≤ u x := by
      filter_upwards [hexp (t / 2) (by exact div_pos ht (by norm_num))] with x hx
      rw [quadraticAt_shift_sub]
      have hh := (abs_le.mp hx).1
      linarith
    have hψ : ContDiffAt ℝ 2 (quadraticAt (B - t • 1) x₀ g (u x₀)) x₀ :=
      (contDiff_quadraticAt (B - t • 1) x₀ g (u x₀)).contDiffAt
    have hH : (hessianMatrix (quadraticAt (B - t • 1) x₀ g (u x₀)) x₀).PosSemidef := by
      rw [hessianMatrix_quadraticAt hpt.1]
      exact hpt
    have hd := det_hessianMatrix_le_of_lower_touch
      hconv hΩ hMA hx₀ hf hfpos.le hψ hH hc htouch
    rwa [hessianMatrix_quadraticAt hpt.1] at hd
  have hminus : Continuous (fun t : ℝ => B - t • 1) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  simpa using le_of_tendsto
    (hminus.matrix_det.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))) hlower

end FunctionalInequalities.Analysis

end LT12E1AlexandrovPointEquation

section LT12D8MollifiedLogdetBound

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

/-! The log-determinant of the Hessian bounds the mollified Monge–Ampère density from above at points with positive definite Hessian (task L-T12d8). -/

namespace FunctionalInequalities.Analysis

private lemma expansion_secondDifference {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x g : EuclideanSpace ℝ (Fin n)}
    {B : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ =>
      (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2)
      (𝓝[>] 0) (𝓝 ⟪v, Matrix.toEuclideanLin B v⟫) := by
  let q := ⟪v, Matrix.toEuclideanLin B v⟫
  have hp (t : ℝ) :
      quadraticAt B x g (u x) (x + t • v) =
        u x + t * ⟪g, v⟫ + (1 / 2) * (t ^ 2 * q) := by
    have he : x + t • v - x = t • v := by abel
    simp only [quadraticAt, he, map_smul, real_inner_smul_left,
      real_inner_smul_right, q]
    ring
  have hm (t : ℝ) :
      quadraticAt B x g (u x) (x - t • v) =
        u x - t * ⟪g, v⟫ + (1 / 2) * (t ^ 2 * q) := by
    simpa only [neg_smul, ← sub_eq_add_neg, neg_mul, neg_sq] using hp (-t)
  have htp : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  have htm : Tendsto (fun t : ℝ => x - t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x - t • v) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    simpa only [zero_smul, sub_zero] using hc.tendsto 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (4 * (‖v‖ ^ 2 + 1))
  have hd : 0 < 4 * (‖v‖ ^ 2 + 1) := by positivity
  have hη : 0 < η := div_pos hε hd
  have hηeq : η * (4 * (‖v‖ ^ 2 + 1)) = ε :=
    div_mul_cancel₀ _ (ne_of_gt hd)
  have hsmall : 2 * η * ‖v‖ ^ 2 < ε := by
    nlinarith [sq_nonneg ‖v‖]
  filter_upwards [(htp.eventually (h η hη)).filter_mono nhdsWithin_le_nhds,
    (htm.eventually (h η hη)).filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with t ht₁ ht₂ ht
  have htpos : 0 < t := ht
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
  have hnum :
      |(u (x + t • v) + u (x - t • v) - 2 * u x) - t ^ 2 * q| ≤
        2 * η * t ^ 2 * ‖v‖ ^ 2 := by
    calc
      _ = |(u (x + t • v) - quadraticAt B x g (u x) (x + t • v)) +
          (u (x - t • v) - quadraticAt B x g (u x) (x - t • v))| := by
        rw [hp, hm]
        congr 1
        ring
      _ ≤ |u (x + t • v) - quadraticAt B x g (u x) (x + t • v)| +
          |u (x - t • v) - quadraticAt B x g (u x) (x - t • v)| :=
        abs_add_le _ _
      _ ≤ η * ‖x + t • v - x‖ ^ 2 + η * ‖x - t • v - x‖ ^ 2 :=
        add_le_add ht₁ ht₂
      _ = _ := by
        have he₁ : x + t • v - x = t • v := by abel
        have he₂ : x - t • v - x = -(t • v) := by abel
        rw [he₁, he₂, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        ring
  have heq :
      (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 - q =
        ((u (x + t • v) + u (x - t • v) - 2 * u x) - t ^ 2 * q) / t ^ 2 := by
    field_simp
  change dist ((u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2) q < ε
  rw [Real.dist_eq, heq, abs_div, abs_of_pos ht2]
  apply (div_lt_iff₀ ht2).mpr
  have hh := mul_lt_mul_of_pos_right hsmall ht2
  nlinarith

private lemma smooth_secondDifference {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ} (hw : ContDiff ℝ 2 w)
    (x v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ =>
      (w (x + t • v) + w (x - t • v) - 2 * w x) / t ^ 2)
      (𝓝[>] 0) (𝓝 ⟪v, Matrix.toEuclideanLin (hessianMatrix w x) v⟫) := by
  apply expansion_secondDifference
    (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ w x))
  intro ε hε
  obtain ⟨r, hr, hb⟩ := exists_taylor_two_hessianMatrix_bound hw.contDiffAt hε
  filter_upwards [ball_mem_nhds x hr] with y hy
  simpa only [quadraticAt, InnerProductSpace.toDual_symm_apply] using hb y hy

private lemma convolution_shift {n : ℕ}
    (ρ u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x a : EuclideanSpace ℝ (Fin n)) :
    (∫ y, u (y + a) * ρ (x - y)) =
      convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + a) := by
  rw [← integral_sub_left_eq_self (fun y => u (y + a) * ρ (x - y)) volume x]
  unfold convolution
  apply integral_congr_ae
  filter_upwards [] with y
  have he : x - y + a = x + a - y := by abel
  simp only [sub_sub_cancel, he, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_comm _ _

private lemma convolution_hessian_integral {n : ℕ}
    {ρ u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ) (hu : Continuous u)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin
      (hessianMatrix (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) v⟫ =
      ∫ y, u y * iteratedFDeriv ℝ 2 (fun z => ρ (x - z)) y (fun _ => v) := by
  let χ := fun y => ρ (x - y)
  let w := convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hχ : ContDiff ℝ 2 χ := hρ.comp (contDiff_const.sub contDiff_id)
  have hχc : HasCompactSupport χ := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hi (a : EuclideanSpace ℝ (Fin n)) :
      Integrable (fun y => u (y + a) * χ y) volume := by
    have hc : Continuous (fun y => u (y + a) * χ y) :=
      (hu.comp (continuous_id.add continuous_const)).mul hχ.continuous
    exact hc.integrable_of_hasCompactSupport hχc.mul_left
  have hi₀ : Integrable (fun y => u y * χ y) volume := by
    simpa only [add_zero] using hi 0
  have he (t : ℝ) :
      (∫ y, (u (y + t • v) + u (y - t • v) - 2 * u y) / t ^ 2 * χ y) =
        (w (x + t • v) + w (x - t • v) - 2 * w x) / t ^ 2 := by
    have him : Integrable (fun y => u (y - t • v) * χ y) volume := by
      simpa only [neg_smul, ← sub_eq_add_neg] using hi ((-t) • v)
    have hip : Integrable
        (fun y => u (y + t • v) * χ y + u (y - t • v) * χ y) volume :=
      (hi (t • v)).add him
    calc
      _ = (∫ y, ((u (y + t • v) * χ y + u (y - t • v) * χ y) -
          2 * (u y * χ y)) / t ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = ((∫ y, u (y + t • v) * χ y) +
          (∫ y, u (y - t • v) * χ y) -
          2 * (∫ y, u y * χ y)) / t ^ 2 := by
        rw [integral_div,
          integral_sub
            (f := fun y => u (y + t • v) * χ y + u (y - t • v) * χ y)
            (g := fun y => 2 * (u y * χ y)) hip (hi₀.const_mul 2),
          integral_add
            (f := fun y => u (y + t • v) * χ y)
            (g := fun y => u (y - t • v) * χ y) (hi (t • v)) him,
          integral_const_mul]
      _ = _ := by
        have he₁ := convolution_shift ρ u x (t • v)
        have he₂ := convolution_shift ρ u x (-(t • v))
        have he₀ := convolution_shift ρ u x 0
        simpa only [χ, w, add_zero, ← sub_eq_add_neg] using
          congrArg (fun p : ℝ × ℝ × ℝ => (p.1 + p.2.1 - 2 * p.2.2) / t ^ 2)
            (show
              ((∫ y, u (y + t • v) * ρ (x - y)),
                (∫ y, u (y + -(t • v)) * ρ (x - y)),
                (∫ y, u (y + 0) * ρ (x - y))) =
              (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + t • v),
                convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + -(t • v)),
                convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume (x + 0)) from
              by rw [he₁, he₂, he₀])
  have hw : ContDiff ℝ 2 w :=
    hρc.contDiff_convolution_left _ hρ hu.locallyIntegrable
  exact tendsto_nhds_unique (smooth_secondDifference hw x v)
    ((tendsto_integral_secondDifference_mul hu hχ hχc v).congr he)

private lemma convolution_convex {n : ℕ}
    {ρ u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hconv : ConvexOn ℝ univ u) :
    ConvexOn ℝ univ (convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hi (z : EuclideanSpace ℝ (Fin n)) :
      Integrable (fun y => ρ y * u (z - y)) volume := by
    have hc : Continuous (fun y => ρ y * u (z - y)) :=
      hρ.mul (hu.comp (continuous_const.sub continuous_id))
    exact hc.integrable_of_hasCompactSupport hρc.mul_right
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ s t hs ht hst
  change (∫ y, ρ y * u (s • a + t • b - y)) ≤
    s * (∫ y, ρ y * u (a - y)) + t * (∫ y, ρ y * u (b - y))
  calc
    _ ≤ ∫ y, s * (ρ y * u (a - y)) + t * (ρ y * u (b - y)) := by
      apply integral_mono (hi _) (((hi a).const_mul s).add ((hi b).const_mul t))
      intro y
      change ρ y * u (s • a + t • b - y) ≤
        s * (ρ y * u (a - y)) + t * (ρ y * u (b - y))
      have hc := hconv.2 (mem_univ (a - y)) (mem_univ (b - y)) hs ht hst
      have he : s • (a - y) + t • (b - y) = s • a + t • b - y := by
        calc
          _ = s • a + t • b - (s + t) • y := by module
          _ = _ := by rw [hst, one_smul]
      rw [he] at hc
      change u (s • a + t • b - y) ≤ s * u (a - y) + t * u (b - y) at hc
      calc
        _ ≤ ρ y * (s * u (a - y) + t * u (b - y)) :=
          mul_le_mul_of_nonneg_left hc (hρ0 y)
        _ = _ := by ring
    _ = _ := by
      rw [integral_add
        (f := fun y => s * (ρ y * u (a - y)))
        (g := fun y => t * (ρ y * u (b - y)))
        ((hi a).const_mul s) ((hi b).const_mul t),
        integral_const_mul, integral_const_mul]

private lemma matrix_quadratic_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin A v⟫ =
      ∑ i, ∑ j, v.ofLp i * (A i j * v.ofLp j) := by
  rw [Matrix.toLpLin_apply 2 2, PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma trace_spectral_quadratic {n : ℕ}
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : J.IsHermitian)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (J * A).trace =
      ∑ i, hJ.eigenvalues i *
        ⟪hJ.eigenvectorBasis i, Matrix.toEuclideanLin A (hJ.eigenvectorBasis i)⟫ := by
  classical
  let U : Matrix (Fin n) (Fin n) ℝ := hJ.eigenvectorUnitary
  let D := Matrix.diagonal hJ.eigenvalues
  have hs : J = U * D * star U := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq] using hJ.spectral_theorem
  have he (i : Fin n) :
      (star U * A * U) i i =
        ⟪hJ.eigenvectorBasis i, Matrix.toEuclideanLin A (hJ.eigenvectorBasis i)⟫ := by
    rw [matrix_quadratic_sum]
    simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Finset.sum_mul,
      U, Matrix.IsHermitian.eigenvectorUnitary_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    (J * A).trace = (U * D * star U * A).trace := by rw [hs]
    _ = (D * (star U * A) * U).trace := by
      rw [Matrix.mul_assoc U D (star U), Matrix.mul_assoc U (D * star U) A,
        Matrix.trace_mul_comm U ((D * star U) * A), Matrix.mul_assoc D (star U) A]
    _ = (D * (star U * A * U)).trace := by rw [Matrix.mul_assoc]
    _ = _ := by
      simp only [D, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, he]

set_option maxHeartbeats 800000 in
private lemma second_weight_integrable {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => u y * iteratedFDeriv ℝ 2 χ y (fun _ => v)) volume := by
  let L := ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ (fun _ => v)
  have hc : Continuous (fun y => iteratedFDeriv ℝ 2 χ y (fun _ => v)) := by
    change Continuous (L ∘ iteratedFDeriv ℝ 2 χ)
    exact L.continuous.comp (ContDiff.continuous_iteratedFDeriv (by norm_num) hχ)
  have hs : HasCompactSupport (fun y => iteratedFDeriv ℝ 2 χ y (fun _ => v)) := by
    change HasCompactSupport (L ∘ iteratedFDeriv ℝ 2 χ)
    exact (hχc.iteratedFDeriv 2).comp_left (g := L) (map_zero L)
  exact (hu.mul hc).integrable_of_hasCompactSupport hs.mul_left

set_option maxHeartbeats 800000 in
private lemma trace_integral_bound {n : ℕ}
    {u F χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧
        F y ≤ Real.log B.det ∧ ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ z in 𝓝 y,
            |u z - quadraticAt B y g (u y) z| ≤ ε * ‖z - y‖ ^ 2)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, Matrix.toEuclideanLin H v⟫ =
        ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v))
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosDef) :
    (∫ y, (F y + Real.log J.det + n) * χ y) ≤ (J * H).trace := by
  classical
  let v := hJ.isHermitian.eigenvectorBasis
  let c := hJ.isHermitian.eigenvalues
  have hc (i : Fin n) : 0 ≤ c i := (hJ.eigenvalues_pos i).le
  have hg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
        (F y + Real.log J.det + n) - ε ≤
          ∑ i, c i * ((u (y + t • v i) + u (y - t • v i) - 2 * u y) / t ^ 2) := by
    filter_upwards [hae] with y hy
    obtain ⟨B, _, hB, hFB, g, hexp⟩ := hy
    have hlim :
        Tendsto (fun t : ℝ => ∑ i, c i *
          ((u (y + t • v i) + u (y - t • v i) - 2 * u y) / t ^ 2))
          (𝓝[>] 0) (𝓝 ((J * B).trace)) := by
      rw [trace_spectral_quadratic hJ.isHermitian B]
      exact tendsto_finsetSum _ fun i _ =>
        (expansion_secondDifference hexp (v i)).const_mul (c i)
    have htr : F y + Real.log J.det + n ≤ (J * B).trace :=
      ((forall_posDef_add_log_det_le_trace_iff hB.posSemidef (F y)).mpr
        ⟨hB, (Real.le_log_iff_exp_le hB.det_pos).mp hFB⟩) J hJ
    intro ε hε
    have hev := hlim.eventually_const_lt (show
      F y + Real.log J.det + n - ε < (J * B).trace by linarith)
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp hev
    refine ⟨δ, hδ, fun t ht htd => (hd ⟨?_, ht⟩).le⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htd
  have hi := integral_mul_le_integral_mul_sum_iteratedFDeriv hconv
    (fun i : Fin n => v i) hc hχ hχc hχ0
    ((hF.add continuous_const).add continuous_const).aestronglyMeasurable hg
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hdi (i : Fin n) := second_weight_integrable hu hχ hχc (v i)
  have he :
      (∫ y, u y * ∑ i, c i * iteratedFDeriv ℝ 2 χ y (fun _ => v i)) =
        (J * H).trace := by
    calc
      _ = ∫ y, ∑ i, c i * (u y * iteratedFDeriv ℝ 2 χ y (fun _ => v i)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, c i * ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v i) := by
        rw [integral_finsetSum _ (fun i _ => (hdi i).const_mul (c i))]
        simp only [integral_const_mul]
      _ = _ := by
        rw [trace_spectral_quadratic hJ.isHermitian H]
        apply Finset.sum_congr rfl
        intro i _
        rw [hH]
  exact he ▸ hi

/-- **Mollified log-det lower bound** (weak Letwin route, N8/N9, task T12d8; KLS500
`weak_moment_mollified_average_det_lower`, via Fatou instead of the viscosity–distribution lemma): if the
convex `u` has at almost every point a second-order expansion with a positive definite symmetric matrix
`B` with `F x ≤ log det B`, `F` continuous, then every mollification `uφ := φ.normed ⋆ u` has a positive
definite Hessian with `(φ.normed ⋆ F)(x) ≤ log det ∇²uφ(x)`. -/
theorem posDef_and_convolution_le_log_det_hessianMatrix {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧ F x ≤ Real.log B.det ∧
        ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    (hessianMatrix (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x).PosDef ∧
      convolution (φ.normed volume) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x ≤
        Real.log (hessianMatrix
          (convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x).det := by
  classical
  let ρ := φ.normed volume
  let w := convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  let χ := fun y => ρ (x - y)
  let H := hessianMatrix w x
  let b := convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x
  have hρ : ContDiff ℝ 2 ρ := φ.contDiff_normed
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hρ0 : ∀ y, 0 ≤ ρ y := φ.nonneg_normed
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hw : ContDiff ℝ 2 w :=
    hρc.contDiff_convolution_left _ hρ hu.locallyIntegrable
  have hwconv : ConvexOn ℝ univ w :=
    convolution_convex hρ.continuous hρc hρ0 hconv
  have hH : H.PosSemidef :=
    posSemidef_hessianMatrix_of_upper_touch hwconv hw.contDiffAt rfl
      (Filter.Eventually.of_forall fun _ => le_rfl)
  have hχ : ContDiff ℝ 2 χ := hρ.comp (contDiff_const.sub contDiff_id)
  have hχc : HasCompactSupport χ := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hχ0 : ∀ y, 0 ≤ χ y := fun y => hρ0 (x - y)
  have hχi : Integrable χ volume :=
    hχ.continuous.integrable_of_hasCompactSupport hχc
  have hχone : (∫ y, χ y) = 1 := by
    dsimp only [χ]
    rw [integral_sub_left_eq_self]
    exact φ.integral_normed
  have hb : (∫ y, F y * χ y) = b := by
    simpa only [χ, b, add_zero] using convolution_shift ρ F x 0
  have hFi : Integrable (fun y => F y * χ y) volume :=
    (hF.mul hχ.continuous).integrable_of_hasCompactSupport hχc.mul_left
  have htrace : ∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef →
      b + Real.log J.det + n ≤ (J * H).trace := by
    intro J hJ
    have ht := trace_integral_bound hconv hF hae hχ hχc hχ0 H
      (fun v => convolution_hessian_integral hρ hρc hu x v) J hJ
    have he :
        (∫ y, (F y + Real.log J.det + n) * χ y) =
          b + Real.log J.det + n := by
      calc
        _ = ∫ y, (F y * χ y + Real.log J.det * χ y) + (n : ℝ) * χ y := by
          apply integral_congr_ae
          filter_upwards [] with y
          ring
        _ = _ := by
          rw [integral_add
              (f := fun y => F y * χ y + Real.log J.det * χ y)
              (g := fun y => (n : ℝ) * χ y)
              (hFi.add (hχi.const_mul (Real.log J.det))) (hχi.const_mul (n : ℝ)),
            integral_add
              (f := fun y => F y * χ y)
              (g := fun y => Real.log J.det * χ y)
              hFi (hχi.const_mul (Real.log J.det)),
            integral_const_mul, integral_const_mul, hχone, hb, mul_one, mul_one]
    exact he ▸ ht
  obtain ⟨hpos, hdet⟩ := (forall_posDef_add_log_det_le_trace_iff hH b).mp htrace
  exact ⟨hpos, (Real.le_log_iff_exp_le hpos.det_pos).mpr hdet⟩

end FunctionalInequalities.Analysis

end LT12D8MollifiedLogdetBound

section LT12D6BAeMongeAmpere

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

/-! **The Monge–Ampère equation almost everywhere**: an Alexandrov solution has, at almost every point, a quadratic expansion with positive definite Hessian whose determinant equals the density (task L-T12d6b). -/

namespace FunctionalInequalities.Analysis

/-- **Alexandrov's theorem in coordinates** (weak Letwin route, task T12d6b): a convex function on
`EuclideanSpace ℝ (Fin n)` has, at almost every point `x`, a second-order expansion
`|u y − quadraticAt B x g (u x) y| ≤ ε ‖y − x‖²` near `x` with a symmetric matrix `B`. -/
theorem ae_exists_quadraticAt_expansion {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ ∃ g : EuclideanSpace ℝ (Fin n),
        ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  filter_upwards [ae_exists_secondOrder_expansion hconv] with x hx
  rcases hx with ⟨p, B, hsym, _, hexp⟩
  let A : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.toEuclideanLin.symm
      (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hA : Matrix.toEuclideanLin A =
      (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
    Matrix.toEuclideanLin.apply_symm_apply _
  have hHermitian : A.IsHermitian := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    rw [hA]
    exact hsym
  have hquad (v : EuclideanSpace ℝ (Fin n)) :
      ⟪v, Matrix.toEuclideanLin A v⟫ = ⟪B v, v⟫ := by
    rw [hA]
    exact real_inner_comm (B v) v
  refine ⟨A, hHermitian, p, ?_⟩
  intro ε hε
  filter_upwards [hexp ε hε] with y hy
  simpa only [quadraticAt, hquad, sub_add_eq_sub_sub] using hy

/-- **The a.e. Monge–Ampère equation for an Alexandrov solution** (weak Letwin route, N8, task T12d6b):
if the subgradient images of the convex `u` on open sets carry a continuous positive density `f`, then at
almost every point `u` has a second-order expansion with a positive definite symmetric `B`, `det B = f x`. -/
theorem ae_exists_posDef_det_eq {n : ℕ} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧ B.det = f x ∧
        ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  filter_upwards [ae_exists_quadraticAt_expansion hconv] with x hx
  rcases hx with ⟨B, hB, g, hexp⟩
  have hresult : B.PosDef ∧ B.det = f x :=
    posDef_and_det_eq_of_quadratic_expansion hconv
      (Ω := univ) isOpen_univ
      (fun G hG _ => hMA G hG)
      (mem_univ x) hf.continuousAt (hfpos x) hB hexp
  exact ⟨B, hB, hresult.1, hresult.2, g, hexp⟩

end FunctionalInequalities.Analysis

end LT12D6BAeMongeAmpere

section LT17BMaximumWithComparison

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

/-! Existence of a penalized maximum with a quadratic comparison function (C^{1,1} estimate N9; task L-T17b). -/

namespace FunctionalInequalities.Analysis

private def n9_average {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (h y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 2 : ℝ) * (g (y + h) + g (y - h))

private lemma n9_average_continuous {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (h : EuclideanSpace ℝ (Fin n)) :
    Continuous (n9_average g h) :=
  continuous_const.mul
    ((hg.comp (continuous_id.add continuous_const)).add
      (hg.comp (continuous_id.sub continuous_const)))

private lemma n9_average_smooth {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 2 g)
    (h : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 2 (n9_average g h) :=
  contDiff_const.mul
    ((hg.comp (contDiff_id.add contDiff_const)).add
      (hg.comp (contDiff_id.sub contDiff_const)))

private lemma n9_hessian_add {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => f y + g y) x =
      hessianMatrix f x + hessianMatrix g x := by
  ext i j
  simp only [Matrix.add_apply, hessianMatrix,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  rw [show (fun y => f y + g y) = f + g from rfl,
    iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt]
  rfl

private lemma n9_hessian_mul {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => c * f y) x = c • hessianMatrix f x := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, hessianMatrix,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  rw [show (fun y => c * f y) = c • f from rfl,
    iteratedFDeriv_const_smul_apply hf.contDiffAt]
  rfl

private lemma n9_hessian_sub_const {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => f y - c) x = hessianMatrix f x := by
  ext i j
  simp only [hessianMatrix, bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  rw [show (fun y => f y - c) = f - (fun _ => c) from rfl,
    iteratedFDeriv_sub_apply hf.contDiffAt contDiffAt_const]
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]

private lemma n9_hessian_translate {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => f (y + h)) x = hessianMatrix f (x + h) := by
  ext i j
  simp only [hessianMatrix, bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    iteratedFDeriv_comp_add_right]

private lemma n9_hessian_sub_translate {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (fun y => f (y - h)) x = hessianMatrix f (x - h) := by
  simpa only [sub_eq_add_neg] using n9_hessian_translate f (-h) x

private lemma n9_hessian_average {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 2 g)
    (h x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix (n9_average g h) x =
      (1 / 2 : ℝ) • (hessianMatrix g (x + h) + hessianMatrix g (x - h)) := by
  have hp : ContDiff ℝ 2 (fun y => g (y + h)) :=
    hg.comp (contDiff_id.add contDiff_const)
  have hm : ContDiff ℝ 2 (fun y => g (y - h)) :=
    hg.comp (contDiff_id.sub contDiff_const)
  unfold n9_average
  rw [n9_hessian_mul (hp.add hm), n9_hessian_add hp hm,
    n9_hessian_translate, n9_hessian_sub_translate]

private lemma n9_midpoint_det {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : a ≤ Real.log A.det) (hb : b ≤ Real.log B.det) :
    Real.exp ((a + b) / 2) ≤ ((1 / 2 : ℝ) • (A + B)).det := by
  have hM := (hA.add hB).smul (by norm_num : (0 : ℝ) < 1 / 2)
  apply ((forall_posDef_add_log_det_le_trace_iff hM.posSemidef
    ((a + b) / 2)).mp ?_).2
  intro J hJ
  have h1 := ((forall_posDef_add_log_det_le_trace_iff hA.posSemidef
    (Real.log A.det)).mpr ⟨hA, by rw [Real.exp_log hA.det_pos]⟩) J hJ
  have h2 := ((forall_posDef_add_log_det_le_trace_iff hB.posSemidef
    (Real.log B.det)).mpr ⟨hB, by rw [Real.exp_log hB.det_pos]⟩) J hJ
  simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
    Matrix.trace_add, smul_eq_mul]
  linarith

private lemma n9_scaled_det_comparison {n : ℕ}
    {α b f : ℝ} {M : Matrix (Fin n) (Fin n) ℝ}
    (ha : 0 < α) (hM : M.PosDef)
    (hl : Real.exp b ≤ M.det) (hu : (α⁻¹ • M).det ≤ Real.exp f) :
    b - n * Real.log α ≤ f := by
  have hl' := Real.log_le_log (Real.exp_pos b) hl
  have hu' := Real.log_le_log ((hM.smul (inv_pos.mpr ha)).det_pos) hu
  rw [Real.log_exp] at hl'
  rw [Matrix.det_smul, Fintype.card_fin,
    Real.log_mul (pow_ne_zero _ (inv_ne_zero ha.ne')) hM.det_pos.ne',
    Real.log_pow, Real.log_inv, Real.log_exp] at hu'
  linarith

private lemma n9_maximizers {E : Type} [TopologicalSpace E] [Zero E]
    {u A : E → ℝ} {V : ℕ → E → ℝ}
    (hu : Continuous u) (hcoer : ∀ R : ℝ, IsCompact {x | u x ≤ R})
    (hV : ∀ k, Continuous (V k))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hc : ∀ k x, |V k x - A x| ≤ δ k)
    {C : ℝ} (hC : ∀ x, A x ≤ u x + C)
    {α : ℝ} (hα : 1 < α) :
    ∃ R : ℝ, ∃ x : ℕ → E,
      (∀ k, u (x k) ≤ R) ∧
      ∀ k y, V k y - α * u y ≤ V k (x k) - α * u (x k) := by
  obtain ⟨D, hD⟩ := hδ.bddAbove_range
  let B := A 0 - α * u 0 - D
  let R := max (u 0) ((C + D - B) / (α - 1))
  have hzero : u 0 ≤ R := le_max_left _ _
  have hbound : ∀ k y,
      V k 0 - α * u 0 ≤ V k y - α * u y → u y ≤ R := by
    intro k y hy
    have hd : δ k ≤ D := hD (mem_range_self k)
    have h1 := (abs_le.mp (hc k 0)).1
    have h2 := (abs_le.mp (hc k y)).2
    have h3 := hC y
    have hb : B ≤ V k 0 - α * u 0 := by
      dsimp [B]
      linarith
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ (by linarith : 0 < α - 1)).2
    nlinarith
  have hex : ∀ k, ∃ x, u x ≤ R ∧
      ∀ y, V k y - α * u y ≤ V k x - α * u x := by
    intro k
    obtain ⟨x, hx, hm⟩ := (hcoer R).exists_isMaxOn ⟨0, hzero⟩
      (((hV k).sub (hu.const_mul α)).continuousOn)
    refine ⟨x, hx, ?_⟩
    intro y
    by_cases hy : V k 0 - α * u 0 ≤ V k y - α * u y
    · exact hm (hbound k y hy)
    · exact (le_of_not_ge hy).trans (hm hzero)
  choose x hx hm using hex
  exact ⟨R, x, hx, hm⟩

private lemma n9_limit {E : Type} [TopologicalSpace E]
    {u : E → ℝ} {V : ℕ → E → ℝ} {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0))
    (hc : ∀ k x, |V k x - u x| ≤ δ k) (hu : Continuous u)
    {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {g : ℕ → E} {x : E} (hg : Tendsto g atTop (𝓝 x)) :
    Tendsto (fun j => V (s j) (g j)) atTop (𝓝 (u x)) := by
  have hd := hδ.comp hs
  have hv := hu.continuousAt.tendsto.comp hg
  have hlo : Tendsto (fun j => u (g j) - δ (s j)) atTop (𝓝 (u x)) := by
    simpa only [sub_zero, Function.comp_def] using hv.sub hd
  have hhi : Tendsto (fun j => u (g j) + δ (s j)) atTop (𝓝 (u x)) := by
    simpa only [add_zero, Function.comp_def] using hv.add hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun j => by
      have hh := (abs_le.mp (hc (s j) (g j))).1
      linarith)
    (fun j => by
      have hh := (abs_le.mp (hc (s j) (g j))).2
      linarith)

private lemma n9_lipschitz_translate {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hl : LipschitzWith L u) (y h : EuclideanSpace ℝ (Fin n)) :
    u (y + h) ≤ u y + (L : ℝ) * ‖h‖ := by
  have H : |u (y + h) - u y| ≤ (L : ℝ) * ‖h‖ := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_left] using
      hl.norm_sub_le (y + h) y
  linarith [(abs_le.mp H).2]

private lemma n9_touch_comparison {n : ℕ}
    {u F g B : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (Real.exp (F x)))
    (hg : ContDiff ℝ 2 g)
    (hpos : ∀ y, (hessianMatrix g y).PosDef)
    (hlog : ∀ y, B y ≤ Real.log (hessianMatrix g y).det)
    (h x : EuclideanSpace ℝ (Fin n)) {α : ℝ} (ha : 0 < α)
    (hm : ∀ y, n9_average g h y - α * u y ≤
      n9_average g h x - α * u x) :
    (B (x + h) + B (x - h)) / 2 - n * Real.log α ≤ F x := by
  let V := n9_average g h
  let M := (1 / 2 : ℝ) • (hessianMatrix g (x + h) + hessianMatrix g (x - h))
  let ψ := fun y => α⁻¹ * (V y - (V x - α * u x))
  have hV : ContDiff ℝ 2 V := n9_average_smooth hg h
  have hM : M.PosDef :=
    ((hpos (x + h)).add (hpos (x - h))).smul (by norm_num)
  have hψ : ContDiff ℝ 2 ψ := contDiff_const.mul (hV.sub contDiff_const)
  have hH : hessianMatrix ψ x = α⁻¹ • M := by
    dsimp [ψ]
    rw [n9_hessian_mul (hV.sub contDiff_const),
      n9_hessian_sub_const hV]
    exact congrArg (fun Q => α⁻¹ • Q) (n9_hessian_average hg h x)
  have hcontact : u x = ψ x := by
    dsimp [ψ]
    field_simp
    ring
  have htouch : ∀ᶠ y in 𝓝 x, ψ y ≤ u y := by
    apply Filter.Eventually.of_forall
    intro y
    apply (inv_mul_le_iff₀ ha).2
    have hy := hm y
    change V y - α * u y ≤ V x - α * u x at hy
    linarith
  have hdet : (α⁻¹ • M).det ≤ Real.exp (F x) := by
    rw [← hH]
    exact det_hessianMatrix_le_of_lower_touch hconv isOpen_univ
      (fun G hG _ => hMA G hG) (mem_univ x)
      (Real.continuous_exp.comp hF).continuousAt (Real.exp_pos _).le
      hψ.contDiffAt (hH ▸ (hM.smul (inv_pos.mpr ha)).posSemidef)
      hcontact htouch
  exact n9_scaled_det_comparison ha hM
    (n9_midpoint_det (hpos (x + h)) (hpos (x - h))
      (hlog (x + h)) (hlog (x - h))) hdet

set_option maxHeartbeats 800000 in
/-- **A penalised maximum with the log-density comparison** (weak Letwin route, N9, task T17b; KLS500
`exists_weak_moment_maximum_with_target_comparison`): let the convex, Lipschitz, coercive `u` be an Alexandrov
solution `vol ∂u(G) = ∫_G e^F` with continuous `F`, and let `uₖ` be `C²` approximations, uniformly close to `u`,
with positive definite Hessians satisfying `Fₖ ≤ log det ∇²uₖ` for `Fₖ → F` locally uniformly. Then for
every `η > 0`, `Δ²ₕu − η u` has a maximiser `x₀` with `F(x₀ + h) + F(x₀ − h) − 2 F(x₀) ≤ η n`. -/
theorem exists_penalized_maximum_with_comparison {n : ℕ} {u F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {L : NNReal} (hLip : LipschitzWith L u)
    (hcoer : ∀ R : ℝ, IsCompact {x | u x ≤ R}) (hF : Continuous F)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (Real.exp (F x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {uk Fk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} (huk : ∀ k, ContDiff ℝ 2 (uk k))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hclose : ∀ k x, |uk k x - u x| ≤ δ k)
    (hFk : TendstoLocallyUniformly Fk F atTop)
    (hpos : ∀ k x, (hessianMatrix (uk k) x).PosDef)
    (hlog : ∀ k x, Fk k x ≤ Real.log (hessianMatrix (uk k) x).det)
    (h : EuclideanSpace ℝ (Fin n)) {η : ℝ} (hη : 0 < η) :
    ∃ x₀ : EuclideanSpace ℝ (Fin n),
      (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
        u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
      F (x₀ + h) + F (x₀ - h) - 2 * F x₀ ≤ η * n := by
  classical
  let α : ℝ := 1 + η / 2
  have hα : 1 < α := by dsimp [α]; linarith
  have hα0 : 0 < α := by linarith
  let A := n9_average u h
  let V := fun k => n9_average (uk k) h
  have hu : Continuous u := hLip.continuous
  have hA : Continuous A := n9_average_continuous hu h
  have hV : ∀ k, ContDiff ℝ 2 (V k) := fun k => n9_average_smooth (huk k) h
  have hc : ∀ k y, |V k y - A y| ≤ δ k := by
    intro k y
    have hp := abs_le.mp (hclose k (y + h))
    have hm := abs_le.mp (hclose k (y - h))
    dsimp [V, A, n9_average]
    apply abs_le.mpr
    constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
  have hbound : ∀ y, A y ≤ u y + (L : ℝ) * ‖h‖ := by
    intro y
    have hp := n9_lipschitz_translate hLip y h
    have hm : u (y - h) ≤ u y + (L : ℝ) * ‖h‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using
        n9_lipschitz_translate hLip y (-h)
    dsimp [A, n9_average]
    linarith
  obtain ⟨R, x, hx, hmax⟩ :=
    n9_maximizers hu hcoer (fun k => (hV k).continuous) hδ hc hbound hα
  obtain ⟨x₀, _, s, hs, hxs⟩ := (hcoer R).tendsto_subseq hx
  have hsTop : Tendsto s atTop atTop := hs.tendsto_atTop
  have hux : Tendsto (fun j => u (x (s j))) atTop (𝓝 (u x₀)) :=
    hu.continuousAt.tendsto.comp hxs
  have hAx : Tendsto (fun j => V (s j) (x (s j))) atTop (𝓝 (A x₀)) :=
    n9_limit hδ hc hA hsTop hxs
  have hmax₀ : ∀ y, A y - α * u y ≤ A x₀ - α * u x₀ := by
    intro y
    have hAy : Tendsto (fun j => V (s j) y) atTop (𝓝 (A y)) :=
      n9_limit hδ hc hA hsTop tendsto_const_nhds
    exact le_of_tendsto_of_tendsto (hAy.sub_const (α * u y))
      (hAx.sub (hux.const_mul α))
      (Filter.Eventually.of_forall (fun j => hmax (s j) y))
  have hcomp : ∀ k,
      (Fk k (x k + h) + Fk k (x k - h)) / 2 -
        n * Real.log α ≤ F (x k) := by
    intro k
    exact n9_touch_comparison hconv hF hMA (huk k) (hpos k) (hlog k)
      h (x k) hα0 (hmax k)
  have hFks : TendstoLocallyUniformly (fun j => Fk (s j)) F atTop := by
    intro U hU z
    obtain ⟨t, ht, he⟩ := hFk U hU z
    exact ⟨t, ht, hsTop.eventually he⟩
  have hp : Tendsto (fun j => Fk (s j) (x (s j) + h))
      atTop (𝓝 (F (x₀ + h))) :=
    hFks.tendsto_comp hF.continuousAt (hxs.add_const h)
  have hm : Tendsto (fun j => Fk (s j) (x (s j) - h))
      atTop (𝓝 (F (x₀ - h))) :=
    hFks.tendsto_comp hF.continuousAt (hxs.sub_const h)
  have hFx : Tendsto (fun j => F (x (s j))) atTop (𝓝 (F x₀)) :=
    hF.continuousAt.tendsto.comp hxs
  have hlim : (F (x₀ + h) + F (x₀ - h)) / 2 -
      n * Real.log α ≤ F x₀ :=
    le_of_tendsto_of_tendsto (((hp.add hm).div_const 2).sub_const
      (n * Real.log α)) hFx
      (Filter.Eventually.of_forall (fun j => hcomp (s j)))
  refine ⟨x₀, ?_, ?_⟩
  · intro y
    have hy := hmax₀ y
    dsimp [A, n9_average, α] at hy
    linarith
  · have hlogα : Real.log α ≤ η / 2 := by
      have hh := Real.log_le_sub_one_of_pos hα0
      dsimp [α] at hh ⊢
      linarith
    have hn := mul_le_mul_of_nonneg_left hlogα (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith

end FunctionalInequalities.Analysis

end LT17BMaximumWithComparison
