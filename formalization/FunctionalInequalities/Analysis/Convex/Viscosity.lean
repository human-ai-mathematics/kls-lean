import FunctionalInequalities.Probability.Stein.HessianKernel
import Mathlib.Analysis.Calculus.DerivativeTest

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
