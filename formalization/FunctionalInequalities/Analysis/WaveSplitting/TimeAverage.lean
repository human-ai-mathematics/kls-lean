import FunctionalInequalities.Analysis.WaveSplitting.Compatibility
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The finite time average of the actual splitting cells

The cellwise time average `q = Σ_k ∫_0^δ (1 - (kδ+θ)/(Nδ)) u_k(θ) dθ` of the actual cells is
smooth and compactly supported. The classical operator
`J_cl f = f - Σ_j (D_j D_j f - b_j D_j f)` applied to `q` satisfies an exact identity. Its
right side consists of the final displacement, the time integral of the residual displacement,
and the weighted divergence of the compatibility defect together with the residual velocity.
The proof uses differentiation under interval integrals, cellwise integration by parts in time
and telescoping over the actual grid nodes. No wave existence, no `p = grad u` and no residual
smallness are assumed.
-/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem state_ext {X Y : State E ι} (hu : X.u = Y.u) (hv : X.v = Y.v)
    (hp : X.p = Y.p) : X = Y := by
  cases X
  cases Y
  cases hu
  cases hv
  cases hp
  rfl

/-! ## Parametric interval integrals of jointly smooth functions -/

section Parametric
variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem continuous_time_slice {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (y : E) :
    Continuous (fun θ => F (θ, y)) := by
  have h := hF.continuous.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => y))
  exact h

omit [FiniteDimensional ℝ E] in
private theorem contDiff_space_slice {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (θ : ℝ) :
    ContDiff ℝ ∞ (fun y => F (θ, y)) := by
  have h := hF.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ fun y : E => (θ, y))
  exact h

/-- Differentiation under a finite interval integral of a jointly smooth function. -/
theorem hasFDerivAt_intervalIntegral_slice {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (a b : ℝ)
    (x : E) :
    HasFDerivAt (fun y => ∫ θ in a..b, F (θ, y))
      (∫ θ in a..b, fderiv ℝ (fun y => F (θ, y)) x) x := by
  have hF' : ContDiff ℝ ∞ (fun z : ℝ × E => fderiv ℝ (fun y => F (z.1, y)) z.2) := by
    have h : ContDiff ℝ ∞ (fun p : (ℝ × E) × E => F (p.1.1, p.2)) :=
      hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    exact h.fderiv contDiff_snd (by simp)
  obtain ⟨C, hC⟩ := (isCompact_uIcc.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn
    hF'.continuous.continuousOn
  have hcont' : Continuous (fun θ => fderiv ℝ (fun z => F (θ, z)) x) := by
    have h := hF'.continuous.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x))
    exact h
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y θ => F (θ, y)) (F' := fun y θ => fderiv ℝ (fun z => F (θ, z)) y)
    (bound := fun _ => C) (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun y => (continuous_time_slice hF y).aestronglyMeasurable)
    ((continuous_time_slice hF x).intervalIntegrable _ _) hcont'.aestronglyMeasurable ?_
    intervalIntegrable_const ?_
  · refine Filter.Eventually.of_forall fun θ hθ y hy => ?_
    exact hC (θ, y) ⟨uIoc_subset_uIcc hθ, Metric.ball_subset_closedBall hy⟩
  · refine Filter.Eventually.of_forall fun θ _ y _ => ?_
    exact (((contDiff_space_slice hF θ).differentiable (by simp)) y).hasFDerivAt

/-- A directional derivative of a parametric interval integral is the integral of the
directional derivatives of the time slices. -/
theorem fderiv_intervalIntegral_slice {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (a b : ℝ)
    (x v : E) :
    fderiv ℝ (fun y => ∫ θ in a..b, F (θ, y)) x v =
      ∫ θ in a..b, fderiv ℝ (fun y => F (θ, y)) x v := by
  have hF' : ContDiff ℝ ∞ (fun z : ℝ × E => fderiv ℝ (fun y => F (z.1, y)) z.2) := by
    have h : ContDiff ℝ ∞ (fun p : (ℝ × E) × E => F (p.1.1, p.2)) :=
      hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    exact h.fderiv contDiff_snd (by simp)
  have hcont' : Continuous (fun θ => fderiv ℝ (fun z => F (θ, z)) x) := by
    have h := hF'.continuous.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x))
    exact h
  rw [(hasFDerivAt_intervalIntegral_slice hF a b x).fderiv,
    ContinuousLinearMap.intervalIntegral_apply (hcont'.intervalIntegrable a b)]

/-- A parametric interval integral of a jointly smooth function is smooth. -/
theorem contDiff_intervalIntegral_slice {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun y => ∫ θ in a..b, F (θ, y)) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing F with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x =>
      (hasFDerivAt_intervalIntegral_slice hF a b x).continuousAt)
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hasFDerivAt_intervalIntegral_slice hF a b x).differentiableAt,
      fun h => absurd h (by simp), fun v => ?_⟩
    have e : (fun x => fderiv ℝ (fun y => ∫ θ in a..b, F (θ, y)) x v) =
        fun x => ∫ θ in a..b, (fun z : ℝ × E => fderiv ℝ (fun y => F (z.1, y)) z.2 v) (θ, x) :=
      funext fun x => fderiv_intervalIntegral_slice hF a b x v
    rw [e]
    exact ih (contDiff_fderiv_slice hF v)

end Parametric

/-! ## The classical operator and the weighted divergence -/

/-- The classical operator `J_cl f = f - Σ_j (D_(a_j) D_(a_j) f - b_j D_(a_j) f)`. For
orthonormal directions and `b = grad U` this is `f - Δf + ⟨grad U, grad f⟩`; that
identification is not used here. -/
def formOperator [Fintype ι] (a : ι → E) (b : ι → E → ℝ) (f : E → ℝ) (x : E) : ℝ :=
  f x - ∑ j, (fderiv ℝ (fun y => fderiv ℝ f y (a j)) x (a j) - b j x * fderiv ℝ f x (a j))

/-- The weighted divergence `Σ_j (D_(a_j) P_j - b_j P_j)` of a coordinate field. -/
def weightedDivergence [Fintype ι] (a : ι → E) (b : ι → E → ℝ) (P : ι → E → ℝ) (x : E) : ℝ :=
  ∑ j, (fderiv ℝ (P j) x (a j) - b j x * P j x)

private theorem contDiff_directional {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- The velocity component of the wave generator splits into `-J_cl u` and the weighted
divergence of the compatibility defect. This is exact; no `p = grad u` is imposed. -/
theorem waveGenerator_v_eq [Fintype ι] (a : ι → E) (b : ι → E → ℝ) {Y : State E ι}
    (hY : Y.Smooth) (x : E) :
    (waveGenerator a b Y).v x = -formOperator a b Y.u x +
      weightedDivergence a b (compatibilityDefect a Y).p x := by
  have hd (j : ι) : fderiv ℝ (fun y => Y.p j y - fderiv ℝ Y.u y (a j)) x (a j) =
      fderiv ℝ (Y.p j) x (a j) - fderiv ℝ (fun y => fderiv ℝ Y.u y (a j)) x (a j) := by
    rw [fderiv_fun_sub (((hY.2.2 j).differentiable (by simp)) x)
      (((contDiff_directional hY.1 (a j)).differentiable (by simp)) x)]
    rfl
  simp only [waveGenerator, formOperator, weightedDivergence, compatibilityDefect, coupling, hd]
  have key : ∑ j, (fderiv ℝ (fun y => fderiv ℝ Y.u y (a j)) x (a j) - b j x * fderiv ℝ Y.u x (a j)) +
      ∑ j, (fderiv ℝ (Y.p j) x (a j) - fderiv ℝ (fun y => fderiv ℝ Y.u y (a j)) x (a j) -
        b j x * (Y.p j x - fderiv ℝ Y.u x (a j))) =
      ∑ j, fderiv ℝ (Y.p j) x (a j) - ∑ j, b j x * Y.p j x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  linarith

omit [NormedSpace ℝ E] in
private theorem fderiv_sum_apply {α : Type*} (s : Finset α) {f : α → E → ℝ}
    [NormedSpace ℝ E] (hf : ∀ k ∈ s, Differentiable ℝ (f k)) (y v : E) :
    fderiv ℝ (fun z => ∑ k ∈ s, f k z) y v = ∑ k ∈ s, fderiv ℝ (f k) y v := by
  rw [fderiv_fun_sum fun k hk => hf k hk y]
  simp

/-- The classical operator is additive over finite sums of smooth functions. -/
theorem formOperator_sum [Fintype ι] (a : ι → E) (b : ι → E → ℝ) {α : Type*} (s : Finset α)
    {f : α → E → ℝ} (hf : ∀ k ∈ s, ContDiff ℝ ∞ (f k)) (x : E) :
    formOperator a b (fun y => ∑ k ∈ s, f k y) x = ∑ k ∈ s, formOperator a b (f k) x := by
  have h₁ (j : ι) : (fun y => fderiv ℝ (fun z => ∑ k ∈ s, f k z) y (a j)) =
      fun y => ∑ k ∈ s, fderiv ℝ (f k) y (a j) := funext fun y =>
    fderiv_sum_apply s (fun k hk => (hf k hk).differentiable (by simp)) y (a j)
  have h₂ (j : ι) : fderiv ℝ (fun y => ∑ k ∈ s, fderiv ℝ (f k) y (a j)) x (a j) =
      ∑ k ∈ s, fderiv ℝ (fun y => fderiv ℝ (f k) y (a j)) x (a j) :=
    fderiv_sum_apply s (fun k hk => (contDiff_directional (hf k hk) (a j)).differentiable
      (by simp)) x (a j)
  unfold formOperator
  simp only [h₁, h₂, fderiv_sum_apply s (fun k hk => (hf k hk).differentiable (by simp)) x]
  have key : ∑ j, (∑ k ∈ s, fderiv ℝ (fun y => fderiv ℝ (f k) y (a j)) x (a j) -
      b j x * ∑ k ∈ s, fderiv ℝ (f k) x (a j)) =
      ∑ k ∈ s, ∑ j, (fderiv ℝ (fun y => fderiv ℝ (f k) y (a j)) x (a j) -
        b j x * fderiv ℝ (f k) x (a j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_comm
  rw [key, Finset.sum_sub_distrib]

section Parametric
variable [FiniteDimensional ℝ E]

/-- The classical operator commutes with a finite time integral of a jointly smooth function. -/
theorem formOperator_intervalIntegral [Fintype ι] (a : ι → E) (b : ι → E → ℝ)
    {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (c₀ c₁ : ℝ) (x : E) :
    formOperator a b (fun y => ∫ θ in c₀..c₁, F (θ, y)) x =
      ∫ θ in c₀..c₁, formOperator a b (fun y => F (θ, y)) x := by
  have hFj (j : ι) := contDiff_fderiv_slice hF (a j)
  have h₁ (j : ι) : (fun y => fderiv ℝ (fun z => ∫ θ in c₀..c₁, F (θ, z)) y (a j)) =
      fun y => ∫ θ in c₀..c₁,
        (fun z : ℝ × E => fderiv ℝ (fun y => F (z.1, y)) z.2 (a j)) (θ, y) :=
    funext fun y => fderiv_intervalIntegral_slice hF c₀ c₁ y (a j)
  have hc {G : ℝ × E → ℝ} (hG : ContDiff ℝ ∞ G) :
      IntervalIntegrable (fun θ => G (θ, x)) volume c₀ c₁ :=
    (continuous_time_slice hG x).intervalIntegrable _ _
  have hA (j : ι) := contDiff_fderiv_slice (hFj j) (a j)
  have e₁ (j : ι) : fderiv ℝ (fun z => ∫ θ in c₀..c₁, F (θ, z)) x (a j) =
      ∫ θ in c₀..c₁, fderiv ℝ (fun y => F (θ, y)) x (a j) :=
    fderiv_intervalIntegral_slice hF c₀ c₁ x (a j)
  have e₂ (j : ι) : fderiv ℝ (fun y => fderiv ℝ (fun z => ∫ θ in c₀..c₁, F (θ, z)) y (a j)) x
      (a j) = ∫ θ in c₀..c₁, fderiv ℝ (fun y => fderiv ℝ (fun z => F (θ, z)) y (a j)) x (a j) := by
    rw [h₁ j]
    exact fderiv_intervalIntegral_slice (hFj j) c₀ c₁ x (a j)
  have hAc (j : ι) : Continuous (fun θ =>
      fderiv ℝ (fun y => fderiv ℝ (fun z => F (θ, z)) y (a j)) x (a j)) := by
    have h := continuous_time_slice (hA j) x
    exact h
  have hBc (j : ι) : Continuous (fun θ => fderiv ℝ (fun y => F (θ, y)) x (a j)) := by
    have h := continuous_time_slice (hFj j) x
    exact h
  have hsum : Continuous (fun θ => ∑ j, (fderiv ℝ (fun y => fderiv ℝ (fun z => F (θ, z)) y (a j))
      x (a j) - b j x * fderiv ℝ (fun y => F (θ, y)) x (a j))) :=
    continuous_finsetSum _ fun j _ => (hAc j).sub (continuous_const.mul (hBc j))
  unfold formOperator
  simp only [e₁, e₂]
  rw [intervalIntegral.integral_sub (hc hF) (hsum.intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (f := fun j θ =>
      fderiv ℝ (fun y => fderiv ℝ (fun z => F (θ, z)) y (a j)) x (a j) -
        b j x * fderiv ℝ (fun y => F (θ, y)) x (a j)) fun j _ =>
      ((hAc j).sub (continuous_const.mul (hBc j))).intervalIntegrable _ _]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_sub
      (f := fun θ => fderiv ℝ (fun y => fderiv ℝ (fun z => F (θ, z)) y (a j)) x (a j))
      (g := fun θ => b j x * fderiv ℝ (fun y => F (θ, y)) x (a j))
      ((hAc j).intervalIntegrable _ _) ((continuous_const.mul (hBc j)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

end Parametric

/-! ## The finite time average -/

/-- The cellwise finite time average of the displacement over the horizon `N δ`. -/
def timeAverage [Fintype ι] [DecidableEq ι] (a : ι → E) (b : ι → E → ℝ) (js : List ι)
    (δ : ℝ) (Y : State E ι) (N : ℕ) (x : E) : ℝ :=
  ∑ k ∈ Finset.range N,
    ∫ θ in (0 : ℝ)..δ, (1 - (k * δ + θ) / (N * δ)) * (cell a b js δ Y k θ).u x

private theorem timeDerivative_step_eq [Fintype ι] [DecidableEq ι] (a : ι → E)
    (b : ι → E → ℝ) (js : List ι) (Y : State E ι) (θ : ℝ) :
    timeDerivative (fun s => step a b js s Y) θ =
      addState (splitGenerator a b js (step a b js θ Y)) (residual a b js Y θ) := by
  rw [residual_eq_subState]
  apply state_ext
  · funext x; simp only [addState, subState]; ring
  · funext x; simp only [addState, subState]; ring
  · funext j x; simp only [addState, subState]; ring

section Parametric
variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem contDiff_cell_integrand [Fintype ι] [DecidableEq ι] (a : ι → E)
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) (js : List ι) {Y : State E ι}
    (hY : Y.Smooth) (δ : ℝ) (N k : ℕ) :
    ContDiff ℝ ∞ (fun z : ℝ × E =>
      (1 - (k * δ + z.1) / (N * δ)) * (cell a b js δ Y k z.1).u z.2) :=
  ((contDiff_const.sub ((contDiff_const.add contDiff_fst).div_const _)).mul
    (hY.joint_cell a hb js δ k).1)

/-- The finite time average of smooth data is smooth. -/
theorem contDiff_timeAverage [Fintype ι] [DecidableEq ι] (a : ι → E) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (js : List ι) {Y : State E ι} (hY : Y.Smooth) (δ : ℝ)
    (N : ℕ) : ContDiff ℝ ∞ (timeAverage a b js δ Y N) := by
  unfold timeAverage
  exact ContDiff.sum fun k _ =>
    contDiff_intervalIntegral_slice (contDiff_cell_integrand a hb js hY δ N k) 0 δ

omit [FiniteDimensional ℝ E] in
/-- The finite time average is supported in the common support ball of all cells. -/
theorem timeAverage_eq_zero_of_supported [Fintype ι] [DecidableEq ι] (a : ι → E)
    (b : ι → E → ℝ) (js : List ι) {Y : State E ι} {R : ℝ} (hR : Y.Supported R) {δ : ℝ}
    (hδ : 0 ≤ δ) (N : ℕ) {x : E} (hx : R + N * (δ * travel a js) < ‖x‖) :
    timeAverage a b js δ Y N x = 0 := by
  unfold timeAverage
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkN : k < N := Finset.mem_range.mp hk
  rw [intervalIntegral.integral_of_le hδ]
  refine (setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_).trans (integral_zero _ _)
  rw [(hR.cell a b js hδ hθ.1.le hθ.2 hkN x hx).1, mul_zero]

/-- The finite time average of compactly supported smooth data is compactly supported. -/
theorem hasCompactSupport_timeAverage [Fintype ι] [DecidableEq ι] (a : ι → E)
    (b : ι → E → ℝ) (js : List ι) {Y : State E ι} {R : ℝ} (hR : Y.Supported R) {δ : ℝ}
    (hδ : 0 ≤ δ) (N : ℕ) : HasCompactSupport (timeAverage a b js δ Y N) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (R + N * (δ * travel a js))) fun x hx =>
    timeAverage_eq_zero_of_supported a b js hR hδ N
      (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

/-! ## Cellwise integration by parts and the exact identity -/

omit [FiniteDimensional ℝ E] in
private theorem hasDerivAt_time_component {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (θ : ℝ)
    (x : E) : HasDerivAt (fun r => F (r, x)) (deriv (fun r => F (r, x)) θ) θ :=
  (((hF.differentiable (by simp)).comp
    (differentiable_id.prodMk (differentiable_const x))) θ).hasDerivAt

omit [FiniteDimensional ℝ E] in
/-- The exact identity on one actual step: `J_cl` of the weighted time integral of the
displacement is expressed through the endpoint values, the residual displacement and the
weighted divergence of the defect together with the residual velocity. -/
theorem integral_formOperator_step {d : ℕ} (a : Fin d → E) {b : Fin d → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Z : State E (Fin d)} (hZ : Z.Smooth) (δ c L : ℝ)
    (hL : L ≠ 0) (x : E) :
    ∫ θ in (0 : ℝ)..δ, (c - θ / L) *
        formOperator a b (step a b (List.finRange d) θ Z).u x =
      -((c - δ / L) * (step a b (List.finRange d) δ Z).v x - c * Z.v x) -
        ((step a b (List.finRange d) δ Z).u x - Z.u x -
          ∫ θ in (0 : ℝ)..δ, (residual a b (List.finRange d) Z θ).u x) / L +
        ∫ θ in (0 : ℝ)..δ, (c - θ / L) *
          (weightedDivergence a b
              (compatibilityDefect a (step a b (List.finRange d) θ Z)).p x +
            (residual a b (List.finRange d) Z θ).v x) := by
  set js := List.finRange d
  have hS : JointSmooth (fun s => step a b js s Z) := (hZ.joint_const.sweep a js).reaction hb
  have hD := hS.timeDerivative
  have hE := jointSmooth_residual a hb js hZ
  have hdef := hS.compatibilityDefect a
  have hcont {G : ℝ × E → ℝ} (hG : ContDiff ℝ ∞ G) :
      Continuous (fun θ => G (θ, x)) := continuous_time_slice hG x
  have hdiv : Continuous (fun θ => weightedDivergence a b
      (compatibilityDefect a (step a b js θ Z)).p x) := by
    unfold weightedDivergence
    exact continuous_finsetSum _ fun j _ =>
      (hcont (contDiff_fderiv_slice (hdef.2.2 j) (a j))).sub
        (continuous_const.mul (hcont (hdef.2.2 j)))
  have hφ : Continuous (fun θ : ℝ => c - θ / L) := continuous_const.sub (continuous_id.div_const L)
  -- the velocity derivative and the displacement derivative along the step
  have hDv (θ : ℝ) : (timeDerivative (fun s => step a b js s Z) θ).v x =
      -formOperator a b (step a b js θ Z).u x +
        weightedDivergence a b (compatibilityDefect a (step a b js θ Z)).p x +
          (residual a b js Z θ).v x := by
    rw [timeDerivative_step_eq, show splitGenerator a b js (step a b js θ Z) =
      waveGenerator a b (step a b js θ Z) from splitGenerator_finRange a b _]
    simp only [addState]
    rw [waveGenerator_v_eq a b (Y := step a b js θ Z) ((hZ.sweep a θ js).reaction hb θ)]
  have hDu (θ : ℝ) : (timeDerivative (fun s => step a b js s Z) θ).u x =
      (step a b js θ Z).v x + (residual a b js Z θ).u x := by
    rw [timeDerivative_step_eq]
    simp [addState, splitGenerator, reactionGenerator]
  -- rewrite the integrand
  have hint : (fun θ => (c - θ / L) * formOperator a b (step a b js θ Z).u x) = fun θ =>
      -((c - θ / L) * (timeDerivative (fun s => step a b js s Z) θ).v x) +
        (c - θ / L) * (weightedDivergence a b
          (compatibilityDefect a (step a b js θ Z)).p x + (residual a b js Z θ).v x) := by
    funext θ
    rw [hDv θ]
    ring
  have iDv : IntervalIntegrable (fun θ => (c - θ / L) *
      (timeDerivative (fun s => step a b js s Z) θ).v x) volume 0 δ :=
    (hφ.mul (hcont hD.2.1)).intervalIntegrable _ _
  have iW : IntervalIntegrable (fun θ => (c - θ / L) * (weightedDivergence a b
      (compatibilityDefect a (step a b js θ Z)).p x + (residual a b js Z θ).v x)) volume 0 δ :=
    (hφ.mul (hdiv.add (hcont hE.2.1))).intervalIntegrable _ _
  rw [hint, intervalIntegral.integral_add
    (f := fun θ => -((c - θ / L) * (timeDerivative (fun s => step a b js s Z) θ).v x))
    (g := fun θ => (c - θ / L) * (weightedDivergence a b
      (compatibilityDefect a (step a b js θ Z)).p x + (residual a b js Z θ).v x)) iDv.neg iW,
    intervalIntegral.integral_neg]
  -- integration by parts in time for the velocity
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := δ)
    (u := fun θ : ℝ => c - θ / L) (u' := fun _ => -(1 / L))
    (v := fun θ => (step a b js θ Z).v x)
    (v' := fun θ => (timeDerivative (fun s => step a b js s Z) θ).v x)
    (fun θ _ => by
      simpa using ((hasDerivAt_id θ).div_const L).const_sub c)
    (fun θ _ => hasDerivAt_time_component (F := fun z : ℝ × E => (step a b js z.1 Z).v z.2)
      hS.2.1 θ x)
    intervalIntegrable_const ((hcont hD.2.1).intervalIntegrable _ _)
  -- the displacement: ∫ v = [u] - ∫ e_u
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := δ)
    (f := fun θ => (step a b js θ Z).u x)
    (f' := fun θ => (timeDerivative (fun s => step a b js s Z) θ).u x)
    (fun θ _ => hasDerivAt_time_component (F := fun z : ℝ × E => (step a b js z.1 Z).u z.2)
      hS.1 θ x) ((hcont hD.1).intervalIntegrable _ _)
  have hsplit : ∫ θ in (0 : ℝ)..δ, (timeDerivative (fun s => step a b js s Z) θ).u x =
      (∫ θ in (0 : ℝ)..δ, (step a b js θ Z).v x) +
        ∫ θ in (0 : ℝ)..δ, (residual a b js Z θ).u x := by
    simp only [hDu]
    exact intervalIntegral.integral_add ((hcont hS.2.1).intervalIntegrable _ _)
      ((hcont hE.1).intervalIntegrable _ _)
  have hconst : ∫ θ in (0 : ℝ)..δ, -(1 / L) * (step a b js θ Z).v x =
      -(1 / L) * ∫ θ in (0 : ℝ)..δ, (step a b js θ Z).v x :=
    intervalIntegral.integral_const_mul _ _
  simp only [step_zero, sub_zero, zero_div] at hibp hftc
  rw [hibp, hconst]
  have hv : ∫ θ in (0 : ℝ)..δ, (step a b js θ Z).v x =
      (step a b js δ Z).u x - Z.u x - ∫ θ in (0 : ℝ)..δ, (residual a b js Z θ).u x := by
    linarith
  rw [hv]
  field_simp
  ring

private theorem sum_range_telescope (N : ℕ) (A B I W : ℕ → ℝ) (L : ℝ) :
    ∑ k ∈ Finset.range N, (-(A (k + 1) - A k) - (B (k + 1) - B k - I k) / L + W k) =
      -(A N - A 0) - (B N - B 0 - ∑ k ∈ Finset.range N, I k) / L +
        ∑ k ∈ Finset.range N, W k := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- **Exact identity for the finite time average.** For the actual cells of the complete
splitting on the horizon `L = N δ ≠ 0`, the classical operator applied to the cellwise time
average satisfies
`J_cl q - v(0) = (u(0) - u(L))/L + (1/L) Σ_k ∫ e_u + Σ_k ∫ (1 - t/L) (div_b d + e_v)`,
where `e` is the actual residual on each cell, started at the computed node, and
`d = p - D u` is the compatibility defect. The endpoint velocity terms telescope over the
nodes and the last one carries the factor `1 - L/L = 0`. -/
theorem formOperator_timeAverage {d : ℕ} (a : Fin d → E) {b : Fin d → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E (Fin d)} (hY : Y.Smooth) {δ : ℝ} {N : ℕ}
    (hL : (N : ℝ) * δ ≠ 0) (x : E) :
    formOperator a b (timeAverage a b (List.finRange d) δ Y N) x - Y.v x =
      (Y.u x - (nodes a b (List.finRange d) δ Y N).u x) / (N * δ) +
      (∑ k ∈ Finset.range N, ∫ θ in (0 : ℝ)..δ,
        (residual a b (List.finRange d) (nodes a b (List.finRange d) δ Y k) θ).u x) /
          (N * δ) +
      ∑ k ∈ Finset.range N, ∫ θ in (0 : ℝ)..δ, (1 - (k * δ + θ) / (N * δ)) *
        (weightedDivergence a b
            (compatibilityDefect a (cell a b (List.finRange d) δ Y k θ)).p x +
          (residual a b (List.finRange d) (nodes a b (List.finRange d) δ Y k) θ).v x) := by
  set js := List.finRange d
  have hk (k : ℕ) := contDiff_cell_integrand a hb js hY δ N k
  unfold timeAverage
  rw [formOperator_sum a b _ fun k _ => contDiff_intervalIntegral_slice (hk k) 0 δ]
  have hcell (k : ℕ) : formOperator a b (fun y => ∫ θ in (0 : ℝ)..δ,
      (1 - (k * δ + θ) / (N * δ)) * (cell a b js δ Y k θ).u y) x =
      -((1 - ((k + 1 : ℕ) : ℝ) * δ / (N * δ)) * (nodes a b js δ Y (k + 1)).v x -
          (1 - (k : ℝ) * δ / (N * δ)) * (nodes a b js δ Y k).v x) -
        ((nodes a b js δ Y (k + 1)).u x - (nodes a b js δ Y k).u x -
          ∫ θ in (0 : ℝ)..δ, (residual a b js (nodes a b js δ Y k) θ).u x) / (N * δ) +
        ∫ θ in (0 : ℝ)..δ, (1 - (k * δ + θ) / (N * δ)) *
          (weightedDivergence a b (compatibilityDefect a (cell a b js δ Y k θ)).p x +
            (residual a b js (nodes a b js δ Y k) θ).v x) := by
    have hslice (θ : ℝ) : formOperator a b (fun y =>
        (1 - (k * δ + θ) / (N * δ)) * (cell a b js δ Y k θ).u y) x =
        (1 - k * δ / (N * δ) - θ / (N * δ)) * formOperator a b (cell a b js δ Y k θ).u x := by
      have hu : ContDiff ℝ ∞ (cell a b js δ Y k θ).u := (hY.cell a hb js δ k θ).1
      unfold formOperator
      have h₁ (y : E) (j : Fin d) : fderiv ℝ (fun z => (1 - (k * δ + θ) / (N * δ)) *
          (cell a b js δ Y k θ).u z) y (a j) =
          (1 - (k * δ + θ) / (N * δ)) * fderiv ℝ (cell a b js δ Y k θ).u y (a j) := by
        rw [fderiv_const_mul ((hu.differentiable (by simp)) y)]
        rfl
      simp only [h₁]
      have h₂ (j : Fin d) : fderiv ℝ (fun y => (1 - (k * δ + θ) / (N * δ)) *
          fderiv ℝ (cell a b js δ Y k θ).u y (a j)) x (a j) =
          (1 - (k * δ + θ) / (N * δ)) *
            fderiv ℝ (fun y => fderiv ℝ (cell a b js δ Y k θ).u y (a j)) x (a j) := by
        rw [fderiv_const_mul (((contDiff_directional hu (a j)).differentiable (by simp)) x)]
        rfl
      simp only [h₂]
      rw [show (1 - k * δ / (N * δ) - θ / (N * δ)) = (1 - (k * δ + θ) / (N * δ)) by ring,
        mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [formOperator_intervalIntegral a b (hk k) 0 δ x]
    have hcongr : ∫ θ in (0 : ℝ)..δ, formOperator a b (fun y =>
        (1 - (k * δ + θ) / (N * δ)) * (cell a b js δ Y k θ).u y) x =
        ∫ θ in (0 : ℝ)..δ, (1 - k * δ / (N * δ) - θ / (N * δ)) *
          formOperator a b (step a b js θ (nodes a b js δ Y k)).u x :=
      intervalIntegral.integral_congr fun θ _ => hslice θ
    rw [hcongr, integral_formOperator_step a hb (hY.nodes a hb js δ k) δ
      (1 - k * δ / (N * δ)) (N * δ) hL x]
    have e₁ : 1 - (k : ℝ) * δ / (N * δ) - δ / (N * δ) = 1 - ((k + 1 : ℕ) : ℝ) * δ / (N * δ) := by
      push_cast; ring
    have e₂ : ∀ θ : ℝ, 1 - (k : ℝ) * δ / (N * δ) - θ / (N * δ) = 1 - (k * δ + θ) / (N * δ) :=
      fun θ => by ring
    rw [e₁]
    simp only [e₂]
    rfl
  rw [Finset.sum_congr rfl fun k _ => hcell k, sum_range_telescope N
    (fun k => (1 - (k : ℝ) * δ / (N * δ)) * (nodes a b js δ Y k).v x)
    (fun k => (nodes a b js δ Y k).u x)
    (fun k => ∫ θ in (0 : ℝ)..δ, (residual a b js (nodes a b js δ Y k) θ).u x)
    (fun k => ∫ θ in (0 : ℝ)..δ, (1 - (k * δ + θ) / (N * δ)) *
      (weightedDivergence a b (compatibilityDefect a (cell a b js δ Y k θ)).p x +
        (residual a b js (nodes a b js δ Y k) θ).v x)) (N * δ)]
  have hN : (1 - ((N : ℕ) : ℝ) * δ / (N * δ)) = 0 := by
    rw [div_self hL, sub_self]
  rw [hN]
  simp only [nodes, CharP.cast_eq_zero, zero_mul, zero_div, sub_zero, one_mul]
  field_simp
  ring

end Parametric
end FunctionalInequalities.Analysis.WaveSplitting
