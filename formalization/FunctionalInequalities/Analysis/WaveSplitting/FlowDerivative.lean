import FunctionalInequalities.Analysis.WaveSplitting.Consistency
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Temporal derivatives of the actual splitting flows at every time

The chain rules below differentiate the explicit flows at an arbitrary time, including a
time-dependent input state. The derivative of a finite sweep keeps every flow factor between
a differentiated generator and the output; no commutation of the generators is used.
The actual residual is identified exactly with the resulting ordered expression.
-/
noncomputable section
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

/-- Pointwise difference of classical states. -/
def subState (X Y : State E ι) : State E ι :=
  ⟨fun x => X.u x - Y.u x, fun x => X.v x - Y.v x, fun j x => X.p j x - Y.p j x⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem subState_self (Y : State E ι) : subState Y Y = zeroState := by
  apply state_ext <;> funext <;> simp [subState, zeroState]

/-- The actual residual is the difference of its two defining states. -/
theorem residual_eq_subState [Fintype ι] [DecidableEq ι] (a : ι → E) (b : ι → E → ℝ)
    (js : List ι) (Y : State E ι) (t : ℝ) :
    residual a b js Y t = subState (timeDerivative (fun s => step a b js s Y) t)
      (splitGenerator a b js (step a b js t Y)) := rfl

section FiniteIndex

variable [DecidableEq ι]

/-! ## Linearity of the explicit flows -/

theorem transport_addState (a : E) (j : ι) (t : ℝ) (X Y : State E ι) :
    transport a j t (addState X Y) = addState (transport a j t X) (transport a j t Y) := by
  apply state_ext
  · rfl
  · funext x; simp only [transport, addState]; ring
  · funext i x
    by_cases hi : i = j
    · subst hi; simp only [transport, addState, ↓reduceIte]; ring
    · simp only [transport, addState, hi, ↓reduceIte]

theorem transport_zeroState (a : E) (j : ι) (t : ℝ) :
    transport a j t (zeroState : State E ι) = zeroState := by
  apply state_ext
  · rfl
  · funext x; simp [transport, zeroState]
  · funext i x
    by_cases hi : i = j <;> simp [transport, zeroState, hi]

theorem sweep_addState (a : ι → E) (t : ℝ) (js : List ι) (X Y : State E ι) :
    sweep a t js (addState X Y) = addState (sweep a t js X) (sweep a t js Y) := by
  induction js generalizing X Y with
  | nil => rfl
  | cons j js ih => simp only [sweep, transport_addState, ih]

theorem sweep_zeroState (a : ι → E) (t : ℝ) (js : List ι) :
    sweep a t js (zeroState : State E ι) = zeroState := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [sweep, transport_zeroState, ih]

end FiniteIndex

section FiniteIndex

variable [Fintype ι]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem coupling_subState (b : ι → E → ℝ) (X Y : State E ι) (x : E) :
    coupling b (subState X Y) x = coupling b X x - coupling b Y x := by
  simp only [coupling, subState, mul_sub, Finset.sum_sub_distrib]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem reaction_subState (b : ι → E → ℝ) (t : ℝ) (X Y : State E ι) :
    reaction b t (subState X Y) = subState (reaction b t X) (reaction b t Y) := by
  apply state_ext
  · funext x; simp only [reaction, coupling_subState]; simp only [subState]; ring
  · funext x; simp only [reaction, coupling_subState]; simp only [subState]; ring
  · rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem reaction_zeroState (b : ι → E → ℝ) (t : ℝ) :
    reaction b t (zeroState : State E ι) = zeroState := by
  apply state_ext <;> funext <;> simp [reaction, zeroState, coupling]

end FiniteIndex

/-! ## Group laws of the explicit flows -/

/-- Coordinate transport is a one-parameter group. -/
theorem transport_transport [DecidableEq ι] (a : E) (j : ι) (s t : ℝ) (Y : State E ι) :
    transport a j s (transport a j t Y) = transport a j (t + s) Y := by
  have e₁ (x : E) : x + s • a + t • a = x + (t + s) • a := by rw [add_smul]; abel
  have e₂ (x : E) : x - s • a - t • a = x - (t + s) • a := by rw [add_smul]; abel
  apply state_ext
  · rfl
  · funext x; simp only [transport, ↓reduceIte]; rw [e₁, e₂]; ring
  · funext i x
    by_cases hi : i = j
    · subst hi; simp only [transport, ↓reduceIte]; rw [e₁, e₂]; ring
    · simp only [transport, hi, ↓reduceIte]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The zero-order flow is a one-parameter group; its coefficient pairing is unchanged. -/
theorem reaction_reaction [Fintype ι] (b : ι → E → ℝ) (s t : ℝ) (Y : State E ι) :
    reaction b s (reaction b t Y) = reaction b (t + s) Y := by
  apply state_ext
  · funext x; simp only [reaction, coupling, Real.cos_add, Real.sin_add]; ring
  · funext x; simp only [reaction, coupling, Real.cos_add, Real.sin_add]; ring
  · rfl

/-! ## Elementary rules for componentwise temporal derivatives -/

private theorem hasDerivAt_of_shift {f : ℝ → ℝ} {d t : ℝ}
    (h : HasDerivAt (fun r => f (t + r)) d 0) : HasDerivAt f d t := by
  have h₁ : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h₂ : HasDerivAt (fun r => f (t + r)) d ((fun s : ℝ => s - t) t) := by simpa using h
  simpa [Function.comp_def] using HasDerivAt.comp (h := fun s : ℝ => s - t) t h₂ h₁

private theorem hasDerivAt_shift {f : ℝ → ℝ} {d t : ℝ}
    (h : HasDerivAt f d t) : HasDerivAt (fun r => f (t + r)) d 0 := by
  have h₁ : HasDerivAt (fun r : ℝ => t + r) 1 0 := (hasDerivAt_id 0).const_add t
  have h₂ : HasDerivAt f d ((fun r : ℝ => t + r) 0) := by simpa using h
  simpa [Function.comp_def] using HasDerivAt.comp (h := fun r : ℝ => t + r) 0 h₂ h₁

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem HasTimeDerivative.of_shift {Y : ℝ → State E ι} {D : State E ι} {t : ℝ}
    (h : HasTimeDerivative (fun r => Y (t + r)) D 0) : HasTimeDerivative Y D t :=
  ⟨fun x => hasDerivAt_of_shift (h.1 x), fun x => hasDerivAt_of_shift (h.2.1 x),
    fun j x => hasDerivAt_of_shift (h.2.2 j x)⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem HasTimeDerivative.shift {Y : ℝ → State E ι} {D : State E ι} {t : ℝ}
    (h : HasTimeDerivative Y D t) : HasTimeDerivative (fun r => Y (t + r)) D 0 :=
  ⟨fun x => hasDerivAt_shift (h.1 x), fun x => hasDerivAt_shift (h.2.1 x),
    fun j x => hasDerivAt_shift (h.2.2 j x)⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem HasTimeDerivative.addState {X Y : ℝ → State E ι} {D F : State E ι} {t : ℝ}
    (hX : HasTimeDerivative X D t) (hY : HasTimeDerivative Y F t) :
    HasTimeDerivative (fun s => WaveSplitting.addState (X s) (Y s)) (WaveSplitting.addState D F) t :=
  ⟨fun x => (hX.1 x).add (hY.1 x), fun x => (hX.2.1 x).add (hY.2.1 x),
    fun j x => (hX.2.2 j x).add (hY.2.2 j x)⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem HasTimeDerivative.subState {X Y : ℝ → State E ι} {D F : State E ι} {t : ℝ}
    (hX : HasTimeDerivative X D t) (hY : HasTimeDerivative Y F t) :
    HasTimeDerivative (fun s => WaveSplitting.subState (X s) (Y s)) (WaveSplitting.subState D F) t :=
  ⟨fun x => (hX.1 x).sub (hY.1 x), fun x => (hX.2.1 x).sub (hY.2.1 x),
    fun j x => (hX.2.2 j x).sub (hY.2.2 j x)⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem hasTimeDerivative_const (Y : State E ι) (t : ℝ) :
    HasTimeDerivative (fun _ : ℝ => Y) zeroState t :=
  ⟨fun x => hasDerivAt_const t (Y.u x), fun x => hasDerivAt_const t (Y.v x),
    fun j x => hasDerivAt_const t (Y.p j x)⟩

/-- A flow with a frozen parameter acts linearly on the temporal derivative. -/
theorem HasTimeDerivative.transport_fixed [DecidableEq ι] {Z : ℝ → State E ι}
    {D : State E ι} {t : ℝ} (h : HasTimeDerivative Z D t) (a : E) (j : ι) (τ : ℝ) :
    HasTimeDerivative (fun s => WaveSplitting.transport a j τ (Z s)) (WaveSplitting.transport a j τ D) t := by
  refine ⟨fun x => h.1 x, fun x => ?_, fun i x => ?_⟩
  · exact ((((h.2.1 (x + τ • a)).add (h.2.2 j (x + τ • a))).add
      ((h.2.1 (x - τ • a)).sub (h.2.2 j (x - τ • a)))).div_const 2)
  · by_cases hi : i = j
    · subst hi
      simp only [WaveSplitting.transport, ↓reduceIte]
      exact ((((h.2.1 (x + τ • a)).add (h.2.2 i (x + τ • a))).sub
          ((h.2.1 (x - τ • a)).sub (h.2.2 i (x - τ • a)))).div_const 2)
    · simpa only [WaveSplitting.transport, hi, ↓reduceIte] using h.2.2 i x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem HasTimeDerivative.reaction_fixed [Fintype ι] {Z : ℝ → State E ι}
    {D : State E ι} {t : ℝ} (h : HasTimeDerivative Z D t) (b : ι → E → ℝ) (τ : ℝ) :
    HasTimeDerivative (fun s => WaveSplitting.reaction b τ (Z s)) (WaveSplitting.reaction b τ D) t := by
  have hc (x : E) : HasDerivAt (fun s => coupling b (Z s) x) (coupling b D x) t :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (h.2.2 j x).const_mul (b j x))
  refine ⟨fun x => ?_, fun x => ?_, fun j x => h.2.2 j x⟩
  · exact (((h.1 x).const_mul (Real.cos τ)).add ((h.2.1 x).const_mul (Real.sin τ))).add
      ((hc x).const_mul (Real.cos τ - 1))
  · exact (((h.1 x).const_mul (-Real.sin τ)).add ((h.2.1 x).const_mul (Real.cos τ))).sub
      ((hc x).const_mul (Real.sin τ))

theorem JointSmooth.shift {Z : ℝ → State E ι} (hZ : JointSmooth Z) (t : ℝ) :
    JointSmooth (fun r => Z (t + r)) := by
  have hs : ContDiff ℝ ∞ (fun z : ℝ × E => (t + z.1, z.2)) :=
    (contDiff_const.add contDiff_fst).prodMk contDiff_snd
  exact ⟨hZ.1.comp hs, hZ.2.1.comp hs, fun j => (hZ.2.2 j).comp hs⟩

section FiniteIndex

variable [DecidableEq ι]

theorem JointSmooth.transport_fixed {Z : ℝ → State E ι}
    (hZ : JointSmooth Z) (a : E) (j : ι) (τ : ℝ) :
    JointSmooth (fun s => WaveSplitting.transport a j τ (Z s)) := by
  have hp : ContDiff ℝ ∞ (fun z : ℝ × E => (z.1, z.2 + τ • a)) :=
    contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
  have hm : ContDiff ℝ ∞ (fun z : ℝ × E => (z.1, z.2 - τ • a)) :=
    contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)
  refine ⟨hZ.1, ?_, fun i => ?_⟩
  · exact (((hZ.2.1.comp hp).add ((hZ.2.2 j).comp hp)).add
      ((hZ.2.1.comp hm).sub ((hZ.2.2 j).comp hm))).div_const 2
  · by_cases hi : i = j
    · subst hi
      simpa only [WaveSplitting.transport, ↓reduceIte, Function.comp_def] using
        (((hZ.2.1.comp hp).add ((hZ.2.2 i).comp hp)).sub
          ((hZ.2.1.comp hm).sub ((hZ.2.2 i).comp hm))).div_const 2
    · simpa only [WaveSplitting.transport, hi, ↓reduceIte] using hZ.2.2 i

/-! ## All-time chain rules -/

/-- Coordinate transport with a time-dependent input, differentiated at an arbitrary time. -/
theorem HasTimeDerivative.transport {Z : ℝ → State E ι} {D : State E ι}
    {t : ℝ} (hD : HasTimeDerivative Z D t) (hZ : JointSmooth Z) (a : E) (j : ι) :
    HasTimeDerivative (fun s => WaveSplitting.transport a j s (Z s))
      (WaveSplitting.addState (WaveSplitting.transport a j t D) (WaveSplitting.coordinateGenerator a j (WaveSplitting.transport a j t (Z t)))) t := by
  have hV := (hD.shift.transport_fixed a j t).transport_zero
    ((hZ.shift t).transport_fixed a j t) a j
  apply HasTimeDerivative.of_shift
  simpa only [transport_transport, add_zero] using hV

end FiniteIndex

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The zero-order flow with a time-dependent input, differentiated at an arbitrary time. -/
theorem HasTimeDerivative.reaction [Fintype ι] {Z : ℝ → State E ι} {D : State E ι}
    {t : ℝ} (hD : HasTimeDerivative Z D t) (b : ι → E → ℝ) :
    HasTimeDerivative (fun s => WaveSplitting.reaction b s (Z s))
      (WaveSplitting.addState (WaveSplitting.reaction b t D) (reactionGenerator b (WaveSplitting.reaction b t (Z t)))) t := by
  have hV := (hD.shift.reaction_fixed b t).reaction_zero b
  apply HasTimeDerivative.of_shift
  simpa only [reaction_reaction, add_zero] using hV

/-- Temporal derivative of a finite sweep with fixed input. Each summand differentiates one
coordinate flow and keeps all later flow factors applied after its generator. -/
def sweepDerivative [DecidableEq ι] (a : ι → E) (t : ℝ) : List ι → State E ι → State E ι
  | [], _ => zeroState
  | j :: js, Y => addState (sweep a t js (coordinateGenerator (a j) j (transport (a j) j t Y)))
      (sweepDerivative a t js (transport (a j) j t Y))

/-- Chain rule for the complete finite sweep with a time-dependent input at an arbitrary
time. The order of the flows and generators is the actual list order. -/
theorem HasTimeDerivative.sweep [DecidableEq ι] {Z : ℝ → State E ι} {D : State E ι}
    {t : ℝ} (hD : HasTimeDerivative Z D t) (hZ : JointSmooth Z) (a : ι → E) (js : List ι) :
    HasTimeDerivative (fun s => WaveSplitting.sweep a s js (Z s))
      (WaveSplitting.addState (WaveSplitting.sweep a t js D) (WaveSplitting.sweepDerivative a t js (Z t))) t := by
  induction js generalizing Z D with
  | nil => simpa [WaveSplitting.sweep, sweepDerivative] using hD
  | cons j js ih =>
    have h := ih (hD.transport hZ (a j) j) (hZ.transport (a j) j)
    simpa only [WaveSplitting.sweep, sweepDerivative, sweep_addState, addState_assoc] using h

section FiniteIndex

variable [Fintype ι] [DecidableEq ι]

/-- The actual complete split step, differentiated at an arbitrary time. -/
theorem step_hasTimeDerivative (a : ι → E) (b : ι → E → ℝ)
    (js : List ι) {Y : State E ι} (hY : Y.Smooth) (t : ℝ) :
    HasTimeDerivative (fun s => step a b js s Y)
      (addState (reaction b t (sweepDerivative a t js Y))
        (reactionGenerator b (step a b js t Y))) t := by
  have h := ((hasTimeDerivative_const Y t).sweep hY.joint_const a js).reaction b
  simpa only [sweep_zeroState, zero_addState, step] using h

/-- Exact ordered form of the actual residual: the reaction generator cancels, while every
coordinate generator remains between its true flow factors. -/
theorem residual_eq (a : ι → E) (b : ι → E → ℝ)
    (js : List ι) {Y : State E ι} (hY : Y.Smooth) (t : ℝ) :
    residual a b js Y t = subState (reaction b t (sweepDerivative a t js Y))
      (sweepGenerator a js (step a b js t Y)) := by
  rw [residual_eq_subState, (step_hasTimeDerivative a b js hY t).timeDerivative_eq]
  apply state_ext
  · funext x; simp only [subState, addState, splitGenerator]; ring
  · funext x; simp only [subState, addState, splitGenerator]; ring
  · funext j x; simp only [subState, addState, splitGenerator]; ring

end FiniteIndex

/-! ## Exchange of temporal and spatial derivatives -/

private theorem slice_fderiv {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (r : ℝ) (x v : E) :
    fderiv ℝ (fun y => F (r, y)) x v = fderiv ℝ F (r, x) (0, v) := by
  have h : HasFDerivAt (fun y => F (r, y))
      ((fderiv ℝ F (r, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x :=
    ((hF.differentiable (by simp)) (r, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right r x)
  rw [h.fderiv]
  rfl

private theorem slice_deriv {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (s : ℝ) (y : E) :
    deriv (fun r => F (r, y)) s = fderiv ℝ F (s, y) (1, 0) := by
  have h := ((hF.differentiable (by simp)) (s, y)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
  exact h.deriv

private theorem hasFDerivAt_fderiv_apply {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (w : ℝ × E) (z : ℝ × E) :
    HasFDerivAt (fun q => fderiv ℝ F q w) ((fderiv ℝ (fderiv ℝ F) z).flip w) z := by
  have hF₁ : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have h := ((hF₁.differentiable (by simp)) z).hasFDerivAt.clm_apply (hasFDerivAt_const w z)
  simpa using h

/-- The temporal derivative of a spatial directional derivative is the spatial derivative of
the temporal derivative, for jointly smooth functions. -/
theorem hasDerivAt_fderiv_slice {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (s : ℝ) (x v : E) :
    HasDerivAt (fun r => fderiv ℝ (fun y => F (r, y)) x v)
      (fderiv ℝ (fun y => deriv (fun r => F (r, y)) s) x v) s := by
  have hd := (hasFDerivAt_fderiv_apply hF (0, v) (s, x)).comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have hfun : (fun r => fderiv ℝ (fun y => F (r, y)) x v) =
      fun r => fderiv ℝ F (r, x) (0, v) := funext fun r => slice_fderiv hF r x v
  have hH : (fun y => deriv (fun r => F (r, y)) s) = fun y => fderiv ℝ F (s, y) (1, 0) :=
    funext fun y => slice_deriv hF s y
  have hK : HasFDerivAt (fun y => fderiv ℝ F (s, y) (1, 0))
      (((fderiv ℝ (fderiv ℝ F) (s, x)).flip (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x :=
    (hasFDerivAt_fderiv_apply hF (1, 0) (s, x)).comp x (hasFDerivAt_prodMk_right s x)
  have hd' : HasDerivAt (fun r => fderiv ℝ F (r, x) (0, v))
      (((fderiv ℝ (fderiv ℝ F) (s, x)).flip (0, v)) (1, 0)) s := hd
  have hsym := (hF.contDiffAt (x := (s, x))).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  rw [hfun, hH, hK.fderiv]
  convert hd' using 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.inr_apply]
  exact hsym (0, v) (1, 0)

/-- A spatial directional derivative of a jointly smooth function is jointly smooth. -/
theorem contDiff_fderiv_slice {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (a : E) :
    ContDiff ℝ ∞ (fun z : ℝ × E => fderiv ℝ (fun x => F (z.1, x)) z.2 a) := by
  have h : ContDiff ℝ ∞ (fun p : (ℝ × E) × E => F (p.1.1, p.2)) :=
    hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact (h.fderiv contDiff_snd (by simp)).clm_apply contDiff_const

/-- The temporal derivative of a jointly smooth function is jointly smooth. -/
theorem contDiff_deriv_slice {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : ℝ × E => deriv (fun t => F (t, z.2)) z.1) := by
  have h : ContDiff ℝ ∞ (fun p : (ℝ × E) × ℝ => F (p.2, p.1.2)) :=
    hF.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  exact (h.fderiv contDiff_fst (by simp)).clm_apply contDiff_const

section FiniteIndex

variable [DecidableEq ι]

/-- A coordinate generator of a jointly smooth curve is jointly smooth. -/
theorem JointSmooth.coordinateGenerator {Z : ℝ → State E ι}
    (hZ : JointSmooth Z) (v : E) (j : ι) :
    JointSmooth (fun r => WaveSplitting.coordinateGenerator v j (Z r)) := by
  refine ⟨contDiff_const, contDiff_fderiv_slice (hZ.2.2 j) v, fun i => ?_⟩
  by_cases hi : i = j
  · simpa only [WaveSplitting.coordinateGenerator, hi, ↓reduceIte] using
      contDiff_fderiv_slice hZ.2.1 v
  · simpa only [WaveSplitting.coordinateGenerator, hi, ↓reduceIte] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × E => (0 : ℝ)))

/-- The time derivative commutes with a coordinate generator on jointly smooth curves. -/
theorem JointSmooth.hasTimeDerivative_coordinateGenerator
    {Z : ℝ → State E ι} (hZ : JointSmooth Z) (v : E) (j : ι) (s : ℝ) :
    HasTimeDerivative (fun r => WaveSplitting.coordinateGenerator v j (Z r))
      (WaveSplitting.coordinateGenerator v j (WaveSplitting.timeDerivative Z s)) s := by
  refine ⟨fun x => hasDerivAt_const s 0, fun x => ?_, fun i x => ?_⟩
  · exact hasDerivAt_fderiv_slice (F := fun z : ℝ × E => (Z z.1).p j z.2) (hZ.2.2 j) s x v
  · by_cases hi : i = j
    · subst hi
      simp only [WaveSplitting.coordinateGenerator, ↓reduceIte]
      exact hasDerivAt_fderiv_slice (F := fun z : ℝ × E => (Z z.1).v z.2) hZ.2.1 s x v
    · simpa only [WaveSplitting.coordinateGenerator, hi, ↓reduceIte] using
        hasDerivAt_const s (0 : ℝ)

end FiniteIndex

theorem JointSmooth.addState {Y Z : ℝ → State E ι} (hY : JointSmooth Y) (hZ : JointSmooth Z) :
    JointSmooth (fun t => WaveSplitting.addState (Y t) (Z t)) :=
  ⟨hY.1.add hZ.1, hY.2.1.add hZ.2.1, fun j => (hY.2.2 j).add (hZ.2.2 j)⟩

theorem JointSmooth.subState {Y Z : ℝ → State E ι} (hY : JointSmooth Y) (hZ : JointSmooth Z) :
    JointSmooth (fun t => WaveSplitting.subState (Y t) (Z t)) :=
  ⟨hY.1.sub hZ.1, hY.2.1.sub hZ.2.1, fun j => (hY.2.2 j).sub (hZ.2.2 j)⟩

section FiniteIndex

variable [DecidableEq ι]

/-- The generator of a finite list, applied along a jointly smooth curve. -/
theorem JointSmooth.listGenerator {Z : ℝ → State E ι}
    (hZ : JointSmooth Z) (a : ι → E) (js : List ι) :
    JointSmooth (fun r => WaveSplitting.sweepGenerator a js (Z r)) := by
  induction js with
  | nil => exact ⟨contDiff_const, contDiff_const, fun _ => contDiff_const⟩
  | cons j js ih => exact (hZ.coordinateGenerator (a j) j).addState ih

/-- The time derivative commutes with the generator of a finite coordinate list. -/
theorem JointSmooth.hasTimeDerivative_sweepGenerator
    {Z : ℝ → State E ι} (hZ : JointSmooth Z) (a : ι → E) (js : List ι) (s : ℝ) :
    HasTimeDerivative (fun r => WaveSplitting.sweepGenerator a js (Z r))
      (WaveSplitting.sweepGenerator a js (WaveSplitting.timeDerivative Z s)) s := by
  induction js with
  | nil => exact hasTimeDerivative_const zeroState s
  | cons j js ih => exact (hZ.hasTimeDerivative_coordinateGenerator (a j) j s).addState ih

theorem JointSmooth.sweepDerivative {Z : ℝ → State E ι}
    (hZ : JointSmooth Z) (a : ι → E) (js : List ι) :
    JointSmooth (fun r => WaveSplitting.sweepDerivative a r js (Z r)) := by
  induction js generalizing Z with
  | nil => exact ⟨contDiff_const, contDiff_const, fun _ => contDiff_const⟩
  | cons j js ih =>
    exact ((hZ.transport (a j) j).coordinateGenerator (a j) j |>.sweep a js).addState
      (ih (hZ.transport (a j) j))

end FiniteIndex

theorem JointSmooth.slice {Z : ℝ → State E ι} (hZ : JointSmooth Z) (s : ℝ) : (Z s).Smooth :=
  ⟨hZ.1.comp (contDiff_const.prodMk contDiff_id),
    hZ.2.1.comp (contDiff_const.prodMk contDiff_id),
    fun j => (hZ.2.2 j).comp (contDiff_const.prodMk contDiff_id)⟩

end FunctionalInequalities.Analysis.WaveSplitting
