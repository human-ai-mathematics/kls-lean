import FunctionalInequalities.Analysis.WaveSplitting.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # First-order consistency of the actual finite splitting composition -/
noncomputable section
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*}

private theorem diagonal_hasDerivAt {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {d₁ d₂ : ℝ} (h₁ : HasDerivAt (fun t => F (t,0)) d₁ 0)
    (h₂ : HasDerivAt (fun t => F (0,t)) d₂ 0) :
    HasDerivAt (fun t => F (t,t)) (d₁ + d₂) 0 := by
  have hf := (hF.differentiable (by simp) (0,0)).hasFDerivAt
  have hp := hf.comp_hasDerivAt (f := fun t : ℝ => (t, 0)) 0 ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))
  have hq := hf.comp_hasDerivAt (f := fun t : ℝ => (0, t)) 0 ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))
  have hd := hf.comp_hasDerivAt (f := fun t : ℝ => (t, t)) 0 ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))
  have he₁ := hp.unique h₁
  have he₂ := hq.unique h₂
  apply HasDerivAt.congr_deriv hd
  rw [← he₁, ← he₂, ← map_add]
  simp

/-- Componentwise classical temporal derivative, before identifying any Hilbert-space class. -/
def HasTimeDerivative (Y : ℝ → State E ι) (D : State E ι) (t : ℝ) : Prop :=
  (∀ x, HasDerivAt (fun s => (Y s).u x) (D.u x) t) ∧
  (∀ x, HasDerivAt (fun s => (Y s).v x) (D.v x) t) ∧
  ∀ j x, HasDerivAt (fun s => (Y s).p j x) (D.p j x) t

/-- A coordinate generator, including the inactive coordinate components. -/
def coordinateGenerator [DecidableEq ι] (a : E) (j : ι) (Y : State E ι) : State E ι :=
  ⟨0, fun x => fderiv ℝ (Y.p j) x a, fun i x => if i = j then fderiv ℝ Y.v x a else 0⟩

/-- Pointwise addition of classical states. -/
def addState (X Y : State E ι) : State E ι :=
  ⟨fun x => X.u x + Y.u x, fun x => X.v x + Y.v x, fun j x => X.p j x + Y.p j x⟩

section FiniteIndex

variable [DecidableEq ι]

private theorem transport_joint_parameters {Y : ℝ → State E ι}
    (hY : JointSmooth Y) (a : E) (j : ι) (x : E) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => (transport a j z.1 (Y z.2)).v x) ∧
    ∀ i, ContDiff ℝ ∞ (fun z : ℝ × ℝ => (transport a j z.1 (Y z.2)).p i x) := by
  have hp : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.2, x + z.1 • a)) :=
    contDiff_snd.prodMk (contDiff_const.add (contDiff_fst.smul contDiff_const))
  have hm : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.2, x - z.1 • a)) :=
    contDiff_snd.prodMk (contDiff_const.sub (contDiff_fst.smul contDiff_const))
  refine ⟨(((hY.2.1.comp hp).add ((hY.2.2 j).comp hp)).add
    ((hY.2.1.comp hm).sub ((hY.2.2 j).comp hm))).div_const 2, ?_⟩
  intro i
  by_cases hi : i = j
  · simpa only [transport, hi, ↓reduceIte, Function.comp_def] using
      (((hY.2.1.comp hp).add ((hY.2.2 j).comp hp)).sub
        ((hY.2.1.comp hm).sub ((hY.2.2 j).comp hm))).div_const 2
  · simpa only [transport, hi, ↓reduceIte, Function.comp_def] using
      (hY.2.2 i).comp (contDiff_snd.prodMk contDiff_const)

/-- Differentiate a coordinate flow whose input state itself varies with time. -/
theorem HasTimeDerivative.transport_zero {Y : ℝ → State E ι}
    {D : State E ι} (hD : HasTimeDerivative Y D 0) (hY : JointSmooth Y) (a : E) (j : ι) :
    HasTimeDerivative (fun t => transport a j t (Y t))
      (addState D (coordinateGenerator a j (Y 0))) 0 := by
  have hs : (Y 0).Smooth := ⟨hY.1.comp (contDiff_const.prodMk contDiff_id),
    hY.2.1.comp (contDiff_const.prodMk contDiff_id),
    fun i => (hY.2.2 i).comp (contDiff_const.prodMk contDiff_id)⟩
  refine ⟨fun x => by simpa [addState, coordinateGenerator, transport] using hD.1 x, ?_, ?_⟩
  · intro x
    have h := diagonal_hasDerivAt (transport_joint_parameters hY a j x).1
      (transport_hasDerivAt_v_zero a j (Y 0) x
        (hs.2.1.differentiable (by simp) x) ((hs.2.2 j).differentiable (by simp) x))
      (by simpa using hD.2.1 x)
    simpa only [addState, coordinateGenerator, add_comm] using h
  · intro i x
    by_cases hi : i = j
    · subst i
      have h := diagonal_hasDerivAt ((transport_joint_parameters hY a j x).2 j)
        (transport_hasDerivAt_p_zero a j (Y 0) x
          (hs.2.1.differentiable (by simp) x) ((hs.2.2 j).differentiable (by simp) x))
        (by simpa using hD.2.2 j x)
      simpa only [addState, coordinateGenerator, ↓reduceIte, add_comm] using h
    · simpa only [addState, coordinateGenerator, transport, hi, ↓reduceIte, add_zero] using hD.2.2 i x

end FiniteIndex

/-- The zero classical state. -/
def zeroState : State E ι := ⟨0, 0, fun _ => 0⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem addState_zero (Y : State E ι) : addState Y zeroState = Y := by
  cases Y; simp [addState, zeroState]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem zero_addState (Y : State E ι) : addState zeroState Y = Y := by
  cases Y; simp [addState, zeroState]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem addState_assoc (X Y Z : State E ι) :
    addState (addState X Y) Z = addState X (addState Y Z) := by
  simp only [addState, add_assoc]

/-- Sum of the generators in the actual sweep list, retaining repeats if present. -/
def sweepGenerator [DecidableEq ι] (a : ι → E) : List ι → State E ι → State E ι
  | [], _ => zeroState
  | j :: js, Y => addState (coordinateGenerator (a j) j Y) (sweepGenerator a js Y)

/-- Chain rule for the entire finite sweep with a time-dependent input. -/
theorem HasTimeDerivative.sweep_zero [DecidableEq ι] {Y : ℝ → State E ι}
    {D : State E ι} (hD : HasTimeDerivative Y D 0) (hY : JointSmooth Y)
    (a : ι → E) (js : List ι) :
    HasTimeDerivative (fun t => sweep a t js (Y t))
      (addState D (sweepGenerator a js (Y 0))) 0 := by
  induction js generalizing Y D with
  | nil => simpa [sweep, sweepGenerator] using hD
  | cons j js ih =>
    have h := ih (hD.transport_zero hY (a j) j) (hY.transport (a j) j)
    simpa [sweep, sweepGenerator, addState_assoc] using h

/-- The zero-order part of the wave generator, with its original coefficient pairing. -/
def reactionGenerator [Fintype ι] (b : ι → E → ℝ) (Y : State E ι) : State E ι :=
  ⟨Y.v, fun x => -Y.u x - coupling b Y x, fun _ => 0⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Chain rule for the reaction with a time-dependent input. -/
theorem HasTimeDerivative.reaction_zero [Fintype ι] {Y : ℝ → State E ι}
    {D : State E ι} (hD : HasTimeDerivative Y D 0) (b : ι → E → ℝ) :
    HasTimeDerivative (fun t => reaction b t (Y t))
      (addState D (reactionGenerator b (Y 0))) 0 := by
  have hc (x : E) : HasDerivAt (fun t => coupling b (Y t) x) (coupling b D x) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hD.2.2 j x).const_mul (b j x))
  refine ⟨?_, ?_, fun j x => by simpa [addState, reactionGenerator, reaction] using hD.2.2 j x⟩
  · intro x
    have h := (((Real.hasDerivAt_cos 0).mul (hD.1 x)).add
      ((Real.hasDerivAt_sin 0).mul (hD.2.1 x))).add
      (((Real.hasDerivAt_cos 0).sub_const 1).mul (hc x))
    apply HasDerivAt.congr_deriv h
    simp [addState, reactionGenerator]
  · intro x
    have h := (((Real.hasDerivAt_sin 0).neg.mul (hD.1 x)).add
      ((Real.hasDerivAt_cos 0).mul (hD.2.1 x))).sub ((Real.hasDerivAt_sin 0).mul (hc x))
    apply HasDerivAt.congr_deriv h
    simp [addState, reactionGenerator]
    ring

/-- Generator of the specified split list; full coordinate lists give the wave system. -/
def splitGenerator [Fintype ι] [DecidableEq ι] (a : ι → E) (b : ι → E → ℝ)
    (js : List ι) (Y : State E ι) : State E ι :=
  addState (sweepGenerator a js Y) (reactionGenerator b Y)

/-- First-order consistency of the actual full splitting formula. -/
theorem step_hasTimeDerivative_zero [Fintype ι] [DecidableEq ι]
    (a : ι → E) (b : ι → E → ℝ) (js : List ι) {Y : State E ι} (hY : Y.Smooth) :
    HasTimeDerivative (fun t => step a b js t Y) (splitGenerator a b js Y) 0 := by
  have hD : HasTimeDerivative (fun _ : ℝ => Y) zeroState 0 :=
    ⟨fun x => hasDerivAt_const 0 (Y.u x), fun x => hasDerivAt_const 0 (Y.v x),
      fun j x => hasDerivAt_const 0 (Y.p j x)⟩
  have h := ((hD.sweep_zero hY.joint_const a js).reaction_zero b)
  simpa only [sweep_zero, zero_addState, splitGenerator, step] using h

section FiniteIndex

variable [DecidableEq ι]

@[simp] theorem sweepGenerator_u (a : ι → E) (js : List ι)
    (Y : State E ι) (x : E) : (sweepGenerator a js Y).u x = 0 := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [sweepGenerator, addState, coordinateGenerator, ih]

theorem sweepGenerator_v (a : ι → E) (js : List ι)
    (Y : State E ι) (x : E) : (sweepGenerator a js Y).v x =
      (js.map (fun j => fderiv ℝ (Y.p j) x (a j))).sum := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [sweepGenerator, addState, coordinateGenerator, ih]

theorem sweepGenerator_p (a : ι → E) (js : List ι)
    (Y : State E ι) (i : ι) (x : E) : (sweepGenerator a js Y).p i x =
      (js.map (fun j => if i = j then fderiv ℝ Y.v x (a j) else 0)).sum := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [sweepGenerator, addState, coordinateGenerator, ih]

end FiniteIndex

/-- The classical scalar/vector wave generator in the specified coordinate directions. -/
def waveGenerator [Fintype ι] (a : ι → E) (b : ι → E → ℝ) (Y : State E ι) : State E ι :=
  ⟨Y.v, fun x => (∑ j, fderiv ℝ (Y.p j) x (a j)) - Y.u x - coupling b Y x,
    fun j x => fderiv ℝ Y.v x (a j)⟩

/-- A complete coordinate sweep has precisely the wave generator, with no missing components. -/
theorem splitGenerator_finRange {d : ℕ} (a : Fin d → E) (b : Fin d → E → ℝ)
    (Y : State E (Fin d)) : splitGenerator a b (List.finRange d) Y = waveGenerator a b Y := by
  apply State.ext
  · funext x
    simp [splitGenerator, addState, reactionGenerator, waveGenerator]
  · funext x
    simp [splitGenerator, addState, reactionGenerator, waveGenerator, sweepGenerator_v,
      List.finRange, List.map_ofFn, List.sum_ofFn]
    ring
  · funext i x
    simp [splitGenerator, addState, reactionGenerator, waveGenerator, sweepGenerator_p,
      List.finRange, List.map_ofFn, List.sum_ofFn]

/-- The actual temporal derivative of a classical state curve. -/
def timeDerivative (Y : ℝ → State E ι) (t : ℝ) : State E ι :=
  ⟨fun x => deriv (fun s => (Y s).u x) t, fun x => deriv (fun s => (Y s).v x) t,
    fun j x => deriv (fun s => (Y s).p j x) t⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem HasTimeDerivative.timeDerivative_eq {Y : ℝ → State E ι} {D : State E ι} {t : ℝ}
    (h : HasTimeDerivative Y D t) : timeDerivative Y t = D := by
  apply State.ext
  · funext x; exact (h.1 x).deriv
  · funext x; exact (h.2.1 x).deriv
  · funext j x; exact (h.2.2 j x).deriv

/-- The actual full-step residual against its list generator. -/
def residual [Fintype ι] [DecidableEq ι] (a : ι → E) (b : ι → E → ℝ)
    (js : List ι) (Y : State E ι) (t : ℝ) : State E ι :=
  let D := timeDerivative (fun s => step a b js s Y) t
  let G := splitGenerator a b js (step a b js t Y)
  ⟨fun x => D.u x - G.u x, fun x => D.v x - G.v x, fun j x => D.p j x - G.p j x⟩

/-- The defined residual vanishes at the start of each step; this is consistency, not yet
an estimate uniform over refined meshes. -/
theorem residual_zero [Fintype ι] [DecidableEq ι] (a : ι → E) (b : ι → E → ℝ)
    (js : List ι) {Y : State E ι} (hY : Y.Smooth) : residual a b js Y 0 = zeroState := by
  simp only [residual, step_zero, (step_hasTimeDerivative_zero a b js hY).timeDerivative_eq]
  simp only [sub_self]
  rfl

private theorem smooth_time_derivative {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : ℝ × E => deriv (fun t => F (t,z.2)) z.1) := by
  have h : ContDiff ℝ ∞ (fun p : (ℝ × E) × ℝ => F (p.2,p.1.2)) :=
    hF.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  exact (h.fderiv contDiff_fst (by simp)).clm_apply contDiff_const

private theorem smooth_space_derivative {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (a : E) :
    ContDiff ℝ ∞ (fun z : ℝ × E => fderiv ℝ (fun x => F (z.1,x)) z.2 a) := by
  have h : ContDiff ℝ ∞ (fun p : (ℝ × E) × E => F (p.1.1,p.2)) :=
    hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact (h.fderiv contDiff_snd (by simp)).clm_apply contDiff_const

/-- Classical time differentiation preserves joint smoothness. -/
theorem JointSmooth.timeDerivative {Y : ℝ → State E ι} (hY : JointSmooth Y) :
    JointSmooth (timeDerivative Y) :=
  ⟨smooth_time_derivative hY.1, smooth_time_derivative hY.2.1,
    fun j => smooth_time_derivative (hY.2.2 j)⟩

private theorem JointSmooth.addState {Y Z : ℝ → State E ι}
    (hY : JointSmooth Y) (hZ : JointSmooth Z) : JointSmooth (fun t => addState (Y t) (Z t)) :=
  ⟨hY.1.add hZ.1, hY.2.1.add hZ.2.1, fun j => (hY.2.2 j).add (hZ.2.2 j)⟩

private theorem JointSmooth.sweepGenerator [DecidableEq ι] {Y : ℝ → State E ι}
    (hY : JointSmooth Y) (a : ι → E) (js : List ι) :
    JointSmooth (fun t => sweepGenerator a js (Y t)) := by
  induction js with
  | nil => exact ⟨contDiff_const, contDiff_const, fun _ => contDiff_const⟩
  | cons j js ih =>
    have hc : JointSmooth (fun t => coordinateGenerator (a j) j (Y t)) := by
      refine ⟨contDiff_const, smooth_space_derivative (hY.2.2 j) (a j), ?_⟩
      intro i
      by_cases hi : i = j
      · simpa only [coordinateGenerator, hi, ↓reduceIte] using smooth_space_derivative hY.2.1 (a j)
      · simpa only [coordinateGenerator, hi, ↓reduceIte] using
          (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × E => (0 : ℝ)))
    exact hc.addState ih

section FiniteIndex

variable [Fintype ι] [DecidableEq ι]

private theorem JointSmooth.splitGenerator
    {Y : ℝ → State E ι} (hY : JointSmooth Y) (a : ι → E)
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) (js : List ι) :
    JointSmooth (fun t => splitGenerator a b js (Y t)) := by
  have hc : ContDiff ℝ ∞ (fun z : ℝ × E => coupling b (Y z.1) z.2) :=
    ContDiff.sum fun j _ => ((hb j).comp contDiff_snd).mul (hY.2.2 j)
  exact (hY.sweepGenerator a js).addState
    ⟨hY.2.1, hY.1.neg.sub hc, fun _ => contDiff_const⟩

/-- The defined residual of the explicit splitting formula is jointly smooth. -/
theorem jointSmooth_residual (a : ι → E)
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) (js : List ι)
    {Y : State E ι} (hY : Y.Smooth) : JointSmooth (residual a b js Y) := by
  have hs := (hY.joint_const.sweep a js).reaction hb
  have hd := hs.timeDerivative
  have hg := hs.splitGenerator a hb js
  exact ⟨hd.1.sub hg.1, hd.2.1.sub hg.2.1, fun j => (hd.2.2 j).sub (hg.2.2 j)⟩

end FiniteIndex

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem integral_derivative_of_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hz : f 0 = 0) (t : ℝ) : f t = ∫ s in (0 : ℝ)..t, deriv f s := by
  have h := intervalIntegral.integral_deriv_eq_sub
    (fun s _ => hf.differentiable (by simp) s)
    ((hf.continuous_deriv (by simp)).intervalIntegrable 0 t)
  simpa only [hz, sub_zero] using h.symm

section FiniteIndex

variable [Fintype ι] [DecidableEq ι]

/-- Exact time-integral representation of the actual residual, valid componentwise on each
smooth cell. Quantitative bounds on the differentiated residual are a separate obligation. -/
theorem residual_integral (a : ι → E)
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) (js : List ι)
    {Y : State E ι} (hY : Y.Smooth) (t : ℝ) (x : E) :
    (residual a b js Y t).u x = ∫ s in (0 : ℝ)..t, deriv (fun r => (residual a b js Y r).u x) s ∧
    (residual a b js Y t).v x = ∫ s in (0 : ℝ)..t, deriv (fun r => (residual a b js Y r).v x) s ∧
    ∀ j, (residual a b js Y t).p j x =
      ∫ s in (0 : ℝ)..t, deriv (fun r => (residual a b js Y r).p j x) s := by
  have hs := jointSmooth_residual a hb js hY
  have hz := residual_zero a b js hY
  refine ⟨integral_derivative_of_zero (hs.1.comp (contDiff_id.prodMk contDiff_const)) ?_ t,
    integral_derivative_of_zero (hs.2.1.comp (contDiff_id.prodMk contDiff_const)) ?_ t,
    fun j => integral_derivative_of_zero ((hs.2.2 j).comp (contDiff_id.prodMk contDiff_const)) ?_ t⟩
  · exact congrArg (fun Z : State E ι => Z.u x) hz
  · exact congrArg (fun Z : State E ι => Z.v x) hz
  · exact congrArg (fun Z : State E ι => Z.p j x) hz

/-- Consistency at the start of every actual mesh cell, with its computed grid state. -/
theorem cell_hasTimeDerivative_zero (a : ι → E)
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) (js : List ι)
    {Y : State E ι} (hY : Y.Smooth) (δ : ℝ) (k : ℕ) :
    HasTimeDerivative (cell a b js δ Y k)
      (splitGenerator a b js (nodes a b js δ Y k)) 0 :=
  step_hasTimeDerivative_zero a b js (hY.nodes a hb js δ k)

end FiniteIndex

end FunctionalInequalities.Analysis.WaveSplitting
