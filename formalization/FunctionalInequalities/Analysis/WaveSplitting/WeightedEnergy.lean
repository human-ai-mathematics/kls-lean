import FunctionalInequalities.Analysis.WaveSplitting.Residual
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Weighted forced energy of the actual splitting cells

For a weight `w` with `D_(a_j) w = -b_j w`, the actual wave generator is skew in the weighted
pairing. Along an actual step the weighted energy therefore changes only through the
actual residual. This gives a growth law whose leading term is the initial weighted norm,
with no exponential factor. Square energies are also shown to be Hilbert seminorms
(Cauchy--Schwarz and Minkowski), including the ordered-coordinate derivative energies.
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

/-! ## Elementary square-root inequalities -/

private theorem sq_sqrt_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (√x + √y) ^ 2 = x + y + 2 * (√x * √y) := by
  rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
  ring

/-- Cauchy--Schwarz from a nonnegative quadratic polynomial. -/
theorem abs_le_sqrt_mul_of_quadratic {A B C : ℝ} (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C) : |B| ≤ √A * √C := by
  have hd := discrim_le_zero (a := C) (b := 2 * B) (c := A) (fun t => by nlinarith [h t])
  rw [discrim] at hd
  rw [← Real.sqrt_mul hA]
  exact Real.abs_le_sqrt (by nlinarith)

/-- Minkowski's inequality for finite sums of square quantities. -/
theorem sum_le_sq_sqrt_add {α : Type*} (s : Finset α) {c a b : α → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (h : ∀ i ∈ s, c i ≤ (√(a i) + √(b i)) ^ 2) :
    ∑ i ∈ s, c i ≤ (√(∑ i ∈ s, a i) + √(∑ i ∈ s, b i)) ^ 2 := by
  have hA : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  have hB : 0 ≤ ∑ i ∈ s, b i := Finset.sum_nonneg hb
  have hcs : ∑ i ∈ s, √(a i) * √(b i) ≤ √(∑ i ∈ s, a i) * √(∑ i ∈ s, b i) := by
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => √(a i)) (fun i => √(b i))
    have ea : ∑ i ∈ s, √(a i) ^ 2 = ∑ i ∈ s, a i :=
      Finset.sum_congr rfl fun i hi => Real.sq_sqrt (ha i hi)
    have eb : ∑ i ∈ s, √(b i) ^ 2 = ∑ i ∈ s, b i :=
      Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hb i hi)
    rw [ea, eb] at h2
    rw [← Real.sqrt_mul hA]
    exact (le_abs_self _).trans (Real.abs_le_sqrt h2)
  calc ∑ i ∈ s, c i ≤ ∑ i ∈ s, (a i + b i + 2 * (√(a i) * √(b i))) :=
        Finset.sum_le_sum fun i hi => (h i hi).trans_eq (sq_sqrt_add (ha i hi) (hb i hi))
    _ = ∑ i ∈ s, a i + ∑ i ∈ s, b i + 2 * ∑ i ∈ s, √(a i) * √(b i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ i ∈ s, a i + ∑ i ∈ s, b i + 2 * (√(∑ i ∈ s, a i) * √(∑ i ∈ s, b i)) := by
        linarith
    _ = _ := (sq_sqrt_add hA hB).symm

private theorem add_le_sq_sqrt_add {c₁ c₂ a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (h₁ : c₁ ≤ (√a₁ + √b₁) ^ 2) (h₂ : c₂ ≤ (√a₂ + √b₂) ^ 2) :
    c₁ + c₂ ≤ (√(a₁ + a₂) + √(b₁ + b₂)) ^ 2 := by
  have h := sum_le_sq_sqrt_add (Finset.univ : Finset (Fin 2)) (c := ![c₁, c₂])
    (a := ![a₁, a₂]) (b := ![b₁, b₂])
    (fun i _ => by fin_cases i <;> simpa) (fun i _ => by fin_cases i <;> simpa)
    (fun i _ => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

/-- A nonnegative function whose derivative is at most `2 η sqrt f` grows at most linearly
in square root. The initial value is not multiplied by any factor. -/
theorem sqrt_le_add_mul_of_hasDerivAt {f f' : ℝ → ℝ} {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hf0 : ∀ s, 0 ≤ f s) (hd : ∀ s, HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Icc 0 θ, f' s ≤ 2 * η * √(f s)) :
    √(f θ) ≤ √(f 0) + θ * η := by
  have key : ∀ ε > 0, √(f θ + ε) ≤ √(f 0 + ε) + θ * η := by
    intro ε hε
    have hpos : ∀ s, 0 < f s + ε := fun s => by linarith [hf0 s]
    have hφ : ∀ s, HasDerivAt (fun r => √(f r + ε) - η * r)
        (f' s / (2 * √(f s + ε)) - η) s := fun s => by
      have h₁ := ((hd s).add_const ε).sqrt (hpos s).ne'
      have h₂ : HasDerivAt (fun r : ℝ => η * r) η s := by
        simpa using (hasDerivAt_id s).const_mul η
      exact h₁.sub h₂
    have hanti : AntitoneOn (fun r => √(f r + ε) - η * r) (Icc 0 θ) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 θ)
      · exact fun s _ => (hφ s).continuousAt.continuousWithinAt
      · exact fun s _ => (hφ s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hφ s).deriv]
        have hs' : s ∈ Icc 0 θ := Ioo_subset_Icc_self hs
        have hsq : √(f s) ≤ √(f s + ε) := Real.sqrt_le_sqrt (by linarith)
        have hden : 0 < 2 * √(f s + ε) := by have := Real.sqrt_pos.mpr (hpos s); positivity
        rw [sub_nonpos, div_le_iff₀ hden]
        nlinarith [hb s hs', mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 * η by positivity)]
    have h := hanti ⟨le_rfl, hθ⟩ ⟨hθ, le_rfl⟩ hθ
    simp only [mul_zero, sub_zero] at h
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have h₁ := key (ε ^ 2) (by positivity)
  have h₂ : √(f θ) ≤ √(f θ + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h₃ : √(f 0 + ε ^ 2) ≤ √(f 0) + ε := by
    have hs := Real.sqrt_nonneg (f 0)
    calc √(f 0 + ε ^ 2) ≤ √((√(f 0) + ε) ^ 2) := Real.sqrt_le_sqrt (by
          nlinarith [Real.sq_sqrt (hf0 0), mul_nonneg hs hε.le])
      _ = √(f 0) + ε := Real.sqrt_sq (by positivity)
  linarith

section FiniteIndex

variable [Fintype ι]

/-! ## Supports -/

omit [NormedSpace ℝ E] in
theorem State.Supported.reactionGenerator {Y : State E ι} {R : ℝ}
    (hY : Y.Supported R) (b : ι → E → ℝ) :
    (WaveSplitting.reactionGenerator b Y).Supported R := fun x hx => by
  obtain ⟨hu, hv, hp⟩ := hY x hx
  exact ⟨hv, by simp [WaveSplitting.reactionGenerator, coupling, hu, hp], fun _ => rfl⟩

/-- The actual residual is supported in the ball swept by the step in a unit time
neighbourhood; its temporal derivative is local in time. -/
theorem State.Supported.residual [DecidableEq ι] {Z : State E ι} {R : ℝ}
    (hZ : Z.Supported R) (a : ι → E) (b : ι → E → ℝ) (js : List ι) (θ : ℝ) :
    (WaveSplitting.residual a b js Z θ).Supported (R + (|θ| + 1) * travel a js) := by
  have htr := travel_nonneg a js
  rw [residual_eq_subState]
  refine State.Supported.subState ?_ ?_
  · intro x hx
    have hev : ∀ᶠ s in nhds θ, (step a b js s Z).u x = 0 ∧ (step a b js s Z).v x = 0 ∧
        ∀ j, (step a b js s Z).p j x = 0 := by
      filter_upwards [Metric.ball_mem_nhds θ one_pos] with s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      have habs : |s| ≤ |θ| + 1 := by have := abs_sub_abs_le_abs_sub s θ; linarith
      exact ((hZ.sweep a s js).reaction b s) x
        (lt_of_le_of_lt (by nlinarith [mul_le_mul_of_nonneg_right habs htr]) hx)
    refine ⟨?_, ?_, fun j => ?_⟩
    · exact (Filter.EventuallyEq.deriv_eq (f := fun _ => (0 : ℝ))
        (hev.mono fun s hs => hs.1)).trans (deriv_const θ 0)
    · exact (Filter.EventuallyEq.deriv_eq (f := fun _ => (0 : ℝ))
        (hev.mono fun s hs => hs.2.1)).trans (deriv_const θ 0)
    · exact (Filter.EventuallyEq.deriv_eq (f := fun _ => (0 : ℝ))
        (hev.mono fun s hs => hs.2.2 j)).trans (deriv_const θ 0)
  · have hs := (hZ.sweep a θ js).reaction b θ
    have hle : R + |θ| * travel a js ≤ R + (|θ| + 1) * travel a js := by nlinarith
    exact ((hs.sweepGenerator a js).addState (hs.reactionGenerator b)).mono hle

end FiniteIndex

/-- Componentwise continuity, used for states that are only known to be continuous. -/
private def ContinuousState (Y : State E ι) : Prop :=
  Continuous Y.u ∧ Continuous Y.v ∧ ∀ j, Continuous (Y.p j)

private theorem State.Smooth.continuousState {Y : State E ι} (hY : Y.Smooth) :
    ContinuousState Y :=
  ⟨hY.1.continuous, hY.2.1.continuous, fun j => (hY.2.2 j).continuous⟩

omit [NormedSpace ℝ E] in
private theorem continuous_pairing [Fintype ι] {w : E → ℝ} (hw : Continuous w)
    {X Z : State E ι} (hX : ContinuousState X) (hZ : ContinuousState Z) :
    Continuous (fun x => w x * (X.u x * Z.u x + X.v x * Z.v x + ∑ j, X.p j x * Z.p j x)) :=
  hw.mul (((hX.1.mul hZ.1).add (hX.2.1.mul hZ.2.1)).add
    (continuous_finsetSum _ fun j _ => (hX.2.2 j).mul (hZ.2.2 j)))

private theorem differentiate_addState {n : ℕ} (v : Fin n → E) {X Z : State E ι}
    (hX : X.Smooth) (hZ : Z.Smooth) :
    differentiate v (addState X Z) = addState (differentiate v X) (differentiate v Z) := by
  apply state_ext
  · exact derivative_add v hX.1 hZ.1
  · exact derivative_add v hX.2.1 hZ.2.1
  · funext j
    exact derivative_add v (hX.2.2 j) (hZ.2.2 j)

omit [NormedSpace ℝ E] in
private theorem derivative_eq_zero_of_supported' {f : E → ℝ} {R : ℝ}
    (hf : ∀ y, R < ‖y‖ → f y = 0) {n : ℕ} [NormedSpace ℝ E] (v : Fin n → E) {x : E}
    (hx : R < ‖x‖) : derivative v f x = 0 := by
  have h : f =ᶠ[nhds x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)
      fun y hy => hf y hy
  unfold derivative
  rw [(h.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
  rfl

private theorem State.Supported.differentiate {Y : State E ι} {R : ℝ} (hY : Y.Supported R)
    {n : ℕ} (v : Fin n → E) : (differentiate v Y).Supported R := fun _ hx =>
  ⟨derivative_eq_zero_of_supported' (fun y hy => (hY y hy).1) v hx,
    derivative_eq_zero_of_supported' (fun y hy => (hY y hy).2.1) v hx,
    fun j => derivative_eq_zero_of_supported' (fun y hy => (hY y hy).2.2 j) v hx⟩

private theorem State.Smooth.continuousState_differentiate {Y : State E ι} (hY : Y.Smooth)
    {n : ℕ} (v : Fin n → E) : ContinuousState (differentiate v Y) :=
  ⟨continuous_derivative v hY.1, continuous_derivative v hY.2.1,
    fun j => continuous_derivative v (hY.2.2 j)⟩

private theorem timeDerivative_step_eq [Fintype ι] [DecidableEq ι] (a : ι → E)
    (b : ι → E → ℝ) (js : List ι) (Y : State E ι) (θ : ℝ) :
    timeDerivative (fun s => step a b js s Y) θ =
      addState (splitGenerator a b js (step a b js θ Y)) (residual a b js Y θ) := by
  rw [residual_eq_subState]
  apply state_ext
  · funext x; simp only [addState, subState]; ring
  · funext x; simp only [addState, subState]; ring
  · funext j x; simp only [addState, subState]; ring

/-! ## Weighted energy and pairing -/

section Integration
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [IsFiniteMeasureOnCompacts m]

/-- Weighted square energy of a classical triple. -/
def weightedEnergy [Fintype ι] (w : E → ℝ) (Y : State E ι) : ℝ :=
  ∫ x, w x * (Y.u x ^ 2 + Y.v x ^ 2 + ∑ j, Y.p j x ^ 2) ∂m

/-- The weighted pairing associated with `weightedEnergy`. -/
def weightedPairing [Fintype ι] (w : E → ℝ) (X Z : State E ι) : ℝ :=
  ∫ x, w x * (X.u x * Z.u x + X.v x * Z.v x + ∑ j, X.p j x * Z.p j x) ∂m

section FiniteIndex

variable [Fintype ι]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [IsFiniteMeasureOnCompacts m] in
theorem weightedEnergy_nonneg {w : E → ℝ} (hw0 : ∀ x, 0 ≤ w x) (Y : State E ι) :
    0 ≤ weightedEnergy m w Y :=
  integral_nonneg fun x => mul_nonneg (hw0 x) (by positivity)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [IsFiniteMeasureOnCompacts m] in
private theorem weightedPairing_self (w : E → ℝ) (X : State E ι) :
    weightedPairing m w X X = weightedEnergy m w X := by
  simp only [weightedPairing, weightedEnergy, pow_two]

end FiniteIndex

variable [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem integrable_of_supported [ProperSpace E] {f : E → ℝ} (hf : Continuous f) {R : ℝ}
    (h : ∀ x, R < ‖x‖ → f x = 0) : Integrable f m :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall 0 R)
    fun x hx => h x (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx))

section FiniteIndex

variable [Fintype ι]

private theorem integrable_pairing {w : E → ℝ} (hw : Continuous w)
    {X Z : State E ι} (hX : ContinuousState X) (hZ : ContinuousState Z) {R : ℝ}
    (hR : X.Supported R) :
    Integrable (fun x => w x * (X.u x * Z.u x + X.v x * Z.v x + ∑ j, X.p j x * Z.p j x)) m :=
  integrable_of_supported m (continuous_pairing hw hX hZ) fun x hx => by
    obtain ⟨hu, hv, hp⟩ := hR x hx
    simp [hu, hv, hp]

private theorem weightedEnergy_add_smul' {w : E → ℝ} (hw : Continuous w)
    {X Z : State E ι} (hX : ContinuousState X) (hZ : ContinuousState Z) {R : ℝ}
    (hXR : X.Supported R) (hZR : Z.Supported R) (t : ℝ) :
    ∫ x, w x * ((X.u x + t * Z.u x) ^ 2 + (X.v x + t * Z.v x) ^ 2 +
        ∑ j, (X.p j x + t * Z.p j x) ^ 2) ∂m =
      weightedEnergy m w X + 2 * t * weightedPairing m w X Z + t ^ 2 * weightedEnergy m w Z := by
  have hp : (fun x => w x * ((X.u x + t * Z.u x) ^ 2 + (X.v x + t * Z.v x) ^ 2 +
      ∑ j, (X.p j x + t * Z.p j x) ^ 2)) = fun x =>
      w x * (X.u x * X.u x + X.v x * X.v x + ∑ j, X.p j x * X.p j x) +
      2 * t * (w x * (X.u x * Z.u x + X.v x * Z.v x + ∑ j, X.p j x * Z.p j x)) +
      t ^ 2 * (w x * (Z.u x * Z.u x + Z.v x * Z.v x + ∑ j, Z.p j x * Z.p j x)) := by
    funext x
    have hs : ∑ j, (X.p j x + t * Z.p j x) ^ 2 = ∑ j, X.p j x * X.p j x +
        2 * t * ∑ j, X.p j x * Z.p j x + t ^ 2 * ∑ j, Z.p j x * Z.p j x := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    ring
  have iXX := integrable_pairing m hw hX hX hXR
  have iXZ := integrable_pairing m hw hX hZ hXR
  have iZZ := integrable_pairing m hw hZ hZ hZR
  rw [hp, integral_add (f := fun x => w x * (X.u x * X.u x + X.v x * X.v x +
      ∑ j, X.p j x * X.p j x) + 2 * t * (w x * (X.u x * Z.u x + X.v x * Z.v x +
        ∑ j, X.p j x * Z.p j x)))
    (g := fun x => t ^ 2 * (w x * (Z.u x * Z.u x + Z.v x * Z.v x + ∑ j, Z.p j x * Z.p j x)))
    (iXX.add (iXZ.const_mul _)) (iZZ.const_mul _),
    integral_add (f := fun x => w x * (X.u x * X.u x + X.v x * X.v x + ∑ j, X.p j x * X.p j x))
    (g := fun x => 2 * t * (w x * (X.u x * Z.u x + X.v x * Z.v x + ∑ j, X.p j x * Z.p j x)))
    iXX (iXZ.const_mul _), integral_const_mul, integral_const_mul, ← weightedPairing_self,
    ← weightedPairing_self]
  rfl

private theorem abs_weightedPairing_le' {w : E → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) {X Z : State E ι} (hX : ContinuousState X) (hZ : ContinuousState Z)
    {R : ℝ} (hXR : X.Supported R) (hZR : Z.Supported R) :
    |weightedPairing m w X Z| ≤ √(weightedEnergy m w X) * √(weightedEnergy m w Z) :=
  abs_le_sqrt_mul_of_quadratic (weightedEnergy_nonneg m hw0 X) fun t => by
      rw [← weightedEnergy_add_smul' m hw hX hZ hXR hZR t]
      exact integral_nonneg fun x => mul_nonneg (hw0 x) (by positivity)

private theorem weightedEnergy_addState_le' {w : E → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) {X Z : State E ι} (hX : ContinuousState X) (hZ : ContinuousState Z)
    {R : ℝ} (hXR : X.Supported R) (hZR : Z.Supported R) :
    weightedEnergy m w (addState X Z) ≤
      (√(weightedEnergy m w X) + √(weightedEnergy m w Z)) ^ 2 := by
  have h := weightedEnergy_add_smul' m hw hX hZ hXR hZR 1
  simp only [one_mul, one_pow, mul_one] at h
  have hc := abs_weightedPairing_le' m hw hw0 hX hZ hXR hZR
  have e : weightedEnergy m w (addState X Z) = weightedEnergy m w X +
      2 * weightedPairing m w X Z + weightedEnergy m w Z := h
  rw [e, sq_sqrt_add (weightedEnergy_nonneg m hw0 X) (weightedEnergy_nonneg m hw0 Z)]
  linarith [le_abs_self (weightedPairing m w X Z)]

private theorem weightedEnergy_subState_le' {w : E → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) {X Z : State E ι} (hX : ContinuousState X) (hZ : ContinuousState Z)
    {R : ℝ} (hXR : X.Supported R) (hZR : Z.Supported R) :
    weightedEnergy m w (subState X Z) ≤
      (√(weightedEnergy m w X) + √(weightedEnergy m w Z)) ^ 2 := by
  have h := weightedEnergy_add_smul' m hw hX hZ hXR hZR (-1)
  have e : weightedEnergy m w (subState X Z) = weightedEnergy m w X +
      2 * (-1) * weightedPairing m w X Z + (-1) ^ 2 * weightedEnergy m w Z := by
    rw [← h]
    simp only [weightedEnergy, subState, neg_one_mul, ← sub_eq_add_neg]
  have hc := abs_weightedPairing_le' m hw hw0 hX hZ hXR hZR
  rw [e, sq_sqrt_add (weightedEnergy_nonneg m hw0 X) (weightedEnergy_nonneg m hw0 Z)]
  linarith [neg_abs_le (weightedPairing m w X Z)]

/-- Cauchy--Schwarz for the weighted pairing of supported smooth states. -/
theorem abs_weightedPairing_le {w : E → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) {X Z : State E ι} (hX : X.Smooth) (hZ : Z.Smooth) {R : ℝ}
    (hXR : X.Supported R) (hZR : Z.Supported R) :
    |weightedPairing m w X Z| ≤ √(weightedEnergy m w X) * √(weightedEnergy m w Z) :=
  abs_weightedPairing_le' m hw hw0 hX.continuousState hZ.continuousState hXR hZR

/-- Minkowski's inequality for the weighted energy. -/
theorem weightedEnergy_addState_le {w : E → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) {X Z : State E ι} (hX : X.Smooth) (hZ : Z.Smooth) {R : ℝ}
    (hXR : X.Supported R) (hZR : Z.Supported R) :
    weightedEnergy m w (addState X Z) ≤
      (√(weightedEnergy m w X) + √(weightedEnergy m w Z)) ^ 2 :=
  weightedEnergy_addState_le' m hw hw0 hX.continuousState hZ.continuousState hXR hZR

/-- Minkowski's inequality for differences in the weighted energy. -/
theorem weightedEnergy_subState_le {w : E → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) {X Z : State E ι} (hX : X.Smooth) (hZ : Z.Smooth) {R : ℝ}
    (hXR : X.Supported R) (hZR : Z.Supported R) :
    weightedEnergy m w (subState X Z) ≤
      (√(weightedEnergy m w X) + √(weightedEnergy m w Z)) ^ 2 :=
  weightedEnergy_subState_le' m hw hw0 hX.continuousState hZ.continuousState hXR hZR

private theorem energy_eq_weightedEnergy_one {Y : State E ι}
    (hY : ContinuousState Y) {R : ℝ} (hR : Y.Supported R) :
    energy m Y = weightedEnergy m (fun _ => 1) Y := by
  have hi {f : E → ℝ} (hf : Continuous f) (hz : ∀ x, R < ‖x‖ → f x = 0) :
      Integrable (fun x => f x ^ 2) m :=
    integrable_of_supported m (R := R) (hf.pow 2) fun x hx => by simp [hz x hx]
  have iu := hi hY.1 fun x hx => (hR x hx).1
  have iv := hi hY.2.1 fun x hx => (hR x hx).2.1
  have ip (j : ι) := hi (hY.2.2 j) fun x hx => (hR x hx).2.2 j
  simp only [weightedEnergy, one_mul]
  rw [integral_add (f := fun x => Y.u x ^ 2 + Y.v x ^ 2) (g := fun x => ∑ j, Y.p j x ^ 2)
      (iu.add iv) (integrable_finsetSum _ fun j _ => ip j),
    integral_add (f := fun x => Y.u x ^ 2) (g := fun x => Y.v x ^ 2) iu iv,
    integral_finsetSum _ fun j _ => ip j]
  rfl

/-- Minkowski's inequality for the ordered-coordinate derivative energy: its square root is
a seminorm on supported smooth states. -/
theorem derivativeEnergy_addState_le_sq (a : ι → E) (k : ℕ) {X Z : State E ι}
    (hX : X.Smooth) (hZ : Z.Smooth) {R : ℝ} (hXR : X.Supported R) (hZR : Z.Supported R) :
    derivativeEnergy m a k (addState X Z) ≤
      (√(derivativeEnergy m a k X) + √(derivativeEnergy m a k Z)) ^ 2 := by
  unfold derivativeEnergy
  apply sum_le_sq_sqrt_add
  · exact fun n _ => Finset.sum_nonneg fun _ _ => energy_nonneg m _
  · exact fun n _ => Finset.sum_nonneg fun _ _ => energy_nonneg m _
  intro n _
  apply sum_le_sq_sqrt_add
  · exact fun _ _ => energy_nonneg m _
  · exact fun _ _ => energy_nonneg m _
  intro v _
  have hdX := hX.continuousState_differentiate (fun i => a (v i))
  have hdZ := hZ.continuousState_differentiate (fun i => a (v i))
  have hRX := hXR.differentiate (fun i => a (v i))
  have hRZ := hZR.differentiate (fun i => a (v i))
  rw [differentiate_addState _ hX hZ,
    energy_eq_weightedEnergy_one m (Y := addState _ _)
      ⟨hdX.1.add hdZ.1, hdX.2.1.add hdZ.2.1, fun j => (hdX.2.2 j).add (hdZ.2.2 j)⟩
      (hRX.addState hRZ),
    energy_eq_weightedEnergy_one m hdX hRX, energy_eq_weightedEnergy_one m hdZ hRZ]
  exact weightedEnergy_addState_le' m continuous_const (fun _ => zero_le_one) hdX hdZ hRX hRZ

end FiniteIndex

/-! ## The weighted skew identity -/

section Haar
variable [m.IsAddHaarMeasure]

omit [IsFiniteMeasureOnCompacts m] in
private theorem integral_fderiv_eq_zero {g : E → ℝ} (hg : ContDiff ℝ 1 g) {R : ℝ}
    (hR : ∀ x, R < ‖x‖ → g x = 0) (v : E) : ∫ x, fderiv ℝ g x v ∂m = 0 := by
  have hgc : HasCompactSupport g := HasCompactSupport.intro (isCompact_closedBall 0 R)
    fun x hx => hR x (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)
  have hd : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport (fun x => fderiv ℝ g x v) :=
    (hgc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L v) (by simp)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := m)
    (f := fun _ : E => (1 : ℝ)) (g := g) (v := v)
    (by simp) (by simpa using hd.integrable_of_hasCompactSupport hdc)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hgc)
    (fun x _ => differentiableAt_const _)
    (fun x _ => (hg.differentiable one_ne_zero) x)
  simpa using h

omit [IsFiniteMeasureOnCompacts m] in
/-- **Weighted skew identity.** If `D_(a_j) w = -b_j w`, the actual wave generator is skew
in the weighted pairing on supported smooth states. No identification `p = grad u` is used. -/
theorem weightedPairing_waveGenerator [Fintype ι] (a : ι → E) (b : ι → E → ℝ)
    {w : E → ℝ} (hw : ContDiff ℝ 1 w) (hwb : ∀ j x, fderiv ℝ w x (a j) = -(b j x * w x))
    {Y : State E ι} (hY : Y.Smooth) {R : ℝ} (hR : Y.Supported R) :
    weightedPairing m w Y (waveGenerator a b Y) = 0 := by
  let H : ι → E → ℝ := fun j x => w x * (Y.v x * Y.p j x)
  have hH (j : ι) : ContDiff ℝ 1 (H j) :=
    hw.mul ((hY.2.1.of_le (by simp)).mul ((hY.2.2 j).of_le (by simp)))
  have hHR (j : ι) : ∀ x, R < ‖x‖ → H j x = 0 := fun x hx => by
    simp [H, (hR x hx).2.1]
  have hfd (j : ι) (x : E) : fderiv ℝ (H j) x (a j) =
      -(b j x * w x) * (Y.v x * Y.p j x) +
        w x * (fderiv ℝ Y.v x (a j) * Y.p j x + Y.v x * fderiv ℝ (Y.p j) x (a j)) := by
    have hwx := (hw.differentiable one_ne_zero) x
    have hvx := (hY.2.1.differentiable (by simp)) x
    have hpx := (hY.2.2 j).differentiable (by simp) x
    have e : fderiv ℝ (H j) x = w x • fderiv ℝ (fun y => Y.v y * Y.p j y) x +
        (Y.v x * Y.p j x) • fderiv ℝ w x := fderiv_fun_mul hwx (hvx.mul hpx)
    rw [e, fderiv_fun_mul hvx hpx]
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hwb]
    ring
  have hpt : (fun x => w x * (Y.u x * (waveGenerator a b Y).u x +
      Y.v x * (waveGenerator a b Y).v x +
        ∑ j, Y.p j x * (waveGenerator a b Y).p j x)) =
      fun x => ∑ j, fderiv ℝ (H j) x (a j) := by
    funext x
    simp only [hfd, waveGenerator, coupling]
    have e₁ : w x * (Y.u x * Y.v x + Y.v x * (∑ j, fderiv ℝ (Y.p j) x (a j) - Y.u x -
        ∑ j, b j x * Y.p j x) + ∑ j, Y.p j x * fderiv ℝ Y.v x (a j)) =
        w x * (Y.v x * ∑ j, fderiv ℝ (Y.p j) x (a j)) -
          w x * (Y.v x * ∑ j, b j x * Y.p j x) + w x * ∑ j, Y.p j x * fderiv ℝ Y.v x (a j) := by
      ring
    rw [e₁]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hi (j : ι) : Integrable (fun x => fderiv ℝ (H j) x (a j)) m :=
    integrable_of_supported m (((hH j).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      fun x hx => by
        have h0 : H j =ᶠ[nhds x] fun _ => (0 : ℝ) :=
          Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)
            fun y hy => hHR j y hy
        rw [h0.fderiv_eq]
        simp
  unfold weightedPairing
  rw [hpt, integral_finsetSum _ fun j _ => hi j]
  exact Finset.sum_eq_zero fun j _ => integral_fderiv_eq_zero m (hH j) (hHR j) (a j)

end Haar

/-! ## Temporal derivative of the weighted energy -/

private theorem hasDerivAt_integral_of_supported {F F' : ℝ → E → ℝ}
    (hF : Continuous (fun z : ℝ × E => F z.1 z.2))
    (hF' : Continuous (fun z : ℝ × E => F' z.1 z.2))
    (hd : ∀ s x, HasDerivAt (fun r => F r x) (F' s x) s) {R s₀ : ℝ}
    (hz : ∀ s ∈ Metric.ball s₀ 1, ∀ x, R < ‖x‖ → F s x = 0 ∧ F' s x = 0) :
    HasDerivAt (fun s => ∫ x, F s x ∂m) (∫ x, F' s₀ x ∂m) s₀ := by
  set K : Set E := Metric.closedBall 0 R
  have hK : IsCompact K := isCompact_closedBall 0 R
  have hout : ∀ x, x ∉ K → R < ‖x‖ := fun x hx => by
    simpa [K, Metric.mem_closedBall, dist_zero_right, not_le] using hx
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ 1).prod hK).exists_bound_of_continuousOn
    hF'.continuousOn
  have hslice {G : ℝ → E → ℝ} (hG : Continuous (fun z : ℝ × E => G z.1 z.2)) (s : ℝ) :
      Continuous (G s) := by
    have h := hG.comp (continuous_const.prodMk continuous_id : Continuous fun x : E => (s, x))
    exact h
  have hs₀ : s₀ ∈ Metric.ball s₀ 1 := Metric.mem_ball_self one_pos
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := K.indicator fun _ => max C 0) (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun s => (hslice hF s).aestronglyMeasurable)
    (integrable_of_supported m (hslice hF s₀) fun x hx => (hz s₀ hs₀ x hx).1)
    (hslice hF' s₀).aestronglyMeasurable ?_ ?_
    (Filter.Eventually.of_forall fun x s _ => hd s x)).2
  · refine Filter.Eventually.of_forall fun x s hs => ?_
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact (hC (s, x) ⟨Metric.ball_subset_closedBall hs, hx⟩).trans (le_max_left _ _)
    · rw [indicator_of_notMem hx, (hz s hs x (hout x hx)).2, norm_zero]
  · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet

section FiniteIndex

variable [Fintype ι]

/-- The weighted energy of a jointly smooth supported curve is differentiable, with the
weighted pairing of the state and its temporal derivative as derivative. -/
theorem hasDerivAt_weightedEnergy {w : E → ℝ} (hw : Continuous w)
    {Z : ℝ → State E ι} (hZ : JointSmooth Z) {R s₀ : ℝ}
    (hR : ∀ s ∈ Metric.ball s₀ 1, (Z s).Supported R) :
    HasDerivAt (fun s => weightedEnergy m w (Z s))
      (2 * weightedPairing m w (Z s₀) (timeDerivative Z s₀)) s₀ := by
  have hD := hZ.timeDerivative
  have hwc : Continuous (fun z : ℝ × E => w z.2) := hw.comp continuous_snd
  have hF : Continuous (fun z : ℝ × E => w z.2 * ((Z z.1).u z.2 ^ 2 + (Z z.1).v z.2 ^ 2 +
      ∑ j, (Z z.1).p j z.2 ^ 2)) :=
    hwc.mul (((hZ.1.continuous.pow 2).add (hZ.2.1.continuous.pow 2)).add
      (continuous_finsetSum _ fun j _ => (hZ.2.2 j).continuous.pow 2))
  have hF' : Continuous (fun z : ℝ × E => 2 * (w z.2 * ((Z z.1).u z.2 *
      (timeDerivative Z z.1).u z.2 + (Z z.1).v z.2 * (timeDerivative Z z.1).v z.2 +
        ∑ j, (Z z.1).p j z.2 * (timeDerivative Z z.1).p j z.2))) :=
    continuous_const.mul (hwc.mul (((hZ.1.continuous.mul hD.1.continuous).add
      (hZ.2.1.continuous.mul hD.2.1.continuous)).add
      (continuous_finsetSum _ fun j _ => (hZ.2.2 j).continuous.mul (hD.2.2 j).continuous)))
  have hcomp {G : ℝ × E → ℝ} (hG : ContDiff ℝ ∞ G) (s : ℝ) (x : E) :
      HasDerivAt (fun r => G (r, x)) (deriv (fun r => G (r, x)) s) s :=
    (((hG.differentiable (by simp)).comp
      (differentiable_id.prodMk (differentiable_const x))) s).hasDerivAt
  have hd : ∀ s x, HasDerivAt (fun r => w x * ((Z r).u x ^ 2 + (Z r).v x ^ 2 +
      ∑ j, (Z r).p j x ^ 2)) (2 * (w x * ((Z s).u x * (timeDerivative Z s).u x +
        (Z s).v x * (timeDerivative Z s).v x +
          ∑ j, (Z s).p j x * (timeDerivative Z s).p j x))) s := by
    intro s x
    have hu := hcomp hZ.1 s x
    have hv := hcomp hZ.2.1 s x
    have hp (j : ι) := hcomp (hZ.2.2 j) s x
    have h := (((hu.pow 2).add (hv.pow 2)).add
      (HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hp j).pow 2)).const_mul (w x)
    refine h.congr_deriv ?_
    simp only [timeDerivative, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    have e : ∑ j, 2 * (Z s).p j x * deriv (fun r => (Z r).p j x) s =
        2 * ∑ j, (Z s).p j x * deriv (fun r => (Z r).p j x) s := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    ring
  have h := hasDerivAt_integral_of_supported m hF hF' hd (R := R) (s₀ := s₀) fun s hs x hx => by
    obtain ⟨hu, hv, hp⟩ := hR s hs x hx
    simp [hu, hv, hp]
  rw [integral_const_mul] at h
  exact h

/-! ## Forced energy along the actual cells -/

private theorem weightedPairing_addState_right {w : E → ℝ} (hw : Continuous w)
    {X A B : State E ι} (hX : ContinuousState X) (hA : ContinuousState A)
    (hB : ContinuousState B) {R : ℝ} (hR : X.Supported R) :
    weightedPairing m w X (addState A B) = weightedPairing m w X A + weightedPairing m w X B := by
  unfold weightedPairing
  rw [← integral_add (integrable_pairing m hw hX hA hR) (integrable_pairing m hw hX hB hR)]
  congr 1
  funext x
  simp only [addState, mul_add, Finset.sum_add_distrib]
  ring

end FiniteIndex

section StructuredSpace

variable [m.IsAddHaarMeasure]

omit [IsFiniteMeasureOnCompacts m] in
/-- **Forced weighted energy on one actual step.** If every residual on `[0,θ]` has weighted
energy at most `η^2`, the weighted norm of the actual step grows by at most `θ η`. The
initial norm enters with coefficient one. -/
theorem sqrt_weightedEnergy_step_le {d : ℕ} (a : Fin d → E)
    {b : Fin d → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hw0 : ∀ x, 0 ≤ w x) (hwb : ∀ j x, fderiv ℝ w x (a j) = -(b j x * w x))
    {Y : State E (Fin d)} (hY : Y.Smooth) {R : ℝ} (hR : Y.Supported R) {θ η : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (he : ∀ s ∈ Icc 0 θ,
      weightedEnergy m w (residual a b (List.finRange d) Y s) ≤ η ^ 2) :
    √(weightedEnergy m w (step a b (List.finRange d) θ Y)) ≤
      √(weightedEnergy m w Y) + θ * η := by
  set js := List.finRange d
  have htr := travel_nonneg a js
  have hZ : JointSmooth (fun s => step a b js s Y) := (hY.joint_const.sweep a js).reaction hb
  have hsupp (s : ℝ) : (step a b js s Y).Supported (R + (|s| + 1) * travel a js) :=
    ((hR.sweep a s js).reaction b s).mono (by nlinarith [abs_nonneg s])
  have hd (s₀ : ℝ) := hasDerivAt_weightedEnergy m hw.continuous hZ
    (R := R + (|s₀| + 2) * travel a js) (s₀ := s₀) fun s hs => by
      rw [Metric.mem_ball, Real.dist_eq] at hs
      have habs : |s| ≤ |s₀| + 1 := by have := abs_sub_abs_le_abs_sub s s₀; linarith
      exact (hsupp s).mono (by nlinarith [mul_le_mul_of_nonneg_right habs htr])
  have h := sqrt_le_add_mul_of_hasDerivAt (f := fun s => weightedEnergy m w (step a b js s Y))
    hθ hη (fun s => weightedEnergy_nonneg m hw0 _) hd ?_
  · simpa only [step_zero] using h
  intro s hs
  have hYs : (step a b js s Y).Smooth := (hY.sweep a s js).reaction hb s
  have hes : (residual a b js Y s).Smooth := (jointSmooth_residual a hb js hY).slice s
  have hGs : (splitGenerator a b js (step a b js s Y)).Smooth :=
    (hYs.sweepGenerator a js).addState (hYs.reactionGenerator hb)
  have heR := hR.residual a b js s
  have hle : R + |s| * travel a js ≤ R + (|s| + 1) * travel a js := by nlinarith
  rw [timeDerivative_step_eq, weightedPairing_addState_right m hw.continuous
      hYs.continuousState hGs.continuousState hes.continuousState ((hsupp s)),
    show splitGenerator a b js (step a b js s Y) = waveGenerator a b (step a b js s Y) from
      splitGenerator_finRange a b _,
    weightedPairing_waveGenerator m a b hw hwb hYs (hsupp s), zero_add]
  have hcs := abs_weightedPairing_le m hw.continuous hw0 hYs hes (hsupp s) heR
  have hsq : √(weightedEnergy m w (residual a b js Y s)) ≤ η := by
    calc _ ≤ √(η ^ 2) := Real.sqrt_le_sqrt (he s hs)
      _ = η := Real.sqrt_sq hη
  have hn := Real.sqrt_nonneg (weightedEnergy m w (step a b js s Y))
  nlinarith [le_abs_self (weightedPairing m w (step a b js s Y) (residual a b js Y s)),
    mul_le_mul_of_nonneg_left hsq hn]

omit [IsFiniteMeasureOnCompacts m] in
/-- Forced weighted energy at the actual grid nodes. -/
theorem sqrt_weightedEnergy_nodes_le {d : ℕ} (a : Fin d → E)
    {b : Fin d → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hw0 : ∀ x, 0 ≤ w x) (hwb : ∀ j x, fderiv ℝ w x (a j) = -(b j x * w x))
    {Y : State E (Fin d)} (hY : Y.Smooth) {R : ℝ} (hR : Y.Supported R) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (k : ℕ)
    (he : ∀ j < k, ∀ s ∈ Icc 0 δ, weightedEnergy m w
      (residual a b (List.finRange d) (nodes a b (List.finRange d) δ Y j) s) ≤ η ^ 2) :
    √(weightedEnergy m w (nodes a b (List.finRange d) δ Y k)) ≤
      √(weightedEnergy m w Y) + k * δ * η := by
  induction k with
  | zero => simp [nodes]
  | succ k ih =>
    have h := sqrt_weightedEnergy_step_le m a hb hw hw0 hwb (hY.nodes a hb _ δ k)
      (hR.nodes a b _ δ k) hδ hη (he k (Nat.lt_succ_self k))
    have ih' := ih fun j hj => he j (Nat.lt_succ_of_lt hj)
    change √(weightedEnergy m w (step a b _ δ (nodes a b _ δ Y k))) ≤ _
    push_cast
    nlinarith

omit [IsFiniteMeasureOnCompacts m] in
/-- Forced weighted energy inside every actual cell. -/
theorem sqrt_weightedEnergy_cell_le {d : ℕ} (a : Fin d → E)
    {b : Fin d → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hw0 : ∀ x, 0 ≤ w x) (hwb : ∀ j x, fderiv ℝ w x (a j) = -(b j x * w x))
    {Y : State E (Fin d)} (hY : Y.Smooth) {R : ℝ} (hR : Y.Supported R) {δ η θ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (k : ℕ)
    (he : ∀ j ≤ k, ∀ s ∈ Icc 0 δ, weightedEnergy m w
      (residual a b (List.finRange d) (nodes a b (List.finRange d) δ Y j) s) ≤ η ^ 2)
    (hθ : 0 ≤ θ) (hθδ : θ ≤ δ) :
    √(weightedEnergy m w (cell a b (List.finRange d) δ Y k θ)) ≤
      √(weightedEnergy m w Y) + (k * δ + θ) * η := by
  have hn := sqrt_weightedEnergy_nodes_le m a hb hw hw0 hwb hY hR hδ hη k
    fun j hj => he j hj.le
  have hs := sqrt_weightedEnergy_step_le m a hb hw hw0 hwb (hY.nodes a hb _ δ k)
    (hR.nodes a b _ δ k) hθ hη fun s hs => he k le_rfl s ⟨hs.1, hs.2.trans hθδ⟩
  change √(weightedEnergy m w (step a b _ θ (nodes a b _ δ Y k))) ≤ _
  nlinarith

end StructuredSpace

section FiniteIndex

variable [Fintype ι]

omit [NormedSpace ℝ E] [BorelSpace E] [IsFiniteMeasureOnCompacts m] [FiniteDimensional ℝ E] in
private theorem weightedEnergy_le_mul {w : E → ℝ}
    {Y : State E ι} {T M : ℝ} (hT : Y.Supported T) (hM : ∀ x, ‖x‖ ≤ T → w x ≤ M)
    (hi : Integrable (fun x => Y.u x ^ 2 + Y.v x ^ 2 + ∑ j, Y.p j x ^ 2) m)
    (hiw : Integrable (fun x => w x * (Y.u x ^ 2 + Y.v x ^ 2 + ∑ j, Y.p j x ^ 2)) m) :
    weightedEnergy m w Y ≤ M * weightedEnergy m (fun _ => 1) Y := by
  unfold weightedEnergy
  simp only [one_mul]
  rw [← integral_const_mul]
  refine integral_mono hiw (hi.const_mul M) fun x => ?_
  by_cases hx : ‖x‖ ≤ T
  · exact mul_le_mul_of_nonneg_right (hM x hx) (by positivity)
  · obtain ⟨hu, hv, hp⟩ := hT x (lt_of_not_ge hx)
    simp [hu, hv, hp]

/-- A continuous weight is controlled on a support ball by the unweighted energy. -/
theorem weightedEnergy_le_mul_energy {w : E → ℝ} (hw : Continuous w)
    {Y : State E ι} (hY : Y.Smooth) {T M : ℝ} (hT : Y.Supported T)
    (hM : ∀ x, ‖x‖ ≤ T → w x ≤ M) : weightedEnergy m w Y ≤ M * energy m Y := by
  have hc := hY.continuousState
  have hq : Continuous (fun x => Y.u x ^ 2 + Y.v x ^ 2 + ∑ j, Y.p j x ^ 2) :=
    ((hc.1.pow 2).add (hc.2.1.pow 2)).add (continuous_finsetSum _ fun j _ => (hc.2.2 j).pow 2)
  have hz : ∀ x, T < ‖x‖ → Y.u x ^ 2 + Y.v x ^ 2 + ∑ j, Y.p j x ^ 2 = 0 := fun x hx => by
    obtain ⟨hu, hv, hp⟩ := hT x hx
    simp [hu, hv, hp]
  rw [energy_eq_weightedEnergy_one m hc hT]
  exact weightedEnergy_le_mul m hT hM (integrable_of_supported m hq hz)
    (integrable_of_supported m (R := T) (hw.mul hq) fun x hx => by simp [hz x hx])

end FiniteIndex

omit [IsFiniteMeasureOnCompacts m] in
/-- **Mesh-uniform forced weighted energy on the actual cells.** For a smooth coefficient `b`
without global bounds and a `C^1` weight with `D_(a_j) w = -b_j w`, one constant works for all
meshes of a fixed horizon:
`sqrt W(cell_k(θ)) <= sqrt W(Y) + C δ`. The leading term is the initial weighted norm with
coefficient one, independent of the horizon; only the remainder depends on `L`. -/
theorem exists_weightedEnergy_cell_bound [m.IsAddHaarMeasure] {d : ℕ} (a : Fin d → E)
    {b : Fin d → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hw0 : ∀ x, 0 ≤ w x) (hwb : ∀ j x, fderiv ℝ w x (a j) = -(b j x * w x))
    {Y : State E (Fin d)} (hY : Y.Smooth) {R : ℝ} (hR : Y.Supported R) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ k : ℕ, k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        √(weightedEnergy m w (cell a b (List.finRange d) δ Y k θ)) ≤
          √(weightedEnergy m w Y) + C * δ := by
  set js := List.finRange d
  obtain ⟨C₀, hC₀, hres⟩ := exists_cell_residual_bound m a js hb hY hR 0 L
  set T := R + (L + 2) * travel a js
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) T).exists_bound_of_continuousOn
    hw.continuous.continuousOn
  have hMw : ∀ x, ‖x‖ ≤ T → w x ≤ max M 0 := fun x hx => by
    have := hM x (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)] at this
    exact this.trans (le_max_left _ _)
  refine ⟨max L 0 * √(max M 0 * C₀), by positivity, ?_⟩
  intro N δ hδ hδ1 hL k hk θ hθ hθδ
  have htr := travel_nonneg a js
  set η := √(max M 0 * C₀) * δ
  have hη : 0 ≤ η := by positivity
  have hη2 : η ^ 2 = max M 0 * C₀ * δ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have he : ∀ j ≤ k, ∀ s ∈ Icc 0 δ, weightedEnergy m w
      (residual a b js (nodes a b js δ Y j) s) ≤ η ^ 2 := by
    intro j hj s hs
    have hjN : j < N := lt_of_le_of_lt hj hk
    have hjN' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
    have hsum : (j : ℝ) * δ + (s + 1) ≤ L + 2 := by nlinarith [hs.2]
    have hsupp := (hR.nodes a b js δ j).residual a b js s
    rw [abs_of_nonneg hδ, abs_of_nonneg hs.1] at hsupp
    have hsuppT := hsupp.mono (show R + j * (δ * travel a js) + (s + 1) * travel a js ≤ T by
      nlinarith [mul_le_mul_of_nonneg_right hsum htr])
    have hsm := (jointSmooth_residual a hb js (hY.nodes a hb js δ j)).slice s
    have h₁ := weightedEnergy_le_mul_energy m hw.continuous hsm hsuppT hMw
    have h₂ := hres N δ hδ hδ1 hL j hjN s hs.1 hs.2
    rw [derivativeEnergy_zero] at h₂
    rw [hη2]
    calc _ ≤ max M 0 * energy m (residual a b js (nodes a b js δ Y j) s) := h₁
      _ ≤ max M 0 * (C₀ * δ ^ 2) := mul_le_mul_of_nonneg_left h₂ (le_max_right _ _)
      _ = _ := by ring
  have h := sqrt_weightedEnergy_cell_le m a hb hw hw0 hwb hY hR hδ hη k he hθ hθδ
  have hkt : (k : ℝ) * δ + θ ≤ max L 0 := by
    have : (k : ℝ) * δ + θ ≤ N * δ := by nlinarith
    exact (this.trans hL).trans (le_max_left _ _)
  calc _ ≤ _ := h
    _ ≤ √(weightedEnergy m w Y) + max L 0 * η := by nlinarith
    _ = _ := by simp only [η]; ring

end Integration
end FunctionalInequalities.Analysis.WaveSplitting
