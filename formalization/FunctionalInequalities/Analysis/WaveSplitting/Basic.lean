import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support

/-!
# Explicit finite wave splitting

Classical scalar/velocity/coordinate-field flows with explicit translation directions.
No L² representative is differentiated. Stability, consistency and the heat-test theorem
are not asserted here.
-/
noncomputable section
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Classical displacement, velocity and vector-field coordinates. -/
structure State (E ι : Type*) where
  u : E → ℝ
  v : E → ℝ
  p : ι → E → ℝ

/-- Spatial smoothness of all components. -/
def State.Smooth (Y : State E ι) : Prop :=
  ContDiff ℝ ∞ Y.u ∧ ContDiff ℝ ∞ Y.v ∧ ∀ j, ContDiff ℝ ∞ (Y.p j)

/-- A common support bound for all components. -/
def State.Supported (Y : State E ι) (R : ℝ) : Prop :=
  ∀ x, R < ‖x‖ → Y.u x = 0 ∧ Y.v x = 0 ∧ ∀ j, Y.p j x = 0

/-- Wave initial data. -/
def initial (h : E → ℝ) : State E ι := ⟨0, h, fun _ => 0⟩

/-- The coordinate pairing `b · p`. -/
def coupling (b : ι → E → ℝ) (Y : State E ι) (x : E) : ℝ :=
  ∑ j, b j x * Y.p j x

/-- The exact zero-order flow, fixing the vector field. -/
def reaction (b : ι → E → ℝ) (t : ℝ) (Y : State E ι) : State E ι where
  u x := Real.cos t * Y.u x + Real.sin t * Y.v x +
    (Real.cos t - 1) * coupling b Y x
  v x := -Real.sin t * Y.u x + Real.cos t * Y.v x - Real.sin t * coupling b Y x
  p := Y.p

/-- Opposite characteristic translations for velocity and coordinate `j`. -/
def transport (a : E) (j : ι) (t : ℝ) (Y : State E ι) : State E ι where
  u := Y.u
  v x := ((Y.v (x + t • a) + Y.p j (x + t • a)) +
    (Y.v (x - t • a) - Y.p j (x - t • a))) / 2
  p i x := if i = j then
    ((Y.v (x + t • a) + Y.p j (x + t • a)) -
      (Y.v (x - t • a) - Y.p j (x - t • a))) / 2 else Y.p i x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι] in
@[simp] theorem reaction_zero (b : ι → E → ℝ) (Y : State E ι) :
    reaction b 0 Y = Y := by
  cases Y
  simp [WaveSplitting.reaction]

omit [Fintype ι] in
@[simp] theorem transport_zero (a : E) (j : ι) (Y : State E ι) :
    transport a j 0 Y = Y := by
  cases Y with
  | mk u v p =>
    unfold transport
    congr 1
    · funext x; simp
    · funext i x; by_cases hi : i = j <;> simp [hi]

omit [Fintype ι] in
/-- The two characteristic fields translate in opposite directions. -/
theorem transport_characteristics (a : E) (j : ι) (t : ℝ) (Y : State E ι) (x : E) :
    (transport a j t Y).v x + (transport a j t Y).p j x =
      Y.v (x + t • a) + Y.p j (x + t • a) ∧
    (transport a j t Y).v x - (transport a j t Y).p j x =
      Y.v (x - t • a) - Y.p j (x - t • a) := by
  simp only [WaveSplitting.transport, ↓reduceIte]
  constructor <;> ring

omit [Fintype ι] [DecidableEq ι] in
theorem smooth_initial {h : E → ℝ} (hh : ContDiff ℝ ∞ h) :
    (initial h : State E ι).Smooth :=
  ⟨contDiff_const, hh, fun _ => contDiff_const⟩

omit [DecidableEq ι] in
theorem State.Smooth.reaction {Y : State E ι} (hY : Y.Smooth)
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) (t : ℝ) :
    (reaction b t Y).Smooth := by
  have hc : ContDiff ℝ ∞ (coupling b Y) :=
    ContDiff.sum fun j _ => (hb j).mul (hY.2.2 j)
  exact ⟨((contDiff_const.mul hY.1).add (contDiff_const.mul hY.2.1)).add
    (contDiff_const.mul hc),
    ((contDiff_const.mul hY.1).add (contDiff_const.mul hY.2.1)).sub
    (contDiff_const.mul hc), hY.2.2⟩

omit [Fintype ι] in
theorem State.Smooth.transport {Y : State E ι} (hY : Y.Smooth)
    (a : E) (j : ι) (t : ℝ) : (transport a j t Y).Smooth := by
  have hp := contDiff_id.add (contDiff_const : ContDiff ℝ ∞ (fun _ : E => t • a))
  have hm := contDiff_id.sub (contDiff_const : ContDiff ℝ ∞ (fun _ : E => t • a))
  refine ⟨hY.1, ?_, fun i => ?_⟩
  · exact (((hY.2.1.comp hp).add ((hY.2.2 j).comp hp)).add
      ((hY.2.1.comp hm).sub ((hY.2.2 j).comp hm))).div_const 2
  · by_cases hi : i = j
    · simpa only [WaveSplitting.transport, hi, ↓reduceIte, Function.comp_def, id_eq] using
        (((hY.2.1.comp hp).add ((hY.2.2 j).comp hp)).sub
          ((hY.2.1.comp hm).sub ((hY.2.2 j).comp hm))).div_const 2
    · simpa only [WaveSplitting.transport, hi, ↓reduceIte, Function.comp_def, id_eq] using hY.2.2 i

omit [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι] in
theorem State.Supported.mono {Y : State E ι} {R S : ℝ}
    (hY : Y.Supported R) (hRS : R ≤ S) : Y.Supported S :=
  fun x hx => hY x (lt_of_le_of_lt hRS hx)

omit [NormedSpace ℝ E] [DecidableEq ι] in
theorem State.Supported.reaction {Y : State E ι} {R : ℝ} (hY : Y.Supported R)
    (b : ι → E → ℝ) (t : ℝ) : (reaction b t Y).Supported R := by
  intro x hx
  obtain ⟨hu, hv, hp⟩ := hY x hx
  simp [WaveSplitting.reaction, coupling, hu, hv, hp]

private theorem norm_shift_gt {R : ℝ} (x a : E) (t : ℝ)
    (hx : R + |t| * ‖a‖ < ‖x‖) : R < ‖x + t • a‖ ∧ R < ‖x - t • a‖ := by
  have hp : ‖x‖ ≤ ‖x + t • a‖ + |t| * ‖a‖ := by
    simpa [norm_smul, Real.norm_eq_abs] using norm_sub_le (x + t • a) (t • a)
  have hm : ‖x‖ ≤ ‖x - t • a‖ + |t| * ‖a‖ := by
    simpa [norm_smul, Real.norm_eq_abs] using norm_add_le (x - t • a) (t • a)
  constructor <;> linarith

omit [Fintype ι] in
theorem State.Supported.transport {Y : State E ι} {R : ℝ} (hY : Y.Supported R)
    (a : E) (j : ι) (t : ℝ) : (transport a j t Y).Supported (R + |t| * ‖a‖) := by
  intro x hx
  have hx0 : R < ‖x‖ := lt_of_le_of_lt (le_add_of_nonneg_right
    (mul_nonneg (abs_nonneg t) (norm_nonneg a))) hx
  obtain ⟨hu, hv, hp⟩ := hY x hx0
  obtain ⟨hplus, hminus⟩ := norm_shift_gt x a t hx
  obtain ⟨_, hvp, hpp⟩ := hY _ hplus
  obtain ⟨_, hvm, hpm⟩ := hY _ hminus
  simp [WaveSplitting.transport, hu, hvp, hpp, hvm, hpm, hp]

/-- Coordinate flows in the supplied order; the empty list is allowed. -/
def sweep (a : ι → E) (t : ℝ) : List ι → State E ι → State E ι
  | [], Y => Y
  | j :: js, Y => sweep a t js (transport (a j) j t Y)

/-- Total direction length for a conservative support estimate. -/
def travel (a : ι → E) (js : List ι) : ℝ := (js.map fun j => ‖a j‖).sum

omit [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι] in
theorem travel_nonneg (a : ι → E) (js : List ι) : 0 ≤ travel a js := by
  induction js with
  | nil => simp [travel]
  | cons j js ih => simpa [travel] using add_nonneg (norm_nonneg (a j)) ih

omit [Fintype ι] in
@[simp] theorem sweep_zero (a : ι → E) (js : List ι) (Y : State E ι) :
    sweep a 0 js Y = Y := by
  induction js generalizing Y with
  | nil => rfl
  | cons j js ih => simp [WaveSplitting.sweep, ih]

omit [Fintype ι] in
theorem State.Smooth.sweep {Y : State E ι} (hY : Y.Smooth)
    (a : ι → E) (t : ℝ) (js : List ι) : (sweep a t js Y).Smooth := by
  induction js generalizing Y with
  | nil => exact hY
  | cons j js ih => exact ih (hY.transport (a j) j t)

omit [Fintype ι] in
theorem State.Supported.sweep {Y : State E ι} {R : ℝ} (hY : Y.Supported R)
    (a : ι → E) (t : ℝ) (js : List ι) :
    (sweep a t js Y).Supported (R + |t| * travel a js) := by
  induction js generalizing Y R with
  | nil => simpa [WaveSplitting.sweep, travel] using hY
  | cons j js ih =>
    have h := ih (hY.transport (a j) j t)
    convert h using 1 <;> simp [WaveSplitting.sweep, travel]; ring

/-- A coordinate sweep followed by the zero-order flow. -/
def step (a : ι → E) (b : ι → E → ℝ) (js : List ι) (t : ℝ) (Y : State E ι) :
    State E ι := reaction b t (sweep a t js Y)

@[simp] theorem step_zero (a : ι → E) (b : ι → E → ℝ) (js : List ι) (Y : State E ι) :
    step a b js 0 Y = Y := by simp [step]

/-- Finite iteration at the grid nodes. -/
def nodes (a : ι → E) (b : ι → E → ℝ) (js : List ι) (δ : ℝ)
    (Y : State E ι) : ℕ → State E ι
  | 0 => Y
  | k + 1 => step a b js δ (nodes a b js δ Y k)

/-- Interpolation on a cell, before choosing a global grid-index convention. -/
def cell (a : ι → E) (b : ι → E → ℝ) (js : List ι) (δ : ℝ)
    (Y : State E ι) (k : ℕ) (θ : ℝ) : State E ι :=
  step a b js θ (nodes a b js δ Y k)

theorem cell_endpoints (a : ι → E) (b : ι → E → ℝ) (js : List ι) (δ : ℝ)
    (Y : State E ι) (k : ℕ) : cell a b js δ Y k δ = cell a b js δ Y (k + 1) 0 := by
  simp [cell, nodes]

theorem State.Smooth.nodes {Y : State E ι} (hY : Y.Smooth)
    (a : ι → E) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    (js : List ι) (δ : ℝ) (k : ℕ) : (nodes a b js δ Y k).Smooth := by
  induction k with
  | zero => exact hY
  | succ k ih => exact (ih.sweep a δ js).reaction hb δ

theorem State.Smooth.cell {Y : State E ι} (hY : Y.Smooth)
    (a : ι → E) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    (js : List ι) (δ : ℝ) (k : ℕ) (θ : ℝ) : (cell a b js δ Y k θ).Smooth :=
  ((hY.nodes a hb js δ k).sweep a θ js).reaction hb θ

theorem State.Supported.nodes {Y : State E ι} {R : ℝ} (hY : Y.Supported R)
    (a : ι → E) (b : ι → E → ℝ) (js : List ι) (δ : ℝ) (k : ℕ) :
    (nodes a b js δ Y k).Supported (R + k * (|δ| * travel a js)) := by
  induction k with
  | zero => simpa [WaveSplitting.nodes] using hY
  | succ k ih =>
    have h := (ih.sweep a δ js).reaction b δ
    convert h using 1 <;> simp [WaveSplitting.nodes, step, Nat.cast_add, Nat.cast_one]; ring

/-- All cells on a finite horizon share one support ball. This is not a sharp speed bound. -/
theorem State.Supported.cell {Y : State E ι} {R : ℝ} (hY : Y.Supported R)
    (a : ι → E) (b : ι → E → ℝ) (js : List ι) {δ θ : ℝ} (hδ : 0 ≤ δ)
    (hθ : 0 ≤ θ) (hθδ : θ ≤ δ) {k N : ℕ} (hk : k < N) :
    (cell a b js δ Y k θ).Supported (R + N * (δ * travel a js)) := by
  apply ((hY.nodes a b js δ k).sweep a θ js).reaction b θ |>.mono
  rw [abs_of_nonneg hδ, abs_of_nonneg hθ]
  have ht := travel_nonneg a js
  have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  nlinarith [mul_le_mul_of_nonneg_right hk' (mul_nonneg hδ ht),
    mul_le_mul_of_nonneg_right hθδ ht]

omit [Fintype ι] [DecidableEq ι] in
/-- In finite dimension the common support ball is compact. -/
theorem State.Supported.hasCompactSupport [FiniteDimensional ℝ E]
    {Y : State E ι} {R : ℝ} (hY : Y.Supported R) :
    HasCompactSupport Y.u ∧ HasCompactSupport Y.v ∧ ∀ j, HasCompactSupport (Y.p j) := by
  have hz (x : E) (hx : x ∉ Metric.closedBall (0 : E) R) :=
    hY x (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)
  exact ⟨HasCompactSupport.intro (isCompact_closedBall 0 R) (fun x hx => (hz x hx).1),
    HasCompactSupport.intro (isCompact_closedBall 0 R) (fun x hx => (hz x hx).2.1),
    fun j => HasCompactSupport.intro (isCompact_closedBall 0 R) (fun x hx => (hz x hx).2.2 j)⟩


/-- Joint smoothness in time and space, before gluing different cells. -/
def JointSmooth (Y : ℝ → State E ι) : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × E => (Y z.1).u z.2) ∧
  ContDiff ℝ ∞ (fun z : ℝ × E => (Y z.1).v z.2) ∧
  ∀ j, ContDiff ℝ ∞ (fun z : ℝ × E => (Y z.1).p j z.2)

omit [Fintype ι] [DecidableEq ι] in
theorem State.Smooth.joint_const {Y : State E ι} (hY : Y.Smooth) :
    JointSmooth (fun _ : ℝ => Y) :=
  ⟨hY.1.comp contDiff_snd, hY.2.1.comp contDiff_snd,
    fun j => (hY.2.2 j).comp contDiff_snd⟩

omit [DecidableEq ι] in
theorem JointSmooth.reaction {Y : ℝ → State E ι} (hY : JointSmooth Y)
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) :
    JointSmooth (fun t => reaction b t (Y t)) := by
  have hc : ContDiff ℝ ∞ (fun z : ℝ × E => coupling b (Y z.1) z.2) :=
    ContDiff.sum fun j _ => ((hb j).comp contDiff_snd).mul (hY.2.2 j)
  have hs : ContDiff ℝ ∞ (fun z : ℝ × E => Real.sin z.1) :=
    Real.contDiff_sin.comp contDiff_fst
  have hcos : ContDiff ℝ ∞ (fun z : ℝ × E => Real.cos z.1) :=
    Real.contDiff_cos.comp contDiff_fst
  exact ⟨((hcos.mul hY.1).add (hs.mul hY.2.1)).add
    ((hcos.sub contDiff_const).mul hc),
    ((hs.neg.mul hY.1).add (hcos.mul hY.2.1)).sub (hs.mul hc), hY.2.2⟩

omit [Fintype ι] in
theorem JointSmooth.transport {Y : ℝ → State E ι} (hY : JointSmooth Y)
    (a : E) (j : ι) : JointSmooth (fun t => transport a j t (Y t)) := by
  have hp : ContDiff ℝ ∞ (fun z : ℝ × E => (z.1, z.2 + z.1 • a)) :=
    contDiff_fst.prodMk (contDiff_snd.add (contDiff_fst.smul contDiff_const))
  have hm : ContDiff ℝ ∞ (fun z : ℝ × E => (z.1, z.2 - z.1 • a)) :=
    contDiff_fst.prodMk (contDiff_snd.sub (contDiff_fst.smul contDiff_const))
  refine ⟨hY.1, ?_, fun i => ?_⟩
  · exact (((hY.2.1.comp hp).add ((hY.2.2 j).comp hp)).add
      ((hY.2.1.comp hm).sub ((hY.2.2 j).comp hm))).div_const 2
  · by_cases hi : i = j
    · simpa only [WaveSplitting.transport, hi, ↓reduceIte, Function.comp_def] using
        (((hY.2.1.comp hp).add ((hY.2.2 j).comp hp)).sub
          ((hY.2.1.comp hm).sub ((hY.2.2 j).comp hm))).div_const 2
    · simpa only [WaveSplitting.transport, hi, ↓reduceIte] using hY.2.2 i

omit [Fintype ι] in
theorem JointSmooth.sweep {Y : ℝ → State E ι} (hY : JointSmooth Y)
    (a : ι → E) (js : List ι) : JointSmooth (fun t => sweep a t js (Y t)) := by
  induction js generalizing Y with
  | nil => exact hY
  | cons j js ih => exact ih (hY.transport (a j) j)

/-- Each entire closed cell extends to a jointly smooth function of time and space. -/
theorem State.Smooth.joint_cell {Y : State E ι} (hY : Y.Smooth)
    (a : ι → E) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    (js : List ι) (δ : ℝ) (k : ℕ) : JointSmooth (WaveSplitting.cell a b js δ Y k) :=
  (((hY.nodes a hb js δ k).joint_const).sweep a js).reaction hb

omit [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι] in
/-- The initial support bound is obtained from compact support, not assumed as extra data. -/
theorem supported_initial {h : E → ℝ} (hh : HasCompactSupport h) :
    ∃ R > 0, (initial h : State E ι).Supported R := by
  obtain ⟨R, hR, hzero⟩ := hh.exists_pos_le_norm
  exact ⟨R, hR, fun x hx => ⟨rfl, hzero x hx.le, fun _ => rfl⟩⟩

/-- Arbitrary compact smooth initial data give actual jointly smooth cell functions sharing
one compact spatial support for every finite number of steps. -/
theorem initial_cells [FiniteDimensional ℝ E]
    (a : ι → E) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    (js : List ι) {h : E → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    (∀ k, JointSmooth (cell a b js δ (initial h) k)) ∧
    ∃ K : Set E, IsCompact K ∧ ∀ k < N, ∀ θ ∈ Set.Icc 0 δ, ∀ x ∉ K,
      (cell a b js δ (initial h) k θ).u x = 0 ∧
      (cell a b js δ (initial h) k θ).v x = 0 ∧
      ∀ j, (cell a b js δ (initial h) k θ).p j x = 0 := by
  obtain ⟨R, _, hR⟩ := supported_initial (ι := ι) hc
  refine ⟨fun k => (smooth_initial hh).joint_cell a hb js δ k,
    Metric.closedBall 0 (R + N * (δ * travel a js)), isCompact_closedBall _ _, ?_⟩
  intro k hk θ hθ x hx
  exact (hR.cell a b js hδ hθ.1 hθ.2 hk) x
    (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι] in
/-- The displacement derivative is exactly the velocity of the zero-order flow. -/
theorem reaction_hasDerivAt_u (b : ι → E → ℝ) (Y : State E ι) (x : E) (t : ℝ) :
    HasDerivAt (fun s => (reaction b s Y).u x) (reaction b t Y |>.v x) t := by
  apply HasDerivAt.congr_deriv
    ((((Real.hasDerivAt_cos t).mul_const (Y.u x)).add
      ((Real.hasDerivAt_sin t).mul_const (Y.v x))).add
      (((Real.hasDerivAt_cos t).sub_const 1).mul_const (coupling b Y x)))
  dsimp only [reaction]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι] in
/-- The velocity derivative includes the original coefficient pairing with its correct sign. -/
theorem reaction_hasDerivAt_v (b : ι → E → ℝ) (Y : State E ι) (x : E) (t : ℝ) :
    HasDerivAt (fun s => (reaction b s Y).v x)
      (-(reaction b t Y).u x - coupling b Y x) t := by
  apply HasDerivAt.congr_deriv
    ((((Real.hasDerivAt_sin t).neg.mul_const (Y.u x)).add
      ((Real.hasDerivAt_cos t).mul_const (Y.v x))).sub
      ((Real.hasDerivAt_sin t).mul_const (coupling b Y x)))
  dsimp only [reaction]
  ring



omit [Fintype ι] in
/-- Pointwise characteristic energy identity, before Haar integration. -/
theorem transport_energy (a : E) (j : ι) (t : ℝ) (Y : State E ι) (x : E) :
    (transport a j t Y).v x ^ 2 + (transport a j t Y).p j x ^ 2 =
      ((Y.v (x + t • a) + Y.p j (x + t • a)) ^ 2 +
        (Y.v (x - t • a) - Y.p j (x - t • a)) ^ 2) / 2 := by
  simp only [transport, ↓reduceIte]
  ring

omit [Fintype ι] in
/-- The infinitesimal velocity equation of the coordinate flow at time zero. -/
theorem transport_hasDerivAt_v_zero (a : E) (j : ι) (Y : State E ι) (x : E)
    (hv : DifferentiableAt ℝ Y.v x) (hp : DifferentiableAt ℝ (Y.p j) x) :
    HasDerivAt (fun t => (transport a j t Y).v x) (fderiv ℝ (Y.p j) x a) 0 := by
  have hplus : HasDerivAt (fun t : ℝ => x + t • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x
  have hminus : HasDerivAt (fun t : ℝ => x - t • a) (-a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_sub x
  have hvp := (show HasFDerivAt Y.v (fderiv ℝ Y.v x) (x + (0 : ℝ) • a) by
    simpa using hv.hasFDerivAt).comp_hasDerivAt 0 hplus
  have hpp := (show HasFDerivAt (Y.p j) (fderiv ℝ (Y.p j) x) (x + (0 : ℝ) • a) by
    simpa using hp.hasFDerivAt).comp_hasDerivAt 0 hplus
  have hvm := (show HasFDerivAt Y.v (fderiv ℝ Y.v x) (x - (0 : ℝ) • a) by
    simpa using hv.hasFDerivAt).comp_hasDerivAt 0 hminus
  have hpm := (show HasFDerivAt (Y.p j) (fderiv ℝ (Y.p j) x) (x - (0 : ℝ) • a) by
    simpa using hp.hasFDerivAt).comp_hasDerivAt 0 hminus
  apply HasDerivAt.congr_deriv (((hvp.add hpp).add (hvm.sub hpm)).div_const 2)
  simp only [map_neg]
  ring

omit [Fintype ι] in
/-- The infinitesimal field equation of the coordinate flow at time zero. -/
theorem transport_hasDerivAt_p_zero (a : E) (j : ι) (Y : State E ι) (x : E)
    (hv : DifferentiableAt ℝ Y.v x) (hp : DifferentiableAt ℝ (Y.p j) x) :
    HasDerivAt (fun t => (transport a j t Y).p j x) (fderiv ℝ Y.v x a) 0 := by
  have hplus : HasDerivAt (fun t : ℝ => x + t • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x
  have hminus : HasDerivAt (fun t : ℝ => x - t • a) (-a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_sub x
  have hvp := (show HasFDerivAt Y.v (fderiv ℝ Y.v x) (x + (0 : ℝ) • a) by
    simpa using hv.hasFDerivAt).comp_hasDerivAt 0 hplus
  have hpp := (show HasFDerivAt (Y.p j) (fderiv ℝ (Y.p j) x) (x + (0 : ℝ) • a) by
    simpa using hp.hasFDerivAt).comp_hasDerivAt 0 hplus
  have hvm := (show HasFDerivAt Y.v (fderiv ℝ Y.v x) (x - (0 : ℝ) • a) by
    simpa using hv.hasFDerivAt).comp_hasDerivAt 0 hminus
  have hpm := (show HasFDerivAt (Y.p j) (fderiv ℝ (Y.p j) x) (x - (0 : ℝ) • a) by
    simpa using hp.hasFDerivAt).comp_hasDerivAt 0 hminus
  simp only [transport, ↓reduceIte]
  apply HasDerivAt.congr_deriv (((hvp.add hpp).sub (hvm.sub hpm)).div_const 2)
  simp only [map_neg]
  ring

end FunctionalInequalities.Analysis.WaveSplitting
