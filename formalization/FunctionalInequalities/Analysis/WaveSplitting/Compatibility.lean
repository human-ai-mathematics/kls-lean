import FunctionalInequalities.Analysis.WaveSplitting.WeightedEnergy

/-!
# Gradient compatibility defect of the actual splitting scheme

The split scheme does not keep `p = grad u`. The defect `d_j = p_j - D_(a_j) u` is tracked
explicitly: along an actual step its temporal derivative is exactly the defect of the actual
residual, `e_(p_j) - D_(a_j) e_u`. Hence it costs one derivative of the residual. Together with
the forced weighted energy this controls the weighted coordinate form energy of `u` by the
initial weighted norm plus a mesh-dependent remainder.
-/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*}

/-- The gradient-compatibility defect `p_j - D_(a_j) u`, stored in the coordinate components;
the displacement and velocity components are zero. -/
def compatibilityDefect (a : ι → E) (Y : State E ι) : State E ι :=
  ⟨0, 0, fun j x => Y.p j x - fderiv ℝ Y.u x (a j)⟩

/-- The coordinate form state `(u, 0, D_(a_j) u)`. For orthonormal directions its weighted
energy is the weighted form energy of `u`; that identification is not used here. -/
def formState (a : ι → E) (Y : State E ι) : State E ι :=
  ⟨Y.u, 0, fun j x => fderiv ℝ Y.u x (a j)⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem subState_zeroState (Y : State E ι) : subState Y zeroState = Y := by
  apply State.ext <;> funext <;> simp [subState, zeroState]

theorem State.Smooth.compatibilityDefect {Y : State E ι} (hY : Y.Smooth) (a : ι → E) :
    (WaveSplitting.compatibilityDefect a Y).Smooth :=
  ⟨contDiff_const, contDiff_const, fun j =>
    (hY.2.2 j).sub ((hY.1.fderiv_right (by simp)).clm_apply contDiff_const)⟩

theorem State.Supported.compatibilityDefect {Y : State E ι} {R : ℝ} (hY : Y.Supported R)
    (a : ι → E) : (WaveSplitting.compatibilityDefect a Y).Supported R := fun x hx =>
  ⟨rfl, rfl, fun j => by
    simp [WaveSplitting.compatibilityDefect, (hY x hx).2.2 j,
      fderiv_eq_zero_of_supported (fun y hy => (hY y hy).1) hx]⟩

theorem State.Smooth.formState {Y : State E ι} (hY : Y.Smooth) (a : ι → E) :
    (WaveSplitting.formState a Y).Smooth :=
  ⟨hY.1, contDiff_const, fun _ => (hY.1.fderiv_right (by simp)).clm_apply contDiff_const⟩

theorem JointSmooth.compatibilityDefect {Z : ℝ → State E ι} (hZ : JointSmooth Z)
    (a : ι → E) : JointSmooth (fun r => WaveSplitting.compatibilityDefect a (Z r)) :=
  ⟨contDiff_const, contDiff_const, fun j => (hZ.2.2 j).sub (contDiff_fderiv_slice hZ.1 (a j))⟩

/-- The time derivative of the defect is the defect of the time derivative. -/
theorem JointSmooth.hasTimeDerivative_compatibilityDefect {Z : ℝ → State E ι}
    (hZ : JointSmooth Z) (a : ι → E) (s : ℝ) :
    HasTimeDerivative (fun r => WaveSplitting.compatibilityDefect a (Z r))
      (WaveSplitting.compatibilityDefect a (WaveSplitting.timeDerivative Z s)) s := by
  refine ⟨fun x => hasDerivAt_const s 0, fun x => hasDerivAt_const s 0, fun j x => ?_⟩
  have hp : HasDerivAt (fun r => (Z r).p j x) (deriv (fun r => (Z r).p j x) s) s :=
    ((((hZ.2.2 j).differentiable (by simp)).comp
      (differentiable_id.prodMk (differentiable_const x))) s).hasDerivAt
  exact hp.sub (hasDerivAt_fderiv_slice (F := fun z : ℝ × E => (Z z.1).u z.2) hZ.1 s x (a j))

private theorem compatibilityDefect_addState (a : ι → E) {X Z : State E ι}
    (hX : X.Smooth) (hZ : Z.Smooth) :
    compatibilityDefect a (addState X Z) =
      addState (compatibilityDefect a X) (compatibilityDefect a Z) := by
  apply State.ext
  · funext x; simp [compatibilityDefect, addState]
  · funext x; simp [compatibilityDefect, addState]
  · funext j x
    simp only [compatibilityDefect, addState]
    rw [fderiv_fun_add ((hX.1.differentiable (by simp)) x) ((hZ.1.differentiable (by simp)) x)]
    simp only [FunLike.coe_add, Pi.add_apply]
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem addState_zeroState (Y : State E ι) : addState zeroState Y = Y := zero_addState Y

/-- The wave generator itself is compatible: its defect vanishes identically. -/
theorem compatibilityDefect_waveGenerator [Fintype ι] (a : ι → E) (b : ι → E → ℝ)
    (Y : State E ι) : compatibilityDefect a (waveGenerator a b Y) = zeroState := by
  apply State.ext
  · rfl
  · rfl
  · funext j x
    simp [compatibilityDefect, waveGenerator, zeroState]

/-- Along the actual complete step, the defect evolves exactly by the defect of the actual
residual, `e_(p_j) - D_(a_j) e_u`. -/
theorem compatibilityDefect_timeDerivative_step {d : ℕ} (a : Fin d → E) {b : Fin d → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E (Fin d)} (hY : Y.Smooth) (s : ℝ) :
    compatibilityDefect a (timeDerivative (fun r => step a b (List.finRange d) r Y) s) =
      compatibilityDefect a (residual a b (List.finRange d) Y s) := by
  have hYs : (step a b (List.finRange d) s Y).Smooth := (hY.sweep a s _).reaction hb s
  have hG : (waveGenerator a b (step a b (List.finRange d) s Y)).Smooth := by
    rw [← splitGenerator_finRange]
    exact (hYs.sweepGenerator a _).addState (hYs.reactionGenerator hb)
  have he : (residual a b (List.finRange d) Y s).Smooth :=
    (jointSmooth_residual a hb _ hY).slice s
  have ht : timeDerivative (fun r => step a b (List.finRange d) r Y) s =
      addState (waveGenerator a b (step a b (List.finRange d) s Y))
        (residual a b (List.finRange d) Y s) := by
    rw [← splitGenerator_finRange, residual_eq_subState]
    apply State.ext
    · funext x; simp only [addState, subState]; ring
    · funext x; simp only [addState, subState]; ring
    · funext j x; simp only [addState, subState]; ring
  rw [ht, compatibilityDefect_addState a hG he, compatibilityDefect_waveGenerator,
    addState_zeroState]

section Integration
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [IsFiniteMeasureOnCompacts m]

/-- Explicit constant for the one-order cost of the defect. -/
def defectConstant [Fintype ι] (k : ℕ) : ℝ :=
  2 + 2 * Fintype.card ι * (jetCount (ι := ι) k : ℝ)

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts m] in
theorem defectConstant_nonneg [Fintype ι] (k : ℕ) : 0 ≤ defectConstant (ι := ι) k := by
  unfold defectConstant
  positivity

/-- The defect of a state costs one derivative order of that state. -/
theorem derivativeEnergy_compatibilityDefect_le [Fintype ι] (a : ι → E) (k : ℕ)
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m a k (compatibilityDefect a Y) ≤
      defectConstant (ι := ι) k * derivativeEnergy m a (k + 1) Y := by
  have hdc : (compatibilityDefect a Y).CompactSupport :=
    ⟨HasCompactSupport.zero, HasCompactSupport.zero, fun j =>
      (hc.2.2 j).sub ((hc.1.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L (a j)) (by simp))⟩
  rw [derivativeEnergy_eq_scalarEnergy m a k (hY.compatibilityDefect a) hdc]
  have hz : scalarEnergy m a k (0 : E → ℝ) = 0 := scalarEnergy_zero m a k
  have hj (j : ι) : scalarEnergy m a k (fun x => Y.p j x - fderiv ℝ Y.u x (a j)) ≤
      2 * (scalarEnergy m a k (Y.p j) +
        (jetCount (ι := ι) k : ℝ) * scalarEnergy m a (k + 1) Y.u) := by
    have h₁ := scalarEnergy_sub_le m a k (hY.2.2 j)
      ((hY.1.fderiv_right (by simp)).clm_apply contDiff_const) (hc.2.2 j)
      ((hc.1.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L (a j)) (by simp))
    have h₂ := scalarEnergy_coordinate_le m a k j hY.1 hc.1
    linarith
  have hsum : ∑ j, scalarEnergy m a k (fun x => Y.p j x - fderiv ℝ Y.u x (a j)) ≤
      2 * ∑ j, scalarEnergy m a k (Y.p j) +
        2 * (Fintype.card ι * (jetCount (ι := ι) k : ℝ)) * scalarEnergy m a (k + 1) Y.u := by
    calc _ ≤ ∑ j, 2 * (scalarEnergy m a k (Y.p j) +
          (jetCount (ι := ι) k : ℝ) * scalarEnergy m a (k + 1) Y.u) :=
        Finset.sum_le_sum fun j _ => hj j
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        ring
  have hEk := derivativeEnergy_mono m a (Nat.le_succ k) Y
  rw [derivativeEnergy_eq_scalarEnergy m a k hY hc,
    derivativeEnergy_eq_scalarEnergy m a (k + 1) hY hc] at hEk
  rw [derivativeEnergy_eq_scalarEnergy m a (k + 1) hY hc]
  have hu := scalarEnergy_nonneg m a k Y.u
  have hv := scalarEnergy_nonneg m a k Y.v
  have hu₁ := scalarEnergy_nonneg m a (k + 1) Y.u
  have hv₁ := scalarEnergy_nonneg m a (k + 1) Y.v
  have hp₁ : 0 ≤ ∑ j, scalarEnergy m a (k + 1) (Y.p j) :=
    Finset.sum_nonneg fun j _ => scalarEnergy_nonneg m a (k + 1) (Y.p j)
  have hq : (0 : ℝ) ≤ Fintype.card ι * (jetCount (ι := ι) k : ℝ) := by positivity
  change scalarEnergy m a k (0 : E → ℝ) + scalarEnergy m a k (0 : E → ℝ) +
    ∑ j, scalarEnergy m a k (fun x => Y.p j x - fderiv ℝ Y.u x (a j)) ≤ _
  rw [hz]
  unfold defectConstant
  nlinarith [mul_le_mul_of_nonneg_left hu₁ hq, mul_le_mul_of_nonneg_left
    (show scalarEnergy m a (k + 1) Y.u ≤ scalarEnergy m a (k + 1) Y.u +
      scalarEnergy m a (k + 1) Y.v + ∑ j, scalarEnergy m a (k + 1) (Y.p j) by linarith) hq]

variable [FiniteDimensional ℝ E]

/-- **Defect growth on one actual step.** If the residuals on `[0,θ]` have `E_(k+1)` at most
`M`, the square root of `E_k` of the defect grows by at most `θ sqrt(defectConstant k M)`. -/
theorem sqrt_derivativeEnergy_defect_step_le {d : ℕ} (a : Fin d → E) {b : Fin d → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E (Fin d)} (hY : Y.Smooth) {R : ℝ}
    (hR : Y.Supported R) (k : ℕ) {θ M : ℝ} (hθ : 0 ≤ θ)
    (hM : ∀ s ∈ Icc 0 θ,
      derivativeEnergy m a (k + 1) (residual a b (List.finRange d) Y s) ≤ M) :
    √(derivativeEnergy m a k (compatibilityDefect a (step a b (List.finRange d) θ Y))) ≤
      √(derivativeEnergy m a k (compatibilityDefect a Y)) +
        θ * √(defectConstant (ι := Fin d) k * M) := by
  set js := List.finRange d
  have htr := travel_nonneg a js
  have hZ : JointSmooth (fun s => step a b js s Y) := (hY.joint_const.sweep a js).reaction hb
  have hdY := hY.compatibilityDefect a
  have hg : JointSmooth (fun s => subState (compatibilityDefect a (step a b js s Y))
      (compatibilityDefect a Y)) := (hZ.compatibilityDefect a).subState hdY.joint_const
  have hsuppθ : ∀ s ∈ Icc 0 θ, (step a b js s Y).Supported (R + θ * travel a js) :=
    fun s hs => ((hR.sweep a s js).reaction b s).mono (by
      rw [abs_of_nonneg hs.1]; nlinarith [mul_le_mul_of_nonneg_right hs.2 htr])
  have hRθ : R ≤ R + θ * travel a js := by nlinarith
  have hderiv (s : ℝ) : timeDerivative (fun s => subState (compatibilityDefect a
      (step a b js s Y)) (compatibilityDefect a Y)) s =
        compatibilityDefect a (residual a b js Y s) := by
    have h := (hZ.hasTimeDerivative_compatibilityDefect a s).subState
      (hasTimeDerivative_const (compatibilityDefect a Y) s)
    rw [h.timeDerivative_eq, subState_zeroState, compatibilityDefect_timeDerivative_step a hb hY]
  have htime := derivativeEnergy_le_of_timeDerivative m a k hg (by simp) (R := R + θ * travel a js)
    (M := defectConstant (ι := Fin d) k * M) hθ
    (fun s hs => ((hsuppθ s hs).compatibilityDefect a).subState ((hR.compatibilityDefect a).mono hRθ))
    (fun s hs => by
      rw [hderiv s]
      have hes := (jointSmooth_residual a hb js hY).slice s
      have hec : (residual a b js Y s).CompactSupport := (hR.residual a b js s).hasCompactSupport
      exact (derivativeEnergy_compatibilityDefect_le m a k hes hec).trans
        (mul_le_mul_of_nonneg_left (hM s hs) (defectConstant_nonneg k)))
  have hid : compatibilityDefect a (step a b js θ Y) = addState (compatibilityDefect a Y)
      (subState (compatibilityDefect a (step a b js θ Y)) (compatibilityDefect a Y)) := by
    apply State.ext
    · funext x; simp [compatibilityDefect, addState, subState]
    · funext x; simp [compatibilityDefect, addState, subState]
    · funext j x; simp only [compatibilityDefect, addState, subState]; ring
  have hstep : (step a b js θ Y).Smooth := (hY.sweep a θ js).reaction hb θ
  have hmin := derivativeEnergy_addState_le_sq m a k hdY
    ((hstep.compatibilityDefect a).subState hdY) ((hR.compatibilityDefect a).mono hRθ)
    (((hsuppθ θ ⟨hθ, le_rfl⟩).compatibilityDefect a).subState
      ((hR.compatibilityDefect a).mono hRθ))
  rw [← hid] at hmin
  have hE₀ := derivativeEnergy_nonneg m a k (compatibilityDefect a Y)
  have hE₁ := derivativeEnergy_nonneg m a k
    (subState (compatibilityDefect a (step a b js θ Y)) (compatibilityDefect a Y))
  have hs₁ : √(derivativeEnergy m a k
      (subState (compatibilityDefect a (step a b js θ Y)) (compatibilityDefect a Y))) ≤
        θ * √(defectConstant (ι := Fin d) k * M) := by
    calc _ ≤ √(θ ^ 2 * (defectConstant (ι := Fin d) k * M)) := Real.sqrt_le_sqrt htime
      _ = θ * √(defectConstant (ι := Fin d) k * M) := by
        rw [Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ]
  have hsq := Real.sqrt_le_sqrt hmin
  rw [Real.sqrt_sq (by positivity)] at hsq
  linarith

/-- Defect growth at the actual grid nodes. -/
theorem sqrt_derivativeEnergy_defect_nodes_le {d : ℕ} (a : Fin d → E) {b : Fin d → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E (Fin d)} (hY : Y.Smooth) {R : ℝ}
    (hR : Y.Supported R) (k : ℕ) {δ M : ℝ} (hδ : 0 ≤ δ) (n : ℕ)
    (hM : ∀ j < n, ∀ s ∈ Icc 0 δ, derivativeEnergy m a (k + 1)
      (residual a b (List.finRange d) (nodes a b (List.finRange d) δ Y j) s) ≤ M) :
    √(derivativeEnergy m a k (compatibilityDefect a (nodes a b (List.finRange d) δ Y n))) ≤
      √(derivativeEnergy m a k (compatibilityDefect a Y)) +
        n * δ * √(defectConstant (ι := Fin d) k * M) := by
  induction n with
  | zero => simp [nodes]
  | succ n ih =>
    have h := sqrt_derivativeEnergy_defect_step_le m a hb (hY.nodes a hb _ δ n)
      (hR.nodes a b _ δ n) k hδ (hM n (Nat.lt_succ_self n))
    have ih' := ih fun j hj => hM j (Nat.lt_succ_of_lt hj)
    change √(derivativeEnergy m a k (compatibilityDefect a
      (step a b _ δ (nodes a b _ δ Y n)))) ≤ _
    push_cast
    nlinarith

/-- Defect growth inside every actual cell. -/
theorem sqrt_derivativeEnergy_defect_cell_le {d : ℕ} (a : Fin d → E) {b : Fin d → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E (Fin d)} (hY : Y.Smooth) {R : ℝ}
    (hR : Y.Supported R) (k : ℕ) {δ M θ : ℝ} (hδ : 0 ≤ δ) (n : ℕ)
    (hM : ∀ j ≤ n, ∀ s ∈ Icc 0 δ, derivativeEnergy m a (k + 1)
      (residual a b (List.finRange d) (nodes a b (List.finRange d) δ Y j) s) ≤ M)
    (hθ : 0 ≤ θ) (hθδ : θ ≤ δ) :
    √(derivativeEnergy m a k (compatibilityDefect a (cell a b (List.finRange d) δ Y n θ))) ≤
      √(derivativeEnergy m a k (compatibilityDefect a Y)) +
        (n * δ + θ) * √(defectConstant (ι := Fin d) k * M) := by
  have hn := sqrt_derivativeEnergy_defect_nodes_le m a hb hY hR k hδ n fun j hj => hM j hj.le
  have hs := sqrt_derivativeEnergy_defect_step_le m a hb (hY.nodes a hb _ δ n)
    (hR.nodes a b _ δ n) k hθ fun s hs => hM n le_rfl s ⟨hs.1, hs.2.trans hθδ⟩
  change √(derivativeEnergy m a k (compatibilityDefect a
    (step a b _ θ (nodes a b _ δ Y n)))) ≤ _
  nlinarith

section CellBounds

omit [IsFiniteMeasureOnCompacts m]
/-- **Mesh-uniform compatibility defect on the actual cells.** For a smooth coefficient without
global bounds and smooth supported initial data, one constant works for all meshes of a fixed
horizon: `sqrt E_order(d(cell_k(θ))) <= sqrt E_order(d(Y)) + C δ`, where `d = p - D u`. -/
theorem exists_defect_cell_bound [m.IsAddHaarMeasure] {d : ℕ} (a : Fin d → E)
    {b : Fin d → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E (Fin d)} (hY : Y.Smooth)
    {R : ℝ} (hR : Y.Supported R) (order : ℕ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ k : ℕ, k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        √(derivativeEnergy m a order
            (compatibilityDefect a (cell a b (List.finRange d) δ Y k θ))) ≤
          √(derivativeEnergy m a order (compatibilityDefect a Y)) + C * δ := by
  obtain ⟨C₁, hC₁, hres⟩ := exists_cell_residual_bound m a (List.finRange d) hb hY hR (order + 1) L
  have hD := defectConstant_nonneg (ι := Fin d) order
  refine ⟨max L 0 * √(defectConstant (ι := Fin d) order * C₁), by positivity, ?_⟩
  intro N δ hδ hδ1 hL k hk θ hθ hθδ
  have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have h := sqrt_derivativeEnergy_defect_cell_le m a hb hY hR order (M := C₁ * δ ^ 2) hδ k
    (fun j hj s hs => hres N δ hδ hδ1 hL j (lt_of_le_of_lt hj hk) s hs.1 hs.2) hθ hθδ
  have hsq : √(defectConstant (ι := Fin d) order * (C₁ * δ ^ 2)) =
      √(defectConstant (ι := Fin d) order * C₁) * δ := by
    rw [← mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_sq hδ]
  rw [hsq] at h
  have hkt : (k : ℝ) * δ + θ ≤ max L 0 := by
    have : (k : ℝ) * δ + θ ≤ N * δ := by nlinarith
    exact (this.trans hL).trans (le_max_left _ _)
  have hr := Real.sqrt_nonneg (defectConstant (ι := Fin d) order * C₁)
  calc _ ≤ _ := h
    _ ≤ √(derivativeEnergy m a order (compatibilityDefect a Y)) +
        max L 0 * (√(defectConstant (ι := Fin d) order * C₁) * δ) := by
      nlinarith [mul_le_mul_of_nonneg_right hkt (mul_nonneg hr hδ)]
    _ = _ := by ring

/-- **Weighted form energy of the displacement on the actual cells.** With a `C^1` weight
satisfying `D_(a_j) w = -b_j w`, the weighted coordinate form energy of `u`, namely
`∫ w (u^2 + Σ_j (D_(a_j) u)^2)`, obeys on every actual cell of a fixed horizon
`sqrt(...) <= sqrt W(Y) + C (sqrt E_0(d(Y)) + δ)`, with one constant for all meshes. The
leading term is the initial weighted norm; for initial data `(0,h,0)` the defect term is
zero. No identification `p = grad u` and no global coefficient bound are used. -/
theorem exists_formEnergy_cell_bound [m.IsAddHaarMeasure] {d : ℕ} (a : Fin d → E)
    {b : Fin d → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hw0 : ∀ x, 0 ≤ w x) (hwb : ∀ j x, fderiv ℝ w x (a j) = -(b j x * w x))
    {Y : State E (Fin d)} (hY : Y.Smooth) {R : ℝ} (hR : Y.Supported R) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ k : ℕ, k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        √(weightedEnergy m w (formState a (cell a b (List.finRange d) δ Y k θ))) ≤
          √(weightedEnergy m w Y) +
            C * (√(derivativeEnergy m a 0 (compatibilityDefect a Y)) + δ) := by
  set js := List.finRange d
  obtain ⟨CW, hCW, hW⟩ := exists_weightedEnergy_cell_bound m a hb hw hw0 hwb hY hR L
  obtain ⟨CD, hCD, hDf⟩ := exists_defect_cell_bound m a hb hY hR 0 L
  set T := R + max L 0 * travel a js
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) T).exists_bound_of_continuousOn
    hw.continuous.continuousOn
  have hMw : ∀ x, ‖x‖ ≤ T → w x ≤ max M 0 := fun x hx => by
    have := hM x (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)] at this
    exact this.trans (le_max_left _ _)
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨CW + √(max M 0) * (1 + CD), by positivity, ?_⟩
  intro N δ hδ hδ1 hL k hk θ hθ hθδ
  have htr := travel_nonneg a js
  have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have hkt : (k : ℝ) * δ + θ ≤ max L 0 := by
    have : (k : ℝ) * δ + θ ≤ N * δ := by nlinarith
    exact (this.trans hL).trans (le_max_left _ _)
  set X := cell a b js δ Y k θ
  have hX : X.Smooth := hY.cell a hb js δ k θ
  have hXR : X.Supported T := by
    have h := ((hR.nodes a b js δ k).sweep a θ js).reaction b θ
    rw [abs_of_nonneg hδ, abs_of_nonneg hθ] at h
    exact h.mono (by nlinarith [mul_le_mul_of_nonneg_right hkt htr])
  let X₀ : State E (Fin d) := ⟨X.u, 0, X.p⟩
  have hX₀ : X₀.Smooth := ⟨hX.1, contDiff_const, hX.2.2⟩
  have hX₀R : X₀.Supported T := fun x hx => ⟨(hXR x hx).1, rfl, (hXR x hx).2.2⟩
  have hid : formState a X = subState X₀ (compatibilityDefect a X) := by
    apply State.ext
    · funext x; simp [formState, subState, compatibilityDefect, X₀]
    · funext x; simp [formState, subState, compatibilityDefect, X₀]
    · funext j x; simp only [formState, subState, compatibilityDefect, X₀]; ring
  have hdX := hX.compatibilityDefect a
  have hdXR := hXR.compatibilityDefect a
  have h₁ := weightedEnergy_subState_le m hw.continuous hw0 hX₀ hdX hX₀R hdXR
  rw [← hid] at h₁
  have hint {Z : State E (Fin d)} (hZ : Z.Smooth) (hZR : Z.Supported T) :
      Integrable (fun x => w x * (Z.u x ^ 2 + Z.v x ^ 2 + ∑ j, Z.p j x ^ 2)) m := by
    refine (hw.continuous.mul (((hZ.1.continuous.pow 2).add (hZ.2.1.continuous.pow 2)).add
      (continuous_finsetSum _ fun j _ => (hZ.2.2 j).continuous.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall 0 T) fun x hx => ?_)
    obtain ⟨hu, hv, hp⟩ := hZR x (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)
    simp [hu, hv, hp]
  have h₂ : weightedEnergy m w X₀ ≤ weightedEnergy m w X :=
    integral_mono (hint hX₀ hX₀R) (hint hX hXR) fun x =>
      mul_le_mul_of_nonneg_left (by simp only [X₀, Pi.zero_apply]; nlinarith [sq_nonneg (X.v x)])
        (hw0 x)
  have h₃ := weightedEnergy_le_mul_energy m hw.continuous hdX hdXR hMw
  rw [← derivativeEnergy_zero m a] at h₃
  have h₄ := hDf N δ hδ hδ1 hL k hk θ hθ hθδ
  have h₅ := hW N δ hδ hδ1 hL k hk θ hθ hθδ
  have hs₁ : √(weightedEnergy m w (formState a X)) ≤
      √(weightedEnergy m w X₀) + √(weightedEnergy m w (compatibilityDefect a X)) := by
    have := Real.sqrt_le_sqrt h₁
    rwa [Real.sqrt_sq (by positivity)] at this
  have hs₂ : √(weightedEnergy m w X₀) ≤ √(weightedEnergy m w X) := Real.sqrt_le_sqrt h₂
  have hs₃ : √(weightedEnergy m w (compatibilityDefect a X)) ≤
      √(max M 0) * √(derivativeEnergy m a 0 (compatibilityDefect a X)) := by
    rw [← Real.sqrt_mul hM0]
    exact Real.sqrt_le_sqrt h₃
  have hsM := Real.sqrt_nonneg (max M 0)
  have hE₀ := Real.sqrt_nonneg (derivativeEnergy m a 0 (compatibilityDefect a Y))
  have h₄' := mul_le_mul_of_nonneg_left h₄ hsM
  nlinarith [mul_nonneg hsM hE₀, mul_nonneg (mul_nonneg hsM hCD) hδ, mul_nonneg hCW hδ]

end CellBounds

end Integration
end FunctionalInequalities.Analysis.WaveSplitting
