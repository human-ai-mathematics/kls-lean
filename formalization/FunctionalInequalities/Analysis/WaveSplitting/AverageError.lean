import FunctionalInequalities.Analysis.WaveSplitting.TimeAverage

/-!
# Quantitative error of the finite time average

For wave initial data `(0,h,0)` the classical error `J_cl q - h` of the cellwise time average
is bounded in the weighted coordinate form energy
`∫ w (f^2 + Σ_j (D_(a_j) f)^2)` by `sqrt(∫ w h^2)/L + C δ`, uniformly for meshes with
`N δ = L`. The leading term comes from the forced weighted form bound, with coefficient
`1/L`. The residual and defect terms are controlled by the mesh-uniform residual and defect
bounds, a time-integral energy lemma and Minkowski's inequality.
-/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*}

/-- A scalar function viewed as the displacement of a classical state. -/
def scalarState (f : E → ℝ) : State E ι := ⟨f, 0, fun _ => 0⟩

omit [NormedSpace ℝ E] in
theorem scalarState_supported {f : E → ℝ} {R : ℝ} (hf : ∀ y, R < ‖y‖ → f y = 0) :
    (scalarState f : State E ι).Supported R := fun x hx => ⟨hf x hx, rfl, fun _ => rfl⟩

theorem scalarState_smooth {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    (scalarState f : State E ι).Smooth := ⟨hf, contDiff_const, fun _ => contDiff_const⟩

theorem formState_supported {Y : State E ι} (a : ι → E) {R : ℝ} (hY : Y.Supported R) :
    (formState a Y).Supported R := fun x hx =>
  ⟨(hY x hx).1, rfl, fun j => by
    simp [formState, fderiv_eq_zero_of_supported (fun y hy => (hY y hy).1) hx]⟩

omit [NormedSpace ℝ E] in
private theorem hasCompactSupport_of_vanishing [ProperSpace E] {f : E → ℝ} {R : ℝ}
    (hf : ∀ y, R < ‖y‖ → f y = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx =>
    hf x (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)

private theorem formState_scalarState_add (a : ι → E) {f g : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) :
    formState a (scalarState (fun x => f x + g x)) =
      addState (formState a (scalarState f)) (formState a (scalarState g)) := by
  apply State.ext
  · rfl
  · funext x; simp [addState, formState]
  · funext j x
    simp only [formState, scalarState, addState]
    rw [fderiv_fun_add ((hf.differentiable (by simp)) x) ((hg.differentiable (by simp)) x)]
    rfl

/-! ## Joint smoothness of time primitives -/

section Parametric
variable [FiniteDimensional ℝ E]

/-- The time primitive of a jointly smooth function is jointly smooth. -/
theorem contDiff_primitive_slice {g : ℝ × E → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun z : ℝ × E => ∫ θ in (0 : ℝ)..z.1, g (θ, z.2)) := by
  have hF : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × E) => p.2.1 * g (p.2.1 * p.1, p.2.2)) :=
    (contDiff_snd.fst).mul (hg.comp (((contDiff_snd.fst).mul contDiff_fst).prodMk
      contDiff_snd.snd))
  have h := contDiff_intervalIntegral_slice (E := ℝ × E) hF 0 1
  have e : (fun z : ℝ × E => ∫ θ in (0 : ℝ)..z.1, g (θ, z.2)) = fun z =>
      ∫ τ in (0 : ℝ)..1, (fun p : ℝ × (ℝ × E) => p.2.1 * g (p.2.1 * p.1, p.2.2)) (τ, z) := by
    funext z
    simp only
    rw [intervalIntegral.integral_const_mul]
    have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (f := fun θ => g (θ, z.2)) z.1
    simp only [smul_eq_mul, mul_zero, mul_one] at this
    exact this.symm
  rw [e]
  exact h

end Parametric

/-! ## Scalar energies -/

section Integration
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [IsFiniteMeasureOnCompacts m]

theorem derivativeEnergy_scalarState [Fintype ι] (a : ι → E) (k : ℕ) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    derivativeEnergy m a k (scalarState f : State E ι) = scalarEnergy m a k f := by
  rw [derivativeEnergy_eq_scalarEnergy m a k (scalarState_smooth hf)
    ⟨hc, HasCompactSupport.zero, fun _ => HasCompactSupport.zero⟩]
  change scalarEnergy m a k f + scalarEnergy m a k (fun _ => 0) +
    ∑ _j : ι, scalarEnergy m a k (fun _ => 0) = _
  simp

theorem scalarEnergy_u_le [Fintype ι] (a : ι → E) (k : ℕ) {Y : State E ι} (hY : Y.Smooth)
    (hc : Y.CompactSupport) : scalarEnergy m a k Y.u ≤ derivativeEnergy m a k Y := by
  rw [derivativeEnergy_eq_scalarEnergy m a k hY hc]
  have := scalarEnergy_nonneg m a k Y.v
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => scalarEnergy_nonneg m a k (Y.p j)
  linarith

theorem scalarEnergy_v_le [Fintype ι] (a : ι → E) (k : ℕ) {Y : State E ι} (hY : Y.Smooth)
    (hc : Y.CompactSupport) : scalarEnergy m a k Y.v ≤ derivativeEnergy m a k Y := by
  rw [derivativeEnergy_eq_scalarEnergy m a k hY hc]
  have := scalarEnergy_nonneg m a k Y.u
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => scalarEnergy_nonneg m a k (Y.p j)
  linarith

theorem scalarEnergy_const_mul [Fintype ι] (a : ι → E) (k : ℕ) (c : ℝ) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    scalarEnergy m a k (fun x => c * f x) = c ^ 2 * scalarEnergy m a k f := by
  rw [scalarEnergy_eq_sum m a k (contDiff_const.mul hf) hc.mul_left,
    scalarEnergy_eq_sum m a k hf hc]
  simp only [derivative_const_mul _ _ hf, squareIntegral_const_mul, Finset.mul_sum]

variable [FiniteDimensional ℝ E]

/-- Minkowski's inequality for the scalar derivative energy. -/
theorem sqrt_scalarEnergy_add_le [Fintype ι] (a : ι → E) (k : ℕ) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {R : ℝ} (hfR : ∀ y, R < ‖y‖ → f y = 0)
    (hgR : ∀ y, R < ‖y‖ → g y = 0) :
    √(scalarEnergy m a k (fun x => f x + g x)) ≤ √(scalarEnergy m a k f) +
      √(scalarEnergy m a k g) := by
  have h := derivativeEnergy_addState_le_sq m a k (scalarState_smooth (ι := ι) hf)
    (scalarState_smooth (ι := ι) hg) (scalarState_supported hfR) (scalarState_supported hgR)
  have e : addState (scalarState f : State E ι) (scalarState g) =
      scalarState (fun x => f x + g x) := by
    apply State.ext
    · rfl
    · funext x; simp [addState, scalarState]
    · funext j x; simp [addState, scalarState]
  rw [e, derivativeEnergy_scalarState m a k (hf.add hg)
      (hasCompactSupport_of_vanishing (R := R) fun y hy => by simp [hfR y hy, hgR y hy]),
    derivativeEnergy_scalarState m a k hf (hasCompactSupport_of_vanishing hfR),
    derivativeEnergy_scalarState m a k hg (hasCompactSupport_of_vanishing hgR)] at h
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (by positivity)] at this

/-- Minkowski's inequality for finite sums in the scalar derivative energy. -/
theorem sqrt_scalarEnergy_sum_le [Fintype ι] (a : ι → E) (k : ℕ) (N : ℕ) {f : ℕ → E → ℝ}
    (hf : ∀ n < N, ContDiff ℝ ∞ (f n)) {R : ℝ} (hR : ∀ n < N, ∀ y, R < ‖y‖ → f n y = 0) :
    √(scalarEnergy m a k (fun x => ∑ n ∈ Finset.range N, f n x)) ≤
      ∑ n ∈ Finset.range N, √(scalarEnergy m a k (f n)) := by
  induction N with
  | zero => simp [scalarEnergy, jetSquare, derivative]
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    have hs : ContDiff ℝ ∞ (fun x => ∑ n ∈ Finset.range N, f n x) :=
      ContDiff.sum fun n hn => hf n (Nat.lt_succ_of_lt (Finset.mem_range.mp hn))
    have hsR : ∀ y, R < ‖y‖ → ∑ n ∈ Finset.range N, f n y = 0 := fun y hy =>
      Finset.sum_eq_zero fun n hn => hR n (Nat.lt_succ_of_lt (Finset.mem_range.mp hn)) y hy
    have ih' := ih (fun n hn => hf n (Nat.lt_succ_of_lt hn))
      (fun n hn => hR n (Nat.lt_succ_of_lt hn))
    exact (sqrt_scalarEnergy_add_le m a k hs (hf N (Nat.lt_succ_self N)) hsR
      (hR N (Nat.lt_succ_self N))).trans (by linarith)

/-- **Time-integral energy bound.** A finite time integral of a jointly smooth function that
stays in one ball costs a factor `δ^2` in every ordered derivative energy. -/
theorem scalarEnergy_intervalIntegral_le [Fintype ι] (a : ι → E) (k : ℕ) {g : ℝ × E → ℝ}
    (hg : ContDiff ℝ ∞ g) {R δ M : ℝ} (hδ : 0 ≤ δ)
    (hR : ∀ θ ∈ Icc 0 δ, ∀ y, R < ‖y‖ → g (θ, y) = 0)
    (hM : ∀ θ ∈ Icc 0 δ, scalarEnergy m a k (fun y => g (θ, y)) ≤ M) :
    scalarEnergy m a k (fun x => ∫ θ in (0 : ℝ)..δ, g (θ, x)) ≤ δ ^ 2 * M := by
  let G : ℝ → State E ι := fun s => scalarState (fun x => ∫ θ in (0 : ℝ)..s, g (θ, x))
  have hP := contDiff_primitive_slice hg
  have hG : JointSmooth G := ⟨hP, contDiff_const, fun _ => contDiff_const⟩
  have hslice (θ : ℝ) : ContDiff ℝ ∞ (fun y => g (θ, y)) := by
    have h := hg.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ fun y : E => (θ, y))
    exact h
  have hcont (x : E) : Continuous (fun θ => g (θ, x)) := by
    have h := hg.continuous.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x))
    exact h
  have h0 : G 0 = zeroState := by
    apply State.ext
    · funext x; simp [G, scalarState, zeroState]
    · rfl
    · rfl
  have hvan (s : ℝ) (hs : s ∈ Icc 0 δ) (y : E) (hy : R < ‖y‖) :
      ∫ θ in (0 : ℝ)..s, g (θ, y) = 0 := by
    rw [intervalIntegral.integral_of_le hs.1]
    refine (setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_).trans (integral_zero _ _)
    exact hR θ ⟨hθ.1.le, hθ.2.trans hs.2⟩ y hy
  have hderiv (s : ℝ) : timeDerivative G s = scalarState (fun y => g (s, y)) := by
    apply State.ext
    · funext x
      exact (hcont x).deriv_integral _ 0 s
    · funext x; simp [timeDerivative, G, scalarState]
    · funext j x; simp [timeDerivative, G, scalarState]
  have h := derivativeEnergy_le_of_timeDerivative m a k hG h0 (R := R) (M := M) hδ
    (fun s hs => scalarState_supported fun y hy => hvan s hs y hy)
    (fun s hs => by
      rw [hderiv s, derivativeEnergy_scalarState m a k (hslice s)
        (hasCompactSupport_of_vanishing fun y hy => hR s hs y hy)]
      exact hM s hs)
  rwa [derivativeEnergy_scalarState m a k (contDiff_intervalIntegral_slice hg 0 δ)
    (hasCompactSupport_of_vanishing fun y hy => hvan δ ⟨hδ, le_rfl⟩ y hy)] at h

end Integration

/-! ## The weighted coordinate form energy -/

section Integration
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [IsFiniteMeasureOnCompacts m]

/-- The weighted coordinate form energy `∫ w (f^2 + Σ_j (D_(a_j) f)^2)` of a scalar function. -/
def weightedFormEnergy [Fintype ι] (w : E → ℝ) (a : ι → E) (f : E → ℝ) : ℝ :=
  weightedEnergy m w (formState a (scalarState f))

omit [NormedSpace ℝ E] [BorelSpace E] [IsFiniteMeasureOnCompacts m] in
theorem weightedFormEnergy_eq [NormedSpace ℝ E] [Fintype ι] (w : E → ℝ) (a : ι → E)
    (f : E → ℝ) : weightedFormEnergy m w a f =
      ∫ x, w x * (f x ^ 2 + ∑ j, fderiv ℝ f x (a j) ^ 2) ∂m := by
  simp [weightedFormEnergy, weightedEnergy, formState, scalarState]

omit [BorelSpace E] [IsFiniteMeasureOnCompacts m] in
theorem weightedFormEnergy_const_mul [Fintype ι] (w : E → ℝ) (a : ι → E) (c : ℝ)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    weightedFormEnergy m w a (fun x => c * f x) = c ^ 2 * weightedFormEnergy m w a f := by
  rw [weightedFormEnergy_eq, weightedFormEnergy_eq, ← integral_const_mul]
  congr 1
  funext x
  have hd (j : ι) : fderiv ℝ (fun x => c * f x) x (a j) = c * fderiv ℝ f x (a j) := by
    rw [fderiv_const_mul ((hf.differentiable (by simp)) x)]
    rfl
  simp only [hd, mul_pow]
  rw [← Finset.mul_sum]
  ring

variable [FiniteDimensional ℝ E]

/-- Minkowski's inequality for the weighted form energy. -/
theorem weightedFormEnergy_add_le [Fintype ι] {w : E → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (a : ι → E) {f g : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {R : ℝ} (hfR : ∀ y, R < ‖y‖ → f y = 0)
    (hgR : ∀ y, R < ‖y‖ → g y = 0) :
    √(weightedFormEnergy m w a (fun x => f x + g x)) ≤
      √(weightedFormEnergy m w a f) + √(weightedFormEnergy m w a g) := by
  have h := weightedEnergy_addState_le m hw hw0 ((scalarState_smooth (ι := ι) hf).formState a)
    ((scalarState_smooth (ι := ι) hg).formState a)
    (formState_supported a (scalarState_supported hfR))
    (formState_supported a (scalarState_supported hgR))
  unfold weightedFormEnergy
  rw [formState_scalarState_add a hf hg]
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (by positivity)] at this

/-- The weighted form energy is controlled by the first-order scalar energy on a ball where
the weight is bounded. -/
theorem weightedFormEnergy_le [Fintype ι] {w : E → ℝ} (hw : Continuous w) (a : ι → E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {T Mw : ℝ} (hfT : ∀ y, T < ‖y‖ → f y = 0)
    (hM : ∀ x, ‖x‖ ≤ T → w x ≤ Mw) (hM0 : 0 ≤ Mw) :
    weightedFormEnergy m w a f ≤ Mw * ((1 + Fintype.card ι) * scalarEnergy m a 1 f) := by
  have hfc := hasCompactSupport_of_vanishing hfT
  have h₁ := weightedEnergy_le_mul_energy m hw ((scalarState_smooth (ι := ι) hf).formState a)
    (formState_supported a (scalarState_supported hfT)) hM
  refine h₁.trans (mul_le_mul_of_nonneg_left ?_ hM0)
  have hjet : Integrable (jetSquare a 1 f) m := integrable_jetSquare m a 1 hf hfc
  have hsq {g : E → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
      (hle : ∀ x, g x ^ 2 ≤ jetSquare a 1 f x) : squareIntegral m g ≤ scalarEnergy m a 1 f := by
    have hi : Integrable (fun x => g x ^ 2) m := by
      have hs : HasCompactSupport (fun x => g x * g x) := hgc.mul_left
      simpa only [pow_two, Pi.mul_def] using (hg.mul hg).integrable_of_hasCompactSupport hs
    exact integral_mono hi hjet hle
  have hu : squareIntegral m f ≤ scalarEnergy m a 1 f :=
    hsq hf.continuous hfc fun x => by
      simpa [wordDerivative] using wordDerivative_sq_le_jetSquare a 1 [] (by simp) hf x
  have hp (j : ι) : squareIntegral m (fun x => fderiv ℝ f x (a j)) ≤ scalarEnergy m a 1 f :=
    hsq ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hfc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L (a j)) (by simp)) fun x => by
        simpa [wordDerivative] using wordDerivative_sq_le_jetSquare a 1 [j] (by simp) hf x
  have hz : squareIntegral m (0 : E → ℝ) = 0 := by simp [squareIntegral]
  change squareIntegral m f + squareIntegral m (0 : E → ℝ) +
    ∑ j, squareIntegral m (fun x => fderiv ℝ f x (a j)) ≤ _
  rw [hz, add_zero]
  have hs := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset ι)) => hp j
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  linarith

end Integration

/-! ## The weighted divergence of the defect -/

private theorem weightedDivergence_vanishing [Fintype ι] (a : ι → E) (b : ι → E → ℝ)
    {P : ι → E → ℝ} {T : ℝ} (hP : ∀ j y, T < ‖y‖ → P j y = 0) :
    ∀ y, T < ‖y‖ → weightedDivergence a b P y = 0 := fun y hy => by
  simp [weightedDivergence, hP _ y hy,
    fderiv_eq_zero_of_supported (fun z hz => hP _ z hz) hy]



theorem compatibilityDefect_initial (a : ι → E) (h : E → ℝ) :
    compatibilityDefect a (initial h : State E ι) = zeroState := by
  apply State.ext
  · rfl
  · rfl
  · funext j x
    simp [compatibilityDefect, initial, zeroState]

/-- For a state without displacement, the weighted divergence of its coordinate field is the
velocity component of the actual wave generator. -/
theorem weightedDivergence_eq_waveGenerator [Fintype ι] (a : ι → E) (b : ι → E → ℝ)
    {D : State E ι} (hu : ∀ x, D.u x = 0) (x : E) :
    weightedDivergence a b D.p x = (waveGenerator a b D).v x := by
  simp only [weightedDivergence, waveGenerator, coupling, hu, sub_zero, Finset.sum_sub_distrib]

private theorem waveGenerator_eq_of_supported [Fintype ι] (a : ι → E)
    {b c : ι → E → ℝ} {T : ℝ} (hbc : ∀ j x, ‖x‖ ≤ T → b j x = c j x) {D : State E ι}
    (hD : D.Supported T) : waveGenerator a b D = waveGenerator a c D := by
  have hcoup : coupling b D = coupling c D := by
    funext x
    apply Finset.sum_congr rfl
    intro j _
    by_cases hx : ‖x‖ ≤ T
    · rw [hbc j x hx]
    · simp only [(hD x (lt_of_not_ge hx)).2.2 j, mul_zero]
  simp only [waveGenerator, hcoup]

section Integration
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [IsFiniteMeasureOnCompacts m]

/-- The weighted divergence of the defect of a supported smooth state costs one order of the
defect, using a localized coefficient with bounded derivatives on its support ball. -/
theorem scalarEnergy_weightedDivergence_le {d : ℕ} (a : Fin d → E) {b c : Fin d → E → ℝ}
    (hc : ∀ j, ContDiff ℝ ∞ (c j)) {T B : ℝ} (hB : 0 ≤ B)
    (hcB : ∀ j r, r.length ≤ 1 → ∀ x, wordDerivative a r (c j) x ^ 2 ≤ B)
    (hbc : ∀ j x, ‖x‖ ≤ T → b j x = c j x) {Z : State E (Fin d)} (hZ : Z.Smooth)
    (hZc : Z.CompactSupport) (hZT : Z.Supported T) :
    scalarEnergy m a 1 (weightedDivergence a b (compatibilityDefect a Z).p) ≤
      generatorConstant (ι := Fin d) (List.finRange d) 1 B *
        derivativeEnergy m a 2 (compatibilityDefect a Z) := by
  set D := compatibilityDefect a Z
  have hD : D.Smooth := hZ.compatibilityDefect a
  have hDc : D.CompactSupport :=
    ⟨HasCompactSupport.zero, HasCompactSupport.zero, fun j =>
      (hZc.2.2 j).sub ((hZc.1.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L (a j)) (by simp))⟩
  have he : weightedDivergence a b D.p = (waveGenerator a c D).v := by
    funext x
    rw [weightedDivergence_eq_waveGenerator a b (fun _ => rfl) x,
      waveGenerator_eq_of_supported a hbc (hZT.compatibilityDefect a)]
  have hG : (waveGenerator a c D).Smooth := by
    rw [← splitGenerator_finRange]
    exact (hD.sweepGenerator a _).addState (hD.reactionGenerator hc)
  have hGc : (waveGenerator a c D).CompactSupport := by
    rw [← splitGenerator_finRange]
    exact (hDc.sweepGenerator a _).addState (hDc.reactionGenerator c)
  rw [he]
  refine (scalarEnergy_v_le m a 1 hG hGc).trans ?_
  rw [← splitGenerator_finRange]
  exact derivativeEnergy_splitGenerator_le m a (List.finRange d) 1 hc hD hDc hB hcB

variable [FiniteDimensional ℝ E]

omit [IsFiniteMeasureOnCompacts m] in
/-- **Quantitative error of the finite time average.** For a smooth coefficient without
global bounds, a `C^1` weight `w >= 0` with `D_(a_j) w = -b_j w`, compactly supported smooth
wave data `(0,h,0)` and a horizon `L > 0`, one constant works for all meshes with `N δ = L`
and `0 < δ <= 1`:
`sqrt FE_w(J_cl q - h) <= sqrt(∫ w h^2)/L + C δ`, where `q` is the actual cellwise time average
and `FE_w(f) = ∫ w (f^2 + Σ_j (D_(a_j) f)^2)`. -/
theorem exists_timeAverage_error_bound [m.IsAddHaarMeasure] {d : ℕ} (a : Fin d → E)
    {b : Fin d → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hw0 : ∀ x, 0 ≤ w x) (hwb : ∀ j x, fderiv ℝ w x (a j) = -(b j x * w x)) {h : E → ℝ}
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → (N : ℝ) * δ = L →
      √(weightedFormEnergy m w a (fun x =>
          formOperator a b (timeAverage a b (List.finRange d) δ (initial h) N) x - h x)) ≤
        √(∫ x, w x * h x ^ 2 ∂m) / L + C * δ := by
  set js := List.finRange d
  obtain ⟨R, _, hR⟩ := supported_initial (ι := Fin d) hhc
  have hY : (initial h : State E (Fin d)).Smooth := smooth_initial hh
  have htr := travel_nonneg a js
  set T := R + (L + 2) * travel a js with hTdef
  obtain ⟨c, hcs, _, heq, hbounds⟩ := exists_localized_coefficient b hb T
  obtain ⟨B, hB, hcB⟩ := hbounds a 1
  have hbc : ∀ j x, ‖x‖ ≤ T → b j x = c j x := fun j x hx => (heq j x hx).symm
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) T).exists_bound_of_continuousOn
    hw.continuous.continuousOn
  have hMw : ∀ x, ‖x‖ ≤ T → w x ≤ max M 0 := fun x hx => by
    have := hM x (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)] at this
    exact this.trans (le_max_left _ _)
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  obtain ⟨CF, hCF, hF⟩ := exists_formEnergy_cell_bound m a hb hw hw0 hwb hY hR L
  obtain ⟨C₁, hC₁, hres⟩ := exists_cell_residual_bound m a js hb hY hR 1 L
  obtain ⟨CD, hCD, hdef⟩ := exists_defect_cell_bound m a hb hY hR 2 L
  set G := generatorConstant (ι := Fin d) js 1 B
  have hG0 : 0 ≤ G := by
    simp only [G, generatorConstant, couplingConstant]; positivity
  set K := max M 0 * (1 + (d : ℝ))
  have hK : 0 ≤ K := by positivity
  refine ⟨CF / L + √K * (√C₁ + L * (√G * CD + √C₁)), by positivity, ?_⟩
  intro N δ hδ hδ1 hNL
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN] at hNL; simp at hNL; linarith
    · exact hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hNδ : ((n + 1 : ℕ) : ℝ) * δ ≠ 0 := by rw [hNL]; exact hL.ne'
  -- supports inside the ball of radius `T`
  have hcellT (k : ℕ) (hk : k < n + 1) (θ : ℝ) (hθ : θ ∈ Icc 0 δ) :
      (cell a b js δ (initial h) k θ).Supported T :=
    (hR.cell a b js hδ.le hθ.1 hθ.2 hk).mono (by
      rw [show ((n + 1 : ℕ) : ℝ) * (δ * travel a js) = L * travel a js by rw [← hNL]; ring]
      nlinarith)
  have hresT (k : ℕ) (hk : k < n + 1) (θ : ℝ) (hθ : θ ∈ Icc 0 δ) :
      (residual a b js (nodes a b js δ (initial h) k) θ).Supported T := by
    have h₁ := (hR.nodes a b js δ k).residual a b js θ
    rw [abs_of_nonneg hδ.le, abs_of_nonneg hθ.1] at h₁
    have hkN : (k : ℝ) + 1 ≤ n + 1 := by exact_mod_cast hk
    have hkL : (k : ℝ) * δ + (θ + 1) ≤ L + 2 := by
      have : ((n : ℝ) + 1) * δ = L := by rw [← hNL]; push_cast; ring
      nlinarith [hθ.2]
    exact h₁.mono (by nlinarith [mul_le_mul_of_nonneg_right hkL htr])
  -- the three remainder functions
  let e : ℕ → ℝ → State E (Fin d) := fun k θ => residual a b js (nodes a b js δ (initial h) k) θ
  have hej (k : ℕ) : JointSmooth (e k) :=
    jointSmooth_residual a hb js (hY.nodes a hb js δ k)
  let Q : ℕ → E → ℝ := fun k x => ∫ θ in (0 : ℝ)..δ, (e k θ).u x
  let φ : ℕ → ℝ → ℝ := fun k θ => 1 - (k * δ + θ) / ((n + 1 : ℕ) * δ)
  let dv : ℕ → ℝ → E → ℝ := fun k θ =>
    weightedDivergence a b (compatibilityDefect a (cell a b js δ (initial h) k θ)).p
  let g₃ : ℕ → ℝ × E → ℝ := fun k z => φ k z.1 * (dv k z.1 z.2 + (e k z.1).v z.2)
  have hdefj (k : ℕ) := (hY.joint_cell a hb js δ k).compatibilityDefect a
  have hdvj (k : ℕ) : ContDiff ℝ ∞ (fun z : ℝ × E => dv k z.1 z.2) := by
    show ContDiff ℝ ∞ (fun z : ℝ × E => ∑ j, (fderiv ℝ (fun y =>
      (compatibilityDefect a (cell a b js δ (initial h) k z.1)).p j y) z.2 (a j) -
        b j z.2 * (compatibilityDefect a (cell a b js δ (initial h) k z.1)).p j z.2))
    exact ContDiff.sum fun j _ => (contDiff_fderiv_slice ((hdefj k).2.2 j) (a j)).sub
      (((hb j).comp contDiff_snd).mul ((hdefj k).2.2 j))
  have hg₃ (k : ℕ) : ContDiff ℝ ∞ (g₃ k) :=
    (contDiff_const.sub ((contDiff_const.add contDiff_fst).div_const _)).mul
      ((hdvj k).add (hej k).2.1)
  let R₃ : ℕ → E → ℝ := fun k x => ∫ θ in (0 : ℝ)..δ, g₃ k (θ, x)
  have hQs (k : ℕ) : ContDiff ℝ ∞ (Q k) :=
    contDiff_intervalIntegral_slice (F := fun z : ℝ × E => (e k z.1).u z.2) (hej k).1 0 δ
  have hRs (k : ℕ) : ContDiff ℝ ∞ (R₃ k) := contDiff_intervalIntegral_slice (hg₃ k) 0 δ
  have hvan_int {g : ℝ × E → ℝ} (hz : ∀ θ ∈ Icc 0 δ, ∀ y, T < ‖y‖ → g (θ, y) = 0) :
      ∀ y, T < ‖y‖ → ∫ θ in (0 : ℝ)..δ, g (θ, y) = 0 := fun y hy => by
    rw [intervalIntegral.integral_of_le hδ.le]
    refine (setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_).trans (integral_zero _ _)
    exact hz θ ⟨hθ.1.le, hθ.2⟩ y hy
  have heu_van (k : ℕ) (hk : k < n + 1) : ∀ θ ∈ Icc 0 δ, ∀ y, T < ‖y‖ → (e k θ).u y = 0 :=
    fun θ hθ y hy => (hresT k hk θ hθ y hy).1
  have hg₃_van (k : ℕ) (hk : k < n + 1) : ∀ θ ∈ Icc 0 δ, ∀ y, T < ‖y‖ → g₃ k (θ, y) = 0 := by
    intro θ hθ y hy
    have h₁ : dv k θ y = 0 := weightedDivergence_vanishing a b
      (fun j z hz => ((hcellT k hk θ hθ).compatibilityDefect a z hz).2.2 j) y hy
    have h₂ : (e k θ).v y = 0 := (hresT k hk θ hθ y hy).2.1
    simp [g₃, h₁, h₂]
  have hQ_van (k : ℕ) (hk : k < n + 1) : ∀ y, T < ‖y‖ → Q k y = 0 :=
    hvan_int (g := fun z : ℝ × E => (e k z.1).u z.2) (heu_van k hk)
  have hR_van (k : ℕ) (hk : k < n + 1) : ∀ y, T < ‖y‖ → R₃ k y = 0 := hvan_int (hg₃_van k hk)
  -- the exact identity
  have hid : (fun x => formOperator a b (timeAverage a b js δ (initial h) (n + 1)) x - h x) =
      fun x => (-1 / L) * (nodes a b js δ (initial h) (n + 1)).u x +
        ((1 / L) * ∑ k ∈ Finset.range (n + 1), Q k x +
          ∑ k ∈ Finset.range (n + 1), R₃ k x) := by
    funext x
    have e₀ := formOperator_timeAverage a hb hY hNδ x
    have hu : (initial h : State E (Fin d)).u x = 0 := rfl
    have hv : (initial h : State E (Fin d)).v x = h x := rfl
    rw [hv, hu, hNL] at e₀
    rw [e₀]
    simp only [Q, R₃, g₃, φ, dv, e, hNL]
    ring
  rw [hid]
  -- smoothness and supports of the pieces
  have hu_N := (hY.nodes a hb js δ (n + 1)).1
  have hNT : ∀ y, T < ‖y‖ → (nodes a b js δ (initial h) (n + 1)).u y = 0 := fun y hy =>
    (hcellT n (Nat.lt_succ_self n) δ ⟨hδ.le, le_rfl⟩ y hy).1
  have hsQ : ContDiff ℝ ∞ (fun x => ∑ k ∈ Finset.range (n + 1), Q k x) :=
    ContDiff.sum fun k _ => hQs k
  have hsR : ContDiff ℝ ∞ (fun x => ∑ k ∈ Finset.range (n + 1), R₃ k x) :=
    ContDiff.sum fun k _ => hRs k
  have hsQ_van : ∀ y, T < ‖y‖ → ∑ k ∈ Finset.range (n + 1), Q k y = 0 := fun y hy =>
    Finset.sum_eq_zero fun k hk => hQ_van k (Finset.mem_range.mp hk) y hy
  have hsR_van : ∀ y, T < ‖y‖ → ∑ k ∈ Finset.range (n + 1), R₃ k y = 0 := fun y hy =>
    Finset.sum_eq_zero fun k hk => hR_van k (Finset.mem_range.mp hk) y hy
  have hT2s : ContDiff ℝ ∞ (fun x => (1 / L) * ∑ k ∈ Finset.range (n + 1), Q k x) :=
    contDiff_const.mul hsQ
  have hT2v : ∀ y, T < ‖y‖ → (1 / L) * ∑ k ∈ Finset.range (n + 1), Q k y = 0 := fun y hy => by
    rw [hsQ_van y hy, mul_zero]
  have hSs := hT2s.add hsR
  have hSv : ∀ y, T < ‖y‖ → (1 / L) * ∑ k ∈ Finset.range (n + 1), Q k y +
      ∑ k ∈ Finset.range (n + 1), R₃ k y = 0 := fun y hy => by
    rw [hT2v y hy, hsR_van y hy, add_zero]
  have hmain := weightedFormEnergy_add_le m hw.continuous hw0 a
    (f := fun x => (-1 / L) * (nodes a b js δ (initial h) (n + 1)).u x)
    (g := fun x => (1 / L) * ∑ k ∈ Finset.range (n + 1), Q k x +
      ∑ k ∈ Finset.range (n + 1), R₃ k x)
    (contDiff_const.mul hu_N) hSs (R := T) (fun y hy => by rw [hNT y hy, mul_zero]) hSv
  -- the leading term
  have hlead : √(weightedFormEnergy m w a
      (fun x => (-1 / L) * (nodes a b js δ (initial h) (n + 1)).u x)) ≤
      (√(∫ x, w x * h x ^ 2 ∂m) + CF * δ) / L := by
    rw [weightedFormEnergy_const_mul m w a _ hu_N, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq_eq_abs, abs_div, abs_neg, abs_one, abs_of_pos hL]
    have hc := hF (n + 1) δ hδ.le hδ1 hNL.le n (Nat.lt_succ_self n) δ hδ.le le_rfl
    rw [compatibilityDefect_initial, derivativeEnergy_zeroState, Real.sqrt_zero, zero_add] at hc
    have hW : weightedEnergy m w (initial h : State E (Fin d)) = ∫ x, w x * h x ^ 2 ∂m := by
      simp [weightedEnergy, initial]
    rw [hW] at hc
    have e₁ : weightedFormEnergy m w a (nodes a b js δ (initial h) (n + 1)).u =
        weightedEnergy m w (formState a (cell a b js δ (initial h) n δ)) := rfl
    rw [e₁, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hc hL.le
  -- the remainder: weighted form energy by the first-order scalar energy
  have hrem₁ : √(weightedFormEnergy m w a (fun x => (1 / L) *
      ∑ k ∈ Finset.range (n + 1), Q k x + ∑ k ∈ Finset.range (n + 1), R₃ k x)) ≤
      √K * √(scalarEnergy m a 1 (fun x => (1 / L) * ∑ k ∈ Finset.range (n + 1), Q k x +
        ∑ k ∈ Finset.range (n + 1), R₃ k x)) := by
    rw [← Real.sqrt_mul hK]
    refine Real.sqrt_le_sqrt ((weightedFormEnergy_le m hw.continuous a hSs hSv hMw hM0).trans ?_)
    simp only [K, Fintype.card_fin]
    rw [mul_assoc]
  have hrem₂ := sqrt_scalarEnergy_add_le m a 1 hT2s hsR hT2v hsR_van
  -- the residual displacement term
  have hQk (k : ℕ) (hk : k < n + 1) : √(scalarEnergy m a 1 (Q k)) ≤ δ * (√C₁ * δ) := by
    have h₁ := scalarEnergy_intervalIntegral_le (ι := Fin d) m a 1
      (g := fun z : ℝ × E => (e k z.1).u z.2) (hej k).1 (M := C₁ * δ ^ 2) hδ.le
      (heu_van k hk) (fun θ hθ => by
        have hes := (hej k).slice θ
        have hec : (e k θ).CompactSupport := (hresT k hk θ hθ).hasCompactSupport
        exact (scalarEnergy_u_le m a 1 hes hec).trans
          (hres (n + 1) δ hδ.le hδ1 hNL.le k hk θ hθ.1 hθ.2))
    calc _ ≤ √(δ ^ 2 * (C₁ * δ ^ 2)) := Real.sqrt_le_sqrt h₁
      _ = δ * (√C₁ * δ) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ.le, Real.sqrt_mul hC₁,
          Real.sqrt_sq hδ.le]
  have hT2 : √(scalarEnergy m a 1 (fun x => (1 / L) * ∑ k ∈ Finset.range (n + 1), Q k x)) ≤
      √C₁ * δ := by
    have hc := hasCompactSupport_of_vanishing hsQ_van
    rw [scalarEnergy_const_mul m a 1 _ hsQ hc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
      (by positivity)]
    have hs := sqrt_scalarEnergy_sum_le (ι := Fin d) m a 1 (n + 1) (fun k _ => hQs k)
      (R := T) hQ_van
    have hsum : ∑ k ∈ Finset.range (n + 1), √(scalarEnergy m a 1 (Q k)) ≤
        ∑ _k ∈ Finset.range (n + 1), δ * (√C₁ * δ) :=
      Finset.sum_le_sum fun k hk => hQk k (Finset.mem_range.mp hk)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hL' : ((n + 1 : ℕ) : ℝ) * δ = L := hNL
    have e₁ : ((n + 1 : ℕ) : ℝ) * (δ * (√C₁ * δ)) = L * (√C₁ * δ) := by rw [← hL']; ring
    rw [e₁] at hsum
    rw [one_div_mul_eq_div, div_le_iff₀ hL]
    nlinarith [hs.trans hsum]
  -- the defect and residual velocity term
  have hRk (k : ℕ) (hk : k < n + 1) :
      √(scalarEnergy m a 1 (R₃ k)) ≤ δ * ((√G * CD + √C₁) * δ) := by
    have h₁ := scalarEnergy_intervalIntegral_le (ι := Fin d) m a 1 (hg₃ k)
      (M := ((√G * CD + √C₁) * δ) ^ 2) hδ.le (hg₃_van k hk) (fun θ hθ => by
        have hZ := hY.cell a hb js δ k θ
        have hZT := hcellT k hk θ hθ
        have hZc : (cell a b js δ (initial h) k θ).CompactSupport := hZT.hasCompactSupport
        have hes := (hej k).slice θ
        have hec : (e k θ).CompactSupport := (hresT k hk θ hθ).hasCompactSupport
        have hdvs : ContDiff ℝ ∞ (dv k θ) := by
          have h := (hdvj k).comp (contDiff_const.prodMk contDiff_id :
            ContDiff ℝ ∞ fun y : E => (θ, y))
          exact h
        have hdvv : ∀ y, T < ‖y‖ → dv k θ y = 0 := weightedDivergence_vanishing a b
          (fun j z hz => (hZT.compatibilityDefect a z hz).2.2 j)
        have hevv : ∀ y, T < ‖y‖ → (e k θ).v y = 0 := fun y hy => (hresT k hk θ hθ y hy).2.1
        have hsum_s : ContDiff ℝ ∞ (fun y => dv k θ y + (e k θ).v y) := hdvs.add hes.2.1
        have hsum_c : HasCompactSupport (fun y => dv k θ y + (e k θ).v y) :=
          hasCompactSupport_of_vanishing (R := T) fun y hy => by rw [hdvv y hy, hevv y hy, add_zero]
        change scalarEnergy m a 1 (fun y => φ k θ * (dv k θ y + (e k θ).v y)) ≤ _
        rw [scalarEnergy_const_mul m a 1 _ hsum_s hsum_c]
        have hφ0 : 0 ≤ φ k θ := by
          have hkN : (k : ℝ) + 1 ≤ n + 1 := by exact_mod_cast hk
          have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * δ := by rw [hNL]; exact hL
          simp only [φ, sub_nonneg]
          rw [div_le_one hpos]
          push_cast
          nlinarith [hθ.2]
        have hφ1 : φ k θ ≤ 1 := by
          have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * δ := by rw [hNL]; exact hL
          simp only [φ, sub_le_self_iff]
          exact div_nonneg (by nlinarith [hθ.1]) hpos.le
        have hφ2 : φ k θ ^ 2 ≤ 1 := by nlinarith
        have hdiv := scalarEnergy_weightedDivergence_le m a hcs hB hcB hbc hZ hZc hZT
        have hd2 := hdef (n + 1) δ hδ.le hδ1 hNL.le k hk θ hθ.1 hθ.2
        rw [compatibilityDefect_initial, derivativeEnergy_zeroState, Real.sqrt_zero,
          zero_add] at hd2
        have hdv1 : √(scalarEnergy m a 1 (dv k θ)) ≤ √G * (CD * δ) := by
          calc _ ≤ √(G * derivativeEnergy m a 2 (compatibilityDefect a
                (cell a b js δ (initial h) k θ))) := Real.sqrt_le_sqrt hdiv
            _ = √G * √(derivativeEnergy m a 2 (compatibilityDefect a
                (cell a b js δ (initial h) k θ))) := Real.sqrt_mul hG0 _
            _ ≤ _ := mul_le_mul_of_nonneg_left hd2 (Real.sqrt_nonneg _)
        have hev1 : √(scalarEnergy m a 1 (e k θ).v) ≤ √C₁ * δ := by
          calc _ ≤ √(C₁ * δ ^ 2) := Real.sqrt_le_sqrt ((scalarEnergy_v_le m a 1 hes hec).trans
                (hres (n + 1) δ hδ.le hδ1 hNL.le k hk θ hθ.1 hθ.2))
            _ = √C₁ * δ := by rw [Real.sqrt_mul hC₁, Real.sqrt_sq hδ.le]
        have hadd := sqrt_scalarEnergy_add_le m a 1 hdvs hes.2.1 hdvv hevv
        have hsq : √(scalarEnergy m a 1 (fun y => dv k θ y + (e k θ).v y)) ≤
            (√G * CD + √C₁) * δ := by nlinarith
        have hnn := scalarEnergy_nonneg m a 1 (fun y => dv k θ y + (e k θ).v y)
        have hsq2 : scalarEnergy m a 1 (fun y => dv k θ y + (e k θ).v y) ≤
            ((√G * CD + √C₁) * δ) ^ 2 := by
          have h0 := Real.sqrt_nonneg (scalarEnergy m a 1 (fun y => dv k θ y + (e k θ).v y))
          calc _ = √(scalarEnergy m a 1 (fun y => dv k θ y + (e k θ).v y)) ^ 2 :=
                (Real.sq_sqrt hnn).symm
            _ ≤ _ := pow_le_pow_left₀ h0 hsq 2
        nlinarith [mul_le_mul_of_nonneg_right hφ2 hnn])
    calc _ ≤ √(δ ^ 2 * ((√G * CD + √C₁) * δ) ^ 2) := Real.sqrt_le_sqrt h₁
      _ = δ * ((√G * CD + √C₁) * δ) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ.le, Real.sqrt_sq (by positivity)]
  have hT3 : √(scalarEnergy m a 1 (fun x => ∑ k ∈ Finset.range (n + 1), R₃ k x)) ≤
      L * ((√G * CD + √C₁) * δ) := by
    have hs := sqrt_scalarEnergy_sum_le (ι := Fin d) m a 1 (n + 1) (fun k _ => hRs k)
      (R := T) hR_van
    have hsum : ∑ k ∈ Finset.range (n + 1), √(scalarEnergy m a 1 (R₃ k)) ≤
        ∑ _k ∈ Finset.range (n + 1), δ * ((√G * CD + √C₁) * δ) :=
      Finset.sum_le_sum fun k hk => hRk k (Finset.mem_range.mp hk)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have e₁ : ((n + 1 : ℕ) : ℝ) * (δ * ((√G * CD + √C₁) * δ)) = L * ((√G * CD + √C₁) * δ) := by
      rw [← hNL]; ring
    rw [e₁] at hsum
    exact hs.trans hsum
  -- assembly
  have hsK := Real.sqrt_nonneg K
  have hS : √(weightedFormEnergy m w a (fun x => (1 / L) *
      ∑ k ∈ Finset.range (n + 1), Q k x + ∑ k ∈ Finset.range (n + 1), R₃ k x)) ≤
      √K * (√C₁ * δ + L * ((√G * CD + √C₁) * δ)) :=
    hrem₁.trans (mul_le_mul_of_nonneg_left (hrem₂.trans (add_le_add hT2 hT3)) hsK)
  calc _ ≤ _ := hmain
    _ ≤ (√(∫ x, w x * h x ^ 2 ∂m) + CF * δ) / L +
        √K * (√C₁ * δ + L * ((√G * CD + √C₁) * δ)) := add_le_add hlead hS
    _ = _ := by field_simp; ring

end Integration
end FunctionalInequalities.Analysis.WaveSplitting
