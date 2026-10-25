import FunctionalInequalities.Analysis.WaveSplitting.FlowDerivative
import FunctionalInequalities.Analysis.WaveSplitting.GeneratorBounds
import FunctionalInequalities.Analysis.WaveSplitting.Localization
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tame bound for the actual split residual

The residual of the actual finite splitting step is estimated in the existing squared
ordered-coordinate energies. The proof differentiates the actual flows, keeps the flow
factors between non-commuting generators, and controls each ordered commutator by an exact
time integral. The quantitative time-integral lemma uses the fundamental theorem of calculus,
Cauchy--Schwarz in time and Fubini on the product of a finite time interval and a compact
spatial ball.
-/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem state_ext {X Y : State E ι} (hu : X.u = Y.u) (hv : X.v = Y.v)
    (hp : X.p = Y.p) : X = Y := by
  cases X
  cases Y
  cases hu
  cases hv
  cases hp
  rfl

/-! ## Ordered spatial derivatives of time slices -/

/-- Every ordered spatial derivative of a jointly smooth function is jointly smooth. -/
theorem contDiff_wordDerivative_slice (a : ι → E) (w : List ι) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : ℝ × E => wordDerivative a w (fun y => F (z.1, y)) z.2) := by
  induction w with
  | nil => exact hF
  | cons j w ih => exact contDiff_fderiv_slice ih (a j)

/-- The temporal derivative commutes with every ordered spatial derivative. -/
theorem hasDerivAt_wordDerivative_slice (a : ι → E) (w : List ι) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (s : ℝ) (x : E) :
    HasDerivAt (fun r => wordDerivative a w (fun y => F (r, y)) x)
      (wordDerivative a w (fun y => deriv (fun r => F (r, y)) s) x) s := by
  induction w generalizing x with
  | nil =>
    exact (((hF.differentiable (by simp)).comp
      (differentiable_id.prodMk (differentiable_const x))) s).hasDerivAt
  | cons j w ih =>
    have h : HasDerivAt (fun r => fderiv ℝ (wordDerivative a w (fun y => F (r, y))) x (a j))
        (fderiv ℝ (fun y => deriv (fun r => wordDerivative a w (fun y => F (r, y)) y) s) x
          (a j)) s :=
      hasDerivAt_fderiv_slice (contDiff_wordDerivative_slice a w hF) s x (a j)
    have he : (fun y => deriv (fun r => wordDerivative a w (fun y => F (r, y)) y) s) =
        wordDerivative a w (fun y => deriv (fun r => F (r, y)) s) :=
      funext fun y => (ih y).deriv
    rw [he] at h
    exact h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem wordDerivative_zero_fun [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ι → E) (w : List ι) : wordDerivative a w (fun _ : E => (0 : ℝ)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons j w ih => funext x; simp [wordDerivative, ih]

section FiniteIndex

variable [Fintype ι]

private theorem jetSquare_eq_word (a : ι → E) (k : ℕ) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : E) :
    jetSquare a k f x = ∑ n ∈ Finset.range (k + 1), ∑ w : Fin n → ι,
      wordDerivative a (List.ofFn w) f x ^ 2 := by
  unfold jetSquare
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
  rw [wordDerivative_ofFn a w hf]

private theorem continuous_jetSquare_slice (a : ι → E) (k : ℕ)
    {G : ℝ × E → ℝ} (hG : ContDiff ℝ ∞ G) :
    Continuous (fun z : ℝ × E => jetSquare a k (fun y => G (z.1, y)) z.2) := by
  have he : (fun z : ℝ × E => jetSquare a k (fun y => G (z.1, y)) z.2) = fun z =>
      ∑ n ∈ Finset.range (k + 1), ∑ w : Fin n → ι,
        wordDerivative a (List.ofFn w) (fun y => G (z.1, y)) z.2 ^ 2 :=
    funext fun z => jetSquare_eq_word a k (hG.comp (contDiff_const.prodMk contDiff_id)) z.2
  rw [he]
  exact continuous_finsetSum _ fun n _ => continuous_finsetSum _ fun w _ =>
    (contDiff_wordDerivative_slice a (List.ofFn w) hG).continuous.pow 2

end FiniteIndex

/-! ## Scalar time-integral estimates -/

private theorem sq_intervalIntegral_le {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, f s) ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, f s ^ 2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  set A := ∫ s in (0 : ℝ)..t, f s
  set Q := ∫ s in (0 : ℝ)..t, f s ^ 2
  have hint (c : ℝ) : ∫ s in (0 : ℝ)..t, (f s - c) ^ 2 = Q - 2 * c * A + c ^ 2 * t := by
    have he : (fun s => (f s - c) ^ 2) = fun s => (f s ^ 2 - (2 * c) * f s) + c ^ 2 := by
      funext s; ring
    have h₁ := intervalIntegral.integral_add (μ := volume) (a := 0) (b := t)
      (f := fun s => f s ^ 2 - (2 * c) * f s) (g := fun _ => c ^ 2)
      (((hf.pow 2).sub (continuous_const.mul hf)).intervalIntegrable _ _)
      intervalIntegrable_const
    have h₂ := intervalIntegral.integral_sub (μ := volume) (a := 0) (b := t)
      (f := fun s => f s ^ 2) (g := fun s => (2 * c) * f s)
      ((hf.pow 2).intervalIntegrable _ _) ((continuous_const.mul hf).intervalIntegrable _ _)
    have h₃ := intervalIntegral.integral_const_mul (μ := volume) (a := 0) (b := t) (2 * c) f
    rw [he, h₁, h₂, h₃, intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero, A, Q]
    ring
  have h0 := intervalIntegral.integral_nonneg (μ := volume) ht.le (fun s _ => sq_nonneg (f s - A / t))
  rw [hint] at h0
  have h1 : 0 ≤ t * (Q - 2 * (A / t) * A + (A / t) ^ 2 * t) := mul_nonneg ht.le h0
  have e : t * (Q - 2 * (A / t) * A + (A / t) ^ 2 * t) = t * Q - A ^ 2 := by
    field_simp
    ring
  nlinarith

private theorem wordDerivative_slice_sq_le (a : ι → E) (w : List ι) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (h0 : ∀ y, F (0, y) = 0) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    wordDerivative a w (fun y => F (t, y)) x ^ 2 ≤
      t * ∫ s in (0 : ℝ)..t, wordDerivative a w (fun y => deriv (fun r => F (r, y)) s) x ^ 2 := by
  have hc : Continuous (fun s => wordDerivative a w (fun y => deriv (fun r => F (r, y)) s) x) :=
    (contDiff_wordDerivative_slice a w (contDiff_deriv_slice hF)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => wordDerivative a w (fun y => F (r, y)) x)
    (fun s _ => hasDerivAt_wordDerivative_slice a w hF s x) (hc.intervalIntegrable 0 t)
  have hz : wordDerivative a w (fun y => F (0, y)) x = 0 := by
    rw [show (fun y => F (0, y)) = fun _ => (0 : ℝ) from funext h0, wordDerivative_zero_fun]
  simp only [hz, sub_zero] at hftc
  rw [← hftc]
  exact sq_intervalIntegral_le hc ht

private theorem sum_le_mul_intervalIntegral {α : Type*} (S : Finset α) {t : ℝ} (c : α → ℝ)
    (f : α → ℝ → ℝ) (hf : ∀ i ∈ S, Continuous (f i))
    (h : ∀ i ∈ S, c i ≤ t * ∫ s in (0 : ℝ)..t, f i s) :
    ∑ i ∈ S, c i ≤ t * ∫ s in (0 : ℝ)..t, ∑ i ∈ S, f i s := by
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).intervalIntegrable _ _),
    Finset.mul_sum]
  exact Finset.sum_le_sum h

private theorem jetSquare_slice_le [Fintype ι] (a : ι → E) (k : ℕ) {F : ℝ × E → ℝ}
    (hF : ContDiff ℝ ∞ F) (h0 : ∀ y, F (0, y) = 0) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    jetSquare a k (fun y => F (t, y)) x ≤
      t * ∫ s in (0 : ℝ)..t, jetSquare a k (fun y => deriv (fun r => F (r, y)) s) x := by
  have hrw (s : ℝ) := jetSquare_eq_word a k
    (f := fun y => deriv (fun r => F (r, y)) s)
    ((contDiff_deriv_slice hF).comp (contDiff_const.prodMk contDiff_id)) x
  simp only [hrw]
  rw [jetSquare_eq_word a k (f := fun y => F (t, y))
    (hF.comp (contDiff_const.prodMk contDiff_id)) x]
  have hc (w : List ι) : Continuous (fun s =>
      wordDerivative a w (fun y => deriv (fun r => F (r, y)) s) x) :=
    (contDiff_wordDerivative_slice a w (contDiff_deriv_slice hF)).continuous.comp
      (continuous_id.prodMk continuous_const)
  apply sum_le_mul_intervalIntegral
  · intro n _
    exact continuous_finsetSum _ fun w _ => (hc (List.ofFn w)).pow 2
  · intro n _
    apply sum_le_mul_intervalIntegral
    · intro w _
      exact (hc (List.ofFn w)).pow 2
    · intro w _
      exact wordDerivative_slice_sq_le a (List.ofFn w) hF h0 ht x

/-! ## State jets -/

/-- Pointwise finite jet of all three classical components. -/
private def stateJet [Fintype ι] (a : ι → E) (k : ℕ) (Y : State E ι) (x : E) : ℝ :=
  jetSquare a k Y.u x + jetSquare a k Y.v x + ∑ j, jetSquare a k (Y.p j) x

section FiniteIndex

variable [Fintype ι]

private theorem stateJet_nonneg (a : ι → E) (k : ℕ) (Y : State E ι) (x : E) :
    0 ≤ stateJet a k Y x :=
  add_nonneg (add_nonneg (jetSquare_nonneg a k _ x) (jetSquare_nonneg a k _ x))
    (Finset.sum_nonneg fun _ _ => jetSquare_nonneg a k _ x)

private theorem continuous_stateJet (a : ι → E) (k : ℕ) {Z : ℝ → State E ι}
    (hZ : JointSmooth Z) : Continuous (fun z : ℝ × E => stateJet a k (Z z.1) z.2) := by
  have hu : Continuous (fun z : ℝ × E => jetSquare a k (Z z.1).u z.2) :=
    continuous_jetSquare_slice a k (G := fun z => (Z z.1).u z.2) hZ.1
  have hv : Continuous (fun z : ℝ × E => jetSquare a k (Z z.1).v z.2) :=
    continuous_jetSquare_slice a k (G := fun z => (Z z.1).v z.2) hZ.2.1
  have hp (j : ι) : Continuous (fun z : ℝ × E => jetSquare a k ((Z z.1).p j) z.2) :=
    continuous_jetSquare_slice a k (G := fun z => (Z z.1).p j z.2) (hZ.2.2 j)
  unfold stateJet
  exact (hu.add hv).add (continuous_finsetSum _ fun j _ => hp j)

private theorem stateJet_le (a : ι → E) (k : ℕ) {g : ℝ → State E ι}
    (hg : JointSmooth g) (h0 : g 0 = zeroState) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    stateJet a k (g t) x ≤ t * ∫ s in (0 : ℝ)..t, stateJet a k (timeDerivative g s) x := by
  have hD := hg.timeDerivative
  have hz : (g 0).u = 0 ∧ (g 0).v = 0 ∧ ∀ j, (g 0).p j = 0 := by
    rw [h0]; exact ⟨rfl, rfl, fun _ => rfl⟩
  have hcs {G : ℝ × E → ℝ} (hG : ContDiff ℝ ∞ G) :
      Continuous (fun s => jetSquare a k (fun y => G (s, y)) x) := by
    have h := (continuous_jetSquare_slice a k hG).comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x))
    exact h
  have hu : jetSquare a k (g t).u x ≤
      t * ∫ s in (0 : ℝ)..t, jetSquare a k (timeDerivative g s).u x :=
    jetSquare_slice_le a k (F := fun z => (g z.1).u z.2) hg.1 (fun y => congrFun hz.1 y) ht x
  have hv : jetSquare a k (g t).v x ≤
      t * ∫ s in (0 : ℝ)..t, jetSquare a k (timeDerivative g s).v x :=
    jetSquare_slice_le a k (F := fun z => (g z.1).v z.2) hg.2.1 (fun y => congrFun hz.2.1 y) ht x
  have hp := sum_le_mul_intervalIntegral Finset.univ
    (fun j => jetSquare a k ((g t).p j) x)
    (fun j s => jetSquare a k ((timeDerivative g s).p j) x)
    (fun j _ => hcs (G := fun z => (timeDerivative g z.1).p j z.2) (hD.2.2 j))
    (fun j _ => jetSquare_slice_le a k (F := fun z => (g z.1).p j z.2) (hg.2.2 j)
      (fun y => congrFun (hz.2.2 j) y) ht x)
  have hiu : IntervalIntegrable (fun s => jetSquare a k (timeDerivative g s).u x) volume 0 t :=
    (hcs (G := fun z => (timeDerivative g z.1).u z.2) hD.1).intervalIntegrable 0 t
  have hiv : IntervalIntegrable (fun s => jetSquare a k (timeDerivative g s).v x) volume 0 t :=
    (hcs (G := fun z => (timeDerivative g z.1).v z.2) hD.2.1).intervalIntegrable 0 t
  have hip : IntervalIntegrable (fun s => ∑ j, jetSquare a k ((timeDerivative g s).p j) x)
      volume 0 t :=
    (continuous_finsetSum _ fun j _ =>
      hcs (G := fun z => (timeDerivative g z.1).p j z.2) (hD.2.2 j)).intervalIntegrable 0 t
  unfold stateJet
  rw [intervalIntegral.integral_add (hiu.add hiv) hip, intervalIntegral.integral_add hiu hiv]
  linarith

end FiniteIndex

/-! ## Supports of derivatives and of temporal derivatives -/

omit [NormedSpace ℝ E] in
private theorem eventually_zero_of_supported {f : E → ℝ} {R : ℝ}
    (hf : ∀ y, R < ‖y‖ → f y = 0) {x : E} (hx : R < ‖x‖) :
    f =ᶠ[nhds x] fun _ => (0 : ℝ) :=
  Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)
    fun y hy => hf y hy

private theorem fderiv_eq_zero_of_supported {f : E → ℝ} {R : ℝ}
    (hf : ∀ y, R < ‖y‖ → f y = 0) {x : E} (hx : R < ‖x‖) : fderiv ℝ f x = 0 := by
  rw [(eventually_zero_of_supported hf hx).fderiv_eq]
  simp

private theorem derivative_eq_zero_of_supported {f : E → ℝ} {R : ℝ}
    (hf : ∀ y, R < ‖y‖ → f y = 0) {n : ℕ} (v : Fin n → E) {x : E} (hx : R < ‖x‖) :
    derivative v f x = 0 := by
  unfold derivative
  rw [((eventually_zero_of_supported hf hx).iteratedFDeriv ℝ n).eq_of_nhds,
    iteratedFDeriv_fun_zero]
  rfl

section FiniteIndex

variable [Fintype ι]

private theorem jetSquare_eq_zero_of_supported (a : ι → E) (k : ℕ) {f : E → ℝ}
    {R : ℝ} (hf : ∀ y, R < ‖y‖ → f y = 0) {x : E} (hx : R < ‖x‖) : jetSquare a k f x = 0 := by
  simp [jetSquare, derivative_eq_zero_of_supported hf _ hx]

private theorem stateJet_eq_zero_of_supported (a : ι → E) (k : ℕ)
    {Y : State E ι} {R : ℝ} (hY : Y.Supported R) {x : E} (hx : R < ‖x‖) :
    stateJet a k Y x = 0 := by
  unfold stateJet
  rw [jetSquare_eq_zero_of_supported a k (fun y hy => (hY y hy).1) hx,
    jetSquare_eq_zero_of_supported a k (fun y hy => (hY y hy).2.1) hx]
  simp [jetSquare_eq_zero_of_supported a k (fun y hy => (hY y hy).2.2 _) hx]

end FiniteIndex

private theorem deriv_eq_zero_of_eqOn_Icc {f : ℝ → ℝ} {t σ : ℝ} (ht : 0 < t)
    (hσ : σ ∈ Icc 0 t) (hf : DifferentiableAt ℝ f σ) (h0 : ∀ r ∈ Icc 0 t, f r = 0) :
    deriv f σ = 0 := by
  have h₁ : HasDerivWithinAt f (deriv f σ) (Icc 0 t) σ := hf.hasDerivAt.hasDerivWithinAt
  have h₂ : HasDerivWithinAt f 0 (Icc 0 t) σ :=
    (hasDerivWithinAt_const σ (Icc 0 t) (0 : ℝ)).congr (fun r hr => h0 r hr) (h0 σ hσ)
  exact (uniqueDiffOn_Icc ht σ hσ).eq_deriv _ h₁ h₂

/-- A curve supported in one ball on a nondegenerate time interval has temporal derivatives
supported in that ball on the closed interval, including its endpoints. -/
private theorem supported_timeDerivative {g : ℝ → State E ι} (hg : JointSmooth g) {R t : ℝ}
    (ht : 0 < t) (hR : ∀ s ∈ Icc 0 t, (g s).Supported R) {σ : ℝ} (hσ : σ ∈ Icc 0 t) :
    (timeDerivative g σ).Supported R := by
  intro x hx
  have hd {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) : DifferentiableAt ℝ (fun r => F (r, x)) σ :=
    ((hF.differentiable (by simp)).comp (differentiable_id.prodMk (differentiable_const x))) σ
  exact ⟨deriv_eq_zero_of_eqOn_Icc ht hσ (hd hg.1) (fun r hr => (hR r hr x hx).1),
    deriv_eq_zero_of_eqOn_Icc ht hσ (hd hg.2.1) (fun r hr => (hR r hr x hx).2.1),
    fun j => deriv_eq_zero_of_eqOn_Icc ht hσ (hd (hg.2.2 j)) (fun r hr => (hR r hr x hx).2.2 j)⟩

/-! ## Support and regularity of the differentiated states -/

omit [NormedSpace ℝ E] in
/-- Compact support of every component gives one common support radius. -/
theorem State.CompactSupport.exists_supported [Fintype ι] {Y : State E ι}
    (hc : Y.CompactSupport) : ∃ R, Y.Supported R := by
  obtain ⟨Ru, hRu, hu⟩ := hc.1.exists_pos_le_norm
  obtain ⟨Rv, hRv, hv⟩ := hc.2.1.exists_pos_le_norm
  choose Rp hRp hp using fun j => (hc.2.2 j).exists_pos_le_norm
  have hS : ∀ j, Rp j ≤ ∑ i, Rp i := fun j =>
    Finset.single_le_sum (fun i _ => (hRp i).le) (Finset.mem_univ j)
  have hS0 : 0 ≤ ∑ i, Rp i := Finset.sum_nonneg fun i _ => (hRp i).le
  exact ⟨Ru + Rv + ∑ i, Rp i, fun x hx => ⟨hu x (by linarith), hv x (by linarith),
    fun j => hp j x (by linarith [hS j])⟩⟩

theorem State.Supported.coordinateGenerator [DecidableEq ι] {Y : State E ι} {R : ℝ}
    (hY : Y.Supported R) (v : E) (j : ι) :
    (WaveSplitting.coordinateGenerator v j Y).Supported R := by
  intro x hx
  refine ⟨rfl, ?_, fun i => ?_⟩
  · show fderiv ℝ (Y.p j) x v = 0
    rw [fderiv_eq_zero_of_supported (fun y hy => (hY y hy).2.2 j) hx]
    rfl
  · by_cases hi : i = j
    · subst hi
      simp only [WaveSplitting.coordinateGenerator, ↓reduceIte]
      rw [fderiv_eq_zero_of_supported (fun y hy => (hY y hy).2.1) hx]
      rfl
    · simp [WaveSplitting.coordinateGenerator, hi]

section SupportedDifferences

omit [NormedSpace ℝ E]
theorem State.Supported.addState {X Y : State E ι} {R : ℝ} (hX : X.Supported R)
    (hY : Y.Supported R) : (WaveSplitting.addState X Y).Supported R := fun x hx => by
  obtain ⟨h₁, h₂, h₃⟩ := hX x hx
  obtain ⟨h₄, h₅, h₆⟩ := hY x hx
  exact ⟨by simp [WaveSplitting.addState, h₁, h₄], by simp [WaveSplitting.addState, h₂, h₅],
    fun j => by simp [WaveSplitting.addState, h₃ j, h₆ j]⟩

theorem State.Supported.subState {X Y : State E ι} {R : ℝ} (hX : X.Supported R)
    (hY : Y.Supported R) : (WaveSplitting.subState X Y).Supported R := fun x hx => by
  obtain ⟨h₁, h₂, h₃⟩ := hX x hx
  obtain ⟨h₄, h₅, h₆⟩ := hY x hx
  exact ⟨by simp [WaveSplitting.subState, h₁, h₄], by simp [WaveSplitting.subState, h₂, h₅],
    fun j => by simp [WaveSplitting.subState, h₃ j, h₆ j]⟩

end SupportedDifferences

section FiniteIndex

variable [DecidableEq ι]

theorem State.Supported.sweepGenerator {Y : State E ι} {R : ℝ}
    (hY : Y.Supported R) (a : ι → E) (js : List ι) :
    (WaveSplitting.sweepGenerator a js Y).Supported R := by
  induction js with
  | nil => intro x _; simp [WaveSplitting.sweepGenerator, zeroState]
  | cons j js ih => exact (hY.coordinateGenerator (a j) j).addState ih

theorem State.Supported.sweepDerivative {Y : State E ι} {R : ℝ}
    (hY : Y.Supported R) (a : ι → E) (t : ℝ) (js : List ι) :
    (WaveSplitting.sweepDerivative a t js Y).Supported (R + |t| * travel a js) := by
  induction js generalizing Y R with
  | nil => intro x _; simp [WaveSplitting.sweepDerivative, zeroState]
  | cons j js ih =>
    have hT := hY.transport (a j) j t
    have h₁ := (hT.coordinateGenerator (a j) j).sweep a t js
    have h₂ := ih hT
    have he : R + |t| * ‖a j‖ + |t| * travel a js = R + |t| * travel a (j :: js) := by
      simp only [travel, List.map_cons, List.sum_cons]
      ring
    rw [he] at h₁ h₂
    exact h₁.addState h₂

end FiniteIndex

theorem State.Smooth.subState {X Y : State E ι} (hX : X.Smooth) (hY : Y.Smooth) :
    (WaveSplitting.subState X Y).Smooth :=
  ⟨hX.1.sub hY.1, hX.2.1.sub hY.2.1, fun j => (hX.2.2 j).sub (hY.2.2 j)⟩

omit [NormedSpace ℝ E] in
theorem State.CompactSupport.subState {X Y : State E ι} (hX : X.CompactSupport)
    (hY : Y.CompactSupport) : (WaveSplitting.subState X Y).CompactSupport :=
  ⟨hX.1.sub hY.1, hX.2.1.sub hY.2.1, fun j => (hX.2.2 j).sub (hY.2.2 j)⟩

section FiniteIndex

variable [DecidableEq ι]

theorem State.Smooth.sweepDerivative {Y : State E ι} (hY : Y.Smooth)
    (a : ι → E) (t : ℝ) (js : List ι) : (WaveSplitting.sweepDerivative a t js Y).Smooth := by
  induction js generalizing Y with
  | nil => exact ⟨contDiff_const, contDiff_const, fun _ => contDiff_const⟩
  | cons j js ih =>
    exact (((hY.transport (a j) j t).coordinateGenerator (a j) j).sweep a t js).addState
      (ih (hY.transport (a j) j t))

theorem State.CompactSupport.sweepDerivative {Y : State E ι}
    (hc : Y.CompactSupport) (a : ι → E) (t : ℝ) (js : List ι) :
    (WaveSplitting.sweepDerivative a t js Y).CompactSupport := by
  induction js generalizing Y with
  | nil => exact ⟨HasCompactSupport.zero, HasCompactSupport.zero, fun _ => HasCompactSupport.zero⟩
  | cons j js ih =>
    exact (((hc.transport (a j) j t).coordinateGenerator (a j) j).sweep a t js).addState
      (ih (hc.transport (a j) j t))

end FiniteIndex

/-! ## The quantitative time-integral lemma -/

section Integration
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [IsFiniteMeasureOnCompacts m]

section FiniteIndex

variable [Fintype ι]

private theorem integrable_stateJet (a : ι → E) (k : ℕ) {Y : State E ι}
    (hY : Y.Smooth) (hc : Y.CompactSupport) : Integrable (stateJet a k Y) m :=
  ((integrable_jetSquare m a k hY.1 hc.1).add (integrable_jetSquare m a k hY.2.1 hc.2.1)).add
    (integrable_finsetSum Finset.univ fun j _ => integrable_jetSquare m a k (hY.2.2 j) (hc.2.2 j))

private theorem integral_stateJet (a : ι → E) (k : ℕ) {Y : State E ι}
    (hY : Y.Smooth) (hc : Y.CompactSupport) :
    ∫ x, stateJet a k Y x ∂m = derivativeEnergy m a k Y := by
  have huv : Integrable (fun x => jetSquare a k Y.u x + jetSquare a k Y.v x) m :=
    (integrable_jetSquare m a k hY.1 hc.1).add (integrable_jetSquare m a k hY.2.1 hc.2.1)
  have hp : Integrable (fun x => ∑ j, jetSquare a k (Y.p j) x) m :=
    integrable_finsetSum Finset.univ fun j _ => integrable_jetSquare m a k (hY.2.2 j) (hc.2.2 j)
  unfold stateJet
  rw [integral_add huv hp,
    integral_add (integrable_jetSquare m a k hY.1 hc.1)
      (integrable_jetSquare m a k hY.2.1 hc.2.1),
    integral_finsetSum Finset.univ (fun j _ => integrable_jetSquare m a k (hY.2.2 j) (hc.2.2 j))]
  exact (derivativeEnergy_eq_scalarEnergy m a k hY hc).symm

section DerivativeEnergy

omit [BorelSpace E] [IsFiniteMeasureOnCompacts m]
theorem derivativeEnergy_zeroState (a : ι → E) (k : ℕ) :
    derivativeEnergy m a k (zeroState : State E ι) = 0 := by
  simp [derivativeEnergy, energy, differentiate, derivative, zeroState, squareIntegral]

theorem derivativeEnergy_nonneg (a : ι → E) (k : ℕ) (Y : State E ι) :
    0 ≤ derivativeEnergy m a k Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => energy_nonneg m _

end DerivativeEnergy

end FiniteIndex

variable [FiniteDimensional ℝ E]

section FiniteIndex

variable [Fintype ι]

/-- Quantitative time-integral bound in the squared ordered-coordinate energy. If a jointly
smooth state curve starts at zero and stays in one ball on `[0,t]`, then its energy at time
`t` is at most `t^2` times any bound for the energies of its temporal derivatives on `[0,t]`.
This is proved from the exact integral, Cauchy--Schwarz in time and Fubini. -/
theorem derivativeEnergy_le_of_timeDerivative (a : ι → E) (k : ℕ)
    {g : ℝ → State E ι} (hg : JointSmooth g) (h0 : g 0 = zeroState) {R t M : ℝ}
    (ht : 0 ≤ t) (hR : ∀ s ∈ Icc 0 t, (g s).Supported R)
    (hM : ∀ s ∈ Icc 0 t, derivativeEnergy m a k (timeDerivative g s) ≤ M) :
    derivativeEnergy m a k (g t) ≤ t ^ 2 * M := by
  rcases ht.eq_or_lt with rfl | htpos
  · rw [h0, derivativeEnergy_zeroState]
    simp
  set K : Set E := Metric.closedBall 0 R with hKdef
  have hK : IsCompact K := isCompact_closedBall 0 R
  have hout : ∀ x, x ∉ K → R < ‖x‖ := fun x hx => by
    simpa [K, Metric.mem_closedBall, dist_zero_right, not_le] using hx
  let σ : ℝ → ℝ := fun s => max 0 (min s t)
  have hσ : ∀ s, σ s ∈ Icc 0 t := fun s => ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩
  have hσid : ∀ s ∈ Icc 0 t, σ s = s := fun s hs => by
    simp only [σ, min_eq_left hs.2, max_eq_right hs.1]
  have hσc : Continuous σ := continuous_const.max (continuous_id.min continuous_const)
  have hD : JointSmooth (timeDerivative g) := hg.timeDerivative
  have hDs : ∀ s, (timeDerivative g (σ s)).Supported R :=
    fun s => supported_timeDerivative hg htpos hR (hσ s)
  let J : ℝ × E → ℝ := fun z => stateJet a k (timeDerivative g (σ z.1)) z.2
  have hJ0c : Continuous (fun z : ℝ × E => stateJet a k (timeDerivative g z.1) z.2) :=
    continuous_stateJet a k hD
  have hJc : Continuous J := by
    have h := hJ0c.comp ((hσc.comp continuous_fst).prodMk continuous_snd)
    exact h
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hJ0c.continuousOn
  have hJb : ∀ z, ‖J z‖ ≤ max C 0 := by
    intro z
    by_cases hz : z.2 ∈ K
    · exact (hC (σ z.1, z.2) ⟨hσ z.1, hz⟩).trans (le_max_left _ _)
    · have hJz : J z = 0 := stateJet_eq_zero_of_supported a k (hDs z.1) (hout z.2 hz)
      rw [hJz, norm_zero]
      exact le_max_right _ _
  have hpt : ∀ x, stateJet a k (g t) x ≤ t * ∫ s in (0 : ℝ)..t, J (s, x) := by
    intro x
    have h := stateJet_le a k hg h0 ht x
    have he : ∫ s in (0 : ℝ)..t, stateJet a k (timeDerivative g s) x =
        ∫ s in (0 : ℝ)..t, J (s, x) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht] at hs
      show stateJet a k (timeDerivative g s) x = stateJet a k (timeDerivative g (σ s)) x
      rw [hσid s hs]
    rwa [he] at h
  have : IsFiniteMeasure (m.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) t)) :=
    isFiniteMeasure_restrict.mpr (by rw [uIoc_of_le ht]; exact measure_Ioc_lt_top.ne)
  have hJint : Integrable (Function.uncurry fun s x => J (s, x))
      ((volume.restrict (uIoc (0 : ℝ) t)).prod (m.restrict K)) :=
    Integrable.of_bound hJc.aestronglyMeasurable (max C 0) (Filter.Eventually.of_forall hJb)
  have hswap := intervalIntegral_integral_swap (μ := m.restrict K) hJint
  have hint_x : Integrable (fun x => ∫ s in (0 : ℝ)..t, J (s, x)) (m.restrict K) := by
    refine hJint.integral_prod_right.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [intervalIntegral.integral_of_le ht, uIoc_of_le ht, Function.uncurry_apply_pair]
  have hgt : (g t).Smooth := hg.slice t
  have hRt := hR t ⟨ht, le_rfl⟩
  have hgc : (g t).CompactSupport := hRt.hasCompactSupport
  have hφ : ∀ s, ∫ x in K, J (s, x) ∂m ≤ M ∧ 0 ≤ ∫ x in K, J (s, x) ∂m := by
    intro s
    have e : ∫ x in K, J (s, x) ∂m = derivativeEnergy m a k (timeDerivative g (σ s)) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => stateJet_eq_zero_of_supported a k (hDs s) (hout x hx))]
      exact integral_stateJet m a k (hD.slice (σ s)) (hDs s).hasCompactSupport
    exact ⟨e ▸ hM (σ s) (hσ s), integral_nonneg fun x => stateJet_nonneg a k _ x⟩
  have hbound : ∫ s in (0 : ℝ)..t, ∫ x in K, J (s, x) ∂m ≤ M * t := by
    rw [intervalIntegral.integral_of_le ht]
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 t)
      (f := fun s => ∫ x in K, J (s, x) ∂m) (C := M) measure_Ioc_lt_top (fun s _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hφ s).2]
        exact (hφ s).1)
    rw [Real.volume_real_Ioc_of_le ht, sub_zero, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  rw [← integral_stateJet m a k hgt hgc,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun x hx => stateJet_eq_zero_of_supported a k hRt (hout x hx))]
  calc ∫ x in K, stateJet a k (g t) x ∂m ≤ ∫ x in K, t * (∫ s in (0 : ℝ)..t, J (s, x)) ∂m :=
        integral_mono (integrable_stateJet m a k hgt hgc).restrict (hint_x.const_mul t) hpt
    _ = t * ∫ s in (0 : ℝ)..t, ∫ x in K, J (s, x) ∂m := by rw [integral_const_mul, hswap]
    _ ≤ t * (M * t) := mul_le_mul_of_nonneg_left hbound ht
    _ = t ^ 2 * M := by ring

omit [FiniteDimensional ℝ E] in
theorem derivativeEnergy_subState_le (a : ι → E) (k : ℕ) {X Y : State E ι}
    (hX : X.Smooth) (hY : Y.Smooth) (hcX : X.CompactSupport) (hcY : Y.CompactSupport) :
    derivativeEnergy m a k (subState X Y) ≤
      2 * (derivativeEnergy m a k X + derivativeEnergy m a k Y) := by
  rw [derivativeEnergy_eq_scalarEnergy m a k (hX.subState hY) (hcX.subState hcY),
    derivativeEnergy_eq_scalarEnergy m a k hX hcX, derivativeEnergy_eq_scalarEnergy m a k hY hcY]
  have hu := scalarEnergy_sub_le m a k hX.1 hY.1 hcX.1 hcY.1
  have hv := scalarEnergy_sub_le m a k hX.2.1 hY.2.1 hcX.2.1 hcY.2.1
  have hp := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun j _ => scalarEnergy_sub_le m a k (hX.2.2 j) (hY.2.2 j) (hcX.2.2 j) (hcY.2.2 j))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hp
  dsimp only [subState]
  nlinarith

end FiniteIndex

section InvariantMeasure

variable [m.IsAddRightInvariant] [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] in
/-- The derivative of a finite sweep, with its flow factors, costs one derivative order. -/
theorem derivativeEnergy_sweepDerivative_le
    (a : ι → E) (k : ℕ) (t : ℝ) (js : List ι) {Y : State E ι} (hY : Y.Smooth)
    (hc : Y.CompactSupport) :
    derivativeEnergy m a k (sweepDerivative a t js Y) ≤
      4 ^ js.length * (jetCount (ι := ι) k : ℝ) * derivativeEnergy m a (k + 1) Y := by
  induction js generalizing Y with
  | nil =>
    simp only [sweepDerivative, derivativeEnergy_zeroState, List.length_nil, pow_zero, one_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (derivativeEnergy_nonneg m a _ Y)
  | cons j js ih =>
    have hT := hY.transport (a j) j t
    have hTc := hc.transport (a j) j t
    have hE := derivativeEnergy_transport m a (k + 1) (a j) j t hY hc
    have h₁ : derivativeEnergy m a k
        (sweep a t js (coordinateGenerator (a j) j (transport (a j) j t Y))) ≤
          (jetCount (ι := ι) k : ℝ) * derivativeEnergy m a (k + 1) Y := by
      rw [derivativeEnergy_sweep m a a k js t (hT.coordinateGenerator _ _)
        (hTc.coordinateGenerator _ _), ← hE]
      exact derivativeEnergy_coordinateGenerator_le m a k j hT hTc
    have h₂ := ih hT hTc
    rw [hE] at h₂
    have hadd := derivativeEnergy_addState_le m a k
      ((hT.coordinateGenerator (a j) j).sweep a t js) (hT.sweepDerivative a t js)
      ((hTc.coordinateGenerator (a j) j).sweep a t js) (hTc.sweepDerivative a t js)
    have hq : 0 ≤ (jetCount (ι := ι) k : ℝ) * derivativeEnergy m a (k + 1) Y :=
      mul_nonneg (Nat.cast_nonneg _) (derivativeEnergy_nonneg m a _ Y)
    have hp : (1 : ℝ) ≤ 4 ^ js.length := one_le_pow₀ (by norm_num)
    change derivativeEnergy m a k (addState _ _) ≤ _
    rw [List.length_cons, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hp hq]

/-- Ordered commutator of a finite coordinate sweep with one coordinate generator. The
sweep flow factors are kept; the estimate costs two derivative orders and is quadratic in
time. -/
theorem derivativeEnergy_sweep_commutator_le (a : ι → E) (k : ℕ) (js : List ι) (j : ι) {X : State E ι}
    (hX : X.Smooth) (hc : X.CompactSupport) {t : ℝ} (ht : 0 ≤ t) :
    derivativeEnergy m a k (subState (sweep a t js (coordinateGenerator (a j) j X))
        (coordinateGenerator (a j) j (sweep a t js X))) ≤
      t ^ 2 * (4 ^ (js.length + 1) * (jetCount (ι := ι) k : ℝ) *
        (jetCount (ι := ι) (k + 1) : ℝ) * derivativeEnergy m a (k + 2) X) := by
  obtain ⟨R, hR⟩ := hc.exists_supported
  have hQ := hX.coordinateGenerator (a j) j
  have hQc := hc.coordinateGenerator (a j) j
  have hg : JointSmooth (fun s => subState (sweep a s js (coordinateGenerator (a j) j X))
      (coordinateGenerator (a j) j (sweep a s js X))) :=
    (hQ.joint_const.sweep a js).subState ((hX.joint_const.sweep a js).coordinateGenerator (a j) j)
  have hderiv (s : ℝ) : HasTimeDerivative
      (fun s => subState (sweep a s js (coordinateGenerator (a j) j X))
        (coordinateGenerator (a j) j (sweep a s js X)))
      (subState (sweepDerivative a s js (coordinateGenerator (a j) j X))
        (coordinateGenerator (a j) j (sweepDerivative a s js X))) s := by
    have h₁ := (hasTimeDerivative_const (coordinateGenerator (a j) j X) s).sweep
      hQ.joint_const a js
    rw [sweep_zeroState, zero_addState] at h₁
    have h₃ := (hasTimeDerivative_const X s).sweep hX.joint_const a js
    rw [sweep_zeroState, zero_addState] at h₃
    have h₂ := (hX.joint_const.sweep a js).hasTimeDerivative_coordinateGenerator (a j) j s
    rw [h₃.timeDerivative_eq] at h₂
    exact h₁.subState h₂
  refine derivativeEnergy_le_of_timeDerivative m a k hg (by simp) (R := R + t * travel a js)
    ht ?_ ?_
  · intro s hs
    have hs' : R + |s| * travel a js ≤ R + t * travel a js := by
      rw [abs_of_nonneg hs.1]
      nlinarith [mul_le_mul_of_nonneg_right hs.2 (travel_nonneg a js)]
    exact (((hR.coordinateGenerator (a j) j).sweep a s js).mono hs').subState
      (((hR.sweep a s js).coordinateGenerator (a j) j).mono hs')
  · intro s _
    rw [(hderiv s).timeDerivative_eq]
    have hSD := derivativeEnergy_sweepDerivative_le m a k s js hQ hQc
    have hQ₁ := derivativeEnergy_coordinateGenerator_le m a (k + 1) j hX hc
    have hSD₂ := derivativeEnergy_sweepDerivative_le m a (k + 1) s js hX hc
    have hQ₂ := derivativeEnergy_coordinateGenerator_le m a k j (hX.sweepDerivative a s js)
      (hc.sweepDerivative a s js)
    have hsub := derivativeEnergy_subState_le m a k (hQ.sweepDerivative a s js)
      ((hX.sweepDerivative a s js).coordinateGenerator (a j) j) (hQc.sweepDerivative a s js)
      ((hc.sweepDerivative a s js).coordinateGenerator (a j) j)
    have hq : 0 ≤ (jetCount (ι := ι) k : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ 4 ^ js.length := by positivity
    have e₁ := mul_le_mul_of_nonneg_left hQ₁ (mul_nonneg h4 hq)
    have e₂ := mul_le_mul_of_nonneg_left hSD₂ hq
    rw [pow_succ]
    nlinarith [e₁, e₂]

/-- Residual of a coordinate sweep against its own list generator: every coordinate is
commuted through the later flow factors, with an explicit two-order quadratic bound. -/
theorem derivativeEnergy_sweepResidual_le (a : ι → E) (k : ℕ) (js : List ι) {Y : State E ι} (hY : Y.Smooth)
    (hc : Y.CompactSupport) {t : ℝ} (ht : 0 ≤ t) :
    derivativeEnergy m a k (subState (sweepDerivative a t js Y)
        (sweepGenerator a js (sweep a t js Y))) ≤
      t ^ 2 * (js.length * 4 ^ (js.length + 1) * (jetCount (ι := ι) k : ℝ) *
        (jetCount (ι := ι) (k + 1) : ℝ) * derivativeEnergy m a (k + 2) Y) := by
  induction js generalizing Y with
  | nil =>
    have hz : subState (sweepDerivative a t [] Y) (sweepGenerator a [] (sweep a t [] Y)) =
        zeroState := subState_self _
    rw [hz, derivativeEnergy_zeroState]
    simp
  | cons j js ih =>
    have hXs := hY.transport (a j) j t
    have hXc := hc.transport (a j) j t
    have hid : subState (sweepDerivative a t (j :: js) Y)
        (sweepGenerator a (j :: js) (sweep a t (j :: js) Y)) =
        addState (subState (sweep a t js (coordinateGenerator (a j) j (transport (a j) j t Y)))
            (coordinateGenerator (a j) j (sweep a t js (transport (a j) j t Y))))
          (subState (sweepDerivative a t js (transport (a j) j t Y))
            (sweepGenerator a js (sweep a t js (transport (a j) j t Y)))) := by
      apply state_ext
      · funext x
        simp only [sweepDerivative, sweepGenerator, sweep, subState, addState]
        ring
      · funext x
        simp only [sweepDerivative, sweepGenerator, sweep, subState, addState]
        ring
      · funext i x
        simp only [sweepDerivative, sweepGenerator, sweep, subState, addState]
        ring
    have hE := derivativeEnergy_transport m a (k + 2) (a j) j t hY hc
    have hcomm := derivativeEnergy_sweep_commutator_le m a k js j hXs hXc ht
    have hres := ih hXs hXc
    rw [hE] at hcomm hres
    have hadd := derivativeEnergy_addState_le m a k
      (((hXs.coordinateGenerator (a j) j).sweep a t js).subState
        ((hXs.sweep a t js).coordinateGenerator (a j) j))
      ((hXs.sweepDerivative a t js).subState ((hXs.sweep a t js).sweepGenerator a js))
      (((hXc.coordinateGenerator (a j) j).sweep a t js).subState
        ((hXc.sweep a t js).coordinateGenerator (a j) j))
      ((hXc.sweepDerivative a t js).subState ((hXc.sweep a t js).sweepGenerator a js))
    rw [hid]
    set P := t ^ 2 * (4 ^ (js.length + 1) * (jetCount (ι := ι) k : ℝ) *
      (jetCount (ι := ι) (k + 1) : ℝ) * derivativeEnergy m a (k + 2) Y) with hP
    have hP0 : 0 ≤ P := by
      have := derivativeEnergy_nonneg m a (k + 2) Y
      positivity
    have hres' : derivativeEnergy m a k (subState (sweepDerivative a t js (transport (a j) j t Y))
        (sweepGenerator a js (sweep a t js (transport (a j) j t Y)))) ≤ js.length * P := by
      rw [hP]; linarith [hres]
    have hgoal : t ^ 2 * (((j :: js).length : ℝ) * 4 ^ ((j :: js).length + 1) *
        (jetCount (ι := ι) k : ℝ) * (jetCount (ι := ι) (k + 1) : ℝ) *
          derivativeEnergy m a (k + 2) Y) = 4 * (js.length + 1) * P := by
      rw [hP]; push_cast [List.length_cons]; ring
    rw [hgoal]
    have hn : (0 : ℝ) ≤ js.length := Nat.cast_nonneg _
    nlinarith [hadd, hcomm, hres', mul_nonneg hn hP0]

end InvariantMeasure

omit [FiniteDimensional ℝ E] in
private theorem couplingConstant_nonneg [Fintype ι] (k : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ couplingConstant (ι := ι) k B := by
  unfold couplingConstant
  positivity

/-- Explicit constant for the ordered reaction/list-generator commutator. -/
def reactionCommutatorConstant [Fintype ι] (js : List ι) (k : ℕ) (B : ℝ) : ℝ :=
  2 * 4 ^ (js.length + 1) * (jetCount (ι := ι) k : ℝ) *
    ((2 + 2 * couplingConstant (ι := ι) k B) * (2 + 4 * couplingConstant (ι := ι) k B) +
      (2 + 2 * couplingConstant (ι := ι) (k + 1) B) *
        (2 + 4 * couplingConstant (ι := ι) (k + 1) B))

/-- Ordered commutator of the actual reaction with a list generator. The reaction does not
commute with the coordinate generators because of its coefficient pairing and rotation. -/
theorem derivativeEnergy_reaction_commutator_le [Fintype ι] [DecidableEq ι]
    (a : ι → E) (k : ℕ) (js : List ι) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k + 1 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B)
    {W : State E ι} (hW : W.Smooth) (hc : W.CompactSupport) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t ≤ 1) :
    derivativeEnergy m a k (subState (reaction b t (sweepGenerator a js W))
        (sweepGenerator a js (reaction b t W))) ≤
      t ^ 2 * (reactionCommutatorConstant (ι := ι) js k B * derivativeEnergy m a (k + 1) W) := by
  obtain ⟨R, hR⟩ := hc.exists_supported
  have hQ := hW.sweepGenerator a js
  have hQc := hc.sweepGenerator a js
  have hbk : ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B :=
    fun j r hr => hbB j r (by omega)
  have hg : JointSmooth (fun s => subState (reaction b s (sweepGenerator a js W))
      (sweepGenerator a js (reaction b s W))) :=
    (hQ.joint_const.reaction hb).subState ((hW.joint_const.reaction hb).listGenerator a js)
  have hderiv (s : ℝ) : HasTimeDerivative
      (fun s => subState (reaction b s (sweepGenerator a js W))
        (sweepGenerator a js (reaction b s W)))
      (subState (reactionGenerator b (reaction b s (sweepGenerator a js W)))
        (sweepGenerator a js (reactionGenerator b (reaction b s W)))) s := by
    have h₁ := (hasTimeDerivative_const (sweepGenerator a js W) s).reaction b
    rw [reaction_zeroState, zero_addState] at h₁
    have h₃ := (hasTimeDerivative_const W s).reaction b
    rw [reaction_zeroState, zero_addState] at h₃
    have h₂ := (hW.joint_const.reaction hb).hasTimeDerivative_sweepGenerator a js s
    rw [h₃.timeDerivative_eq] at h₂
    exact h₁.subState h₂
  refine derivativeEnergy_le_of_timeDerivative m a k hg (by simp) (R := R) ht ?_ ?_
  · intro s _
    exact ((hR.sweepGenerator a js).reaction b s).subState ((hR.reaction b s).sweepGenerator a js)
  · intro s hs
    have hs0 := hs.1
    have hs1 := hs.2.trans ht1
    rw [(hderiv s).timeDerivative_eq]
    have hC₀ := couplingConstant_nonneg (ι := ι) k hB
    have hC₁ := couplingConstant_nonneg (ι := ι) (k + 1) hB
    have hRQ := hQ.reaction hb s
    have hRQc := hQc.reaction b s
    have hRW := hW.reaction hb s
    have hRWc := hc.reaction b s
    have a₁ := derivativeEnergy_reactionGenerator_le m a k hb hRQ hRQc hB hbk
    have a₂ := derivativeEnergy_reaction_le m a k hb hQ hQc hB hbk hs0 hs1
    have a₃ := derivativeEnergy_sweepGenerator_le m a k js hW hc
    have b₁ := derivativeEnergy_sweepGenerator_le m a k js (hRW.reactionGenerator hb)
      (hRWc.reactionGenerator b)
    have b₂ := derivativeEnergy_reactionGenerator_le m a (k + 1) hb hRW hRWc hB hbB
    have b₃ := derivativeEnergy_reaction_le m a (k + 1) hb hW hc hB hbB hs0 hs1
    have hsub := derivativeEnergy_subState_le m a k (hRQ.reactionGenerator hb)
      ((hRW.reactionGenerator hb).sweepGenerator a js) (hRQc.reactionGenerator b)
      ((hRWc.reactionGenerator b).sweepGenerator a js)
    set Ck := couplingConstant (ι := ι) k B
    set Ck₁ := couplingConstant (ι := ι) (k + 1) B
    set q := (jetCount (ι := ι) k : ℝ)
    set F := derivativeEnergy m a (k + 1) W
    have hq : 0 ≤ q := Nat.cast_nonneg _
    have hF : 0 ≤ F := derivativeEnergy_nonneg m a _ W
    have h4 : (0 : ℝ) ≤ 4 ^ (js.length + 1) := by positivity
    have hA : derivativeEnergy m a k (reactionGenerator b (reaction b s (sweepGenerator a js W))) ≤
        (2 + 2 * Ck) * ((2 + 4 * Ck) * (4 ^ (js.length + 1) * q * F)) := by
      have f₁ : 1 + (1 + 4 * Ck) * s ≤ 2 + 4 * Ck := by nlinarith
      calc _ ≤ (2 + 2 * Ck) * derivativeEnergy m a k (reaction b s (sweepGenerator a js W)) := a₁
        _ ≤ (2 + 2 * Ck) * ((2 + 4 * Ck) * derivativeEnergy m a k (sweepGenerator a js W)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact a₂.trans (mul_le_mul_of_nonneg_right f₁ (derivativeEnergy_nonneg m a _ _))
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left a₃ (by positivity)
    have hB' : derivativeEnergy m a k (sweepGenerator a js (reactionGenerator b (reaction b s W))) ≤
        4 ^ (js.length + 1) * q * ((2 + 2 * Ck₁) * ((2 + 4 * Ck₁) * F)) := by
      have f₁ : 1 + (1 + 4 * Ck₁) * s ≤ 2 + 4 * Ck₁ := by nlinarith
      calc _ ≤ 4 ^ (js.length + 1) * q *
            derivativeEnergy m a (k + 1) (reactionGenerator b (reaction b s W)) := b₁
        _ ≤ 4 ^ (js.length + 1) * q *
            ((2 + 2 * Ck₁) * derivativeEnergy m a (k + 1) (reaction b s W)) :=
          mul_le_mul_of_nonneg_left b₂ (by positivity)
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact b₃.trans (mul_le_mul_of_nonneg_right f₁ hF)
    unfold reactionCommutatorConstant
    nlinarith [hsub, hA, hB']

/-- Explicit, non-sharp constant in the tame residual estimate. It depends only on the
number of coordinates, the split list, the derivative order and the coefficient bound. -/
def residualConstant [Fintype ι] (js : List ι) (k : ℕ) (B : ℝ) : ℝ :=
  2 * ((2 + 4 * couplingConstant (ι := ι) k B) * (js.length * 4 ^ (js.length + 1) *
    (jetCount (ι := ι) k : ℝ) * (jetCount (ι := ι) (k + 1) : ℝ)) +
    reactionCommutatorConstant (ι := ι) js k B)

omit [FiniteDimensional ℝ E] in
theorem residualConstant_nonneg [Fintype ι] (js : List ι) (k : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ residualConstant (ι := ι) js k B := by
  have h₀ := couplingConstant_nonneg (ι := ι) k hB
  have h₁ := couplingConstant_nonneg (ι := ι) (k + 1) hB
  unfold residualConstant reactionCommutatorConstant
  positivity

/-- **Tame residual estimate for the actual split step.** For the actual step
`S(t)Y = step a b js t Y` and its actual residual `e_Y(t) = residual a b js Y t`,
`E_k(e_Y(t)) <= C t^2 E_(k+2)(Y)` for `0 <= t <= 1`. The constant `residualConstant js k B`
depends only on the number of coordinates, the split list, `k` and the bound `B` on the squared
coefficient derivatives through order `k+1`; it is independent of `Y` and `t`. -/
theorem derivativeEnergy_residual_le [m.IsAddRightInvariant] [Fintype ι] [DecidableEq ι]
    (a : ι → E) (js : List ι) (k : ℕ) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k + 1 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B)
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t ≤ 1) :
    derivativeEnergy m a k (residual a b js Y t) ≤
      residualConstant (ι := ι) js k B * t ^ 2 * derivativeEnergy m a (k + 2) Y := by
  have hbk : ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B :=
    fun j r hr => hbB j r (by omega)
  have hid : residual a b js Y t =
      addState (reaction b t (subState (sweepDerivative a t js Y)
          (sweepGenerator a js (sweep a t js Y))))
        (subState (reaction b t (sweepGenerator a js (sweep a t js Y)))
          (sweepGenerator a js (reaction b t (sweep a t js Y)))) := by
    rw [residual_eq a b js hY t, reaction_subState]
    apply state_ext
    · funext x; simp only [addState, subState, step]; ring
    · funext x; simp only [addState, subState, step]; ring
    · funext i x; simp only [addState, subState, step]; ring
  have hW := hY.sweep a t js
  have hWc := hc.sweep a t js
  have hρ := (hY.sweepDerivative a t js).subState (hW.sweepGenerator a js)
  have hρc := (hc.sweepDerivative a t js).subState (hWc.sweepGenerator a js)
  have hK := ((hW.sweepGenerator a js).reaction hb t).subState
    ((hW.reaction hb t).sweepGenerator a js)
  have hKc := ((hWc.sweepGenerator a js).reaction b t).subState
    ((hWc.reaction b t).sweepGenerator a js)
  have hadd := derivativeEnergy_addState_le m a k (hρ.reaction hb t) hK (hρc.reaction b t) hKc
  have e₂ := derivativeEnergy_reaction_le m a k hb hρ hρc hB hbk ht ht1
  have e₃ := derivativeEnergy_sweepResidual_le m a k js hY hc ht
  have e₄ := derivativeEnergy_reaction_commutator_le m a k js hb hB hbB hW hWc ht ht1
  rw [derivativeEnergy_sweep m a a (k + 1) js t hY hc] at e₄
  have e₆ := derivativeEnergy_mono m a (show k + 1 ≤ k + 2 by omega) Y
  have hC := couplingConstant_nonneg (ι := ι) k hB
  have hRC : 0 ≤ reactionCommutatorConstant (ι := ι) js k B := by
    have := couplingConstant_nonneg (ι := ι) (k + 1) hB
    unfold reactionCommutatorConstant
    positivity
  set Ck := couplingConstant (ι := ι) k B
  set r := (js.length : ℝ) * 4 ^ (js.length + 1) * (jetCount (ι := ι) k : ℝ) *
    (jetCount (ι := ι) (k + 1) : ℝ)
  set E₂ := derivativeEnergy m a (k + 2) Y
  have hr : 0 ≤ r := by positivity
  have hE₂ : 0 ≤ E₂ := derivativeEnergy_nonneg m a _ Y
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have f₁ : 1 + (1 + 4 * Ck) * t ≤ 2 + 4 * Ck := by nlinarith
  have hA : derivativeEnergy m a k (reaction b t (subState (sweepDerivative a t js Y)
      (sweepGenerator a js (sweep a t js Y)))) ≤ (2 + 4 * Ck) * (t ^ 2 * (r * E₂)) := by
    calc _ ≤ _ := e₂
      _ ≤ (2 + 4 * Ck) * derivativeEnergy m a k (subState (sweepDerivative a t js Y)
          (sweepGenerator a js (sweep a t js Y))) :=
        mul_le_mul_of_nonneg_right f₁ (derivativeEnergy_nonneg m a _ _)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc _ ≤ _ := e₃
          _ = t ^ 2 * (r * E₂) := by ring
  have hB₂ : derivativeEnergy m a k (subState (reaction b t (sweepGenerator a js (sweep a t js Y)))
      (sweepGenerator a js (reaction b t (sweep a t js Y)))) ≤
        t ^ 2 * (reactionCommutatorConstant (ι := ι) js k B * E₂) := by
    refine e₄.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e₆ hRC) ht2)
  rw [hid]
  unfold residualConstant
  nlinarith [hadd, hA, hB₂, mul_nonneg ht2 (mul_nonneg hr hE₂)]

section FiniteIndex

variable [Fintype ι]

/-! ## Actual grid cells for the original smooth coefficient -/

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts m]
  [FiniteDimensional ℝ E] in
private theorem coupling_eq_of_supported {W : State E ι} {T : ℝ}
    (hW : W.Supported T) {b c : ι → E → ℝ} (hbc : ∀ j x, ‖x‖ ≤ T → b j x = c j x) :
    coupling b W = coupling c W := by
  funext x
  apply Finset.sum_congr rfl
  intro j _
  by_cases hx : ‖x‖ ≤ T
  · rw [hbc j x hx]
  · simp only [(hW x (lt_of_not_ge hx)).2.2 j, mul_zero]

omit [MeasurableSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts m] [FiniteDimensional ℝ E] in
/-- The actual residual only sees the coefficient on the propagated support ball. The
temporal derivative is local in time, so agreement of the steps near `θ` is used. -/
theorem residual_eq_of_supported [DecidableEq ι] {Z : State E ι} {R T θ : ℝ}
    (hZ : Z.Supported R) (a : ι → E) (js : List ι) {b c : ι → E → ℝ}
    (hbc : ∀ j x, ‖x‖ ≤ T → b j x = c j x) (hT : R + (|θ| + 1) * travel a js ≤ T) :
    residual a b js Z θ = residual a c js Z θ := by
  have htr := travel_nonneg a js
  have hstep : ∀ s, |s| ≤ |θ| + 1 → step a b js s Z = step a c js s Z := fun s hs =>
    step_eq_of_supported hZ a js hbc s (by nlinarith [mul_le_mul_of_nonneg_right hs htr])
  have hev : ∀ᶠ s in nhds θ, step a b js s Z = step a c js s Z := by
    filter_upwards [Metric.ball_mem_nhds θ one_pos] with s hs
    apply hstep
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have := abs_sub_abs_le_abs_sub s θ
    linarith
  have hθ := hstep θ (by linarith [abs_nonneg θ])
  have hWs : (step a c js θ Z).Supported T :=
    ((hZ.sweep a θ js).reaction c θ).mono (by nlinarith [abs_nonneg θ])
  have hu (x : E) : deriv (fun s => (step a b js s Z).u x) θ =
      deriv (fun s => (step a c js s Z).u x) θ :=
    Filter.EventuallyEq.deriv_eq (hev.mono fun s hs => by simp only [hs])
  have hv (x : E) : deriv (fun s => (step a b js s Z).v x) θ =
      deriv (fun s => (step a c js s Z).v x) θ :=
    Filter.EventuallyEq.deriv_eq (hev.mono fun s hs => by simp only [hs])
  have hp (j : ι) (x : E) : deriv (fun s => (step a b js s Z).p j x) θ =
      deriv (fun s => (step a c js s Z).p j x) θ :=
    Filter.EventuallyEq.deriv_eq (hev.mono fun s hs => by simp only [hs])
  rw [residual_eq_subState, residual_eq_subState, hθ]
  simp only [timeDerivative, hu, hv, hp, splitGenerator, reactionGenerator,
    coupling_eq_of_supported hWs hbc]

end FiniteIndex

/-- **Mesh-uniform residual bound on the actual grid cells.** For an original smooth
coefficient without global bounds, smooth initial data supported in a ball, any derivative
order and a fixed horizon `L`, one constant works for all meshes `0 <= δ <= 1` with
`N δ <= L`, every cell `k < N` and every `0 <= θ <= δ`:
`E_order(e_(nodes k)(θ)) <= C δ^2`. Here `e_Z(θ)` is the actual residual of the step started
at the computed node. The proof localizes the coefficient once, before the mesh is chosen. -/
theorem exists_cell_residual_bound [m.IsAddRightInvariant] [Fintype ι] [DecidableEq ι]
    (a : ι → E) (js : List ι) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) {R : ℝ} (hR : Y.Supported R) (order : ℕ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ k : ℕ, k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        derivativeEnergy m a order (residual a b js (nodes a b js δ Y k) θ) ≤ C * δ ^ 2 := by
  obtain ⟨c, hcs, _, heq, hbounds⟩ :=
    exists_localized_coefficient b hb (R + (L + 2) * travel a js)
  obtain ⟨B, hB, hcB⟩ := hbounds a (order + 2)
  have hCs : 0 ≤ 1 + 4 * couplingConstant (ι := ι) (order + 2) B := by
    have := couplingConstant_nonneg (ι := ι) (order + 2) hB
    positivity
  have hRc := residualConstant_nonneg (ι := ι) js order hB
  have hE := derivativeEnergy_nonneg m a (order + 2) Y
  refine ⟨residualConstant (ι := ι) js order B *
    Real.exp ((1 + 4 * couplingConstant (ι := ι) (order + 2) B) * L) *
      derivativeEnergy m a (order + 2) Y, by positivity, ?_⟩
  intro N δ hδ hδ1 hL k hk θ hθ hθδ
  have htr := travel_nonneg a js
  have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have hkL : (k : ℝ) * δ ≤ L := by nlinarith
  have hsum : (k : ℝ) * δ + θ + 1 ≤ L + 2 := by nlinarith
  have hsym : ∀ j x, ‖x‖ ≤ R + (L + 2) * travel a js → b j x = c j x :=
    fun j x hx => (heq j x hx).symm
  have hnodes := nodes_eq_of_supported hR a js N hsym
    (by rw [abs_of_nonneg hδ]; nlinarith [mul_le_mul_of_nonneg_right hL htr]) k hk.le
  have hZ := hR.nodes a c js δ k
  rw [hnodes, residual_eq_of_supported hZ a js hsym
    (by rw [abs_of_nonneg hδ, abs_of_nonneg hθ]; nlinarith [mul_le_mul_of_nonneg_right hsum htr])]
  have hres := derivativeEnergy_residual_le m a js order hcs hB
    (fun j r hr => hcB j r (by omega)) (hY.nodes a hcs js δ k)
    (State.CompactSupport.nodes hR.hasCompactSupport a c js δ k) hθ (hθδ.trans hδ1)
  have hst := derivativeEnergy_nodes_le_exp m a (order + 2) js hcs hY hR.hasCompactSupport
    hB hcB hδ hδ1 k
  have hθ2 : θ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hθ hθδ 2
  have hexp : Real.exp ((1 + 4 * couplingConstant (ι := ι) (order + 2) B) * (k * δ)) ≤
      Real.exp ((1 + 4 * couplingConstant (ι := ι) (order + 2) B) * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkL hCs)
  have hZE := derivativeEnergy_nonneg m a (order + 2) (nodes a c js δ Y k)
  calc _ ≤ residualConstant (ι := ι) js order B * θ ^ 2 *
        derivativeEnergy m a (order + 2) (nodes a c js δ Y k) := hres
    _ ≤ residualConstant (ι := ι) js order B * δ ^ 2 *
        (Real.exp ((1 + 4 * couplingConstant (ι := ι) (order + 2) B) * L) *
          derivativeEnergy m a (order + 2) Y) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hθ2 hRc)
        (hst.trans (mul_le_mul_of_nonneg_right hexp hE)) hZE (by positivity)
    _ = _ := by ring

end Integration

end FunctionalInequalities.Analysis.WaveSplitting
