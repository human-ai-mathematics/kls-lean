import FunctionalInequalities.Analysis.WaveSplitting.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Finite derivative energies for explicit wave splitting

Derivatives are evaluated on finite ordered tuples of directions and remain real-valued.
The energy is the sum of their squared integrals, not a multilinear operator norm.
These are energies on classical functions, not completed Sobolev spaces.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*}

/-- Compact support of each classical component. -/
def State.CompactSupport (Y : State E ι) : Prop :=
  HasCompactSupport Y.u ∧ HasCompactSupport Y.v ∧ ∀ j, HasCompactSupport (Y.p j)

/-- A scalar iterated derivative evaluated on an ordered direction tuple. -/
def derivative {n : ℕ} (v : Fin n → E) (f : E → ℝ) (x : E) : ℝ :=
  iteratedFDeriv ℝ n f x v

/-- Differentiate every scalar component using the same direction tuple. -/
def differentiate {n : ℕ} (v : Fin n → E) (Y : State E ι) : State E ι :=
  ⟨derivative v Y.u, derivative v Y.v, fun j => derivative v (Y.p j)⟩

theorem continuous_derivative {n : ℕ} (v : Fin n → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) : Continuous (derivative v f) :=
  (hf.continuous_iteratedFDeriv (m := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).eval continuous_const

theorem hasCompactSupport_derivative {n : ℕ} (v : Fin n → E) {f : E → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (derivative v f) :=
  (hf.iteratedFDeriv n).comp_left (g := fun p : E [×n]→L[ℝ] ℝ => p v) (by simp)

@[simp] theorem derivative_zero (v : Fin 0 → E) (f : E → ℝ) : derivative v f = f := by
  funext x
  exact iteratedFDeriv_zero_apply v

@[simp] theorem derivative_add {n : ℕ} (v : Fin n → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    derivative v (fun x => f x + g x) = fun x => derivative v f x + derivative v g x := by
  funext x
  simp [derivative, fun_iteratedFDeriv_add_apply (hf.of_le (show (n : WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
    (hg.of_le (show (n : WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt]

@[simp] theorem derivative_sub {n : ℕ} (v : Fin n → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    derivative v (fun x => f x - g x) = fun x => derivative v f x - derivative v g x := by
  funext x
  simp [derivative, fun_iteratedFDeriv_sub_apply (hf.of_le (show (n : WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
    (hg.of_le (show (n : WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt]

@[simp] theorem derivative_const_mul {n : ℕ} (v : Fin n → E) (c : ℝ) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    derivative v (fun x => c * f x) = fun x => c * derivative v f x := by
  funext x
  simpa [derivative, smul_eq_mul] using congrArg (fun p : E [×n]→L[ℝ] ℝ => p v)
    (iteratedFDeriv_const_smul_apply' (a := c) (hf.of_le (show (n : WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt)

@[simp] theorem derivative_translate {n : ℕ} (v : Fin n → E) (a : E) (f : E → ℝ) :
    derivative v (fun x => f (x + a)) = fun x => derivative v f (x + a) := by
  funext x
  simp only [derivative, iteratedFDeriv_comp_add_right]

@[simp] theorem derivative_translate_sub {n : ℕ} (v : Fin n → E) (a : E) (f : E → ℝ) :
    derivative v (fun x => f (x - a)) = fun x => derivative v f (x - a) := by
  funext x
  simp only [derivative, iteratedFDeriv_comp_sub]

section FiniteIndex

variable [DecidableEq ι]

/-- All directional derivatives commute with the actual characteristic flow. -/
theorem differentiate_transport {n : ℕ} (v : Fin n → E)
    (a : E) (j : ι) (t : ℝ) {Y : State E ι} (hY : Y.Smooth) :
    differentiate v (transport a j t Y) = transport a j t (differentiate v Y) := by
  have hp := contDiff_id.add (contDiff_const : ContDiff ℝ ∞ (fun _ : E => t • a))
  have hm := contDiff_id.sub (contDiff_const : ContDiff ℝ ∞ (fun _ : E => t • a))
  have hvp := hY.2.1.comp hp
  have hpp := (hY.2.2 j).comp hp
  have hvm := hY.2.1.comp hm
  have hpm := (hY.2.2 j).comp hm
  simp only [Function.comp_def, id_eq] at hvp hpp hvm hpm
  have hadd := (hvp.add hpp).add (hvm.sub hpm)
  have hsub := (hvp.add hpp).sub (hvm.sub hpm)
  have divrule {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
      derivative v (fun x => f x / 2) = fun x => derivative v f x / 2 := by
    simpa only [div_eq_mul_inv, mul_comm] using derivative_const_mul v (2 : ℝ)⁻¹ hf
  unfold differentiate transport
  congr 1
  · dsimp only
    rw [divrule hadd, derivative_add v (hvp.add hpp) (hvm.sub hpm),
      derivative_add v hvp hpp, derivative_sub v hvm hpm]
    simp only [derivative_translate, derivative_translate_sub]
  · funext i
    by_cases hi : i = j
    · subst i
      simp only [↓reduceIte]
      rw [divrule hsub, derivative_sub v (hvp.add hpp) (hvm.sub hpm),
        derivative_add v hvp hpp, derivative_sub v hvm hpm]
      simp only [derivative_translate, derivative_translate_sub]
    · simp only [hi, ↓reduceIte]

/-- Compact support is preserved by an actual coordinate flow. -/
theorem State.CompactSupport.transport {Y : State E ι}
    (hY : Y.CompactSupport) (a : E) (j : ι) (t : ℝ) :
    (transport a j t Y).CompactSupport := by
  have hvp : HasCompactSupport (fun x => Y.v (x + t • a)) :=
    hY.2.1.comp_homeomorph (Homeomorph.addRight (t • a))
  have hpp : HasCompactSupport (fun x => Y.p j (x + t • a)) :=
    (hY.2.2 j).comp_homeomorph (Homeomorph.addRight (t • a))
  have hvm : HasCompactSupport (fun x => Y.v (x - t • a)) := by
    have h : HasCompactSupport (fun x => Y.v (x + (-t • a))) :=
      hY.2.1.comp_homeomorph (Homeomorph.addRight (-t • a))
    simpa only [sub_eq_add_neg, neg_smul] using h
  have hpm : HasCompactSupport (fun x => Y.p j (x - t • a)) := by
    have h : HasCompactSupport (fun x => Y.p j (x + (-t • a))) :=
      (hY.2.2 j).comp_homeomorph (Homeomorph.addRight (-t • a))
    simpa only [sub_eq_add_neg, neg_smul] using h
  have divrule {f : E → ℝ} (hf : HasCompactSupport f) :
      HasCompactSupport (fun x => f x / 2) :=
    hf.comp_left (g := fun z : ℝ => z / 2) (by simp)
  refine ⟨hY.1, divrule ((hvp.add hpp).add (hvm.sub hpm)), fun i => ?_⟩
  by_cases hi : i = j
  · simpa only [WaveSplitting.transport, hi, ↓reduceIte, Pi.add_apply, Pi.sub_apply] using
      divrule ((hvp.add hpp).sub (hvm.sub hpm))
  · simpa only [WaveSplitting.transport, hi, ↓reduceIte] using hY.2.2 i

end FiniteIndex

section FiniteIndex

variable [Fintype ι]

section CompactCoupling

omit [NormedSpace ℝ E]
private theorem compact_coupling (b : ι → E → ℝ) (Y : State E ι)
    (hp : ∀ j, HasCompactSupport (Y.p j)) : HasCompactSupport (coupling b Y) := by
  have heq : coupling b Y = ∑ j, fun x => b j x * Y.p j x := by
    funext x
    simp only [coupling, Finset.sum_apply]
  rw [heq]
  exact HasCompactSupport.finset_sum fun j _ => (hp j).mul_left

/-- The coefficient multiplication in the reaction does not enlarge support. -/
theorem State.CompactSupport.reaction {Y : State E ι}
    (hY : Y.CompactSupport) (b : ι → E → ℝ) (t : ℝ) :
    (reaction b t Y).CompactSupport := by
  have hc : HasCompactSupport (coupling b Y) :=
    compact_coupling b Y hY.2.2
  have mulrule {f : E → ℝ} (hf : HasCompactSupport f) (c : ℝ) :
      HasCompactSupport (fun x => c * f x) :=
    hf.comp_left (g := fun z : ℝ => c * z) (by simp)
  exact ⟨((mulrule hY.1 _).add (mulrule hY.2.1 _)).add (mulrule hc _),
    ((mulrule hY.1 _).add (mulrule hY.2.1 _)).sub (mulrule hc _), hY.2.2⟩

end CompactCoupling

end FiniteIndex

/-- Elementary perturbation estimate used by the zero-order reaction flow. -/
private theorem perturbed_pair_bound (u v e f c t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (he : e ^ 2 + f ^ 2 ≤ 2 * t ^ 2 * c ^ 2) :
    (u + e) ^ 2 + (v + f) ^ 2 ≤ (1 + t) * (u ^ 2 + v ^ 2) + 4 * t * c ^ 2 := by
  have hy : 2 * t * (u * e + v * f) ≤ t ^ 2 * (u ^ 2 + v ^ 2) +
      e ^ 2 + f ^ 2 := by nlinarith [sq_nonneg (t * u - e), sq_nonneg (t * v - f)]
  have hd := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + t by linarith)
  have ht2 : t ^ 2 * c ^ 2 * t ≤ t ^ 2 * c ^ 2 :=
    mul_le_of_le_one_right (mul_nonneg (sq_nonneg t) (sq_nonneg c)) ht1
  nlinarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A first-order-in-time squared-energy bound for the actual reaction formula. -/
theorem reaction_pair_bound [Fintype ι] (b : ι → E → ℝ) (Y : State E ι) (x : E)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (reaction b t Y).u x ^ 2 + (reaction b t Y).v x ^ 2 ≤
      (1 + t) * (Y.u x ^ 2 + Y.v x ^ 2) + 4 * t * coupling b Y x ^ 2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hcos : (Real.cos t - 1) ^ 2 ≤ t ^ 2 := by
    have h := Real.abs_cos_sub_cos_le t 0
    simp only [Real.cos_zero, sub_zero, abs_of_pos ht] at h
    nlinarith [sq_abs (Real.cos t - 1), abs_nonneg (Real.cos t - 1)]
  have hsin : Real.sin t ^ 2 ≤ t ^ 2 := Real.sin_sq_le_sq
  have he : ((Real.cos t - 1) * coupling b Y x) ^ 2 +
      (-Real.sin t * coupling b Y x) ^ 2 ≤ 2 * t ^ 2 * coupling b Y x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hcos (sq_nonneg (coupling b Y x)),
      mul_le_mul_of_nonneg_right hsin (sq_nonneg (coupling b Y x))]
  have hrot : (Real.cos t * Y.u x + Real.sin t * Y.v x) ^ 2 +
      (-Real.sin t * Y.u x + Real.cos t * Y.v x) ^ 2 = Y.u x ^ 2 + Y.v x ^ 2 := by
    linear_combination (Y.u x ^ 2 + Y.v x ^ 2) * Real.sin_sq_add_cos_sq t
  have h := perturbed_pair_bound (Real.cos t * Y.u x + Real.sin t * Y.v x)
    (-Real.sin t * Y.u x + Real.cos t * Y.v x)
    ((Real.cos t - 1) * coupling b Y x) (-Real.sin t * coupling b Y x)
    (coupling b Y x) t ht ht1 he
  rw [hrot] at h
  simpa only [reaction, sub_eq_add_neg, neg_mul] using h

theorem State.CompactSupport.sweep [DecidableEq ι] {Y : State E ι}
    (hY : Y.CompactSupport) (a : ι → E) (t : ℝ) (js : List ι) :
    (sweep a t js Y).CompactSupport := by
  induction js generalizing Y with
  | nil => exact hY
  | cons j js ih => exact ih (hY.transport (a j) j t)

theorem State.CompactSupport.nodes [Fintype ι] [DecidableEq ι] {Y : State E ι}
    (hY : Y.CompactSupport) (a : ι → E) (b : ι → E → ℝ) (js : List ι) (δ : ℝ) (k : ℕ) :
    (nodes a b js δ Y k).CompactSupport := by
  induction k with
  | zero => exact hY
  | succ k ih => exact (ih.sweep a δ js).reaction b δ

section Integration
variable [MeasurableSpace E] [BorelSpace E]
  (m : Measure E) [IsFiniteMeasureOnCompacts m]

/-- The integral of the square of a classical scalar function. -/
def squareIntegral (f : E → ℝ) : ℝ := ∫ x, f x ^ 2 ∂m

/-- Scalar plus velocity plus coordinate-field squared energy. -/
def energy [Fintype ι] (Y : State E ι) : ℝ :=
  squareIntegral m Y.u + squareIntegral m Y.v + ∑ j, squareIntegral m (Y.p j)

/-- Finite ordered-coordinate derivative energy, including order zero. -/
def derivativeEnergy [Fintype ι] (a : ι → E) (k : ℕ) (Y : State E ι) : ℝ :=
  ∑ n ∈ Finset.range (k + 1), ∑ w : Fin n → ι,
    energy m (differentiate (fun i => a (w i)) Y)

section SquareIntegrals

omit [NormedSpace ℝ E]
private theorem integrable_sq {f : E → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => f x ^ 2) m :=
  by
    have hp : HasCompactSupport (fun x => f x * f x) := hc.mul_left
    simpa only [pow_two, Pi.mul_def] using (hf.mul hf).integrable_of_hasCompactSupport hp

/-- The scalar parallelogram identity under the integral, with actual integrability. -/
theorem squareIntegral_add_sub {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    squareIntegral m (fun x => f x + g x) + squareIntegral m (fun x => f x - g x) =
      2 * (squareIntegral m f + squareIntegral m g) := by
  unfold squareIntegral
  rw [← integral_add (integrable_sq m (f := fun x => f x + g x) (hf.add hg) (hfc.add hgc))
    (integrable_sq m (f := fun x => f x - g x) (hf.sub hg) (hfc.sub hgc))]
  have heq : (fun x => (f x + g x) ^ 2 + (f x - g x) ^ 2) =
      fun x => (2 : ℝ) * (f x ^ 2 + g x ^ 2) := by funext x; ring
  rw [heq, integral_const_mul, integral_add (integrable_sq m hf hfc) (integrable_sq m hg hgc)]

end SquareIntegrals

omit [NormedSpace ℝ E] [IsFiniteMeasureOnCompacts m] in
/-- Translating a scalar square leaves its integral unchanged for a Haar-type measure. -/
theorem squareIntegral_translate [m.IsAddRightInvariant] (f : E → ℝ) (a : E) :
    squareIntegral m (fun x => f (x + a)) = squareIntegral m f :=
  integral_add_right_eq_self (μ := m) (fun x => f x ^ 2) a

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [IsFiniteMeasureOnCompacts m] [BorelSpace E] in
/-- Constant scalar multiplication scales the squared integral quadratically. -/
theorem squareIntegral_const_mul (c : ℝ) (f : E → ℝ) :
    squareIntegral m (fun x => c * f x) = c ^ 2 * squareIntegral m f := by
  simp only [squareIntegral, mul_pow, integral_const_mul]

section InvariantMeasure

variable [m.IsAddRightInvariant]

/-- Haar energy preservation for the active pair of an actual characteristic flow. -/
theorem transport_pair_energy [DecidableEq ι]
    (a : E) (j : ι) (t : ℝ) (Y : State E ι)
    (hv : Continuous Y.v) (hp : Continuous (Y.p j))
    (hvc : HasCompactSupport Y.v) (hpc : HasCompactSupport (Y.p j)) :
    squareIntegral m (transport a j t Y).v + squareIntegral m ((transport a j t Y).p j) =
      squareIntegral m Y.v + squareIntegral m (Y.p j) := by
  let f : E → ℝ := fun x => Y.v (x + t • a) + Y.p j (x + t • a)
  let g : E → ℝ := fun x => Y.v (x - t • a) - Y.p j (x - t • a)
  have hf : Continuous f := (hv.add hp).comp (continuous_id.add continuous_const)
  have hg : Continuous g := (hv.sub hp).comp (continuous_id.sub continuous_const)
  have hfc : HasCompactSupport f :=
    (hvc.add hpc).comp_homeomorph (Homeomorph.addRight (t • a))
  have hgc : HasCompactSupport g := by
    have h : HasCompactSupport (fun x => Y.v (x + (-t • a)) - Y.p j (x + (-t • a))) :=
      (hvc.sub hpc).comp_homeomorph (Homeomorph.addRight (-t • a))
    simpa only [g, sub_eq_add_neg, neg_smul] using h
  have hpar := squareIntegral_add_sub m hf hg hfc hgc
  have hpar0 := squareIntegral_add_sub m hv hp hvc hpc
  have htplus : squareIntegral m f = squareIntegral m (fun x => Y.v x + Y.p j x) :=
    squareIntegral_translate m (fun x => Y.v x + Y.p j x) (t • a)
  have htminus : squareIntegral m g = squareIntegral m (fun x => Y.v x - Y.p j x) := by
    exact integral_sub_right_eq_self (μ := m) (fun x => (Y.v x - Y.p j x) ^ 2) (t • a)
  have heqv : (transport a j t Y).v = fun x => (2 : ℝ)⁻¹ * (f x + g x) := by
    funext x; simp only [transport, f, g]; ring
  have heqp : (transport a j t Y).p j = fun x => (2 : ℝ)⁻¹ * (f x - g x) := by
    funext x; simp only [transport, if_true, f, g]; ring
  rw [heqv, heqp, squareIntegral_const_mul, squareIntegral_const_mul]
  rw [htplus, htminus] at hpar
  linarith

section FiniteIndex

variable [Fintype ι] [DecidableEq ι]

/-- The other coordinates and displacement are fixed, hence the whole energy is preserved. -/
theorem energy_transport
    (a : E) (j : ι) (t : ℝ) (Y : State E ι)
    (hv : Continuous Y.v) (hp : Continuous (Y.p j))
    (hvc : HasCompactSupport Y.v) (hpc : HasCompactSupport (Y.p j)) :
    energy m (transport a j t Y) = energy m Y := by
  have hpair := transport_pair_energy m a j t Y hv hp hvc hpc
  have hsum : (∑ i, (squareIntegral m ((transport a j t Y).p i) - squareIntegral m (Y.p i))) =
      squareIntegral m ((transport a j t Y).p j) - squareIntegral m (Y.p j) := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      simp [transport, hij]
    · simp
  rw [Finset.sum_sub_distrib] at hsum
  unfold energy
  change squareIntegral m Y.u + _ + _ = _
  linarith

/-- Exact preservation of every finite ordered-coordinate derivative energy. -/
theorem derivativeEnergy_transport
    (directions : ι → E) (k : ℕ) (a : E) (j : ι) (t : ℝ)
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m directions k (transport a j t Y) = derivativeEnergy m directions k Y := by
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro w _
  rw [differentiate_transport _ a j t hY]
  exact energy_transport m a j t _ (continuous_derivative _ hY.2.1)
    (continuous_derivative _ (hY.2.2 j)) (hasCompactSupport_derivative _ hc.2.1)
    (hasCompactSupport_derivative _ (hc.2.2 j))

/-- Any finite coordinate sweep preserves the same energy, including an empty sweep. -/
theorem derivativeEnergy_sweep
    (directions a : ι → E) (k : ℕ) (js : List ι) (t : ℝ)
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m directions k (sweep a t js Y) = derivativeEnergy m directions k Y := by
  induction js generalizing Y with
  | nil => rfl
  | cons j js ih =>
    rw [sweep, ih (hY.transport (a j) j t) (hc.transport (a j) j t),
      derivativeEnergy_transport m directions k (a j) j t hY hc]

end FiniteIndex

end InvariantMeasure

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [IsFiniteMeasureOnCompacts m] [BorelSpace E] in
theorem squareIntegral_nonneg (f : E → ℝ) : 0 ≤ squareIntegral m f :=
  integral_nonneg fun _ => sq_nonneg _

section FiniteIndex

variable [Fintype ι]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [IsFiniteMeasureOnCompacts m] [BorelSpace E] in
theorem energy_nonneg (Y : State E ι) : 0 ≤ energy m Y :=
  add_nonneg (add_nonneg (squareIntegral_nonneg m _) (squareIntegral_nonneg m _))
    (Finset.sum_nonneg fun _ _ => squareIntegral_nonneg m _)

/-- The actual reaction has an integrated first-order bound with its coefficient pairing. -/
theorem energy_reaction_pair {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth)
    (hc : Y.CompactSupport) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    squareIntegral m (reaction b t Y).u + squareIntegral m (reaction b t Y).v ≤
      (1 + t) * (squareIntegral m Y.u + squareIntegral m Y.v) +
      4 * t * squareIntegral m (coupling b Y) := by
  have hR := hY.reaction hb t
  have hRc := hc.reaction b t
  have hbc : Continuous (coupling b Y) :=
    continuous_finsetSum _ fun j _ => (hb j).continuous.mul (hY.2.2 j).continuous
  have hbcc : HasCompactSupport (coupling b Y) :=
    compact_coupling b Y hc.2.2
  have hu := integrable_sq m hY.1.continuous hc.1
  have hv := integrable_sq m hY.2.1.continuous hc.2.1
  have hcouple := integrable_sq m hbc hbcc
  have hru := integrable_sq m hR.1.continuous hRc.1
  have hrv := integrable_sq m hR.2.1.continuous hRc.2.1
  have hint := integral_mono (hru.add hrv)
    (((hu.add hv).const_mul (1 + t)).add (hcouple.const_mul (4 * t)))
    (fun x => reaction_pair_bound b Y x ht ht1)
  simp only [Pi.add_apply] at hint
  have hi1 : Integrable (fun x => (1 + t) * (Y.u x ^ 2 + Y.v x ^ 2)) m :=
    (hu.add hv).const_mul (1 + t)
  have hi2 : Integrable (fun x => 4 * t * coupling b Y x ^ 2) m := hcouple.const_mul (4 * t)
  rw [integral_add hru hrv, integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    integral_add hu hv] at hint
  exact hint

/-- A bounded coefficient vector controls the actual pairing. The bound is an explicit
coefficient assumption of this stability lemma, not an assumption added to a heat frontend. -/
theorem squareIntegral_coupling_le {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth)
    (hc : Y.CompactSupport) {B : ℝ} (hB : ∀ x, ∑ j, b j x ^ 2 ≤ B) :
    squareIntegral m (coupling b Y) ≤ B * ∑ j, squareIntegral m (Y.p j) := by
  have hbc : Continuous (coupling b Y) :=
    continuous_finsetSum _ fun j _ => (hb j).continuous.mul (hY.2.2 j).continuous
  have hbcc : HasCompactSupport (coupling b Y) :=
    compact_coupling b Y hc.2.2
  have hp (j : ι) := integrable_sq m (hY.2.2 j).continuous (hc.2.2 j)
  have hsum : Integrable (fun x => ∑ j, Y.p j x ^ 2) m := integrable_finsetSum _ fun j _ => hp j
  have hint := integral_mono (integrable_sq m hbc hbcc) (hsum.const_mul B) (fun x =>
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => b j x) (fun j => Y.p j x)).trans
      (mul_le_mul_of_nonneg_right (hB x) (Finset.sum_nonneg fun j _ => sq_nonneg (Y.p j x))))
  simpa only [squareIntegral, coupling, integral_const_mul, integral_finsetSum _ (fun j _ => hp j)]
    using hint

/-- Zero-order stability of the actual reaction, with a linear-in-time factor. -/
theorem energy_reaction_le {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth)
    (hc : Y.CompactSupport) {B t : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ∑ j, b j x ^ 2 ≤ B)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    energy m (reaction b t Y) ≤ (1 + (1 + 4 * B) * t) * energy m Y := by
  have hpair := energy_reaction_pair m hb hY hc ht ht1
  have hcouple := squareIntegral_coupling_le m hb hY hc hB
  have hu := squareIntegral_nonneg m Y.u
  have hv := squareIntegral_nonneg m Y.v
  have hp : 0 ≤ ∑ j, squareIntegral m (Y.p j) :=
    Finset.sum_nonneg fun _ _ => squareIntegral_nonneg m _
  have hc' := mul_le_mul_of_nonneg_left hcouple (show 0 ≤ 4 * t by positivity)
  have hextra : 0 ≤ 4 * B * t * (squareIntegral m Y.u + squareIntegral m Y.v) := by positivity
  have hextrap : 0 ≤ t * ∑ j, squareIntegral m (Y.p j) := mul_nonneg ht hp
  change squareIntegral m (reaction b t Y).u + squareIntegral m (reaction b t Y).v +
    ∑ j, squareIntegral m (Y.p j) ≤ _
  unfold energy
  nlinarith

omit [BorelSpace E] [IsFiniteMeasureOnCompacts m] in
/-- Order zero is precisely the original three-component energy. -/
theorem derivativeEnergy_zero (a : ι → E) (Y : State E ι) :
    derivativeEnergy m a 0 Y = energy m Y := by
  simp [derivativeEnergy, differentiate]

end FiniteIndex

section InvariantMeasure

variable [m.IsAddRightInvariant] [Fintype ι] [DecidableEq ι]

/-- Haar energy is preserved by an entire coordinate sweep. -/
theorem energy_sweep
    (a : ι → E) (js : List ι) (t : ℝ) {Y : State E ι} (hY : Y.Smooth)
    (hc : Y.CompactSupport) : energy m (sweep a t js Y) = energy m Y := by
  simpa only [derivativeEnergy_zero] using derivativeEnergy_sweep m a a 0 js t hY hc

/-- A full split step has the same zero-order stability factor as its reaction. -/
theorem energy_step_le
    (a : ι → E) (js : List ι) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) {B t : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, ∑ j, b j x ^ 2 ≤ B) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    energy m (step a b js t Y) ≤ (1 + (1 + 4 * B) * t) * energy m Y := by
  have h := energy_reaction_le m hb (hY.sweep a t js) (hc.sweep a t js) hB0 hB ht ht1
  rwa [energy_sweep m a js t hY hc] at h

/-- Iterating actual split steps gives a quantitative bound, without assuming stability. -/
theorem energy_nodes_le
    (a : ι → E) (js : List ι) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) {B δ : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, ∑ j, b j x ^ 2 ≤ B) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    energy m (nodes a b js δ Y k) ≤ (1 + (1 + 4 * B) * δ) ^ k * energy m Y := by
  induction k with
  | zero => simp [nodes]
  | succ k ih =>
    calc
      energy m (nodes a b js δ Y (k + 1)) ≤
          (1 + (1 + 4 * B) * δ) * energy m (nodes a b js δ Y k) :=
        energy_step_le m a js hb (hY.nodes a hb js δ k) (hc.nodes a b js δ k) hB0 hB hδ hδ1
      _ ≤ (1 + (1 + 4 * B) * δ) * ((1 + (1 + 4 * B) * δ) ^ k * energy m Y) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ]; ring

/-- The zero-order grid bound depends on elapsed time `k*δ`, not separately on the mesh size. -/
theorem energy_nodes_le_exp
    (a : ι → E) (js : List ι) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) {B δ : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, ∑ j, b j x ^ 2 ≤ B) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    energy m (nodes a b js δ Y k) ≤ Real.exp ((1 + 4 * B) * (k * δ)) * energy m Y := by
  apply (energy_nodes_le m a js hb hY hc hB0 hB hδ hδ1 k).trans
  apply mul_le_mul_of_nonneg_right _ (energy_nonneg m Y)
  have hbase : 1 + (1 + 4 * B) * δ ≤ Real.exp ((1 + 4 * B) * δ) := by
    simpa only [add_comm] using Real.add_one_le_exp ((1 + 4 * B) * δ)
  have hpow := pow_le_pow_left₀ (show 0 ≤ 1 + (1 + 4 * B) * δ by positivity) hbase k
  rw [← Real.exp_nat_mul] at hpow
  convert hpow using 1
  congr 1
  ring

end InvariantMeasure

end Integration
end FunctionalInequalities.Analysis.WaveSplitting
