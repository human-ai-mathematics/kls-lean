import FunctionalInequalities.Analysis.WaveSplitting.Consistency
import FunctionalInequalities.Analysis.WaveSplitting.Stability

/-! # Derivative losses for the actual splitting generators -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

/-- Appending a word differentiates the inner function first, retaining the actual order. -/
theorem wordDerivative_append (a : ι → E) (w r : List ι) (f : E → ℝ) :
    wordDerivative a (w ++ r) f = wordDerivative a w (wordDerivative a r f) := by
  induction w with
  | nil => rfl
  | cons j w ih => simp only [List.cons_append, wordDerivative, ih]

/-- One coordinate derivative costs one order, in the actual finite scalar jet. -/
theorem jetSquare_coordinate_le [Fintype ι] (a : ι → E) (k : ℕ) (j : ι)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    jetSquare a k (fun y => fderiv ℝ f y (a j)) x ≤
      (jetCount (ι := ι) k : ℝ) * jetSquare a (k + 1) f x := by
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ f y (a j)) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have h (n : ℕ) (hn : n ∈ Finset.range (k + 1)) (w : Fin n → ι) :
      derivative (fun i => a (w i)) (fun y => fderiv ℝ f y (a j)) x ^ 2 ≤
        jetSquare a (k + 1) f x := by
    rw [← wordDerivative_ofFn a w hd]
    change wordDerivative a (List.ofFn w) (wordDerivative a [j] f) x ^ 2 ≤ _
    rw [← wordDerivative_append]
    apply wordDerivative_sq_le_jetSquare a (k + 1) _ _ hf x
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    simp only [Finset.mem_range] at hn
    omega
  calc
    _ ≤ ∑ n ∈ Finset.range (k + 1), ∑ _w : Fin n → ι, jetSquare a (k + 1) f x :=
      Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun w _ => h n hn w
    _ = _ := by simp [jetCount, Nat.cast_sum, ← Finset.sum_mul]

section FiniteIndex

variable [DecidableEq ι]

/-- A coordinate generator preserves spatial smoothness. -/
theorem State.Smooth.coordinateGenerator {Y : State E ι}
    (hY : Y.Smooth) (v : E) (j : ι) : (coordinateGenerator v j Y).Smooth := by
  refine ⟨contDiff_const, (hY.2.2 j).fderiv_right (by simp) |>.clm_apply contDiff_const, ?_⟩
  intro i
  by_cases hi : i = j
  · simpa only [WaveSplitting.coordinateGenerator, hi, ↓reduceIte] using
      (hY.2.1.fderiv_right (by simp)).clm_apply (contDiff_const (c := v))
  · simpa only [WaveSplitting.coordinateGenerator, hi, ↓reduceIte] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)))

/-- A coordinate generator preserves componentwise compact support. -/
theorem State.CompactSupport.coordinateGenerator {Y : State E ι}
    (hc : Y.CompactSupport) (v : E) (j : ι) : (coordinateGenerator v j Y).CompactSupport := by
  have hv : HasCompactSupport (fun x => fderiv ℝ Y.v x v) :=
    (hc.2.1.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L v) (by simp)
  have hp : HasCompactSupport (fun x => fderiv ℝ (Y.p j) x v) :=
    ((hc.2.2 j).fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L v) (by simp)
  refine ⟨HasCompactSupport.zero, hp, ?_⟩
  intro i
  by_cases hi : i = j
  · simpa only [WaveSplitting.coordinateGenerator, hi, ↓reduceIte] using hv
  · simp only [WaveSplitting.coordinateGenerator, hi, ↓reduceIte]
    exact HasCompactSupport.zero

end FiniteIndex

private theorem smooth_coupling {b : ι → E → ℝ} [Fintype ι]
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth) :
    ContDiff ℝ ∞ (coupling b Y) := ContDiff.sum fun j _ => (hb j).mul (hY.2.2 j)

section FiniteIndex

variable [Fintype ι]

omit [NormedSpace ℝ E] in
private theorem compact_coupling (b : ι → E → ℝ) {Y : State E ι}
    (hc : Y.CompactSupport) : HasCompactSupport (coupling b Y) := by
  have he : coupling b Y = ∑ j, fun x => b j x * Y.p j x := by funext x; simp [coupling]
  rw [he]
  exact HasCompactSupport.finset_sum fun j _ => (hc.2.2 j).mul_left

/-- The reaction generator preserves smooth compact classical states. -/
theorem State.Smooth.reactionGenerator {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth) :
    (reactionGenerator b Y).Smooth :=
  ⟨hY.2.1, hY.1.neg.sub (smooth_coupling hb hY), fun _ => contDiff_const⟩

omit [NormedSpace ℝ E] in
theorem State.CompactSupport.reactionGenerator (b : ι → E → ℝ)
    {Y : State E ι} (hc : Y.CompactSupport) : (reactionGenerator b Y).CompactSupport :=
  ⟨hc.2.1, hc.1.neg.sub (compact_coupling b hc), fun _ => HasCompactSupport.zero⟩

end FiniteIndex

theorem State.Smooth.addState {X Y : State E ι} (hX : X.Smooth) (hY : Y.Smooth) :
    (addState X Y).Smooth := ⟨hX.1.add hY.1, hX.2.1.add hY.2.1, fun j => (hX.2.2 j).add (hY.2.2 j)⟩

omit [NormedSpace ℝ E] in
theorem State.CompactSupport.addState {X Y : State E ι} (hX : X.CompactSupport) (hY : Y.CompactSupport) :
    (addState X Y).CompactSupport := ⟨hX.1.add hY.1, hX.2.1.add hY.2.1, fun j => (hX.2.2 j).add (hY.2.2 j)⟩

section FiniteIndex

variable [DecidableEq ι]

theorem State.Smooth.sweepGenerator {Y : State E ι} (hY : Y.Smooth)
    (a : ι → E) (js : List ι) : (sweepGenerator a js Y).Smooth := by
  induction js with
  | nil => exact ⟨contDiff_const, contDiff_const, fun _ => contDiff_const⟩
  | cons j js ih => exact (hY.coordinateGenerator (a j) j).addState ih

theorem State.CompactSupport.sweepGenerator {Y : State E ι}
    (hc : Y.CompactSupport) (a : ι → E) (js : List ι) : (sweepGenerator a js Y).CompactSupport := by
  induction js with
  | nil => exact ⟨HasCompactSupport.zero, HasCompactSupport.zero, fun _ => HasCompactSupport.zero⟩
  | cons j js ih => exact (hc.coordinateGenerator (a j) j).addState ih

end FiniteIndex

section Integration
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [IsFiniteMeasureOnCompacts m]

section FiniteIndex

variable [Fintype ι]

/-- Integrated coordinate differentiation bound, with one derivative loss. -/
theorem scalarEnergy_coordinate_le (a : ι → E) (k : ℕ) (j : ι)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    scalarEnergy m a k (fun x => fderiv ℝ f x (a j)) ≤
      (jetCount (ι := ι) k : ℝ) * scalarEnergy m a (k + 1) f := by
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ f x (a j)) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc : HasCompactSupport (fun x => fderiv ℝ f x (a j)) :=
    (hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L (a j)) (by simp)
  have h := integral_mono (integrable_jetSquare m a k hd hdc)
    ((integrable_jetSquare m a (k + 1) hf hc).const_mul (jetCount (ι := ι) k))
    (jetSquare_coordinate_le a k j hf)
  simpa only [scalarEnergy, integral_const_mul] using h

omit [BorelSpace E] [IsFiniteMeasureOnCompacts m] in
/-- Nonnegativity of the integrated scalar jet. -/
theorem scalarEnergy_nonneg (a : ι → E) (k : ℕ) (f : E → ℝ) :
    0 ≤ scalarEnergy m a k f := integral_nonneg (jetSquare_nonneg a k f)

omit [BorelSpace E] [IsFiniteMeasureOnCompacts m] in
@[simp] theorem scalarEnergy_zero (a : ι → E) (k : ℕ) :
    scalarEnergy m a k (fun _ : E => (0 : ℝ)) = 0 := by
  simp [scalarEnergy, jetSquare, derivative]

section FiniteIndex

variable [DecidableEq ι]

/-- The actual coordinate generator has an explicit one-order energy bound. -/
theorem derivativeEnergy_coordinateGenerator_le
    (a : ι → E) (k : ℕ) (j : ι) {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m a k (coordinateGenerator (a j) j Y) ≤
      (jetCount (ι := ι) k : ℝ) * derivativeEnergy m a (k + 1) Y := by
  rw [derivativeEnergy_eq_scalarEnergy m a k (hY.coordinateGenerator (a j) j)
    (hc.coordinateGenerator (a j) j)]
  have he : (∑ i, scalarEnergy m a k ((coordinateGenerator (a j) j Y).p i)) =
      scalarEnergy m a k (fun x => fderiv ℝ Y.v x (a j)) := by
    rw [Finset.sum_eq_single j]
    · simp only [coordinateGenerator, ↓reduceIte]
    · intro i hi hij
      simp only [coordinateGenerator, hij, ↓reduceIte, scalarEnergy_zero]
    · simp
  rw [he]
  change scalarEnergy m a k (fun _ => 0) + _ + _ ≤ _
  rw [scalarEnergy_zero, zero_add]
  have hv := scalarEnergy_coordinate_le m a k j hY.2.1 hc.2.1
  have hp := scalarEnergy_coordinate_le m a k j (hY.2.2 j) (hc.2.2 j)
  have hj : scalarEnergy m a (k + 1) (Y.p j) ≤ ∑ i, scalarEnergy m a (k + 1) (Y.p i) :=
    Finset.single_le_sum (fun i _ => scalarEnergy_nonneg m a (k + 1) (Y.p i)) (Finset.mem_univ j)
  rw [derivativeEnergy_eq_scalarEnergy m a (k + 1) hY hc]
  have hmul := mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg (jetCount (ι := ι) k))
  have hu := mul_nonneg (Nat.cast_nonneg (jetCount (ι := ι) k)) (scalarEnergy_nonneg m a (k + 1) Y.u)
  dsimp only [coordinateGenerator] at *
  nlinarith

/-- Two actual coordinate generators cost at most two spatial derivative orders. -/
theorem derivativeEnergy_two_coordinates_le
    (a : ι → E) (k : ℕ) (i j : ι) {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m a k (coordinateGenerator (a i) i (coordinateGenerator (a j) j Y)) ≤
      (jetCount (ι := ι) k : ℝ) * (jetCount (ι := ι) (k + 1) : ℝ) *
        derivativeEnergy m a (k + 2) Y := by
  have h₁ := derivativeEnergy_coordinateGenerator_le m a k i
    (hY.coordinateGenerator (a j) j) (hc.coordinateGenerator (a j) j)
  have h₂ := derivativeEnergy_coordinateGenerator_le m a (k + 1) j hY hc
  calc
    _ ≤ (jetCount (ι := ι) k : ℝ) * derivativeEnergy m a (k + 1) (coordinateGenerator (a j) j Y) := h₁
    _ ≤ (jetCount (ι := ι) k : ℝ) * ((jetCount (ι := ι) (k + 1) : ℝ) *
        derivativeEnergy m a (k + 2) Y) := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg _)
    _ = _ := by ring

end FiniteIndex

/-- Scalar subtraction in the finite derivative energy. -/
theorem scalarEnergy_sub_le (a : ι → E) (k : ℕ) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    scalarEnergy m a k (fun x => f x - g x) ≤
      2 * (scalarEnergy m a k f + scalarEnergy m a k g) := by
  have hp (x : E) : jetSquare a k (fun y => f y - g y) x ≤
      2 * (jetSquare a k f x + jetSquare a k g x) := by
    unfold jetSquare
    simp only [derivative_sub _ hf hg]
    calc
      _ ≤ ∑ n ∈ Finset.range (k + 1), ∑ w : Fin n → ι,
          2 * (derivative (fun i => a (w i)) f x ^ 2 + derivative (fun i => a (w i)) g x ^ 2) := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro w hw
        nlinarith [sq_nonneg (derivative (fun i => a (w i)) f x + derivative (fun i => a (w i)) g x)]
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hi : Integrable (fun x => jetSquare a k f x + jetSquare a k g x) m :=
    (integrable_jetSquare m a k hf hfc).add (integrable_jetSquare m a k hg hgc)
  have h := integral_mono (integrable_jetSquare m a k (hf.sub hg) (hfc.sub hgc)) (hi.const_mul 2) hp
  simpa only [scalarEnergy, integral_const_mul,
    integral_add (integrable_jetSquare m a k hf hfc) (integrable_jetSquare m a k hg hgc)] using h

/-- Sign reversal preserves the scalar squared energy. -/
theorem scalarEnergy_neg (a : ι → E) (k : ℕ) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    scalarEnergy m a k (fun x => -f x) = scalarEnergy m a k f := by
  have he : (fun x => -f x) = fun x => (-1 : ℝ) * f x := by funext x; ring
  rw [he, scalarEnergy_eq_sum m a k (contDiff_const.mul hf) hc.mul_left,
    scalarEnergy_eq_sum m a k hf hc]
  simp only [derivative_const_mul _ _ hf, squareIntegral_const_mul, neg_one_sq, one_mul]

/-- The integrated actual coefficient pairing is controlled at the same derivative order. -/
theorem scalarEnergy_coupling_le (a : ι → E) (k : ℕ)
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) :
    scalarEnergy m a k (coupling b Y) ≤
      couplingConstant (ι := ι) k B * ∑ j, scalarEnergy m a k (Y.p j) := by
  have hp : Integrable (fun x => ∑ j, jetSquare a k (Y.p j) x) m :=
    integrable_finsetSum Finset.univ fun j _ => integrable_jetSquare m a k (hY.2.2 j) (hc.2.2 j)
  have h := integral_mono (integrable_jetSquare m a k (smooth_coupling hb hY) (compact_coupling b hc))
    (hp.const_mul (couplingConstant (ι := ι) k B)) (jetSquare_coupling_le a k hb hY hB hbB)
  simpa only [scalarEnergy, integral_const_mul, integral_finsetSum Finset.univ
    (fun j _ => integrable_jetSquare m a k (hY.2.2 j) (hc.2.2 j))] using h

/-- The actual reaction generator costs no spatial derivative order. -/
theorem derivativeEnergy_reactionGenerator_le (a : ι → E) (k : ℕ)
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) :
    derivativeEnergy m a k (reactionGenerator b Y) ≤
      (2 + 2 * couplingConstant (ι := ι) k B) * derivativeEnergy m a k Y := by
  have hs := scalarEnergy_sub_le m a k hY.1.neg (smooth_coupling hb hY) hc.1.neg (compact_coupling b hc)
  rw [scalarEnergy_neg m a k hY.1 hc.1] at hs
  have hcouple := scalarEnergy_coupling_le m a k hb hY hc hB hbB
  rw [derivativeEnergy_eq_scalarEnergy m a k (hY.reactionGenerator hb) (hc.reactionGenerator b),
    derivativeEnergy_eq_scalarEnergy m a k hY hc]
  have hz : scalarEnergy m a k (0 : E → ℝ) = 0 := scalarEnergy_zero m a k
  simp only [reactionGenerator, hz, Finset.sum_const_zero, add_zero]
  have hu := scalarEnergy_nonneg m a k Y.u
  have hv := scalarEnergy_nonneg m a k Y.v
  have hp : 0 ≤ ∑ j, scalarEnergy m a k (Y.p j) :=
    Finset.sum_nonneg fun j _ => scalarEnergy_nonneg m a k (Y.p j)
  have hC : 0 ≤ couplingConstant (ι := ι) k B := by unfold couplingConstant; positivity
  have hCu := mul_nonneg hC hu
  have hCv := mul_nonneg hC hv
  nlinarith

theorem scalarEnergy_add_le (a : ι → E) (k : ℕ) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    scalarEnergy m a k (fun x => f x + g x) ≤
      2 * (scalarEnergy m a k f + scalarEnergy m a k g) := by
  simpa only [sub_neg_eq_add, scalarEnergy_neg m a k hg hgc] using
    scalarEnergy_sub_le m a k hf hg.neg hfc hgc.neg

theorem derivativeEnergy_addState_le (a : ι → E) (k : ℕ)
    {X Y : State E ι} (hX : X.Smooth) (hY : Y.Smooth) (hcX : X.CompactSupport) (hcY : Y.CompactSupport) :
    derivativeEnergy m a k (addState X Y) ≤ 2 * (derivativeEnergy m a k X + derivativeEnergy m a k Y) := by
  rw [derivativeEnergy_eq_scalarEnergy m a k (hX.addState hY) (hcX.addState hcY),
    derivativeEnergy_eq_scalarEnergy m a k hX hcX, derivativeEnergy_eq_scalarEnergy m a k hY hcY]
  have hu := scalarEnergy_add_le m a k hX.1 hY.1 hcX.1 hcY.1
  have hv := scalarEnergy_add_le m a k hX.2.1 hY.2.1 hcX.2.1 hcY.2.1
  have hp := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun j _ => scalarEnergy_add_le m a k (hX.2.2 j) (hY.2.2 j) (hcX.2.2 j) (hcY.2.2 j))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hp
  dsimp only [addState]
  nlinarith

omit [BorelSpace E] [IsFiniteMeasureOnCompacts m] in
theorem derivativeEnergy_mono (a : ι → E) {k l : ℕ} (hkl : k ≤ l) (Y : State E ι) :
    derivativeEnergy m a k Y ≤ derivativeEnergy m a l Y :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun _ _ _ => Finset.sum_nonneg fun _ _ => energy_nonneg m _)

/-- A finite list of actual coordinate generators has a one-order energy bound. -/
theorem derivativeEnergy_sweepGenerator_le [DecidableEq ι]
    (a : ι → E) (k : ℕ) (js : List ι) {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m a k (sweepGenerator a js Y) ≤
      (4 : ℝ) ^ (js.length + 1) * (jetCount (ι := ι) k : ℝ) * derivativeEnergy m a (k + 1) Y := by
  have hE : 0 ≤ derivativeEnergy m a (k + 1) Y :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => energy_nonneg m _
  induction js with
  | nil =>
    have hz : derivativeEnergy m a k (zeroState : State E ι) = 0 := by
      simp [derivativeEnergy, energy, differentiate, derivative, zeroState, squareIntegral]
    simp only [sweepGenerator, hz]
    positivity
  | cons j js ih =>
    have hadd := derivativeEnergy_addState_le m a k (hY.coordinateGenerator (a j) j)
      (hY.sweepGenerator a js) (hc.coordinateGenerator (a j) j) (hc.sweepGenerator a js)
    have hj := derivativeEnergy_coordinateGenerator_le m a k j hY hc
    have hp : (1 : ℝ) ≤ 4 ^ (js.length + 1) := one_le_pow₀ (by norm_num)
    have hq : 0 ≤ (jetCount (ι := ι) k : ℝ) * derivativeEnergy m a (k + 1) Y := by positivity
    change derivativeEnergy m a k (addState _ _) ≤ _
    simp only [List.length_cons]
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hp hq]

end FiniteIndex

/-- An explicit, non-sharp constant for the generator of a finite splitting list. -/
def generatorConstant [Fintype ι] (js : List ι) (k : ℕ) (B : ℝ) : ℝ :=
  2 * (4 ^ (js.length + 1) * (jetCount (ι := ι) k : ℝ) + 2 + 2 * couplingConstant (ι := ι) k B)

section FiniteIndex

variable [Fintype ι] [DecidableEq ι]

/-- The actual split generator costs one spatial derivative order. -/
theorem derivativeEnergy_splitGenerator_le
    (a : ι → E) (js : List ι) (k : ℕ) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) :
    derivativeEnergy m a k (splitGenerator a b js Y) ≤
      generatorConstant (ι := ι) js k B * derivativeEnergy m a (k + 1) Y := by
  have hs := derivativeEnergy_sweepGenerator_le m a k js hY hc
  have hr := derivativeEnergy_reactionGenerator_le m a k hb hY hc hB hbB
  have hadd := derivativeEnergy_addState_le m a k (hY.sweepGenerator a js) (hY.reactionGenerator hb)
    (hc.sweepGenerator a js) (hc.reactionGenerator b)
  have hm := derivativeEnergy_mono m a (Nat.le_succ k) Y
  have hC : 0 ≤ couplingConstant (ι := ι) k B := by unfold couplingConstant; positivity
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 + 2 * couplingConstant (ι := ι) k B by positivity)
  change derivativeEnergy m a k (addState _ _) ≤ _
  unfold generatorConstant
  nlinarith

/-- Applying the actual split generator twice costs two spatial derivative orders. -/
theorem derivativeEnergy_splitGenerator_sq_le
    (a : ι → E) (js : List ι) (k : ℕ) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k + 1 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) :
    derivativeEnergy m a k (splitGenerator a b js (splitGenerator a b js Y)) ≤
      generatorConstant (ι := ι) js k B * generatorConstant (ι := ι) js (k + 1) B *
        derivativeEnergy m a (k + 2) Y := by
  have hs : (splitGenerator a b js Y).Smooth := (hY.sweepGenerator a js).addState (hY.reactionGenerator hb)
  have hcs : (splitGenerator a b js Y).CompactSupport := (hc.sweepGenerator a js).addState (hc.reactionGenerator b)
  have h₁ := derivativeEnergy_splitGenerator_le m a js k hb hs hcs hB
    (fun j r hr => hbB j r (by omega))
  have h₂ := derivativeEnergy_splitGenerator_le m a js (k + 1) hb hY hc hB hbB
  have hC : 0 ≤ generatorConstant (ι := ι) js k B := by
    unfold generatorConstant couplingConstant
    positivity
  exact h₁.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h₂ hC)

end FiniteIndex

/-- Either the reaction generator (`none`) or one coordinate generator (`some j`). -/
def elementaryGenerator [Fintype ι] [DecidableEq ι] (a : ι → E) (b : ι → E → ℝ)
    (i : Option ι) (Y : State E ι) : State E ι :=
  match i with
  | none => reactionGenerator b Y
  | some j => coordinateGenerator (a j) j Y

/-- A common bound for every elementary generator, useful for differentiated products. -/
def elementaryConstant [Fintype ι] (k : ℕ) (B : ℝ) : ℝ :=
  (jetCount (ι := ι) k : ℝ) + 2 + 2 * couplingConstant (ι := ι) k B

section FiniteIndex

variable [Fintype ι] [DecidableEq ι]

theorem derivativeEnergy_elementaryGenerator_le
    (a : ι → E) (k : ℕ) (i : Option ι) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) :
    derivativeEnergy m a k (elementaryGenerator a b i Y) ≤
      elementaryConstant (ι := ι) k B * derivativeEnergy m a (k + 1) Y := by
  have hE : 0 ≤ derivativeEnergy m a (k + 1) Y :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => energy_nonneg m _
  have hC : 0 ≤ couplingConstant (ι := ι) k B := by unfold couplingConstant; positivity
  cases i with
  | none =>
    have h := derivativeEnergy_reactionGenerator_le m a k hb hY hc hB hbB
    have hm := mul_le_mul_of_nonneg_left (derivativeEnergy_mono m a (Nat.le_succ k) Y)
      (show 0 ≤ 2 + 2 * couplingConstant (ι := ι) k B by positivity)
    have hq := mul_nonneg (Nat.cast_nonneg (jetCount (ι := ι) k)) hE
    change derivativeEnergy m a k (reactionGenerator b Y) ≤ _
    unfold elementaryConstant
    nlinarith
  | some j =>
    have h := derivativeEnergy_coordinateGenerator_le m a k j hY hc
    have hextra := mul_nonneg (show 0 ≤ 2 + 2 * couplingConstant (ι := ι) k B by positivity) hE
    change derivativeEnergy m a k (coordinateGenerator (a j) j Y) ≤ _
    unfold elementaryConstant
    nlinarith

/-- Every ordered pair of actual elementary generators, including mixed reaction/transport
pairs, obeys a two-order bound. No commutation of the two generators is assumed. -/
theorem derivativeEnergy_two_elementary_le
    (a : ι → E) (k : ℕ) (i j : Option ι) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k + 1 → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) :
    derivativeEnergy m a k (elementaryGenerator a b i (elementaryGenerator a b j Y)) ≤
      elementaryConstant (ι := ι) k B * elementaryConstant (ι := ι) (k + 1) B *
        derivativeEnergy m a (k + 2) Y := by
  have hs : (elementaryGenerator a b j Y).Smooth := by
    cases j with
    | none => exact hY.reactionGenerator hb
    | some j => exact hY.coordinateGenerator (a j) j
  have hcs : (elementaryGenerator a b j Y).CompactSupport := by
    cases j with
    | none => exact hc.reactionGenerator b
    | some j => exact hc.coordinateGenerator (a j) j
  have h₁ := derivativeEnergy_elementaryGenerator_le m a k i hb hs hcs hB
    (fun j r hr => hbB j r (by omega))
  have h₂ := derivativeEnergy_elementaryGenerator_le m a (k + 1) j hb hY hc hB hbB
  have hC : 0 ≤ elementaryConstant (ι := ι) k B := by unfold elementaryConstant couplingConstant; positivity
  exact h₁.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h₂ hC)

end FiniteIndex

end Integration
end FunctionalInequalities.Analysis.WaveSplitting
