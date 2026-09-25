import FunctionalInequalities.Analysis.WaveSplitting.Product

/-! # Finite-order stability of the actual reaction and splitting flows -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Explicit coupling constant for bounded squared coefficient derivatives through order `k`. -/
def couplingConstant (k : ℕ) (B : ℝ) : ℝ :=
  Fintype.card ι * (jetCount (ι := ι) k : ℝ) * 4 ^ k * B

private theorem smooth_coupling {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) : ContDiff ℝ ∞ (coupling b Y) :=
  ContDiff.sum fun j _ => (hb j).mul (hY.2.2 j)

/-- The scalar coefficient pairing satisfies the actual finite-jet product bound. -/
theorem jetSquare_coupling_le (a : ι → E) (k : ℕ) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) (x : E) :
    jetSquare a k (coupling b Y) x ≤
      couplingConstant (ι := ι) k B * ∑ j, jetSquare a k (Y.p j) x := by
  have h := jetSquare_sum_le Finset.univ a k (fun j y => b j y * Y.p j y)
    (fun j _ => (hb j).mul (hY.2.2 j)) x
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun j _ => jetSquare_mul_le a k (hb j) (hY.2.2 j) hB (hbB j) x)
  have hh := h.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  change jetSquare a k (fun y => ∑ j, b j y * Y.p j y) x ≤ _
  simpa only [Finset.card_univ, couplingConstant, ← Finset.mul_sum, mul_assoc] using hh

private theorem derivative_reaction_pair {n : ℕ} (v : Fin n → E) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth)
    (x : E) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    derivative v (reaction b t Y).u x ^ 2 + derivative v (reaction b t Y).v x ^ 2 ≤
      (1 + t) * (derivative v Y.u x ^ 2 + derivative v Y.v x ^ 2) +
      4 * t * derivative v (coupling b Y) x ^ 2 := by
  have hc := smooth_coupling hb hY
  let Z : State E Unit := ⟨derivative v Y.u, derivative v Y.v,
    fun _ => derivative v (coupling b Y)⟩
  have h := reaction_pair_bound (fun (_ : Unit) (_ : E) => (1 : ℝ)) Z x ht ht1
  have hu : ContDiff ℝ ∞ (fun y => Real.cos t * Y.u y + Real.sin t * Y.v y) :=
    (contDiff_const.mul hY.1).add (contDiff_const.mul hY.2.1)
  change derivative v (fun y => Real.cos t * Y.u y + Real.sin t * Y.v y +
    (Real.cos t - 1) * coupling b Y y) x ^ 2 +
    derivative v (fun y => -Real.sin t * Y.u y + Real.cos t * Y.v y -
      Real.sin t * coupling b Y y) x ^ 2 ≤ _
  rw [derivative_add v hu (contDiff_const.mul hc),
    derivative_sub v ((contDiff_const.mul hY.1).add (contDiff_const.mul hY.2.1))
      (contDiff_const.mul hc)]
  simp only [derivative_add v (contDiff_const.mul hY.1) (contDiff_const.mul hY.2.1),
    derivative_const_mul v _ hY.1, derivative_const_mul v _ hY.2.1,
    derivative_const_mul v _ hc]
  simpa only [reaction, Z, coupling, Fintype.sum_unique, one_mul] using h

/-- High-order pointwise reaction estimate, before integration. -/
theorem jetSquare_reaction_le (a : ι → E) (k : ℕ) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth)
    {B t : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : E) :
    jetSquare a k (reaction b t Y).u x + jetSquare a k (reaction b t Y).v x +
      ∑ j, jetSquare a k ((reaction b t Y).p j) x ≤
    (1 + (1 + 4 * couplingConstant (ι := ι) k B) * t) *
      (jetSquare a k Y.u x + jetSquare a k Y.v x + ∑ j, jetSquare a k (Y.p j) x) := by
  have h := Finset.sum_le_sum (s := Finset.range (k + 1)) (fun n _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → ι)))
      (fun w _ => derivative_reaction_pair (fun i => a (w i)) hb hY x ht ht1))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  change jetSquare a k (reaction b t Y).u x + jetSquare a k (reaction b t Y).v x ≤
    (1 + t) * (jetSquare a k Y.u x + jetSquare a k Y.v x) +
    4 * t * jetSquare a k (coupling b Y) x at h
  have hcouple := jetSquare_coupling_le a k hb hY hB hbB x
  have hu := jetSquare_nonneg a k Y.u x
  have hv := jetSquare_nonneg a k Y.v x
  have hp : 0 ≤ ∑ j, jetSquare a k (Y.p j) x :=
    Finset.sum_nonneg fun j _ => jetSquare_nonneg a k (Y.p j) x
  have hC : 0 ≤ couplingConstant (ι := ι) k B := by unfold couplingConstant; positivity
  have hc' := mul_le_mul_of_nonneg_left hcouple (show 0 ≤ 4 * t by positivity)
  have hextra : 0 ≤ 4 * couplingConstant (ι := ι) k B * t *
      (jetSquare a k Y.u x + jetSquare a k Y.v x) := by positivity
  have hextrap := mul_nonneg ht hp
  change _ + _ + ∑ j, jetSquare a k (Y.p j) x ≤ _
  nlinarith

section Integration
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [IsFiniteMeasureOnCompacts m]

/-- The state energy is the sum of its scalar component energies. -/
theorem derivativeEnergy_eq_scalarEnergy (a : ι → E) (k : ℕ) {Y : State E ι}
    (hY : Y.Smooth) (hc : Y.CompactSupport) :
    derivativeEnergy m a k Y = scalarEnergy m a k Y.u + scalarEnergy m a k Y.v +
      ∑ j, scalarEnergy m a k (Y.p j) := by
  rw [scalarEnergy_eq_sum m a k hY.1 hc.1, scalarEnergy_eq_sum m a k hY.2.1 hc.2.1]
  simp only [scalarEnergy_eq_sum m a k (hY.2.2 _) (hc.2.2 _), derivativeEnergy,
    energy, differentiate, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]

private theorem integral_stateJet (a : ι → E) (k : ℕ) {Y : State E ι}
    (hY : Y.Smooth) (hc : Y.CompactSupport) :
    (∫ x, jetSquare a k Y.u x + jetSquare a k Y.v x + ∑ j, jetSquare a k (Y.p j) x ∂m) =
      derivativeEnergy m a k Y := by
  have huv : Integrable (fun x => jetSquare a k Y.u x + jetSquare a k Y.v x) m :=
    (integrable_jetSquare m a k hY.1 hc.1).add (integrable_jetSquare m a k hY.2.1 hc.2.1)
  have hp : Integrable (fun x => ∑ j, jetSquare a k (Y.p j) x) m :=
    integrable_finsetSum Finset.univ fun j _ => integrable_jetSquare m a k (hY.2.2 j) (hc.2.2 j)
  rw [integral_add huv hp,
    integral_add (integrable_jetSquare m a k hY.1 hc.1)
      (integrable_jetSquare m a k hY.2.1 hc.2.1),
    integral_finsetSum Finset.univ (fun j _ => integrable_jetSquare m a k (hY.2.2 j) (hc.2.2 j))]
  exact (derivativeEnergy_eq_scalarEnergy m a k hY hc).symm

/-- Stability of the actual reaction at every finite derivative order. -/
theorem derivativeEnergy_reaction_le (a : ι → E) (k : ℕ) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth)
    (hc : Y.CompactSupport) {B t : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    derivativeEnergy m a k (reaction b t Y) ≤
      (1 + (1 + 4 * couplingConstant (ι := ι) k B) * t) * derivativeEnergy m a k Y := by
  have hint {Z : State E ι} (hs : Z.Smooth) (hc : Z.CompactSupport) :
      Integrable (fun x => jetSquare a k Z.u x + jetSquare a k Z.v x +
        ∑ j, jetSquare a k (Z.p j) x) m :=
    ((integrable_jetSquare m a k hs.1 hc.1).add
      (integrable_jetSquare m a k hs.2.1 hc.2.1)).add
      (integrable_finsetSum Finset.univ fun j _ => integrable_jetSquare m a k (hs.2.2 j) (hc.2.2 j))
  have h := integral_mono (hint (hY.reaction hb t) (hc.reaction b t))
    ((hint hY hc).const_mul _) (jetSquare_reaction_le a k hb hY hB hbB ht ht1)
  simpa only [integral_const_mul, integral_stateJet m a k hY hc,
    integral_stateJet m a k (hY.reaction hb t) (hc.reaction b t)] using h

/-- A full split step has the same finite-order stability factor as its reaction. -/
theorem derivativeEnergy_step_le [m.IsAddRightInvariant] [DecidableEq ι]
    (a : ι → E) (order : ℕ) (js : List ι) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) {B t : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ j r, r.length ≤ order → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    derivativeEnergy m a order (step a b js t Y) ≤ (1 + (1 + 4 * couplingConstant (ι := ι) order B) * t) * derivativeEnergy m a order Y := by
  have h := derivativeEnergy_reaction_le m a order hb (hY.sweep a t js) (hc.sweep a t js) hB0 hB ht ht1
  rwa [derivativeEnergy_sweep m a a order js t hY hc] at h

/-- Iterating actual split steps gives a quantitative bound, without assuming stability. -/
theorem derivativeEnergy_nodes_le [m.IsAddRightInvariant] [DecidableEq ι]
    (a : ι → E) (order : ℕ) (js : List ι) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) {B δ : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ j r, r.length ≤ order → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    derivativeEnergy m a order (nodes a b js δ Y k) ≤ (1 + (1 + 4 * couplingConstant (ι := ι) order B) * δ) ^ k * derivativeEnergy m a order Y := by
  have hC : 0 ≤ couplingConstant (ι := ι) order B := by unfold couplingConstant; positivity
  induction k with
  | zero => simp [nodes]
  | succ k ih =>
    calc
      derivativeEnergy m a order (nodes a b js δ Y (k + 1)) ≤
          (1 + (1 + 4 * couplingConstant (ι := ι) order B) * δ) * derivativeEnergy m a order (nodes a b js δ Y k) :=
        derivativeEnergy_step_le m a order js hb (hY.nodes a hb js δ k) (hc.nodes a b js δ k) hB0 hB hδ hδ1
      _ ≤ (1 + (1 + 4 * couplingConstant (ι := ι) order B) * δ) * ((1 + (1 + 4 * couplingConstant (ι := ι) order B) * δ) ^ k * derivativeEnergy m a order Y) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ]; ring

/-- The finite-order grid bound depends on elapsed time `k*δ`, not separately on the mesh size. -/
theorem derivativeEnergy_nodes_le_exp [m.IsAddRightInvariant] [DecidableEq ι]
    (a : ι → E) (order : ℕ) (js : List ι) {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    {Y : State E ι} (hY : Y.Smooth) (hc : Y.CompactSupport) {B δ : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ j r, r.length ≤ order → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    derivativeEnergy m a order (nodes a b js δ Y k) ≤ Real.exp ((1 + 4 * couplingConstant (ι := ι) order B) * (k * δ)) * derivativeEnergy m a order Y := by
  have hC : 0 ≤ couplingConstant (ι := ι) order B := by unfold couplingConstant; positivity
  apply (derivativeEnergy_nodes_le m a order js hb hY hc hB0 hB hδ hδ1 k).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => energy_nonneg m _)
  have hbase : 1 + (1 + 4 * couplingConstant (ι := ι) order B) * δ ≤ Real.exp ((1 + 4 * couplingConstant (ι := ι) order B) * δ) := by
    simpa only [add_comm] using Real.add_one_le_exp ((1 + 4 * couplingConstant (ι := ι) order B) * δ)
  have hpow := pow_le_pow_left₀ (show 0 ≤ 1 + (1 + 4 * couplingConstant (ι := ι) order B) * δ by positivity) hbase k
  rw [← Real.exp_nat_mul] at hpow
  convert hpow using 1
  congr 1
  ring

/-- The same mesh-independent estimate holds inside each actual smooth cell. -/
theorem derivativeEnergy_cell_le_exp [m.IsAddRightInvariant] [DecidableEq ι]
    (a : ι → E) (order : ℕ) (js : List ι) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι} (hY : Y.Smooth)
    (hc : Y.CompactSupport) {B δ θ : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j r, r.length ≤ order → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (k : ℕ) :
    derivativeEnergy m a order (cell a b js δ Y k θ) ≤
      Real.exp ((1 + 4 * couplingConstant (ι := ι) order B) * (k * δ + θ)) *
        derivativeEnergy m a order Y := by
  let C := 1 + 4 * couplingConstant (ι := ι) order B
  have hC : 0 ≤ C := by dsimp [C, couplingConstant]; positivity
  have hE : 0 ≤ derivativeEnergy m a order Y :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => energy_nonneg m _
  have hn := derivativeEnergy_nodes_le_exp m a order js hb hY hc hB0 hB hδ hδ1 k
  have hs := derivativeEnergy_step_le m a order js hb (hY.nodes a hb js δ k)
    (hc.nodes a b js δ k) hB0 hB hθ hθ1
  calc
    _ ≤ (1 + C * θ) * derivativeEnergy m a order (nodes a b js δ Y k) := hs
    _ ≤ (1 + C * θ) * (Real.exp (C * (k * δ)) * derivativeEnergy m a order Y) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ ≤ Real.exp (C * θ) * (Real.exp (C * (k * δ)) * derivativeEnergy m a order Y) :=
      mul_le_mul_of_nonneg_right (by simpa [add_comm] using Real.add_one_le_exp (C * θ))
        (mul_nonneg (Real.exp_pos _).le hE)
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

end Integration
end FunctionalInequalities.Analysis.WaveSplitting
