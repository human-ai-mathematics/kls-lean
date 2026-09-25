import FunctionalInequalities.Analysis.WaveSplitting.Energy
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Ordered directional derivatives of products

Finite words retain the actual scalar derivatives used by the splitting energies.
-/
noncomputable section
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

/-- Repeated differentiation along a finite word of directions. -/
def wordDerivative (a : ι → E) : List ι → (E → ℝ) → E → ℝ
  | [], f => f
  | j :: w, f => fun x => fderiv ℝ (wordDerivative a w f) x (a j)

theorem smooth_wordDerivative (a : ι → E) (w : List ι) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (wordDerivative a w f) := by
  induction w with
  | nil => exact hf
  | cons j w ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- The recursive derivatives agree with evaluation of the iterated Fréchet derivative. -/
theorem wordDerivative_ofFn (a : ι → E) {n : ℕ} (w : Fin n → ι) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    wordDerivative a (List.ofFn w) f = derivative (fun i => a (w i)) f := by
  induction n with
  | zero => simp [wordDerivative]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [wordDerivative, ih]
    funext x
    symm
    exact DifferentiableAt.iteratedFDeriv_succ_apply_left'
      (hf.differentiable_iteratedFDeriv (by exact_mod_cast (ENat.natCast_lt_top n)) x)

/-- Every choice of which factor receives each derivative, retaining multiplicities. -/
def wordSplits : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | j :: w =>
      (wordSplits w).map (fun p => (j :: p.1, p.2)) ++
      (wordSplits w).map (fun p => (p.1, j :: p.2))

@[simp] theorem length_wordSplits (w : List ι) : (wordSplits w).length = 2 ^ w.length := by
  induction w with
  | nil => simp [wordSplits]
  | cons j w ih => simp [wordSplits, ih, pow_succ]; omega

private theorem smooth_list_sum {α : Type*} (l : List α) (F : α → E → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) :
    ContDiff ℝ ∞ (fun y => (l.map (fun i => F i y)).sum) := by
  induction l with
  | nil => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)))
  | cons j l ih => simpa using (hF j).add ih

private theorem fderiv_list_sum {α : Type*} (l : List α) (F : α → E → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (x : E) (v : E) :
    fderiv ℝ (fun y => (l.map (fun i => F i y)).sum) x v =
      (l.map (fun i => fderiv ℝ (F i) x v)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hs := smooth_list_sum l F hF
    simp only [List.map_cons, List.sum_cons]
    rw [fderiv_fun_add ((hF i).differentiable (by simp) x) (hs.differentiable (by simp) x)]
    simp [ih]

/-- The exact finite Leibniz expansion, without a multilinear operator norm. -/
theorem wordDerivative_mul (a : ι → E) (w : List ι) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    wordDerivative a w (fun x => f x * g x) = fun x =>
      ((wordSplits w).map (fun p => wordDerivative a p.1 f x *
        wordDerivative a p.2 g x)).sum := by
  induction w with
  | nil => simp [wordDerivative, wordSplits]
  | cons j w ih =>
    simp only [wordDerivative, ih]
    funext x
    rw [fderiv_list_sum (wordSplits w) (fun p y =>
      wordDerivative a p.1 f y * wordDerivative a p.2 g y) (fun p =>
      (smooth_wordDerivative a p.1 hf).mul (smooth_wordDerivative a p.2 hg))]
    simp only [wordSplits, List.map_append, List.map_map, List.sum_append,
      Function.comp_def, wordDerivative]
    rw [← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [fderiv_fun_mul
      ((smooth_wordDerivative a p.1 hf).differentiable (by simp) x)
      ((smooth_wordDerivative a p.2 hg).differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring

/-- Each factor receives at most the number of derivatives in the original word. -/
theorem lengths_mem_wordSplits (w : List ι) {p : List ι × List ι}
    (hp : p ∈ wordSplits w) : p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil => simp [wordSplits] at hp; subst p; rfl
  | cons j w ih =>
    simp only [wordSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;>
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg Nat.succ (ih hq)

private theorem list_sum_sq_le {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum ^ 2 ≤ (l.length : ℝ) * (l.map (fun i => f i ^ 2)).sum := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin l.length))
    (fun _ => (1 : ℝ)) (fun i => f (l.get i))
  have he (g : α → ℝ) : (∑ i : Fin l.length, g (l.get i)) = (l.map g).sum := by
    rw [← List.sum_ofFn]
    change (List.ofFn (g ∘ l.get)).sum = _
    rw [← List.map_ofFn, List.ofFn_get]
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, he f, he (fun i => f i ^ 2)] using h

/-- A scalar square estimate for the exact product expansion. -/
theorem wordDerivative_mul_sq_le (a : ι → E) (w : List ι) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    wordDerivative a w (fun y => f y * g y) x ^ 2 ≤
      (2 : ℝ) ^ w.length * ((wordSplits w).map (fun p =>
        wordDerivative a p.1 f x ^ 2 * wordDerivative a p.2 g x ^ 2)).sum := by
  rw [wordDerivative_mul a w hf hg]
  simpa [mul_pow] using list_sum_sq_le (wordSplits w)
    (fun p => wordDerivative a p.1 f x * wordDerivative a p.2 g x)

/-- Sum of scalar squared derivatives over all ordered coordinate tuples up to order `k`. -/
def jetSquare [Fintype ι] (a : ι → E) (k : ℕ) (f : E → ℝ) (x : E) : ℝ :=
  ∑ n ∈ Finset.range (k + 1), ∑ w : Fin n → ι, derivative (fun i => a (w i)) f x ^ 2

theorem jetSquare_nonneg [Fintype ι] (a : ι → E) (k : ℕ) (f : E → ℝ) (x : E) :
    0 ≤ jetSquare a k f x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem wordDerivative_sq_le_jetSquare [Fintype ι] (a : ι → E) (k : ℕ)
    (w : List ι) (hw : w.length ≤ k) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    wordDerivative a w f x ^ 2 ≤ jetSquare a k f x := by
  have he := congrFun (wordDerivative_ofFn a w.get hf) x
  rw [List.ofFn_get] at he
  rw [he]
  have h₁ : derivative (fun j => a (w.get j)) f x ^ 2 ≤
      ∑ i : Fin w.length → ι, derivative (fun j => a (i j)) f x ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (derivative (fun j => a (i j)) f x)) (Finset.mem_univ w.get)
  have h₂ : (∑ i : Fin w.length → ι, derivative (fun j => a (i j)) f x ^ 2) ≤
      jetSquare a k f x :=
    Finset.single_le_sum (f := fun n => ∑ i : Fin n → ι, derivative (fun j => a (i j)) f x ^ 2)
      (fun n _ => Finset.sum_nonneg fun (i : Fin n → ι) _ =>
        sq_nonneg (derivative (fun j => a (i j)) f x))
      (Finset.mem_range.mpr (show w.length < k + 1 by omega))
  exact h₁.trans h₂

/-- A bounded scalar coefficient multiplies the finite jet with an explicit finite constant. -/
theorem wordDerivative_mul_sq_le_jetSquare [Fintype ι] (a : ι → E) (k : ℕ)
    (w : List ι) (hw : w.length ≤ k) {b f : E → ℝ}
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ r : List ι, r.length ≤ k → ∀ x, wordDerivative a r b x ^ 2 ≤ B)
    (x : E) :
    wordDerivative a w (fun y => b y * f y) x ^ 2 ≤
      (4 : ℝ) ^ w.length * B * jetSquare a k f x := by
  have hs : ((wordSplits w).map (fun p => wordDerivative a p.1 b x ^ 2 *
      wordDerivative a p.2 f x ^ 2)).sum ≤
      ((wordSplits w).map (fun _ => B * jetSquare a k f x)).sum := by
    apply List.sum_le_sum
    intro p hp
    have hl := lengths_mem_wordSplits w hp
    exact mul_le_mul (hbB p.1 (by omega) x)
      (wordDerivative_sq_le_jetSquare a k p.2 (by omega) hf x) (sq_nonneg _) hB
  have h := (wordDerivative_mul_sq_le a w hb hf x).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))
  simpa [List.sum_replicate, ← mul_assoc, ← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num] using h

/-- Number of ordered coordinate tuples through order `k`, including the empty tuple. -/
def jetCount [Fintype ι] (k : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (k + 1), Fintype.card (Fin n → ι)

/-- Pointwise finite-jet multiplication bound; no direction-basis hypothesis is needed. -/
theorem jetSquare_mul_le [Fintype ι] (a : ι → E) (k : ℕ) {b f : E → ℝ}
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ r : List ι, r.length ≤ k → ∀ x, wordDerivative a r b x ^ 2 ≤ B)
    (x : E) :
    jetSquare a k (fun y => b y * f y) x ≤
      (jetCount (ι := ι) k : ℝ) * 4 ^ k * B * jetSquare a k f x := by
  have hh : ∀ n ∈ Finset.range (k + 1), ∀ w : Fin n → ι,
      derivative (fun i => a (w i)) (fun y => b y * f y) x ^ 2 ≤
        4 ^ k * B * jetSquare a k f x := by
    intro n hn w
    have hn' : n ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    have he := congrFun (wordDerivative_ofFn a w (hb.mul hf)) x
    rw [← he]
    exact (wordDerivative_mul_sq_le_jetSquare a k (List.ofFn w) (by simpa) hb hf hB hbB x).trans
      (by
        simp only [List.length_ofFn]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn') hB)
          (jetSquare_nonneg a k f x))
  calc
    _ ≤ ∑ n ∈ Finset.range (k + 1), ∑ _w : Fin n → ι,
        4 ^ k * B * jetSquare a k f x :=
      Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun w _ => hh n hn w
    _ = _ := by simp [jetCount, Nat.cast_sum, ← Finset.sum_mul, mul_assoc]

@[simp] theorem derivative_sum {α : Type*} (s : Finset α) {n : ℕ} (v : Fin n → E)
    (f : α → E → ℝ) (hf : ∀ j ∈ s, ContDiff ℝ ∞ (f j)) :
    derivative v (fun x => ∑ j ∈ s, f j x) = fun x => ∑ j ∈ s, derivative v (f j) x := by
  funext x
  simp only [derivative, iteratedFDeriv_fun_sum_apply (fun j hj =>
    ((hf j hj).of_le (show (n : WithTop ℕ∞) ≤ ∞ by
      exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt),
    sum_apply]

/-- Cauchy--Schwarz for a finite sum in the pointwise jet. -/
theorem jetSquare_sum_le [Fintype ι] {α : Type*} (s : Finset α)
    (a : ι → E) (k : ℕ) (f : α → E → ℝ) (hf : ∀ j ∈ s, ContDiff ℝ ∞ (f j)) (x : E) :
    jetSquare a k (fun y => ∑ j ∈ s, f j y) x ≤
      (s.card : ℝ) * ∑ j ∈ s, jetSquare a k (f j) x := by
  unfold jetSquare
  simp only [derivative_sum s _ f hf]
  calc
    _ ≤ ∑ n ∈ Finset.range (k + 1), ∑ w : Fin n → ι,
        (s.card : ℝ) * ∑ j ∈ s, derivative (fun i => a (w i)) (f j) x ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro w hw
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ))
        (fun j => derivative (fun i => a (w i)) (f j) x)
    _ = _ := by
      simp only [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]

section Integration
open MeasureTheory
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [IsFiniteMeasureOnCompacts m]

/-- Integrated scalar jet energy, with all ordered tuples counted. -/
def scalarEnergy [Fintype ι] (a : ι → E) (k : ℕ) (f : E → ℝ) : ℝ :=
  ∫ x, jetSquare a k f x ∂m

private theorem integrable_derivative_sq {n : ℕ} (v : Fin n → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun x => derivative v f x ^ 2) m := by
  have hs := (hasCompactSupport_derivative v hc).mul_left
    (f := derivative v f)
  simpa only [pow_two, Pi.mul_def] using
    ((continuous_derivative v hf).mul (continuous_derivative v hf)).integrable_of_hasCompactSupport hs

theorem integrable_jetSquare [Fintype ι] (a : ι → E) (k : ℕ) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Integrable (jetSquare a k f) m :=
  integrable_finsetSum _ fun _ _ => integrable_finsetSum _ fun _ _ =>
    integrable_derivative_sq m _ hf hc

/-- The integral agrees with the finite sum of squared derivative integrals. -/
theorem scalarEnergy_eq_sum [Fintype ι] (a : ι → E) (k : ℕ) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    scalarEnergy m a k f = ∑ n ∈ Finset.range (k + 1), ∑ w : Fin n → ι,
      squareIntegral m (derivative (fun i => a (w i)) f) := by
  unfold scalarEnergy jetSquare
  rw [integral_finsetSum _ (fun _ _ => integrable_finsetSum _ fun _ _ =>
    integrable_derivative_sq m _ hf hc)]
  congr 1
  funext n
  exact integral_finsetSum _ fun _ _ => integrable_derivative_sq m _ hf hc

/-- Actual integrated multiplication bound from raw bounds on coefficient derivatives. -/
theorem scalarEnergy_mul_le [Fintype ι] (a : ι → E) (k : ℕ) {b f : E → ℝ}
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ r : List ι, r.length ≤ k → ∀ x, wordDerivative a r b x ^ 2 ≤ B) :
    scalarEnergy m a k (fun x => b x * f x) ≤
      (jetCount (ι := ι) k : ℝ) * 4 ^ k * B * scalarEnergy m a k f := by
  have h := integral_mono (integrable_jetSquare m a k (hb.mul hf) hc.mul_left)
    ((integrable_jetSquare m a k hf hc).const_mul ((jetCount (ι := ι) k : ℝ) * 4 ^ k * B))
    (jetSquare_mul_le a k hb hf hB hbB)
  simpa only [scalarEnergy, integral_const_mul] using h

end Integration
end FunctionalInequalities.Analysis.WaveSplitting
