import FunctionalInequalities.Analysis.EuclideanCoordinates
import FunctionalInequalities.Analysis.Holder.Cutoff
import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Holder
import FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates

/-!
# Locally Hölder derivatives: the `C^{m,α}_loc` invariant of the Schauder bootstrap

Supporting Letwin, arXiv:2607.24164v1, Lemma 2.2 (strong regular class), through the higher-order
Schauder bootstrap of Gilbarg–Trudinger, Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16,
pp. 463–464. The induction `C^{k,α}_loc ⇒ C^{k+1,α}_loc` for the moment potential needs a class of
functions closed under the algebraic operations appearing in the differentiated equations.

* `LocHolderMap F`: on every ball `ball 0 s` the map `F : ℝⁿ → G` is Hölder with some exponent
  `η ∈ (0, 1)` and some constant (both may depend on `s`);
* `LocHolderDeriv m h`: `h : ℝⁿ → ℝ` is `C^m` and `iteratedFDeriv ℝ m h` is `LocHolderMap`
  (locally `C^{m,α}` with a ball-dependent exponent);
* closure: sums, products, inverses of nonvanishing functions, finite sums and products,
  constants, `C¹` maps (`LocHolderMap.of_contDiff_one`), compositions with `C¹` maps;
* the derivative calculus: `LocHolderDeriv.directional` (`C^{m+1,α} ⇒ D_e h ∈ C^{m,α}`),
  `LocHolderDeriv.of_coordinate` (`h ∈ C¹` and all `D_{e_i} h ∈ C^{m,α} ⇒ h ∈ C^{m+1,α}`),
  `LocHolderDeriv.of_le` (`C^{m',α} ⊆ C^{m,α}` for `m ≤ m'`), `LocHolderDeriv.comp_gradient`
  (`G ∘ ∇u ∈ C^{m,α}` for smooth `G` and `u ∈ C^{m+1,α}`), `LocHolderDeriv.hessianEntry`,
  `LocHolderDeriv.det`, `LocHolderDeriv.matrix_inv_entry` (entries of the inverse of a matrix
  field with `C^{m,α}` entries and nonvanishing determinant);
* norm identities relating `iteratedFDeriv` to nested `fderiv` (`norm_iteratedFDeriv_two_sub`,
  `norm_iteratedFDeriv_three_sub`) and the patching lemma `holder_of_local_holder_of_bound`.

Only the function class and its calculus are set up here; no equation and no regularity gain is
proved in this module.
-/

/-- Closes order goals between natural-number casts into `WithTop ℕ∞`. -/
local macro "nat_cast_le" : tactic => `(tactic| first | (norm_cast; done) | (norm_cast; omega))

noncomputable section

namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms

open Set Metric Filter Topology
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
open scoped NNReal ContDiff BigOperators


section NormIdentities

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The zeroth iterated derivative is an isometric copy of the function. -/
theorem norm_iteratedFDeriv_zero_sub (f : X → F) (x y : X) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f y‖ = ‖f x - f y‖ := by
  rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]

/-- Differences of the `(m+1)`-st iterated derivative are isometric to differences of the `m`-th
iterated derivative of the derivative. -/
theorem norm_iteratedFDeriv_succ_sub (f : X → F) (m : ℕ) (x y : X) :
    ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) f y‖ =
      ‖iteratedFDeriv ℝ m (fderiv ℝ f) x - iteratedFDeriv ℝ m (fderiv ℝ f) y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    Function.comp_apply, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]

theorem norm_iteratedFDeriv_one_sub (f : X → F) (x y : X) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
  rw [norm_iteratedFDeriv_succ_sub, norm_iteratedFDeriv_zero_sub]

theorem norm_iteratedFDeriv_two_sub (f : X → F) (x y : X) :
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ =
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ :=
  (norm_iteratedFDeriv_succ_sub f 1 x y).trans (norm_iteratedFDeriv_one_sub (fderiv ℝ f) x y)

end NormIdentities

section HolderTools

variable {X : Type*} [NormedAddCommGroup X]

/-- Lowering the Hölder exponent on a set of diameter at most `D`. -/
theorem holder_lower_exponent {F : Type*} [NormedAddCommGroup F] {G : X → F} {s : Set X}
    {C D η η' : ℝ} (hC : 0 ≤ C) (hηη : η' ≤ η) (hη : 0 < η)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, ‖x - y‖ ≤ D)
    (h : ∀ x ∈ s, ∀ y ∈ s, ‖G x - G y‖ ≤ C * ‖x - y‖ ^ η) :
    ∀ x ∈ s, ∀ y ∈ s, ‖G x - G y‖ ≤ C * D ^ (η - η') * ‖x - y‖ ^ η' := by
  intro x hx y hy
  have ht : 0 ≤ ‖x - y‖ := norm_nonneg _
  have e : ‖x - y‖ ^ η = ‖x - y‖ ^ (η - η') * ‖x - y‖ ^ η' := by
    rw [← Real.rpow_add' ht (by rw [sub_add_cancel]; exact hη.ne')]
    rw [sub_add_cancel]
  have h2 : ‖x - y‖ ^ (η - η') ≤ D ^ (η - η') :=
    Real.rpow_le_rpow ht (hdiam x hx y hy) (by linarith)
  calc ‖G x - G y‖ ≤ C * ‖x - y‖ ^ η := h x hx y hy
    _ = C * (‖x - y‖ ^ (η - η') * ‖x - y‖ ^ η') := by rw [e]
    _ ≤ C * (D ^ (η - η') * ‖x - y‖ ^ η') := by
        gcongr
    _ = C * D ^ (η - η') * ‖x - y‖ ^ η' := by ring

/-- A common positive exponent below finitely many exponents in `(0, 1)`. -/
theorem exists_common_exponent {ι : Type*} [Fintype ι] (η : ι → ℝ≥0) (h0 : ∀ i, 0 < η i)
    (h1 : ∀ i, η i < 1) : ∃ η₀ : ℝ≥0, 0 < η₀ ∧ η₀ < 1 ∧ ∀ i, η₀ ≤ η i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1 / 2, by norm_num, by norm_num, fun i => (IsEmpty.false i).elim⟩
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty η, ?_, ?_, fun i => Finset.inf'_le _ (by simp)⟩
    · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty η
      rw [hi]; exact h0 i
    · obtain ⟨i⟩ := hι
      exact (Finset.inf'_le _ (Finset.mem_univ i)).trans_lt (h1 i)

/-- Patching: a map bounded by `K` and `η`-Hölder with constant `K` on every ball `ball c R`
centred in `ball 0 s` is `η`-Hölder on `ball 0 s` with constant `K (1 + 2 R^{-η})`. -/
theorem holder_of_local_holder_of_bound {F : Type*} [NormedAddCommGroup F] {G : X → F}
    {s R K η : ℝ} (hR : 0 < R) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (h : ∀ c ∈ ball (0:X) s, (∀ x ∈ ball c R, ‖G x‖ ≤ K) ∧
      ∀ x ∈ ball c R, ∀ y ∈ ball c R, ‖G x - G y‖ ≤ K * ‖x - y‖ ^ η) :
    ∀ x ∈ ball (0:X) s, ∀ y ∈ ball (0:X) s,
      ‖G x - G y‖ ≤ K * (1 + 2 * R ^ (-η)) * ‖x - y‖ ^ η := by
  intro x hx y hy
  have hpow : 0 ≤ ‖x - y‖ ^ η := by positivity
  have hRη : 0 ≤ R ^ (-η) := by positivity
  by_cases hxy : ‖x - y‖ < R
  · have hy' : y ∈ ball x R := by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hxy
    have := (h x hx).2 x (mem_ball_self hR) y hy'
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hpow)
    nlinarith
  · have hxy : R ≤ ‖x - y‖ := not_lt.mp hxy
    have hbx := (h x hx).1 x (mem_ball_self hR)
    have hby := (h y hy).1 y (mem_ball_self hR)
    have hsub := norm_sub_le (G x) (G y)
    -- `1 ≤ R^{-η} ‖x - y‖^η`
    have h1 : R ^ η ≤ ‖x - y‖ ^ η := Real.rpow_le_rpow hR.le hxy hη
    have h2 : R ^ (-η) * R ^ η = 1 := by
      rw [← Real.rpow_add hR]; simp
    have h3 : 1 ≤ R ^ (-η) * ‖x - y‖ ^ η := by
      calc (1:ℝ) = R ^ (-η) * R ^ η := h2.symm
        _ ≤ R ^ (-η) * ‖x - y‖ ^ η := mul_le_mul_of_nonneg_left h1 hRη
    calc ‖G x - G y‖ ≤ 2 * K := by linarith
      _ = (2 * K) * 1 := (mul_one _).symm
      _ ≤ (2 * K) * (R ^ (-η) * ‖x - y‖ ^ η) := by gcongr
      _ ≤ K * (1 + 2 * R ^ (-η)) * ‖x - y‖ ^ η := by nlinarith

end HolderTools

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Differences of the third iterated derivative of a real function on `ℝⁿ` are isometric to
differences of the nested third derivative. -/
theorem norm_iteratedFDeriv_three_sub (f : E → ℝ) (x y : E) :
    ‖iteratedFDeriv ℝ 3 f x - iteratedFDeriv ℝ 3 f y‖ =
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y‖ :=
  (norm_iteratedFDeriv_succ_sub f 2 x y).trans (norm_iteratedFDeriv_two_sub (fderiv ℝ f) x y)

/-- `k ≤ ∞` in `WithTop ℕ∞`. -/
theorem natCast_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by
  change ((k : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

theorem natCast_succ_le_infty (k : ℕ) : (k : WithTop ℕ∞) + 1 ≤ ∞ := by
  have := natCast_le_infty (k + 1)
  push_cast at this
  exact this

section LocHolderMap

/-- A map `F : ℝⁿ → G` is **locally Hölder** if on every ball `ball 0 s` it is Hölder with some
exponent `η ∈ (0, 1)` and some constant (both may depend on `s`). -/
def LocHolderMap {G : Type*} [NormedAddCommGroup G] (F : E → G) : Prop :=
  ∀ s : ℝ, 0 < s → ∃ η : ℝ≥0, 0 < η ∧ η < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ ball (0:E) s, ∀ y ∈ ball (0:E) s, ‖F x - F y‖ ≤ C * ‖x - y‖ ^ (η:ℝ)

variable {G : Type*} [NormedAddCommGroup G]

/-- Two points of `ball 0 s` are at distance less than `2s`. -/
theorem norm_sub_le_two_mul_of_mem_ball {x y : E} {s : ℝ} (hx : x ∈ ball (0:E) s)
    (hy : y ∈ ball (0:E) s) : ‖x - y‖ ≤ 2 * s := by
  rw [mem_ball_zero_iff] at hx hy
  calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    _ ≤ 2 * s := by linarith

/-- **Domination by a finite family.** If on every ball `ball 0 s` the differences of `G'` are
dominated by a nonnegative combination of the differences of finitely many locally Hölder maps,
then `G'` is locally Hölder. -/
theorem LocHolderMap.of_le_sum {ι : Type*} [Fintype ι] {G' : Type*} [NormedAddCommGroup G']
    {F : ι → E → G} {G₀ : E → G'} (hF : ∀ i, LocHolderMap (F i))
    (hle : ∀ s : ℝ, 0 < s → ∃ L : ι → ℝ, (∀ i, 0 ≤ L i) ∧
      ∀ x ∈ ball (0:E) s, ∀ y ∈ ball (0:E) s,
        ‖G₀ x - G₀ y‖ ≤ ∑ i, L i * ‖F i x - F i y‖) :
    LocHolderMap G₀ := by
  intro s hs
  choose η hη0 hη1 C hC hhol using fun i => hF i s hs
  obtain ⟨η₀, hη₀0, hη₀1, hη₀le⟩ := exists_common_exponent η hη0 hη1
  obtain ⟨L, hL, hle⟩ := hle s hs
  have hdiam : ∀ x ∈ ball (0:E) s, ∀ y ∈ ball (0:E) s, ‖x - y‖ ≤ 2 * s :=
    fun x hx y hy => norm_sub_le_two_mul_of_mem_ball hx hy
  have hlow : ∀ i, ∀ x ∈ ball (0:E) s, ∀ y ∈ ball (0:E) s,
      ‖F i x - F i y‖ ≤ C i * (2 * s) ^ ((η i : ℝ) - η₀) * ‖x - y‖ ^ (η₀:ℝ) := fun i =>
    holder_lower_exponent (hC i) (by exact_mod_cast hη₀le i) (hη0 i) hdiam (hhol i)
  refine ⟨η₀, hη₀0, hη₀1, ∑ i, L i * (C i * (2 * s) ^ ((η i : ℝ) - η₀)),
    Finset.sum_nonneg fun i _ => mul_nonneg (hL i) (mul_nonneg (hC i) (by positivity)), ?_⟩
  intro x hx y hy
  refine (hle x hx y hy).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hlow i x hx y hy) (hL i)

/-- Domination by a single locally Hölder map. -/
theorem LocHolderMap.of_le_norm {G' : Type*} [NormedAddCommGroup G'] {F : E → G} {G₀ : E → G'}
    (hF : LocHolderMap F) {L : ℝ} (hL : 0 ≤ L)
    (hle : ∀ x y, ‖G₀ x - G₀ y‖ ≤ L * ‖F x - F y‖) : LocHolderMap G₀ :=
  LocHolderMap.of_le_sum (ι := Unit) (fun _ => hF) fun _ _ =>
    ⟨fun _ => L, fun _ => hL, fun x _ y _ => by simpa using hle x y⟩

theorem LocHolderMap.add {F₁ F₂ : E → G} (h₁ : LocHolderMap F₁) (h₂ : LocHolderMap F₂) :
    LocHolderMap (fun x => F₁ x + F₂ x) := by
  refine LocHolderMap.of_le_sum (ι := Fin 2) (F := ![F₁, F₂]) (fun i => by fin_cases i <;> simpa)
    fun s _ => ⟨fun _ => 1, fun _ => zero_le_one, fun x _ y _ => ?_⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
  calc ‖F₁ x + F₂ x - (F₁ y + F₂ y)‖ = ‖(F₁ x - F₁ y) + (F₂ x - F₂ y)‖ := by congr 1; abel
    _ ≤ ‖F₁ x - F₁ y‖ + ‖F₂ x - F₂ y‖ := norm_add_le _ _

theorem LocHolderMap.neg {F : E → G} (h : LocHolderMap F) : LocHolderMap (fun x => -F x) :=
  h.of_le_norm zero_le_one fun x y => by rw [one_mul, neg_sub_neg, norm_sub_rev]

theorem LocHolderMap.sub {F₁ F₂ : E → G} (h₁ : LocHolderMap F₁) (h₂ : LocHolderMap F₂) :
    LocHolderMap (fun x => F₁ x - F₂ x) := by
  have := h₁.add h₂.neg
  simpa [sub_eq_add_neg] using this

theorem LocHolderMap.const (c : G) : LocHolderMap (fun _ : E => c) :=
  fun _ _ => ⟨1 / 2, by norm_num, by norm_num, 0, le_rfl, fun x _ y _ => by simp⟩

theorem LocHolderMap.const_smul {F : E → G} [NormedSpace ℝ G] (h : LocHolderMap F) (c : ℝ) :
    LocHolderMap (fun x => c • F x) :=
  h.of_le_norm (norm_nonneg c) fun x y => by rw [← smul_sub, norm_smul]

theorem LocHolderMap.finset_sum {ι : Type*} (t : Finset ι) {F : ι → E → G}
    (h : ∀ i ∈ t, LocHolderMap (F i)) : LocHolderMap (fun x => ∑ i ∈ t, F i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using LocHolderMap.const (0 : G)
  | insert a t ha ih =>
      have := (h a (Finset.mem_insert_self a t)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using this

/-- A locally Hölder map is bounded on every ball. -/
theorem LocHolderMap.exists_bound {F : E → G} (h : LocHolderMap F) {s : ℝ} (hs : 0 < s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ ball (0:E) s, ‖F x‖ ≤ B := by
  obtain ⟨η, hη0, hη1, C, hC, hhol⟩ := h s hs
  refine ⟨‖F 0‖ + C * (2 * s) ^ (η:ℝ), by positivity, fun x hx => ?_⟩
  have h1 := hhol x hx 0 (mem_ball_self hs)
  have h2 : ‖x - 0‖ ^ (η:ℝ) ≤ (2 * s) ^ (η:ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le_two_mul_of_mem_ball hx (mem_ball_self hs))
      η.coe_nonneg
  calc ‖F x‖ = ‖(F x - F 0) + F 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖F x - F 0‖ + ‖F 0‖ := norm_add_le _ _
    _ ≤ C * (2 * s) ^ (η:ℝ) + ‖F 0‖ := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hC)
    _ = ‖F 0‖ + C * (2 * s) ^ (η:ℝ) := by ring

/-- Products of locally Hölder real functions are locally Hölder. -/
theorem LocHolderMap.mul {F₁ F₂ : E → ℝ} (h₁ : LocHolderMap F₁) (h₂ : LocHolderMap F₂) :
    LocHolderMap (fun x => F₁ x * F₂ x) := by
  refine LocHolderMap.of_le_sum (ι := Fin 2) (F := ![F₁, F₂]) (fun i => by fin_cases i <;> simpa)
    fun s hs => ?_
  obtain ⟨B₁, hB₁, hb₁⟩ := h₁.exists_bound hs
  obtain ⟨B₂, hB₂, hb₂⟩ := h₂.exists_bound hs
  refine ⟨![B₂, B₁], fun i => by fin_cases i <;> simpa, fun x hx y hy => ?_⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs]
  have e : F₁ x * F₂ x - F₁ y * F₂ y = (F₁ x - F₁ y) * F₂ y + F₁ x * (F₂ x - F₂ y) := by ring
  rw [e]
  calc |(F₁ x - F₁ y) * F₂ y + F₁ x * (F₂ x - F₂ y)|
      ≤ |(F₁ x - F₁ y) * F₂ y| + |F₁ x * (F₂ x - F₂ y)| := abs_add_le _ _
    _ = |F₁ x - F₁ y| * |F₂ y| + |F₁ x| * |F₂ x - F₂ y| := by rw [abs_mul, abs_mul]
    _ ≤ |F₁ x - F₁ y| * B₂ + B₁ * |F₂ x - F₂ y| := by
        gcongr
        · exact hb₂ y hy
        · exact hb₁ x hx
    _ = B₂ * |F₁ x - F₁ y| + B₁ * |F₂ x - F₂ y| := by ring

/-- A locally Hölder map is continuous. -/
theorem LocHolderMap.continuous {F : E → G} (h : LocHolderMap F) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨η, hη0, hη1, C, hC, hhol⟩ := h (‖x‖ + 1) (by positivity)
  have hx : x ∈ ball (0:E) (‖x‖ + 1) := mem_ball_zero_iff.mpr (by linarith)
  have hH : HolderOnWith (Real.toNNReal C) η F (ball (0:E) (‖x‖ + 1)) :=
    by
      intro x hx y hy
      rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg η.coe_nonneg,
        ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal C hC, ← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using hhol x hx y hy)
  exact (hH.continuousOn hη0).continuousAt (isOpen_ball.mem_nhds hx)

/-- The reciprocal of a nonvanishing locally Hölder real function is locally Hölder. -/
theorem LocHolderMap.inv {F : E → ℝ} (h : LocHolderMap F) (h0 : ∀ x, F x ≠ 0) :
    LocHolderMap (fun x => (F x)⁻¹) := by
  refine LocHolderMap.of_le_sum (ι := Unit) (fun _ => h) fun s hs => ?_
  -- a positive lower bound of `|F|` on the closed ball
  have hcont : ContinuousOn (fun x => |F x|) (closedBall (0:E) s) :=
    (continuous_abs.comp h.continuous).continuousOn
  obtain ⟨m, hm, hmle⟩ := (isCompact_closedBall (0:E) s).exists_forall_le' hcont
    (a := 0) fun x _ => abs_pos.mpr (h0 x)
  refine ⟨fun _ => (m * m)⁻¹, fun _ => by positivity, fun x hx y hy => ?_⟩
  simp only [Finset.univ_unique, Finset.sum_singleton, Real.norm_eq_abs]
  rw [inv_sub_inv (h0 x) (h0 y), abs_div, abs_mul, abs_sub_comm (F y) (F x),
    div_le_iff₀ (mul_pos (abs_pos.mpr (h0 x)) (abs_pos.mpr (h0 y)))]
  have hx' := hmle x (ball_subset_closedBall hx)
  have hy' := hmle y (ball_subset_closedBall hy)
  have hmm : m * m ≤ |F x| * |F y| := mul_le_mul hx' hy' hm.le (abs_nonneg _)
  calc |F x - F y| = (m * m)⁻¹ * |F x - F y| * (m * m) := by field_simp
    _ ≤ (m * m)⁻¹ * |F x - F y| * (|F x| * |F y|) := by gcongr

/-- A `C¹` map is locally Hölder (locally Lipschitz, hence Hölder of exponent `1/2`). -/
theorem LocHolderMap.of_contDiff_one [NormedSpace ℝ G] {F : E → G} (h : ContDiff ℝ 1 F) :
    LocHolderMap F := by
  intro s hs
  have hd : Differentiable ℝ F := h.differentiable one_ne_zero
  have hcont : ContinuousOn (fderiv ℝ F) (closedBall (0:E) s) :=
    (h.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨N, hN⟩ := (isCompact_closedBall (0:E) s).exists_bound_of_continuousOn hcont
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (mem_closedBall_self hs.le))
  refine ⟨1 / 2, by norm_num, by norm_num, N * (2 * s) ^ (1 - (1 / 2 : ℝ)), by positivity, ?_⟩
  intro x hx y hy
  have hlip : ‖F x - F y‖ ≤ N * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z)
      (fun z hz => hN z (ball_subset_closedBall hz)) (convex_ball 0 s) hy hx
  have h2 := le_rpow_one_sub_mul_rpow (norm_nonneg (x - y)) (norm_sub_le_two_mul_of_mem_ball hx hy)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  calc ‖F x - F y‖ ≤ N * ‖x - y‖ := hlip
    _ ≤ N * ((2 * s) ^ (1 - (1 / 2 : ℝ)) * ‖x - y‖ ^ ((1 / 2 : ℝ≥0) : ℝ)) := by
        push_cast
        exact mul_le_mul_of_nonneg_left h2 hN0
    _ = N * (2 * s) ^ (1 - (1 / 2 : ℝ)) * ‖x - y‖ ^ ((1 / 2 : ℝ≥0) : ℝ) := by ring

/-- Composition with a `C¹` map on the left. -/
theorem LocHolderMap.comp_contDiff {F : E → E} (hF : LocHolderMap F) {G₀ : E → ℝ}
    (hG : ContDiff ℝ 1 G₀) : LocHolderMap (fun x => G₀ (F x)) := by
  refine LocHolderMap.of_le_sum (ι := Unit) (fun _ => hF) fun s hs => ?_
  obtain ⟨B, hB, hb⟩ := hF.exists_bound hs
  have hd : Differentiable ℝ G₀ := hG.differentiable one_ne_zero
  have hcont : ContinuousOn (fderiv ℝ G₀) (closedBall (0:E) B) :=
    (hG.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨N, hN⟩ := (isCompact_closedBall (0:E) B).exists_bound_of_continuousOn hcont
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (mem_closedBall_self hB))
  refine ⟨fun _ => N, fun _ => hN0, fun x hx y hy => ?_⟩
  simp only [Finset.univ_unique, Finset.sum_singleton]
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z) hN (convex_closedBall 0 B)
    (mem_closedBall_zero_iff.mpr (hb y hy)) (mem_closedBall_zero_iff.mpr (hb x hx))

end LocHolderMap

section LocHolderDeriv

/-- `h : ℝⁿ → ℝ` is **locally `C^{m,α}`**: `C^m` with locally Hölder `m`-th derivative (exponent
and constant may depend on the ball). -/
def LocHolderDeriv (m : ℕ) (h : E → ℝ) : Prop :=
  ContDiff ℝ m h ∧ LocHolderMap (iteratedFDeriv ℝ m h)

theorem LocHolderDeriv.contDiff {m : ℕ} {h : E → ℝ} (hh : LocHolderDeriv m h) :
    ContDiff ℝ m h := hh.1

/-- Locally `C^{0,α}` is locally Hölder. -/
theorem locHolderDeriv_zero_iff {h : E → ℝ} : LocHolderDeriv 0 h ↔ LocHolderMap h := by
  constructor
  · intro hh
    exact hh.2.of_le_norm zero_le_one fun x y => by
      rw [one_mul, norm_iteratedFDeriv_zero_sub]
  · intro hh
    refine ⟨contDiff_zero.mpr hh.continuous, ?_⟩
    exact hh.of_le_norm zero_le_one fun x y => by rw [one_mul, norm_iteratedFDeriv_zero_sub]

theorem LocHolderDeriv.add {m : ℕ} {f g : E → ℝ} (hf : LocHolderDeriv m f)
    (hg : LocHolderDeriv m g) : LocHolderDeriv m (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  have e : ∀ x, iteratedFDeriv ℝ m (fun x => f x + g x) x =
      iteratedFDeriv ℝ m f x + iteratedFDeriv ℝ m g x := fun x =>
    iteratedFDeriv_add_apply hf.1.contDiffAt hg.1.contDiffAt
  have := hf.2.add hg.2
  simp only [← e] at this
  exact this

theorem LocHolderDeriv.neg {m : ℕ} {f : E → ℝ} (hf : LocHolderDeriv m f) :
    LocHolderDeriv m (fun x => -f x) := by
  refine ⟨hf.1.neg, ?_⟩
  have e : ∀ x, iteratedFDeriv ℝ m (fun x => -f x) x = -iteratedFDeriv ℝ m f x := fun x =>
    iteratedFDeriv_neg_apply
  have := hf.2.neg
  simp only [← e] at this
  exact this

theorem LocHolderDeriv.sub {m : ℕ} {f g : E → ℝ} (hf : LocHolderDeriv m f)
    (hg : LocHolderDeriv m g) : LocHolderDeriv m (fun x => f x - g x) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

theorem LocHolderDeriv.const_mul {m : ℕ} {f : E → ℝ} (hf : LocHolderDeriv m f) (c : ℝ) :
    LocHolderDeriv m (fun x => c * f x) := by
  refine ⟨contDiff_const.mul hf.1, ?_⟩
  have e : ∀ x, iteratedFDeriv ℝ m (fun x => c * f x) x = c • iteratedFDeriv ℝ m f x := by
    intro x
    have := iteratedFDeriv_const_smul_apply' (a := c) (hf.1.contDiffAt (x := x))
    simpa [smul_eq_mul] using this
  have := hf.2.const_smul c
  simp only [← e] at this
  exact this

theorem LocHolderDeriv.const (m : ℕ) (c : ℝ) : LocHolderDeriv m (fun _ : E => c) := by
  refine ⟨contDiff_const, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact (LocHolderMap.const c).of_le_norm zero_le_one fun x y => by
      rw [one_mul, norm_iteratedFDeriv_zero_sub]
  · rw [iteratedFDeriv_const_of_ne hm.ne' c]
    exact LocHolderMap.const 0

theorem LocHolderDeriv.finset_sum {m : ℕ} {ι : Type*} (t : Finset ι) {f : ι → E → ℝ}
    (h : ∀ i ∈ t, LocHolderDeriv m (f i)) : LocHolderDeriv m (fun x => ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using LocHolderDeriv.const m 0
  | insert a t ha ih =>
      have := (h a (Finset.mem_insert_self a t)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using this

/-- **Weakening.** Locally `C^{m+1,α}` implies locally `C^{m,α}`. -/
theorem LocHolderDeriv.weaken {m : ℕ} {h : E → ℝ} (hh : LocHolderDeriv (m + 1) h) :
    LocHolderDeriv m h := by
  refine ⟨hh.1.of_le (by exact_mod_cast Nat.le_succ m), ?_⟩
  have h1 : ContDiff ℝ 1 (iteratedFDeriv ℝ m h) :=
    hh.1.iteratedFDeriv_right (m := 1) (i := m) (by nat_cast_le)
  exact LocHolderMap.of_contDiff_one h1

theorem LocHolderDeriv.of_le {m m' : ℕ} (hm : m ≤ m') {h : E → ℝ} (hh : LocHolderDeriv m' h) :
    LocHolderDeriv m h := by
  induction m' with
  | zero =>
      have : m = 0 := by omega
      subst this; exact hh
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact ih (by omega) hh.weaken
      · have : m = k + 1 := by omega
        subst this; exact hh

/-- A continuous linear functional on `ℝⁿ` applied to `v` is the sum of the coordinates of `v`
times its values on the standard basis. -/
theorem clm_apply_eq_sum_coord (L : E →L[ℝ] ℝ) (v : E) :
    L v = ∑ i, v i * L (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  simpa only [EuclideanSpace.basisFun_apply, smul_eq_mul] using clm_apply_eq_sum_single L v

/-- **Down.** The directional derivative of a locally `C^{m+1,α}` function is locally
`C^{m,α}`. -/
theorem LocHolderDeriv.directional {m : ℕ} {h : E → ℝ} (hh : LocHolderDeriv (m + 1) h) (e : E) :
    LocHolderDeriv m (fun x => fderiv ℝ h x e) := by
  have hD : ContDiff ℝ m (fderiv ℝ h) := hh.1.fderiv_right (by norm_cast)
  refine ⟨hD.clm_apply contDiff_const, ?_⟩
  have hT : ∀ z, iteratedFDeriv ℝ m (fun x => fderiv ℝ h x e) z =
      (ContinuousLinearMap.apply ℝ ℝ e).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (fderiv ℝ h) z) := fun z =>
    ContinuousLinearMap.iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ ℝ e)
      hD.contDiffAt le_rfl
  refine hh.2.of_le_norm (norm_nonneg e) fun x y => ?_
  rw [norm_iteratedFDeriv_succ_sub, hT, hT]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [sub_apply]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  rw [← sub_apply, ← sub_apply]
  calc ‖((iteratedFDeriv ℝ m (fderiv ℝ h) x - iteratedFDeriv ℝ m (fderiv ℝ h) y) v) e‖
      ≤ ‖(iteratedFDeriv ℝ m (fderiv ℝ h) x - iteratedFDeriv ℝ m (fderiv ℝ h) y) v‖ * ‖e‖ :=
        ContinuousLinearMap.le_opNorm _ e
    _ ≤ (‖iteratedFDeriv ℝ m (fderiv ℝ h) x - iteratedFDeriv ℝ m (fderiv ℝ h) y‖ *
          ∏ i, ‖v i‖) * ‖e‖ := by
        gcongr
        exact ContinuousMultilinearMap.le_opNorm _ v
    _ = ‖e‖ * ‖iteratedFDeriv ℝ m (fderiv ℝ h) x - iteratedFDeriv ℝ m (fderiv ℝ h) y‖ *
          ∏ i, ‖v i‖ := by ring

/-- The `(m+1)`-st iterated derivative evaluated on `v` is the sum over the coordinates of the
last vector of the `m`-th iterated derivatives of the coordinate directional derivatives. -/
theorem iteratedFDeriv_succ_apply_eq_sum_coordinate {m : ℕ} {h : E → ℝ}
    (hD : ContDiff ℝ m (fderiv ℝ h)) (x : E) (v : Fin (m + 1) → E) :
    iteratedFDeriv ℝ (m + 1) h x v =
      ∑ i, (v (Fin.last m)) i * iteratedFDeriv ℝ m
        (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) x (Fin.init v) := by
  rw [iteratedFDeriv_succ_apply_right, clm_apply_eq_sum_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hT : iteratedFDeriv ℝ m (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) x =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (fderiv ℝ h) x) :=
    ContinuousLinearMap.iteratedFDeriv_comp_left
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)) hD.contDiffAt le_rfl
  rw [hT]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]

/-- **Up.** A `C¹` function all of whose coordinate directional derivatives are locally
`C^{m,α}` is locally `C^{m+1,α}`. -/
theorem LocHolderDeriv.of_coordinate {m : ℕ} {h : E → ℝ} (h1 : ContDiff ℝ 1 h)
    (hd : ∀ i : Fin n, LocHolderDeriv m
      (fun x => fderiv ℝ h x (EuclideanSpace.basisFun (Fin n) ℝ i))) :
    LocHolderDeriv (m + 1) h := by
  -- `C^{m+1}` from the coordinate directional derivatives
  have hD : ContDiff ℝ m (fderiv ℝ h) := by
    have e : fderiv ℝ h = fun x => ∑ i, fderiv ℝ h x (EuclideanSpace.basisFun (Fin n) ℝ i) •
        EuclideanSpace.proj (𝕜 := ℝ) i := by
      funext x
      ext v
      rw [clm_apply_eq_sum_coord]
      simp only [sum_apply, smul_apply, EuclideanSpace.coe_proj, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact ContDiff.sum fun i _ => (hd i).1.smul contDiff_const
  have hC : ContDiff ℝ (m + 1) h := by
    rw [contDiff_succ_iff_fderiv]
    exact ⟨h1.differentiable one_ne_zero, by simp, hD⟩
  refine ⟨hC, ?_⟩
  refine LocHolderMap.of_le_sum (ι := Fin n) (fun i => (hd i).2) fun s _ =>
    ⟨fun _ => 1, fun _ => zero_le_one, fun x _ y _ => ?_⟩
  simp only [one_mul]
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _)
    fun v => ?_
  rw [sub_apply, iteratedFDeriv_succ_apply_eq_sum_coordinate hD,
    iteratedFDeriv_succ_apply_eq_sum_coordinate hD, ← Finset.sum_sub_distrib,
    Fin.prod_univ_castSucc, Real.norm_eq_abs]
  have hinit : ∀ j : Fin m, Fin.init v j = v (Fin.castSucc j) := fun j => rfl
  calc |∑ i, ((v (Fin.last m)) i * iteratedFDeriv ℝ m
          (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) x (Fin.init v) -
        (v (Fin.last m)) i * iteratedFDeriv ℝ m
          (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) y (Fin.init v))|
      ≤ ∑ i, |(v (Fin.last m)) i * iteratedFDeriv ℝ m
          (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) x (Fin.init v) -
        (v (Fin.last m)) i * iteratedFDeriv ℝ m
          (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) y (Fin.init v)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖v (Fin.last m)‖ * (‖iteratedFDeriv ℝ m
          (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) x -
          iteratedFDeriv ℝ m
          (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) y‖ *
          ∏ j : Fin m, ‖v (Fin.castSucc j)‖) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← mul_sub, abs_mul]
        refine mul_le_mul (by simpa using PiLp.norm_apply_le (v (Fin.last m)) i) ?_ (abs_nonneg _)
          (norm_nonneg _)
        rw [← Real.norm_eq_abs, ← sub_apply]
        have := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ m
          (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) x -
          iteratedFDeriv ℝ m
          (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) y) (Fin.init v)
        simpa only [hinit] using this
    _ = (∑ i, ‖iteratedFDeriv ℝ m
          (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) x -
          iteratedFDeriv ℝ m
          (fun y => fderiv ℝ h y (EuclideanSpace.basisFun (Fin n) ℝ i)) y‖) *
          ((∏ j : Fin m, ‖v (Fin.castSucc j)‖) * ‖v (Fin.last m)‖) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- Products of locally `C^{m,α}` functions are locally `C^{m,α}`. -/
theorem LocHolderDeriv.mul {m : ℕ} {f g : E → ℝ} (hf : LocHolderDeriv m f)
    (hg : LocHolderDeriv m g) : LocHolderDeriv m (fun x => f x * g x) := by
  induction m generalizing f g with
  | zero =>
      exact locHolderDeriv_zero_iff.mpr
        ((locHolderDeriv_zero_iff.mp hf).mul (locHolderDeriv_zero_iff.mp hg))
  | succ k ih =>
      refine LocHolderDeriv.of_coordinate (hf.1.mul hg.1 |>.of_le (by nat_cast_le)) fun i => ?_
      have hfd : Differentiable ℝ f := hf.1.differentiable (by nat_cast_le)
      have hgd : Differentiable ℝ g := hg.1.differentiable (by nat_cast_le)
      have e : (fun x => fderiv ℝ (fun y => f y * g y) x (EuclideanSpace.basisFun (Fin n) ℝ i)) =
          fun x => f x * fderiv ℝ g x (EuclideanSpace.basisFun (Fin n) ℝ i) +
            g x * fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
        funext x
        rw [fderiv_fun_mul (hfd x) (hgd x), add_apply, smul_apply, smul_apply, smul_eq_mul,
          smul_eq_mul]
      rw [e]
      exact (ih hf.weaken (hg.directional _)).add (ih hg.weaken (hf.directional _))

theorem LocHolderDeriv.finset_prod {m : ℕ} {ι : Type*} (t : Finset ι) {f : ι → E → ℝ}
    (h : ∀ i ∈ t, LocHolderDeriv m (f i)) : LocHolderDeriv m (fun x => ∏ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using LocHolderDeriv.const m 1
  | insert a t ha ih =>
      have := (h a (Finset.mem_insert_self a t)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      simpa [Finset.prod_insert ha] using this

/-- Reciprocals of nonvanishing locally `C^{m,α}` functions are locally `C^{m,α}`. -/
theorem LocHolderDeriv.inv {m : ℕ} {f : E → ℝ} (hf : LocHolderDeriv m f) (h0 : ∀ x, f x ≠ 0) :
    LocHolderDeriv m (fun x => (f x)⁻¹) := by
  induction m generalizing f with
  | zero => exact locHolderDeriv_zero_iff.mpr ((locHolderDeriv_zero_iff.mp hf).inv h0)
  | succ k ih =>
      have hC : ContDiff ℝ (k + 1) (fun x => (f x)⁻¹) := hf.1.inv h0
      refine LocHolderDeriv.of_coordinate (hC.of_le (by nat_cast_le)) fun i => ?_
      have hfd : Differentiable ℝ f := hf.1.differentiable (by nat_cast_le)
      have e : (fun x => fderiv ℝ (fun y => (f y)⁻¹) x (EuclideanSpace.basisFun (Fin n) ℝ i)) =
          fun x => -((f x)⁻¹ * (f x)⁻¹ * fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
        funext x
        have hc : (fun y => (f y)⁻¹) = (fun t : ℝ => t⁻¹) ∘ f := rfl
        rw [hc, fderiv_comp x (differentiableAt_inv (h0 x)) (hfd x), fderiv_inv,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
        field_simp
      rw [e]
      exact (((ih hf.weaken h0).mul (ih hf.weaken h0)).mul (hf.directional _)).neg

end LocHolderDeriv

section Gradient

/-- The gradient of a locally `C^{1,α}` function is locally Hölder. -/
theorem LocHolderDeriv.gradient_locHolderMap {u : E → ℝ} (hu : LocHolderDeriv 1 u) :
    LocHolderMap (gradient u) := by
  refine hu.2.of_le_norm zero_le_one fun x y => ?_
  rw [one_mul, norm_iteratedFDeriv_one_sub]
  simp only [gradient]
  rw [← map_sub, LinearIsometryEquiv.norm_map]

/-- **Composition with the gradient.** For smooth `G` and locally `C^{m+1,α}` `u`, the function
`x ↦ G (∇u x)` is locally `C^{m,α}`. -/
theorem LocHolderDeriv.comp_gradient (m : ℕ) : ∀ {G₀ : E → ℝ}, ContDiff ℝ ∞ G₀ →
    ∀ {u : E → ℝ}, LocHolderDeriv (m + 1) u → LocHolderDeriv m (fun x => G₀ (gradient u x)) := by
  induction m with
  | zero =>
      intro G₀ hG u hu
      exact locHolderDeriv_zero_iff.mpr
        (hu.gradient_locHolderMap.comp_contDiff (hG.of_le (by
          change (↑(1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top)))
  | succ k ih =>
      intro G₀ hG u hu
      have hu2 : ContDiff ℝ 2 u := hu.1.of_le (by nat_cast_le)
      have hG1 : ContDiff ℝ 1 G₀ := hG.of_le (by
        change (↑(1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
      have hgrad : ContDiff ℝ (k + 1) (gradient u) :=
        contDiff_gradient hu.1 (by norm_cast)
      have hC : ContDiff ℝ (k + 1) (fun x => G₀ (gradient u x)) :=
        (hG.of_le (natCast_succ_le_infty k)).comp hgrad
      refine LocHolderDeriv.of_coordinate (hC.of_le (by nat_cast_le)) fun i => ?_
      have e : (fun x => fderiv ℝ (fun x => G₀ (gradient u x)) x
          (EuclideanSpace.basisFun (Fin n) ℝ i)) =
          fun x => ∑ j, hessianMatrix u x i j * gradient G₀ (gradient u x) j := by
        funext x
        exact chain_coordinate hu2 hG1 x i
      rw [e]
      refine LocHolderDeriv.finset_sum _ fun j _ => LocHolderDeriv.mul ?_ ?_
      · -- the Hessian entry is a double directional derivative
        have e2 : (fun x => hessianMatrix u x i j) = fun x =>
            fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
              (EuclideanSpace.basisFun (Fin n) ℝ i) := by
          funext x
          exact bilinearIteratedFDerivTwo_eq_fderiv_apply hu2 x _ _
        rw [e2]
        exact (hu.directional _).directional _
      · have hGj : ContDiff ℝ ∞ (fun y => gradient G₀ y j) := by
          have h1 : ContDiff ℝ ∞ (gradient G₀) := contDiff_gradient hG le_rfl
          exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp h1
        exact ih hGj hu.weaken

/-- Entries of the Hessian matrix of a locally `C^{m+2,α}` function are locally `C^{m,α}`. -/
theorem LocHolderDeriv.hessianEntry {m : ℕ} {u : E → ℝ} (hu : LocHolderDeriv (m + 2) u)
    (i j : Fin n) : LocHolderDeriv m (fun x => hessianMatrix u x i j) := by
  have hu2 : ContDiff ℝ 2 u := hu.1.of_le (by nat_cast_le)
  have e2 : (fun x => hessianMatrix u x i j) = fun x =>
      fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    funext x
    exact bilinearIteratedFDerivTwo_eq_fderiv_apply hu2 x _ _
  rw [e2]
  exact (hu.directional _).directional _

end Gradient

section MatrixInverse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of a matrix field with locally `C^{m,α}` entries is locally `C^{m,α}`. -/
theorem LocHolderDeriv.det {m : ℕ} {M : E → Matrix ι ι ℝ}
    (hM : ∀ i j, LocHolderDeriv m (fun x => M x i j)) :
    LocHolderDeriv m (fun x => (M x).det) := by
  have e : (fun x => (M x).det) = fun x => ∑ σ : Equiv.Perm ι,
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M x (σ i) i := by
    funext x
    exact Matrix.det_apply' (M x)
  rw [e]
  exact LocHolderDeriv.finset_sum _ fun σ _ =>
    (LocHolderDeriv.finset_prod _ fun i _ => hM (σ i) i).const_mul _

/-- Entries of the inverse of a matrix field with locally `C^{m,α}` entries and nonvanishing
determinant are locally `C^{m,α}`. -/
theorem LocHolderDeriv.matrix_inv_entry {m : ℕ} {M : E → Matrix ι ι ℝ}
    (hM : ∀ i j, LocHolderDeriv m (fun x => M x i j)) (hdet : ∀ x, (M x).det ≠ 0) (i j : ι) :
    LocHolderDeriv m (fun x => (M x)⁻¹ i j) := by
  have e : (fun x => (M x)⁻¹ i j) = fun x =>
      ((M x).det)⁻¹ * ((M x).updateRow j (Pi.single i 1)).det := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, Matrix.adjugate_apply]
  rw [e]
  refine ((LocHolderDeriv.det hM).inv hdet).mul (LocHolderDeriv.det fun k l => ?_)
  by_cases hk : k = j
  · subst hk
    simp only [Matrix.updateRow_self]
    exact LocHolderDeriv.const m _
  · simp only [Matrix.updateRow_ne hk]
    exact hM k l

end MatrixInverse

end FunctionalInequalities.Analysis
