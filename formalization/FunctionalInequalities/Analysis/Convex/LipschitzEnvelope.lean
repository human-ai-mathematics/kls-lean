module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The Pasch–Hausdorff Lipschitz envelope

For a nonempty set `D` of a real normed space, a function `φ` bounded below on `D` and `L ≥ 0`,
the Pasch–Hausdorff envelope is
`lipschitzEnvelope D φ L x = inf_{y ∈ D} (φ y + L ‖x - y‖)`.
It is the largest `L`-Lipschitz function below `φ` on `D`. This module proves the properties used
to approximate a convex potential `φ : D → ℝ` from below by finite convex functions:

* the envelope lies below `φ` on `D` and is `L`-Lipschitz (`le_of_mem`, `dist_le`, `lipschitzWith`);
* it is convex on the whole space when `D` is convex and `φ` is convex on `D` (`convexOn`);
* it increases with `L` (`mono`) and keeps a linear lower bound `a ‖x‖ - b` of `φ` when `a ≤ L`
  (`ge_mul_norm_sub`);
* it is at least `c` at `x` as soon as `φ ≥ c` on `D ∩ ball x δ` and `L δ ≥ c - inf_D φ`
  (`ge_of_ge_on_ball`), the localization behind its pointwise convergence to `φ` as `L → ∞`
  at points of lower semicontinuity.

No finite dimension, measure or smoothness is used.
-/

@[expose] public section

open Set Metric

noncomputable section

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E]

/-- The **Pasch–Hausdorff envelope** `x ↦ inf_{y ∈ D} (φ y + L ‖x - y‖)`. It is meaningful when
`D` is nonempty and `φ` is bounded below on `D`; otherwise the real infimum is the junk value. -/
def lipschitzEnvelope (D : Set E) (φ : E → ℝ) (L : ℝ) (x : E) : ℝ :=
  ⨅ y : D, φ y + L * ‖x - y‖

namespace lipschitzEnvelope

variable {D : Set E} {φ : E → ℝ} {L m : ℝ}

theorem bddBelow (hL : 0 ≤ L) (hb : ∀ y ∈ D, m ≤ φ y) (x : E) :
    BddBelow (range fun y : D => φ y + L * ‖x - y‖) := by
  refine ⟨m, ?_⟩
  rintro _ ⟨y, rfl⟩
  have := hb y y.2
  nlinarith [norm_nonneg (x - y)]

/-- Each point of `D` bounds the envelope from above. -/
theorem le_of_mem (hL : 0 ≤ L) (hb : ∀ y ∈ D, m ≤ φ y) (x : E) {y : E} (hy : y ∈ D) :
    lipschitzEnvelope D φ L x ≤ φ y + L * ‖x - y‖ :=
  ciInf_le (bddBelow hL hb x) (⟨y, hy⟩ : D)

/-- The envelope lies below `φ` on `D`. -/
theorem le_self (hL : 0 ≤ L) (hb : ∀ y ∈ D, m ≤ φ y) {y : E} (hy : y ∈ D) :
    lipschitzEnvelope D φ L y ≤ φ y := by
  simpa using le_of_mem hL hb y hy

/-- A lower bound for every term bounds the envelope from below. -/
theorem le_of_forall (hD : D.Nonempty) {x : E} {c : ℝ}
    (h : ∀ y ∈ D, c ≤ φ y + L * ‖x - y‖) : c ≤ lipschitzEnvelope D φ L x := by
  have : Nonempty D := hD.to_subtype
  exact le_ciInf fun y => h y y.2

/-- The envelope is bounded below by the lower bound of `φ`. -/
theorem ge_of_bound (hD : D.Nonempty) (hL : 0 ≤ L) (hb : ∀ y ∈ D, m ≤ φ y) (x : E) :
    m ≤ lipschitzEnvelope D φ L x :=
  le_of_forall hD fun y hy => by nlinarith [hb y hy, norm_nonneg (x - y)]

/-- **One-sided Lipschitz bound**: `env x ≤ env x' + L ‖x - x'‖`. -/
theorem le_add_mul_norm (hD : D.Nonempty) (hL : 0 ≤ L) (hb : ∀ y ∈ D, m ≤ φ y) (x x' : E) :
    lipschitzEnvelope D φ L x ≤ lipschitzEnvelope D φ L x' + L * ‖x - x'‖ := by
  have h : lipschitzEnvelope D φ L x - L * ‖x - x'‖ ≤ lipschitzEnvelope D φ L x' := by
    refine le_of_forall hD fun y hy => ?_
    have h1 := le_of_mem hL hb x hy
    have h2 : ‖x - y‖ ≤ ‖x - x'‖ + ‖x' - y‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub x x' y
    nlinarith
  linarith

/-- **The envelope is `L`-Lipschitz**: `|env x - env x'| ≤ L ‖x - x'‖`. -/
theorem dist_le (hD : D.Nonempty) (hL : 0 ≤ L) (hb : ∀ y ∈ D, m ≤ φ y) (x x' : E) :
    dist (lipschitzEnvelope D φ L x) (lipschitzEnvelope D φ L x') ≤ L * dist x x' := by
  rw [Real.dist_eq, dist_eq_norm, abs_sub_le_iff]
  constructor
  · linarith [le_add_mul_norm hD hL hb x x']
  · have := le_add_mul_norm hD hL hb x' x
    rw [norm_sub_rev] at this
    linarith

theorem lipschitzWith (hD : D.Nonempty) (hL : 0 ≤ L) (hb : ∀ y ∈ D, m ≤ φ y) :
    LipschitzWith (Real.toNNReal L) (lipschitzEnvelope D φ L) :=
  LipschitzWith.of_dist_le_mul fun x x' => by
    rw [Real.coe_toNNReal _ hL]
    exact dist_le hD hL hb x x'

theorem continuous (hD : D.Nonempty) (hL : 0 ≤ L) (hb : ∀ y ∈ D, m ≤ φ y) :
    Continuous (lipschitzEnvelope D φ L) :=
  (lipschitzWith hD hL hb).continuous

/-- **Convexity**: if `D` is convex and `φ` is convex on `D`, the envelope is convex on the
whole space. -/
theorem convexOn [NormedSpace ℝ E] (hD : D.Nonempty) (hL : 0 ≤ L) (hb : ∀ y ∈ D, m ≤ φ y)
    (hφ : ConvexOn ℝ D φ) : ConvexOn ℝ univ (lipschitzEnvelope D φ L) := by
  refine ⟨convex_univ, fun x₁ _ x₂ _ a b ha hb' hab => ?_⟩
  have : Nonempty D := hD.to_subtype
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨y₁, hy₁⟩ := exists_lt_of_ciInf_lt
    (show lipschitzEnvelope D φ L x₁ < lipschitzEnvelope D φ L x₁ + ε by linarith)
  obtain ⟨y₂, hy₂⟩ := exists_lt_of_ciInf_lt
    (show lipschitzEnvelope D φ L x₂ < lipschitzEnvelope D φ L x₂ + ε by linarith)
  have hmem : a • (y₁ : E) + b • (y₂ : E) ∈ D := hφ.1 y₁.2 y₂.2 ha hb' hab
  have hconv := hφ.2 y₁.2 y₂.2 ha hb' hab
  have hnorm : ‖a • x₁ + b • x₂ - (a • (y₁ : E) + b • (y₂ : E))‖ ≤
      a * ‖x₁ - y₁‖ + b * ‖x₂ - y₂‖ := by
    have he : a • x₁ + b • x₂ - (a • (y₁ : E) + b • (y₂ : E)) =
        a • (x₁ - y₁) + b • (x₂ - y₂) := by
      simp only [smul_sub]; abel
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb']
  have hle := le_of_mem hL hb (a • x₁ + b • x₂) hmem
  simp only [smul_eq_mul] at hconv ⊢
  have h1 : a * (φ y₁ + L * ‖x₁ - y₁‖) ≤ a * (lipschitzEnvelope D φ L x₁ + ε) :=
    mul_le_mul_of_nonneg_left hy₁.le ha
  have h2 : b * (φ y₂ + L * ‖x₂ - y₂‖) ≤ b * (lipschitzEnvelope D φ L x₂ + ε) :=
    mul_le_mul_of_nonneg_left hy₂.le hb'
  have h3 : L * ‖a • x₁ + b • x₂ - (a • (y₁ : E) + b • (y₂ : E))‖ ≤
      L * (a * ‖x₁ - y₁‖ + b * ‖x₂ - y₂‖) := mul_le_mul_of_nonneg_left hnorm hL
  calc lipschitzEnvelope D φ L (a • x₁ + b • x₂)
      ≤ φ (a • (y₁ : E) + b • (y₂ : E)) +
          L * ‖a • x₁ + b • x₂ - (a • (y₁ : E) + b • (y₂ : E))‖ := hle
    _ ≤ a * (φ y₁ + L * ‖x₁ - y₁‖) + b * (φ y₂ + L * ‖x₂ - y₂‖) := by nlinarith
    _ ≤ a * (lipschitzEnvelope D φ L x₁ + ε) + b * (lipschitzEnvelope D φ L x₂ + ε) :=
        add_le_add h1 h2
    _ = a * lipschitzEnvelope D φ L x₁ + b * lipschitzEnvelope D φ L x₂ + ε := by
        linear_combination ε * hab

/-- **Monotonicity in the Lipschitz constant.** -/
theorem mono (hD : D.Nonempty) (hL : 0 ≤ L) (hb : ∀ y ∈ D, m ≤ φ y) {L' : ℝ} (hLL' : L ≤ L')
    (x : E) : lipschitzEnvelope D φ L x ≤ lipschitzEnvelope D φ L' x :=
  le_of_forall hD fun y hy =>
    (le_of_mem hL hb x hy).trans (by nlinarith [norm_nonneg (x - y)])

/-- **Linear lower bounds pass to the envelope**: if `a ‖y‖ - b ≤ φ y` on `D` with `0 ≤ a ≤ L`,
then `a ‖x‖ - b ≤ env x` everywhere. -/
theorem ge_mul_norm_sub (hD : D.Nonempty) {a b : ℝ} (ha : 0 ≤ a) (haL : a ≤ L)
    (hgrow : ∀ y ∈ D, a * ‖y‖ - b ≤ φ y) (x : E) :
    a * ‖x‖ - b ≤ lipschitzEnvelope D φ L x :=
  le_of_forall hD fun y hy => by
    have h1 := hgrow y hy
    have h2 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
      simpa using norm_le_insert' x y
    nlinarith [norm_nonneg (x - y), mul_le_mul_of_nonneg_left h2 ha]

/-- **Localization**: if `c ≤ φ` on `D ∩ ball x δ`, `m ≤ φ` on `D` and
`c - m ≤ L δ`, then `c ≤ env x` (for `δ ≤ 0` the first premise is vacuous). -/
theorem ge_of_ge_on_ball (hD : D.Nonempty) (hb : ∀ y ∈ D, m ≤ φ y) {x : E} {c δ : ℝ}
    (hc : ∀ y ∈ D, ‖x - y‖ < δ → c ≤ φ y) (hLδ : c - m ≤ L * δ) (hL : 0 ≤ L) :
    c ≤ lipschitzEnvelope D φ L x :=
  le_of_forall hD fun y hy => by
    by_cases hxy : ‖x - y‖ < δ
    · have := hc y hy hxy
      nlinarith [norm_nonneg (x - y)]
    · push Not at hxy
      have := hb y hy
      nlinarith [mul_le_mul_of_nonneg_left hxy hL]

end lipschitzEnvelope

end FunctionalInequalities.Analysis
