import FunctionalInequalities.Analysis.Convex.Quadratic
import FunctionalInequalities.Analysis.Convex.Extension
import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
import FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
import FunctionalInequalities.Analysis.Convex.Viscosity.Touching

noncomputable section
open Set Metric Filter Topology Classical
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
namespace LetwinCompactExtensionAudit

/-! A genuine Euclidean client, valid for every `n : ℕ`, including `n = 0`. -/

def clientQ (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  quadraticAt
    (1 : Matrix (Fin n) (Fin n) ℝ)
    (0 : EuclideanSpace ℝ (Fin n))
    (0 : EuclideanSpace ℝ (Fin n))
    0

def clientOmega (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.ball 0 2

def clientK (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

def clientVData (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x =>
    if x ∈ clientOmega n then clientQ n x else 0

theorem actual_quadratic_patch (n : ℕ) :
    ∃ V : EuclideanSpace ℝ (Fin n) → ℝ,
      ConvexOn ℝ univ V ∧
      (∀ x ∈ clientK n, V x = clientVData n x) ∧
      (∀ G ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2 : ℝ),
        subgradientImage V G =
          {p |
            ∃ x ∈ G, ∀ y ∈ clientOmega n,
              clientVData n x + ⟪p, y - x⟫ ≤ clientVData n y}) := by
  let E := EuclideanSpace ℝ (Fin n)
  let Ω : Set E := ball 0 2
  let K : Set E := closedBall 0 1
  let q : E → ℝ := quadraticAt 1 0 0 0
  let v : E → ℝ := fun x => if x ∈ Ω then q x else 0
  change ∃ V : E → ℝ, ConvexOn ℝ univ V ∧ (∀ x ∈ K, V x = v x) ∧
    ∀ G ⊆ ball (0 : E) (1/2 : ℝ), subgradientImage V G = {p | ∃ x ∈ G, ∀ y ∈ Ω, v x + ⟪p, y - x⟫ ≤ v y}
  have hq2 : ContDiff ℝ 2 q := contDiff_quadraticAt _ _ _ _
  have hq : ContDiff ℝ 1 q := hq2.of_le (by norm_num)
  have hqs : StrictConvexOn ℝ univ q := strictConvexOn_quadraticAt Matrix.PosDef.one _ _ _
  have heq (x : E) (hx : x ∈ Ω) : v x = q x := by
    dsimp [v]
    rw [if_pos hx]
  have hvstrict : StrictConvexOn ℝ Ω v := by
    refine ⟨convex_ball _ _, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hxyΩ : a • x + b • y ∈ Ω :=
      (convex_ball (0 : E) 2) hx hy ha.le hb.le hab
    rw [heq x hx, heq y hy, heq _ hxyΩ]
    exact hqs.2 (mem_univ _) (mem_univ _) hxy ha hb hab
  have hv : ContDiffOn ℝ 1 v Ω := hq.contDiffOn.congr heq
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKn : K.Nonempty := ⟨0, by simp [K]⟩
  have hKO : K ⊆ Ω := by
    intro x hx
    have hx' : dist x 0 ≤ (1 : ℝ) := hx
    change dist x 0 < 2
    linarith
  obtain ⟨V, hVconv, hVK, hImage⟩ :=
    exists_compact_convex_extension isOpen_ball hvstrict hv hK hKn hKO
  have hhalf : ball (0 : E) (1/2 : ℝ) ⊆ interior K := by
    intro x hx
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨(1/2 : ℝ), by norm_num, ?_⟩
    intro y hy
    change dist y 0 ≤ 1
    have hx' : dist x 0 < (1/2 : ℝ) := hx
    have hy' : dist y x < (1/2 : ℝ) := hy
    linarith [dist_triangle y x 0]
  exact ⟨V, hVconv, hVK, fun G hG => hImage G (hG.trans hhalf)⟩

end LetwinCompactExtensionAudit
set_option pp.fullNames true

#print axioms LetwinCompactExtensionAudit.actual_quadratic_patch
#print axioms FunctionalInequalities.Analysis.subgradientOn_eq_gradient
#print axioms FunctionalInequalities.Analysis.subgradient_eq_gradient
#print axioms FunctionalInequalities.Analysis.exists_compact_convex_extension
#check LetwinCompactExtensionAudit.actual_quadratic_patch 0
