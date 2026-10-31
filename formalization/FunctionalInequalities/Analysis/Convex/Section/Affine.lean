module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.Linarith

/-! # Affine tilts and convex sections

Elementary section/sublevel algebra on arbitrary real inner-product spaces.
No finite dimension, measure, differentiability or positive height is needed.
-/

@[expose] public section

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A section is the negative sublevel of the corresponding affine tilt. -/
theorem section_eq_sublevel (u : E → ℝ) (x p : E) (h : ℝ) :
    {y | u y < u x + ⟪p, y - x⟫ + h} =
      {y | u y - (⟪p, y⟫ + (u x - ⟪p, x⟫ + h)) < 0} := by
  ext y
  constructor
  · intro hy
    change u y < u x + ⟪p, y - x⟫ + h at hy
    change u y - (⟪p, y⟫ + (u x - ⟪p, x⟫ + h)) < 0
    rw [inner_sub_right] at hy
    linarith
  · intro hy
    change u y - (⟪p, y⟫ + (u x - ⟪p, x⟫ + h)) < 0 at hy
    change u y < u x + ⟪p, y - x⟫ + h
    rw [inner_sub_right]
    linarith


/-- Subtracting a real affine functional preserves convexity. -/
theorem convexOn_sub_inner_add_const {u : E → ℝ} (hconv : ConvexOn ℝ Set.univ u) (p : E) (k : ℝ) :
    ConvexOn ℝ Set.univ (fun y => u y - (⟪p, y⟫ + k)) := by
  refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
  have h := hconv.2 (Set.mem_univ y) (Set.mem_univ z) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  simp only [inner_add_right, inner_smul_right]
  have hk : k = a * k + b * k := by rw [← add_mul, hab, one_mul]
  nlinarith [h, hk]


end FunctionalInequalities.Analysis
