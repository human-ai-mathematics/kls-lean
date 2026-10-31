module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Uniform quadratic ellipticity of compact matrix families

Supporting the ellipticity constants `λ, Λ` of the averaged coefficients in Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7),
Lemma 17.16, pp. 463–464, and Theorem 6.2, pp. 90–92.

`exists_uniform_quadratic_bounds`: a continuous family `A : X → Matrix ι ι ℝ` of positive definite
matrices on a compact space `X` admits constants `a, b > 0` with
`a ‖ξ‖² ≤ Σᵢⱼ Aᵢⱼ(x) ξᵢ ξⱼ ≤ b ‖ξ‖²` for every `x` and every `ξ ∈ EuclideanSpace ℝ ι`. The constants
are chosen before `x` and `ξ`; the lower bound is a positive quadratic bound, not an entry
bound.

The zero vector is handled separately, and the compact minimum argument also covers an empty unit
sphere, so the statement holds for an empty index type as well.
-/

@[expose] public section
noncomputable section
namespace FunctionalInequalities.Analysis
open Set Metric Matrix
open scoped BigOperators ComplexOrder

variable {ι X : Type*} [Fintype ι]

/-- The real matrix quadratic form in the Euclidean standard coordinates. -/
private def quadratic (M : Matrix ι ι ℝ) (ξ : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ j, M i j * ξ i * ξ j

/-- Quadratic scaling, including scalar zero. -/
private theorem quadratic_smul (M : Matrix ι ι ℝ) (a : ℝ) (ξ : EuclideanSpace ℝ ι) :
    quadratic M (a • ξ) = a ^ 2 * quadratic M ξ := by
  unfold quadratic
  simp only [PiLp.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positive definiteness is strict positivity of this quadratic form. -/
private theorem quadratic_pos {M : Matrix ι ι ℝ} (hM : M.PosDef)
    {ξ : EuclideanSpace ℝ ι} (hξ : ξ ≠ 0) : 0 < quadratic M ξ := by
  have hfun : (fun i => ξ i) ≠ 0 := by
    intro h
    apply hξ
    ext i
    exact congrFun h i
  have hp := hM.dotProduct_mulVec_pos hfun
  simpa only [quadratic, dotProduct, Matrix.mulVec, star_trivial,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hp

/-- Uniform lower and upper quadratic bounds for a compact continuous positive definite family.
The constants precede both the family parameter and the vector. -/
theorem exists_uniform_quadratic_bounds [TopologicalSpace X] [CompactSpace X]
    (A : X → Matrix ι ι ℝ) (hA : Continuous A) (hpos : ∀ x, (A x).PosDef) :
    ∃ a b : ℝ,
      0 < a ∧
        0 < b ∧
          ∀ x (ξ : EuclideanSpace ℝ ι),
            a * ‖ξ‖ ^ 2 ≤ (∑ i, ∑ j, A x i j * ξ i * ξ j) ∧
              (∑ i, ∑ j, A x i j * ξ i * ξ j) ≤ b * ‖ξ‖ ^ 2 := by
  let S : Set (X × EuclideanSpace ℝ ι) := univ ×ˢ sphere 0 1
  let F : X × EuclideanSpace ℝ ι → ℝ := fun z => quadratic (A z.1) z.2
  have hS : IsCompact S := isCompact_univ.prod (isCompact_sphere 0 1)
  have hc : Continuous F := by
    unfold F quadratic
    fun_prop
  have hp (z : X × EuclideanSpace ℝ ι) (hz : z ∈ S) : 0 < F z := by
    apply quadratic_pos (hpos z.1)
    have hn : ‖z.2‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz.2
    intro hzero
    simp only [hzero, norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨a, ha, hlo⟩ := hS.exists_forall_le' hc.continuousOn hp
  obtain ⟨U, hU⟩ := (hS.image hc).isBounded.exists_norm_le
  let b : ℝ := |U| + 1
  have hb : 0 < b := add_pos_of_nonneg_of_pos (abs_nonneg U) zero_lt_one
  refine ⟨a, b, ha, hb, ?_⟩
  intro x ξ
  by_cases hz : ξ = 0
  · simp only [hz, PiLp.zero_apply, mul_zero, Finset.sum_const_zero, norm_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl, and_self]
  have hw : ‖NormedSpace.normalize ξ‖ = 1 := NormedSpace.norm_normalize hz
  have hm : (x, NormedSpace.normalize ξ) ∈ S := by
    exact ⟨mem_univ _, by simpa only [mem_sphere_iff_norm, sub_zero] using hw⟩
  have hlo' := hlo (x, NormedSpace.normalize ξ) hm
  have hup' : F (x, NormedSpace.normalize ξ) ≤ b := by
    have hu := hU (F (x, NormedSpace.normalize ξ)) ⟨(x, NormedSpace.normalize ξ), hm, rfl⟩
    have hu' : |F (x, NormedSpace.normalize ξ)| ≤ U := by simpa only [Real.norm_eq_abs] using hu
    exact
      (le_abs_self _).trans
        (hu'.trans ((le_abs_self U).trans (le_add_of_nonneg_right zero_le_one)))
  have hscale := quadratic_smul (A x) ‖ξ‖ (NormedSpace.normalize ξ)
  rw [NormedSpace.norm_smul_normalize] at hscale
  constructor
  · calc
      a * ‖ξ‖ ^ 2 = ‖ξ‖ ^ 2 * a := mul_comm _ _
      _ ≤ ‖ξ‖ ^ 2 * F (x, NormedSpace.normalize ξ) :=
        mul_le_mul_of_nonneg_left hlo' (sq_nonneg _)
      _ = quadratic (A x) ξ := hscale.symm
  · calc
      quadratic (A x) ξ = ‖ξ‖ ^ 2 * F (x, NormedSpace.normalize ξ) := hscale
      _ ≤ ‖ξ‖ ^ 2 * b := mul_le_mul_of_nonneg_left hup' (sq_nonneg _)
      _ = b * ‖ξ‖ ^ 2 := mul_comm _ _

end FunctionalInequalities.Analysis
