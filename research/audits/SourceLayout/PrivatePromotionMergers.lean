import Lean
import FunctionalInequalities.Analysis.WaveSplitting.AverageError
import FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion
import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SmallTime.Perimeter
import FunctionalInequalities.Analysis.Convex.Caffarelli.MomentRegularity
import FunctionalInequalities.KLS.Geometry.Cheeger.UpperMinkowskiContent
import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! The lower private copies are public declarations of modules already in every
consumer's import closure; the higher private copies and the two public Mathlib duplicates
are absent. The contracts below restate the removed statements with their original
hypotheses (no completeness, finite dimension or measure assumption added). -/
set_option maxHeartbeats 0 in
run_cmd do
  let removed : Array String := #[
    "_private.FunctionalInequalities.Analysis.WaveSplitting.Compatibility.0.FunctionalInequalities.Analysis.WaveSplitting.fderiv_eq_zero_of_supported",
    "_private.FunctionalInequalities.Analysis.WaveSplitting.AverageError.0.FunctionalInequalities.Analysis.WaveSplitting.fderiv_eq_zero_of_vanishing",
    "_private.FunctionalInequalities.KLS.BKL.PoissonIterate.Defect.0.FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two",
    "_private.FunctionalInequalities.KLS.BKL.PoissonIterate.Symmetry.0.FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two",
    "_private.FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion.0.FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two'",
    "_private.FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion.0.FunctionalInequalities.KLS.LogConcave.PoissonIterate.mul_mem_fixingOutside'",
    "_private.FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion.0.FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_mem_fixingOutside'",
    "_private.FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian.0.FunctionalInequalities.Analysis.mean_hessian_basis_entry",
    "_private.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SmallTime.Perimeter.0.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.pi_coefficient_le",
    "_private.FunctionalInequalities.Analysis.Convex.Caffarelli.MomentRegularity.0.FunctionalInequalities.Analysis.eq_of_common_supporting_slope",
    "FunctionalInequalities.KLS.Isoperimetry.liminf_coe_mul",
    "FunctionalInequalities.KLS.Isoperimetry.limsup_coe_mul"]
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if removed.contains name.toString then
      throwError "Removed duplicate survives: {name}"
  let owners : Array (Lean.Name × Lean.Name) := #[
    (`FunctionalInequalities.Analysis.WaveSplitting.fderiv_eq_zero_of_supported,
      `FunctionalInequalities.Analysis.WaveSplitting.Residual),
    (`FunctionalInequalities.Analysis.Tensor.mul_mem_fixingOutside,
      `FunctionalInequalities.Analysis.Tensor.Symmetrization),
    (`FunctionalInequalities.Analysis.Tensor.inv_mem_fixingOutside,
      `FunctionalInequalities.Analysis.Tensor.Symmetrization),
    (`FunctionalInequalities.Analysis.inner_basisFun_toEuclideanLin,
      `FunctionalInequalities.Analysis.Convex.Quadratic),
    (`FunctionalInequalities.KLS.LogConcave.HeatSemigroup.two_mul_sqrt_div_pi_le_sqrt_two_mul,
      `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SmallTime.Approximation),
    (`FunctionalInequalities.Analysis.eq_of_strictConvexOn_of_support,
      `FunctionalInequalities.Analysis.Convex.TruncatedConjugate)]
  for (decl, mod) in owners do
    let some idx := env.getModuleIdxFor? decl
      | throwError "Promoted owner missing: {decl}"
    unless env.header.moduleNames[idx.toNat]! == mod do
      throwError "{decl} is not owned by {mod}"

set_option autoImplicit false
open FunctionalInequalities Filter
open scoped NNReal ENNReal RealInnerProductSpace

namespace SourceLayout

theorem fderiv_eq_zero_of_supported_contract {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {R : ℝ} (hf : ∀ y, R < ‖y‖ → f y = 0) {x : E}
    (hx : R < ‖x‖) : fderiv ℝ f x = 0 :=
  Analysis.WaveSplitting.fderiv_eq_zero_of_supported hf hx

theorem contDiff_two_of_hasTemperateGrowth_contract {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {U : V → ℝ} (hUt : U.HasTemperateGrowth) : ContDiff ℝ 2 U :=
  hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)

theorem mul_mem_fixingOutside_contract {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {s : Finset Ω} {σ τ : Equiv.Perm Ω} (hσ : σ ∈ Analysis.Tensor.fixingOutside s)
    (hτ : τ ∈ Analysis.Tensor.fixingOutside s) : σ * τ ∈ Analysis.Tensor.fixingOutside s :=
  Analysis.Tensor.mul_mem_fixingOutside hσ hτ

theorem inv_mem_fixingOutside_contract {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {s : Finset Ω} {σ : Equiv.Perm Ω} (hσ : σ ∈ Analysis.Tensor.fixingOutside s) :
    σ⁻¹ ∈ Analysis.Tensor.fixingOutside s :=
  Analysis.Tensor.inv_mem_fixingOutside hσ

theorem inner_basisFun_toEuclideanLin_contract {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Matrix.toEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ = A i j :=
  Analysis.inner_basisFun_toEuclideanLin A i j

theorem pi_coefficient_contract {t : ℝ} (ht : 0 ≤ t) :
    2 * Real.sqrt (t / Real.pi) ≤ Real.sqrt (2 * t) :=
  KLS.LogConcave.HeatSemigroup.two_mul_sqrt_div_pi_le_sqrt_two_mul ht

theorem eq_of_strictConvexOn_of_support_contract {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} (hstrict : StrictConvexOn ℝ Set.univ u) {x z p : E}
    (hx : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) (hz : ∀ y, u z + ⟪p, y - z⟫ ≤ u y) : x = z :=
  Analysis.eq_of_strictConvexOn_of_support hstrict hx hz

theorem liminf_coe_mul_contract' {ι : Type*} {l : Filter ι} [l.NeBot] (c : ℝ≥0)
    (u : ι → ℝ≥0∞) : liminf (fun i => (c : ℝ≥0∞) * u i) l = c * liminf u l :=
  ENNReal.liminf_const_mul_of_ne_top (a := (c : ℝ≥0∞)) ENNReal.coe_ne_top

theorem limsup_coe_mul_contract {ι : Type*} {l : Filter ι} [l.NeBot] (c : ℝ≥0)
    (u : ι → ℝ≥0∞) : limsup (fun i => (c : ℝ≥0∞) * u i) l = c * limsup u l :=
  ENNReal.limsup_const_mul_of_ne_top (a := (c : ℝ≥0∞)) ENNReal.coe_ne_top

#print axioms fderiv_eq_zero_of_supported_contract
#print axioms contDiff_two_of_hasTemperateGrowth_contract
#print axioms mul_mem_fixingOutside_contract
#print axioms inv_mem_fixingOutside_contract
#print axioms inner_basisFun_toEuclideanLin_contract
#print axioms pi_coefficient_contract
#print axioms eq_of_strictConvexOn_of_support_contract
#print axioms liminf_coe_mul_contract'
#print axioms limsup_coe_mul_contract

end SourceLayout

#check @FunctionalInequalities.KLS.Isoperimetry.minkowskiContent_smul
#check @FunctionalInequalities.KLS.Isoperimetry.upperMinkowskiContent_smul
#check @FunctionalInequalities.KLS.MetricBV.relaxedMinkowskiContent_smul
#check @FunctionalInequalities.KLS.MetricBV.relaxedUpperMinkowskiContent_smul_le
#check @FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_gradField_gradField_iter
#check @FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_symmetrize_taylorField_grad0_iter_sq_le
#check @FunctionalInequalities.Analysis.hessianMatrix_quadraticAt
