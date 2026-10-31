module

public import Lean
public import FunctionalInequalities.Analysis.EuclideanCoordinates
meta import Lean

/-! Exact legacy coordinate contracts through the shared low-level module; all dimensions,
including zero. -/

@[expose] public section

universe u u_1 u_2 u_3

example :
∀ {n : ℕ} (L : ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℝ) (EuclideanSpace.{0, 0} ℝ (Fin n)) ℝ),
  Eq.{1} L
    (∑ i, HSMul.hSMul.{0, 0, 0} (L ((EuclideanSpace.basisFun.{0, 0} (Fin n) ℝ) i)) (EuclideanSpace.proj.{0, 0} i)) :=
  @FunctionalInequalities.Analysis.eq_sum_apply_basisFun_smul_proj

example :
∀ {n : ℕ}
  (B :
    ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℝ) (EuclideanSpace.{0, 0} ℝ (Fin n))
      (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} ℝ) (EuclideanSpace.{0, 0} ℝ (Fin n)) ℝ)),
  LE.le.{0} (Norm.norm.{0} B)
    (∑ i,
      ∑ j, abs.{0} ((B ((EuclideanSpace.basisFun.{0, 0} (Fin n) ℝ) i)) ((EuclideanSpace.basisFun.{0, 0} (Fin n) ℝ) j))) :=
  @FunctionalInequalities.Analysis.norm_le_sum_abs_apply_basisFun_apply

run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    if name.toString.startsWith "FunctionalInequalities.Analysis.Newtonian." ||
        name.toString.startsWith "FunctionalInequalities.KLS." then
      throwError "Euclidean coordinates must remain below Newtonian and KLS"
