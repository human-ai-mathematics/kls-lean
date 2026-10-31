module

public import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
public import Lean
meta import Lean

/-! All eight concrete instances still choose the standard nested operator norm, and the
scoped namespace exports exactly these eight instances. -/

@[expose] public section
noncomputable section
open scoped FunctionalInequalities.Analysis.DerivativeNorms

example {n : ℕ} : (inferInstance : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ) =
    ContinuousLinearMap.toNormedAddCommGroup := rfl

example {n : ℕ} : (inferInstance : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ) =
    ContinuousLinearMap.toNormedSpace := rfl

example {n : ℕ} : (inferInstance : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ) =
    ContinuousLinearMap.toNormedAddCommGroup := rfl

example {n : ℕ} : (inferInstance : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ) =
    ContinuousLinearMap.toNormedSpace := rfl

example {n : ℕ} : (inferInstance : NormedAddCommGroup
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ) =
    ContinuousLinearMap.toNormedAddCommGroup := rfl

example {n : ℕ} : (inferInstance : NormedAddCommGroup
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ) =
    ContinuousLinearMap.toNormedAddCommGroup := rfl

example {n : ℕ} : (inferInstance : NormedSpace ℝ
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ) =
    ContinuousLinearMap.toNormedSpace := rfl

example {n : ℕ} : (inferInstance : NormedSpace ℝ
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ) =
    ContinuousLinearMap.toNormedSpace := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.header.moduleNames.any (fun n => n.toString.startsWith "FunctionalInequalities.KLS") then
    throwError "Operator-norm foundation imports KLS"
  -- Exact export contract: the scoped namespace contains exactly these eight instances.
  let expected : Array String := #["bilinearGroup", "bilinearSpace", "trilinearGroup",
    "trilinearSpace", "timeLinearGroup", "timeLinearSpace", "timeTrilinearGroup",
    "timeTrilinearSpace"].map ("FunctionalInequalities.Analysis.DerivativeNorms." ++ ·)
  let mut found : Array String := #[]
  for (name, _) in env.constants.toList do
    let s := name.toString
    if s.startsWith "FunctionalInequalities.Analysis.DerivativeNorms." then
      if name.isInternal then
        -- Compiler-generated auxiliaries (e.g. `_proof_i`) must belong to an expected instance.
        unless expected.any (fun e => s.startsWith (e ++ ".")) do
          throwError "Unexpected internal name in the operator-norm scope: {name}"
      else
        unless expected.contains s do
          throwError "Unexpected public name in the operator-norm scope: {name}"
        found := found.push s
  for e in expected do
    unless found.contains e do
      throwError "Missing scoped operator-norm instance: {e}"
