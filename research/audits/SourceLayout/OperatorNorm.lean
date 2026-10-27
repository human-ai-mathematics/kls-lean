import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
import Lean

/-! All eight concrete instances still choose the standard nested operator norm. -/
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
  for (name, _) in env.constants.toList do
    let s := name.toString
    if s.startsWith "FunctionalInequalities.Analysis.DerivativeNorms." then
      throwError "Operator-norm setup leaked a public implementation name: {name}"
