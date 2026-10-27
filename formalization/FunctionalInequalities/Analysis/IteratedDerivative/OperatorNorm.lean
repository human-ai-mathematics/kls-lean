import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Operator norms for finite-dimensional iterated derivatives

Concrete second/third spatial derivatives and their scalar-time derivatives use the
standard nested continuous-linear-map operator norms. Open the `DerivativeNorms`
scope where inference needs these concrete instances. The instances are private
implementation details; this scope changes neither the norm nor the scalar action.

Supports the interior derivative bootstrap used for Letwin, arXiv:2607.24164v1,
Lemma 2.2, and the BKL regular test-class estimates.
-/

noncomputable section
namespace FunctionalInequalities.Analysis.DerivativeNorms

private scoped instance bilinearGroup {n : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private scoped instance bilinearSpace {n : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private scoped instance trilinearGroup {n : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private scoped instance trilinearSpace {n : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private scoped instance timeLinearGroup {n : ℕ} : NormedAddCommGroup
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private scoped instance timeLinearSpace {n : ℕ} : NormedSpace ℝ
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private scoped instance timeTrilinearGroup {n : ℕ} : NormedAddCommGroup
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private scoped instance timeTrilinearSpace {n : ℕ} : NormedSpace ℝ
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end FunctionalInequalities.Analysis.DerivativeNorms
