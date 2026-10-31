module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Operator norms for finite-dimensional iterated derivatives

Concrete second/third spatial derivatives and their scalar-time derivatives use the
standard nested continuous-linear-map operator norms. Open the `DerivativeNorms`
scope where inference needs these concrete instances. The eight instances are scoped, so
they act only where the scope is opened; they are exported because importing modules can use
only exported instances. The scope changes neither the norm nor the scalar action.

Supports the interior derivative bootstrap used for Letwin, arXiv:2607.24164v1,
Lemma 2.2, and the BKL regular test-class estimates.
-/

@[expose] public section

noncomputable section
namespace FunctionalInequalities.Analysis.DerivativeNorms

scoped instance bilinearGroup {n : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

scoped instance bilinearSpace {n : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

scoped instance trilinearGroup {n : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

scoped instance trilinearSpace {n : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

scoped instance timeLinearGroup {n : ℕ} : NormedAddCommGroup
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

scoped instance timeLinearSpace {n : ℕ} : NormedSpace ℝ
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

scoped instance timeTrilinearGroup {n : ℕ} : NormedAddCommGroup
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

scoped instance timeTrilinearSpace {n : ℕ} : NormedSpace ℝ
    (ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end FunctionalInequalities.Analysis.DerivativeNorms
