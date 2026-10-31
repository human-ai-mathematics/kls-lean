module

public import FunctionalInequalities.Analysis.Lipschitz.Componentwise
public import FunctionalInequalities.Analysis.Lipschitz.Refinement
public import FunctionalInequalities.Analysis.Lipschitz.C1Pieces

/-! # Exact `C¹` pieces of a Lipschitz map into a finite-dimensional target

The vector counterpart of `Analysis.exists_contDiff_pieces`: a Lipschitz map `u : V → W` agrees to
first order — value **and** differential — with a `C¹` map on each of countably many disjoint
measurable pieces whose union is conull.

The proof is componentwise and uses **no** vector Whitney extension.  Against the orthonormal chart
`(stdOrthonormalBasis ℝ W).repr` each coordinate `fun y => e (u y) i` is a scalar Lipschitz function
(`lipschitzWith_coord`) and gets its own partition from the scalar theorem;
`exists_common_refinement` merges the `finrank ℝ W` partitions into one; on a merged piece every
coordinate agrees to first order with its `C¹` scalar representative, `differentiableAt_of_coord`
gives differentiability of `u` there and `eq_and_fderiv_eq_of_coord` upgrades the coordinatewise
agreement to agreement of `u` with the assembled `C¹` map `e.symm ∘ (representatives)`.

The target carries no measurable structure: only the domain is integrated over.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module Set
open scoped ContDiff NNReal

namespace FunctionalInequalities.Analysis

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Exact `C¹` representatives of a Lipschitz map into `W`, on countably many disjoint
measurable pieces covering almost every point, with the original ambient differential on each
piece.**  Word for word `Analysis.exists_contDiff_pieces` with target `W` in place of `ℝ`. -/
theorem exists_contDiff_pieces_vector {u : V → W} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∃ (S : ℕ → Set V) (v : ℕ → V → W),
      (∀ j, MeasurableSet (S j)) ∧ Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧ (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ S j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x := by
  classical
  set e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W)) := (stdOrthonormalBasis ℝ W).repr with he
  set L : (Fin (finrank ℝ W) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W)) :=
    ((EuclideanSpace.equiv (Fin (finrank ℝ W)) ℝ).symm :
      (Fin (finrank ℝ W) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W))) with hL
  choose S w hSm hSd hSnull hwC hjet using fun i : Fin (finrank ℝ W) =>
    exists_contDiff_pieces (lipschitzWith_coord e hu i)
  obtain ⟨T, hTm, hTd, hTnull, hTsub⟩ :=
    exists_common_refinement (finrank ℝ W) S hSm hSd hSnull
  choose f hf using hTsub
  have hvC : ∀ n, ContDiff ℝ 1 (fun y => e.symm (L (fun i => w i (f n i) y))) := by
    intro n
    have hpi : ContDiff ℝ 1 (fun y => (fun i => w i (f n i) y : Fin (finrank ℝ W) → ℝ)) :=
      contDiff_pi.2 fun i => hwC i (f n i)
    exact e.symm.toLinearIsometry.toContinuousLinearMap.contDiff.comp (L.contDiff.comp hpi)
  refine ⟨T, fun n y => e.symm (L (fun i => w i (f n i) y)), hTm, hTd, hTnull, hvC, ?_⟩
  · intro n x hx
    have hcoord := fun i => hjet i (f n i) x (Set.mem_iInter.1 (hf n hx) i)
    have hdu : DifferentiableAt ℝ u x := differentiableAt_of_coord e fun i => (hcoord i).1
    have hev : ∀ (y : V) (i : Fin (finrank ℝ W)),
        e (e.symm (L (fun i => w i (f n i) y))) i = w i (f n i) y := by
      intro y i
      rw [LinearIsometryEquiv.apply_symm_apply]
      rfl
    refine ⟨hdu, eq_and_fderiv_eq_of_coord e hdu ((hvC n).differentiable one_ne_zero x)
      (fun i => ?_) (fun i => ?_)⟩
    · rw [hev x i]
      exact (hcoord i).2.1
    · have hfun : (fun y => e (e.symm (L (fun i => w i (f n i) y))) i) = w i (f n i) :=
        funext fun y => hev y i
      rw [hfun]
      exact (hcoord i).2.2

end FunctionalInequalities.Analysis
