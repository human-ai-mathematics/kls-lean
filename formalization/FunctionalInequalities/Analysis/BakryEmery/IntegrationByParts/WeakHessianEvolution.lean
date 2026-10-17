import FunctionalInequalities.Analysis.Lipschitz.Gradient
import FunctionalInequalities.Analysis.WeakDerivative.Basic
import FunctionalInequalities.Analysis.WeakDerivative.Calculus
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak

/-!
# Weak Hessian evolution of C1 Monge–Ampère potentials

Weak counterpart of the second evolution identity (2.6) of Letwin arXiv:2607.24164v1 Lemma 2.4 for a C1
potential `u` with Lipschitz gradient, a Lipschitz Monge–Ampère exponent `-u + W(∇u)` with
`det ∇²u = exp(-u + W(∇u))` a.e., a given compact-local L2 weak Hessian tensor `T` and weak inverse-Hessian
derivatives:

* `exists_lipschitzWith_weak_fderiv_comp_gradient`, `hasWeakDerivAlong_mongeAmpere_first_rhs`: weak derivatives
  of `∂ₐW(∇u)` and of the first Monge–Ampère right-hand side;
* `localLp_hessian_flux_trace_forcing`, `integral_weak_hessian_flux_eq_trace_derivative`: compact-local L2 flux,
  locally integrable forcing and the unweighted compact C1 test identity;
* `integral_exp_neg_hessian_flux_eq_curvature_gram`: the weighted identity with curvature and Gram forcing;
* `integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test`: its extension to bounded compact tests
  with compact global L2 coordinate weak derivatives.

All finite dimensions are included. No C2 regularity of `u`, global inverse bound, global L2 bound of `T` or
energy estimate is assumed. The energy comparison (2.14), Theorem 2.5 and the constant-8 theorem are not proved
here. One-use supports are private.
-/

noncomputable section


section WeakCoordinateComposition
open MeasureTheory Set
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

/-- Closed composition of the existing negative-exponent result with the
original Lipschitz potential. A local helper, not a new public interface. -/
private theorem exists_lipschitz_comp_gradient {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hULip : LipschitzWith L u) (hGradLip : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∃ C : NNReal, LipschitzWith C (fun x => V (gradient u x)) := by
  obtain ⟨LF, hNegCompLip⟩ :=
    exists_lipschitzWith_neg_add_comp_gradient hULip hGradLip hV
  have hSum := hNegCompLip.add hULip
  change LipschitzWith (LF + L) (fun x => (-u x + V (gradient u x)) + u x) at hSum
  have hCancel : (fun x => (-u x + V (gradient u x)) + u x) =
      (fun x => V (gradient u x)) := by
    funext x
    ring
  rw [hCancel] at hSum
  exact ⟨LF + L, hSum⟩

/-- The scalar derivative bound and compact-local L2 calculation already used
by the accepted Piola-row consumer, with an arbitrary Lipschitz scalar f. -/
private theorem memLp_coordinate_fderiv_of_lipschitz {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {C : NNReal}
    (hLip : LipschitzWith C f) (j : Fin n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ j))
      2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hMeas : Measurable (fun x => fderiv ℝ f x (e j)) :=
    (show Continuous (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A (e j)) from
      continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ f)
  have hBound (x : EuclideanSpace ℝ (Fin n)) : ‖fderiv ℝ f x (e j)‖ ≤ (C : ℝ) := by
    have hEval := (fderiv ℝ f x).le_opNorm (e j)
    rw [e.norm_eq_one j, mul_one] at hEval
    exact hEval.trans (norm_fderiv_le_of_lipschitz ℝ hLip)
  exact MemLp.of_bound hMeas.aestronglyMeasurable (C : ℝ)
    (Filter.Eventually.of_forall hBound)

set_option maxHeartbeats 800000 in
/-- Actual weak derivative of a smooth coordinate derivative composed with a
C1 potential's Lipschitz gradient. Supporting component for weak Letwin (2.6). -/
theorem exists_lipschitzWith_weak_fderiv_comp_gradient {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hULip : LipschitzWith L u)
    (hGradLip : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (a : Fin n) :
    ∃ C : NNReal,
      LipschitzWith C (fun x => fderiv ℝ W (gradient u x)
        (EuclideanSpace.basisFun (Fin n) ℝ a)) ∧
      ∀ j : Fin n,
        HasWeakDerivAlong
          (fun x => fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
          (fun x => ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp
            (fun x => ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let V : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => fderiv ℝ W z (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hV : ContDiff ℝ 1 V := by
    change ContDiff ℝ 1
      (fun z => fderiv ℝ W z (EuclideanSpace.basisFun (Fin n) ℝ a))
    exact (hW.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  obtain ⟨C, hCompLip⟩ :=
    exists_lipschitz_comp_gradient hULip hGradLip hV
  have hCoord (z : EuclideanSpace ℝ (Fin n)) (b : Fin n) :
      fderiv ℝ V z (EuclideanSpace.basisFun (Fin n) ℝ b) =
        hessianMatrix W z b a := by
    change fderiv ℝ
        (fun y => fderiv ℝ W y (EuclideanSpace.basisFun (Fin n) ℝ a)) z
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      bilinearIteratedFDerivTwo ℝ W z
        (EuclideanSpace.basisFun (Fin n) ℝ b)
        (EuclideanSpace.basisFun (Fin n) ℝ a)
    exact
      (FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply
        hW z (EuclideanSpace.basisFun (Fin n) ℝ b)
        (EuclideanSpace.basisFun (Fin n) ℝ a)).symm
  refine ⟨C, ?_, ?_⟩
  · simpa only [V] using hCompLip
  · intro j
    constructor
    · change HasWeakDerivAlong
        (fun x => V (gradient u x))
        (fun x => ∑ b : Fin n,
          hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
        (EuclideanSpace.basisFun (Fin n) ℝ j)
      have hExp :=
        FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent
          hu hGradLip hV
      have hDiffComp :
          ∀ᵐ x : EuclideanSpace ℝ (Fin n)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            DifferentiableAt ℝ (fun y => V (gradient u y)) x :=
        hCompLip.ae_differentiableAt (μ := volume)
      have hAe :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n)))]
            (fun x => ∑ b : Fin n,
              hessianMatrix u x j b * hessianMatrix W (gradient u x) b a) := by
        filter_upwards [hExp, hDiffComp] with x hxExp hxComp
        have hux : DifferentiableAt ℝ u x :=
          hu.differentiable one_ne_zero x
        have hsum :=
          hux.hasFDerivAt.neg.add hxComp.hasFDerivAt
        have hEval := congrArg
          (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
            A (EuclideanSpace.basisFun (Fin n) ℝ j))
          hsum.fderiv
        have hfun :
            (-u + (fun y => V (gradient u y))) =
              (fun y => -u y + V (gradient u y)) := by
          funext y
          rfl
        rw [hfun] at hEval
        have heval :
            fderiv ℝ (fun y => -u y + V (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ j) =
              -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
                fderiv ℝ (fun y => V (gradient u y)) x
                  (EuclideanSpace.basisFun (Fin n) ℝ j) := by
          simpa only [neg_apply, add_apply] using hEval
        have hSum :
            (∑ b : Fin n, hessianMatrix u x j b *
              fderiv ℝ V (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ b)) =
              ∑ b : Fin n, hessianMatrix u x j b *
                hessianMatrix W (gradient u x) b a := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hCoord]
        have hxExp' := hxExp j
        rw [hSum] at hxExp'
        linarith [heval, hxExp']
      have hWeakClassical :
          HasWeakDerivAlong
            (fun x => V (gradient u x))
            (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j))
            (EuclideanSpace.basisFun (Fin n) ℝ j) :=
        hasWeakDerivAlong_of_lipschitz hCompLip
          (EuclideanSpace.basisFun (Fin n) ℝ j)
      exact hWeakClassical.congr_ae
        (Filter.Eventually.of_forall (fun x => rfl)) hAe
    · intro S hS
      have hClassicalL2 :=
        memLp_coordinate_fderiv_of_lipschitz hCompLip j S hS
      have hExp :=
        FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent
          hu hGradLip hV
      have hDiffComp :
          ∀ᵐ x : EuclideanSpace ℝ (Fin n)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            DifferentiableAt ℝ (fun y => V (gradient u y)) x :=
        hCompLip.ae_differentiableAt (μ := volume)
      have hAe :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n)))]
            (fun x => ∑ b : Fin n,
              hessianMatrix u x j b * hessianMatrix W (gradient u x) b a) := by
        filter_upwards [hExp, hDiffComp] with x hxExp hxComp
        have hux : DifferentiableAt ℝ u x :=
          hu.differentiable one_ne_zero x
        have hsum :=
          hux.hasFDerivAt.neg.add hxComp.hasFDerivAt
        have hEval := congrArg
          (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
            A (EuclideanSpace.basisFun (Fin n) ℝ j))
          hsum.fderiv
        have hfun :
            (-u + (fun y => V (gradient u y))) =
              (fun y => -u y + V (gradient u y)) := by
          funext y
          rfl
        rw [hfun] at hEval
        have heval :
            fderiv ℝ (fun y => -u y + V (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ j) =
              -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
                fderiv ℝ (fun y => V (gradient u y)) x
                  (EuclideanSpace.basisFun (Fin n) ℝ j) := by
          simpa only [neg_apply, add_apply] using hEval
        have hSum :
            (∑ b : Fin n, hessianMatrix u x j b *
              fderiv ℝ V (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ b)) =
              ∑ b : Fin n, hessianMatrix u x j b *
                hessianMatrix W (gradient u x) b a := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hCoord]
        have hxExp' := hxExp j
        rw [hSum] at hxExp'
        linarith [heval, hxExp']
      have hRestricted :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S]
            (fun x => ∑ b : Fin n,
              hessianMatrix u x j b * hessianMatrix W (gradient u x) b a) :=
        MeasureTheory.ae_restrict_of_ae hAe
      exact (MeasureTheory.memLp_congr_ae hRestricted).mp hClassicalL2

end FunctionalInequalities.Analysis
end WeakCoordinateComposition


section MongeAmpereFirstRhsDerivative
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

private lemma differentiableAt_fderiv_of_differentiableAt_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx

private lemma hessian_coord_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      hessianMatrix u x i j := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ j) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j)).differentiableAt
  have h := fderiv_clm_apply hfd hc
  have h' := congrArg
    (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using h'

/-- Closed weak-coordinate calculation already used inside the canonical
weak third-derivative symmetry proof; kept private for its consuming module. -/
private theorem hasWeakDerivAlong_fderiv_of_lipschitz_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hGradLip : LipschitzWith G (gradient u)) (i j : Fin n) :
    HasWeakDerivAlong
      (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i))
      (fun x => hessianMatrix u x j i) (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => hessianMatrix u x j i) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hCoordLip : LipschitzWith (‖(innerSL ℝ) (e i)‖₊ * G)
      (fun x => fderiv ℝ u x (e i)) := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) (e i)).lipschitz.comp hGradLip)
  have hAE : (fun x => fderiv ℝ (fun y => fderiv ℝ u y (e i)) x (e j)) =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => hessianMatrix u x j i) := by
    filter_upwards [hGradLip.ae_differentiableAt (μ := volume)] with x hx
    exact hessian_coord_of_gradient_diff (i := j) (j := i) hx
  refine ⟨(hasWeakDerivAlong_of_lipschitz hCoordLip (e j)).congr_ae
    (Filter.Eventually.of_forall fun _ => rfl) hAE, ?_⟩
  intro S hS
  exact memLp_hessianMatrix_entry_of_isCompact hGradLip j i hS


/-- Compact-local essential boundedness of the total Hessian entry, reusing its
canonical measurability and Lipschitz-gradient pointwise bound. -/
private theorem memLp_top_hessianMatrix_entry_of_isCompact {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hGradLip : LipschitzWith G (gradient u)) (i j : Fin n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => hessianMatrix u x i j) (⊤ : ENNReal)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact MemLp.of_bound
    (measurable_hessianMatrix_entry u i j).aestronglyMeasurable (G : ℝ)
    (Filter.Eventually.of_forall fun x => norm_hessianMatrix_entry_le_of_lipschitz_gradient hGradLip x i j)



/-- Closed finite linearity for one negative term and a finite sum, encoded by
Option with coefficient -1 at none and 1 at every some. Kept local. -/
private theorem hasWeakDerivAlong_neg_add_sum {n m : ℕ}
    {f₀ df₀ : EuclideanSpace ℝ (Fin n) → ℝ}
    {f df : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (h₀ : HasWeakDerivAlong f₀ df₀ v)
    (h₀₂ : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df₀ 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hf : ∀ i : Fin m, HasWeakDerivAlong (f i) (df i) v)
    (hdf₂ : ∀ i : Fin m, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => -f₀ x + ∑ i : Fin m, f i x)
      (fun x => -df₀ x + ∑ i : Fin m, df i x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => -df₀ x + ∑ i : Fin m, df i x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let F : Option (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ := fun i =>
    match i with
    | none => f₀
    | some i => f i
  let D : Option (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ := fun i =>
    match i with
    | none => df₀
    | some i => df i
  let c : Option (Fin m) → ℝ := fun i =>
    match i with
    | none => -1
    | some _ => 1
  have hF (i : Option (Fin m)) : HasWeakDerivAlong (F i) (D i) v := by
    cases i with
    | none => exact h₀
    | some i => exact hf i
  have hD (i : Option (Fin m)) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (D i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    cases i with
    | none => exact h₀₂ S hS
    | some i => exact hdf₂ i S hS
  have h := hasWeakDerivAlong_finsetSum_mul (Finset.univ : Finset (Option (Fin m))) c
    (f := F) (df := D) (fun i _ => hF i) (fun i _ => hD i)
  simpa only [Fintype.sum_option, F, D, c, one_mul, neg_one_mul] using h


set_option maxHeartbeats 800000 in
/-- Weak derivative of the right-hand side `-∂ᵢu + Σₐ Hᵢₐ ∂ₐW(∇u)` of the first weak Monge–Ampère identity
along every coordinate, with compact-local L2 density, for a C1 potential with Lipschitz gradient, a C2
`W` and a given compact-local L2 weak Hessian tensor `T`. -/
theorem hasWeakDerivAlong_mongeAmpere_first_rhs {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ}
    {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
          ∑ a : Fin n, hessianMatrix u x i a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
        (fun x => -hessianMatrix u x j i +
          ∑ a : Fin n,
            (T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
        (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => -hessianMatrix u x j i +
            ∑ a : Fin n,
              (T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  intro i j
  have hPartial :=
    hasWeakDerivAlong_fderiv_of_lipschitz_gradient hG i j
  have hProducts :
      ∀ a : Fin n,
        HasWeakDerivAlong
          (fun x => hessianMatrix u x i a *
            fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a))
          (fun x =>
            T x j i a * fderiv ℝ W (gradient u x)
              (EuclideanSpace.basisFun (Fin n) ℝ a) +
            hessianMatrix u x i a *
              ∑ b : Fin n, hessianMatrix u x j b *
                hessianMatrix W (gradient u x) b a)
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp
            (fun x =>
              T x j i a * fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a) +
              hessianMatrix u x i a *
                ∑ b : Fin n, hessianMatrix u x j b *
                  hessianMatrix W (gradient u x) b a)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro a
    obtain ⟨_, hCompLip, hComp⟩ :=
      exists_lipschitzWith_weak_fderiv_comp_gradient hu hL hG hW a
    exact
      (hT j i a).1.mul_of_locally_bounded
        (hComp j).1
        (fun S hS =>
          memLp_top_hessianMatrix_entry_of_isCompact hG i a S hS)
        (fun S hS =>
          memLp_top_restrict_of_continuous hCompLip.continuous S hS)
        (hT j i a).2
        (hComp j).2
  exact
    hasWeakDerivAlong_neg_add_sum
      hPartial.1 hPartial.2
      (fun a => (hProducts a).1)
      (fun a => (hProducts a).2)

end FunctionalInequalities.Analysis
end MongeAmpereFirstRhsDerivative


section HessianFluxTraceForcing
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

set_option maxHeartbeats 800000 in
/-- Compact-local L2 Hessian flux `Jᵢⱼₐ = Σ_b (H⁻¹)_{ba} T_{bij}` and local integrability of the trace
forcing `Cᵢⱼ` from compact-local L2 tensor and inverse-derivative data and compact-local inverse bounds. -/
theorem localLp_hessian_flux_trace_forcing {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT2 : ∀ k i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => T x k i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv2 : ∀ k i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
        (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hRtop : ∀ i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (Q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (hQ : ∀ i j : Fin n, LocallyIntegrable (fun x => Q x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  dsimp only
  intro i j
  constructor
  · intro a S hS
    apply MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin n))
    intro b _hb
    exact (hT2 b i j S hS).mul' (hRtop b a S hS)
  · have hTD :
        LocallyIntegrable
          (fun x => ∑ a : Fin n, ∑ b : Fin n,
            T x i a b *
              -(((hessianMatrix u x)⁻¹ *
                (Matrix.of fun c d => T x j c d) *
                (hessianMatrix u x)⁻¹) b a))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro a _ha
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro b _hb
      exact locallyIntegrable_mul_of_compact_L2
        (hT2 i a b) (hInv2 j b a)
    have hdouble :
        LocallyIntegrable
          (fun x => ∑ b : Fin n, ∑ a : Fin n,
            T x b i j *
              -(((hessianMatrix u x)⁻¹ *
                (Matrix.of fun c d => T x a c d) *
                (hessianMatrix u x)⁻¹) b a))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro b _hb
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro a _ha
      exact locallyIntegrable_mul_of_compact_L2
        (hT2 b i j) (hInv2 a b a)
    have hRow :
        LocallyIntegrable
          (fun x => ∑ b : Fin n, T x b i j *
            (∑ a : Fin n,
              -(((hessianMatrix u x)⁻¹ *
                (Matrix.of fun c d => T x a c d) *
                (hessianMatrix u x)⁻¹) b a)))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [Finset.mul_sum] using hdouble
    exact ((hQ i j).sub hTD).add hRow

end FunctionalInequalities.Analysis
end HessianFluxTraceForcing


section ArrayPairBalance
open MeasureTheory
namespace FunctionalInequalities.Analysis

set_option maxHeartbeats 1200000 in
/-- Finite integral balance of paired integrable arrays; one-use support of the flux identity. -/
private theorem integral_array_pair_balance {n : ℕ}
    (A B C D : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : ∀ a b, Integrable (A a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hB : ∀ a b, Integrable (B a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hC : ∀ a b, Integrable (C a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hD : ∀ a b, Integrable (D a b) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hF : Integrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hPair : ∀ a b,
      (∫ x, A a b x + B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, C a b x + D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hTrace : (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    -(∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
      ∑ a : Fin n, ∑ b : Fin n, A a b x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hA_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, A a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hA a b
  have hB_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, B a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hB a b
  have hC_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, C a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hC a b
  have hD_inner :
      ∀ a : Fin n,
        Integrable (fun x => ∑ b : Fin n, D a b x)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro b _
    exact hD a b
  have hA_total :
      Integrable (fun x => ∑ a : Fin n, ∑ b : Fin n, A a b x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro a _
    exact hA_inner a
  have hC_total :
      Integrable (fun x => ∑ a : Fin n, ∑ b : Fin n, C a b x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      Finset.univ
    intro a _
    exact hC_inner a
  have hIA :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, A a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hA_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hA a b)
  have hIB :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, B a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hB_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hB a b)
  have hIC :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hC_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hC a b)
  have hID :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∑ a : Fin n, ∫ x, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun a _ => hD_inner a)
      _ = ∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply Finset.sum_congr rfl
        intro a _
        exact integral_finsetSum
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Finset.univ
          (fun b _ => hD a b)
  have hPairSum :
      (∑ a : Fin n, ∑ b : Fin n,
        ((∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) =
      (∑ a : Fin n, ∑ b : Fin n,
        ((∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have h := hPair a b
    rw [integral_add (hA a b) (hB a b),
      integral_add (hC a b) (hD a b)] at h
    exact h
  have hSums :
      (∑ a : Fin n, ∑ b : Fin n,
        (∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) +
        (∑ a : Fin n, ∑ b : Fin n,
          (∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) =
      (∑ a : Fin n, ∑ b : Fin n,
        (∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) +
        (∑ a : Fin n, ∑ b : Fin n,
          (∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    simpa only [Finset.sum_add_distrib] using hPairSum
  have hBalance :
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, B a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, A a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [hIA, hIB]
      _ =
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, C a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∑ a : Fin n, ∑ b : Fin n,
            ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hSums
      _ =
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [← hIC, ← hID]
  have hDTrace :
      (∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∑ a : Fin n, ∑ b : Fin n,
          ∫ x, D a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, ∑ a : Fin n, ∑ b : Fin n, D a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hID.symm
      _ = -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hTrace
  have hExpand :
      (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
          ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        (∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
          (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
          ∑ a : Fin n, ∑ b : Fin n, A a b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (∫ x, F x - (∑ a : Fin n, ∑ b : Fin n, C a b x)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        exact integral_add (hF.sub hC_total) hA_total
      _ =
          (∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, C a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
            (∫ x, ∑ a : Fin n, ∑ b : Fin n, A a b x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
        rw [integral_sub hF hC_total]
  rw [hExpand]
  linarith [hBalance, hDTrace]

end FunctionalInequalities.Analysis
end ArrayPairBalance


section WeakHessianFlux
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

private theorem memLp_two_of_compact_local_memLp_top {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  intro S hS
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact (hf S hS).mono_exponent le_top

/-- Closed actual inverse/Hessian pairwise compact curl test, before any trace assembly. -/
private theorem integral_compact_hessian_inverse_curl {n : ℕ}
    {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i j a b : Fin n) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k r s => -((R x * (Matrix.of fun c d => T x k c d) * R x) r s)
    (∫ x, T x j i b * (ψ x * D x a b a +
      fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a) * R x b a)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    ∫ x, T x a i b * (ψ x * D x j b a +
      fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j) * R x b a)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hηj := HasWeakDerivAlong.compact_mul_data
    (hInv j b a).1 (hInv j b a).2.1 (hInv j b a).2.2 hψ hψc
  have hηa := HasWeakDerivAlong.compact_mul_data
    (hInv a b a).1 (hInv a b a).2.1 (hInv a b a).2.2 hψ hψc
  exact integral_weakDeriv_mul_eq_swap
    (hT j i b).1 (hT a i b).1 (hT j i b).2 (hT a i b).2
    hηj.1 hηa.1 hηj.2.1 hηj.2.2.1 hηa.2.2.1 hηj.2.2.2 hηa.2.2.2



private theorem integrable_compact_continuous_mul_of_local_memLp_two {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun x => χ x * f x) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  simpa only [smul_eq_mul] using
    (locallyIntegrable_of_compact_local_memLp_two hf).integrable_smul_left_of_hasCompactSupport
      hχ hχc


set_option maxHeartbeats 1200000 in
/-- Unweighted weak Hessian flux identity: for every compactly supported C1 `ψ`,
`∫ Σₐ Jᵢⱼₐ ∂ₐψ = -∫ Cᵢⱼ ψ`, with `J` compact-local L2 and `C` locally integrable, from a C1 potential
with Lipschitz gradient, its weak Hessian tensor, weak inverse derivatives and a weak trace derivative. -/
theorem integral_weak_hessian_flux_eq_trace_derivative {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (Q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (hQ : ∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => Q x i j) (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => Q x i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let R := fun x => (hessianMatrix u x)⁻¹
  let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
  let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
  let C₀ := fun x i j => Q x i j -
    (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
    ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
  change ∀ i j : Fin n, _
  intro i j
  have hdata := localLp_hessian_flux_trace_forcing T
    (fun k i j => (hT k i j).2)
    (fun k i j => (hInv k i j).2.1)
    (fun i j => (hInv i i j).2.2)
    Q (fun i j => (hQ i j).1.2.1)
  refine ⟨(hdata i j).1, (hdata i j).2, ?_⟩
  intro ψ hψ hψc
  let e : Fin n → EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ
  let dψ := fun x a => fderiv ℝ ψ x (e a)
  let A := fun a b x => ψ x * (T x b i j * D x a b a)
  let B := fun a b x => dψ x a * (T x b i j * R x b a)
  let C := fun a b x => ψ x * (T x i a b * D x j b a)
  let E := fun a b x => dψ x j * (T x i a b * R x b a)
  let F := fun x => Q x i j * ψ x
  have hR2 (b a : Fin n) : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => R x b a) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    memLp_two_of_compact_local_memLp_top (hInv i b a).2.2
  have hdψ (a : Fin n) : Continuous (fun x => dψ x a) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψc (a : Fin n) : HasCompactSupport (fun x => dψ x a) :=
    hψc.fderiv_apply ℝ (e a)
  have hTD (k l m v b a : Fin n) :
      LocallyIntegrable (fun x => T x k l m * D x v b a)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_mul_of_compact_L2 (hT k l m).2 (hInv v b a).2.1
  have hTR (k l m b a : Fin n) :
      LocallyIntegrable (fun x => T x k l m * R x b a)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_mul_of_compact_L2 (hT k l m).2 (hR2 b a)
  have hA (a b : Fin n) : Integrable (A a b)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTD b i j a b a).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have hB (a b : Fin n) : Integrable (B a b)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTR b i j b a).integrable_smul_left_of_hasCompactSupport (hdψ a) (hdψc a)
  have hC (a b : Fin n) : Integrable (C a b)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTD i a b j b a).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have hE (a b : Fin n) : Integrable (E a b)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTR i a b b a).integrable_smul_left_of_hasCompactSupport (hdψ j) (hdψc j)
  have hF : Integrable F (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hf := integrable_compact_continuous_mul_of_local_memLp_two
      (hQ i j).2 hψ.continuous hψc
    simpa only [mul_comm] using hf
  have hsymm := ae_weak_third_derivative_symm hu hG (fun k i j => (hT k i j).1)
  have hPair (a b : Fin n) :
      (∫ x, A a b x + B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, C a b x + E a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hc := integral_compact_hessian_inverse_curl T hT hInv hψ hψc i j a b
    change (∫ x, T x j i b * (ψ x * D x a b a + dψ x a * R x b a)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, T x a i b * (ψ x * D x j b a + dψ x j * R x b a)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) at hc
    calc
      _ = ∫ x, T x j i b * (ψ x * D x a b a + dψ x a * R x b a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply integral_congr_ae
        filter_upwards [hsymm] with x hx
        have ht : T x j i b = T x b i j :=
          (hx j i b).1.trans ((hx i j b).2.trans (hx i b j).1)
        dsimp only [A, B]
        rw [ht]
        ring
      _ = _ := hc
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hsymm] with x hx
        dsimp only [C, E]
        rw [(hx a i b).1]
        ring
  have hTracePoint (x : EuclideanSpace ℝ (Fin n)) :
      (∑ a : Fin n, ∑ b : Fin n, E a b x) =
        (R x * (Matrix.of fun a b => T x i a b)).trace * dψ x j := by
    dsimp only [E]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hTrace : (∫ x, ∑ a : Fin n, ∑ b : Fin n, E a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      _ = ∫ x, (R x * (Matrix.of fun a b => T x i a b)).trace * dψ x j
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        integral_congr_ae (Filter.Eventually.of_forall hTracePoint)
      _ = _ := (hQ i j).1.2.2 ψ hψ hψc
  have hBalance := integral_array_pair_balance A B C E F hA hB hC hE hF hPair hTrace
  have hFluxPoint (x : EuclideanSpace ℝ (Fin n)) :
      (∑ a : Fin n, J x i j a * dψ x a) =
        ∑ a : Fin n, ∑ b : Fin n, B a b x := by
    dsimp only [J, B]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hForcePoint (x : EuclideanSpace ℝ (Fin n)) :
      C₀ x i j * ψ x = F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
        ∑ a : Fin n, ∑ b : Fin n, A a b x := by
    dsimp only [C₀, F, C, A]
    simp only [sub_mul, add_mul, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
  change (∫ x, ∑ a : Fin n, J x i j a * dψ x a
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    -(∫ x, C₀ x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
  rw [integral_congr_ae (Filter.Eventually.of_forall hFluxPoint)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hForcePoint)]
  exact hBalance

end FunctionalInequalities.Analysis
end WeakHessianFlux


section WeightedWeakHessianEvolution
open Matrix MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff
open scoped BigOperators
namespace FunctionalInequalities.Analysis

/-- Closed scalar contraction form of the negative trace product. -/
private theorem sum_entry_mul_neg_eq_neg_trace {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, B a b * (-(A b a))) = -(A * B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mul_neg, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

/-- The inverse-derivative contraction has the standard Gram trace order;
only trace cyclicity is used, never commutation of the matrices. -/
private theorem sum_inverse_derivative_contraction_eq_neg_gram {n : ℕ}
    (R Ti Tj : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, Ti a b * (-((R * Tj * R) b a))) =
      -(R * Ti * R * Tj).trace := by
  rw [sum_entry_mul_neg_eq_neg_trace]
  have hCyclic : (R * Tj * R * Ti).trace = (R * Ti * R * Tj).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (R * Tj) (R * Ti)
  rw [hCyclic]

/-- The coordinate curvature expression before Hessian symmetry is applied. -/
private theorem sum_curvature_eq_mul_transpose {n : ℕ}
    (H A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (∑ a : Fin n, H i a * ∑ b : Fin n, H j b * A b a) =
      (H * Aᵀ * Hᵀ) i j := by
  rw [Matrix.mul_mul_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (fun t : ℝ => H i a * t)
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

/-- The actual symmetric Hessian data identify the standard H A H entry. -/
private theorem sum_curvature_eq_mul_of_symm {n : ℕ}
    (H A : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ = H) (hA : Aᵀ = A)
    (i j : Fin n) :
    (∑ a : Fin n, H i a * ∑ b : Fin n, H j b * A b a) = (H * A * H) i j := by
  rw [sum_curvature_eq_mul_transpose, hH, hA]

/-- Row inverse/gradient cancellation in the Piola drift term. -/
private theorem sum_row_mul_neg_add_hessian_eq {n : ℕ}
    (R H : Matrix (Fin n) (Fin n) ℝ) (hRH : R * H = 1)
    (v w : Fin n → ℝ) (b : Fin n) :
    (∑ a : Fin n, R b a * (-v a + ∑ c : Fin n, H a c * w c)) =
      -(∑ a : Fin n, R b a * v a) + w b := by
  have hVec : R.mulVec (-v + H.mulVec w) = -(R.mulVec v) + w := by
    rw [Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hRH, Matrix.one_mulVec]
  have hEntry := congrFun hVec b
  simpa only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.neg_apply] using hEntry

/-- Closed row/trace algebra after the actual curl identity, before weighting. -/
private theorem sum_weak_hessian_divergence_minus_drift_eq {n : ℕ}
    (R H A : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : Hᵀ = H) (hA : Aᵀ = A) (hRH : R * H = 1)
    (hT : ∀ k i j : Fin n, T k i j = T i k j ∧ T k i j = T k j i)
    (v w : Fin n → ℝ)
    (hrow : ∀ b : Fin n,
      (∑ a : Fin n, -((R * T a * R) b a)) =
        -(∑ a : Fin n, R b a * (-v a + ∑ c : Fin n, H a c * w c)))
    (i j : Fin n) :
    let D := fun k b a => -((R * T k * R) b a)
    let J := fun a => ∑ b : Fin n, R b a * T b i j
    let Q := -H j i + ∑ a : Fin n,
      (T j i a * w a + H i a * ∑ b : Fin n, H j b * A b a)
    Q - (∑ a : Fin n, ∑ b : Fin n, T i a b * D j b a) +
        (∑ b : Fin n, T b i j * (∑ a : Fin n, D a b a)) -
        (∑ a : Fin n, J a * v a) =
      -H i j + (H * A * H) i j + (R * T i * R * T j).trace := by
  dsimp only
  let D := fun k b a => -((R * T k * R) b a)
  let J := fun a => ∑ b : Fin n, R b a * T b i j
  let Q := -H j i + ∑ a : Fin n,
    (T j i a * w a + H i a * ∑ b : Fin n, H j b * A b a)
  change Q - (∑ a : Fin n, ∑ b : Fin n, T i a b * D j b a) +
      (∑ b : Fin n, T b i j * (∑ a : Fin n, D a b a)) -
      (∑ a : Fin n, J a * v a) = _
  have hHij : H j i = H i j := congrFun (congrFun hH i) j
  have hTperm (a : Fin n) : T j i a = T a i j :=
    (hT j i a).1.trans ((hT i j a).2.trans (hT i a j).1)
  have hQ : Q = -H i j + (H * A * H) i j + ∑ a : Fin n, T a i j * w a := by
    dsimp [Q]
    rw [Finset.sum_add_distrib, sum_curvature_eq_mul_of_symm H A hH hA i j, hHij]
    simp_rw [hTperm]
    ring
  have hGram : (∑ a : Fin n, ∑ b : Fin n, T i a b * D j b a) =
      -(R * T i * R * T j).trace :=
    sum_inverse_derivative_contraction_eq_neg_gram R (T i) (T j)
  have hrow' (b : Fin n) : (∑ a : Fin n, D a b a) =
      (∑ a : Fin n, R b a * v a) - w b := by
    change (∑ a : Fin n, -((R * T a * R) b a)) = _
    rw [hrow b, sum_row_mul_neg_add_hessian_eq R H hRH v w b]
    ring
  have hRowTerm : (∑ b : Fin n, T b i j * (∑ a : Fin n, D a b a)) =
      (∑ b : Fin n, T b i j * (∑ a : Fin n, R b a * v a)) -
      (∑ b : Fin n, T b i j * w b) := by
    simp_rw [hrow']
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hcancel : (∑ b : Fin n, T b i j * (∑ a : Fin n, R b a * v a)) =
      ∑ a : Fin n, J a * v a := by
    simp only [J, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hQ, hGram, hRowTerm, hcancel]
  ring


set_option maxHeartbeats 1200000 in
private theorem ae_hessian_flux_forcing_minus_drift {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let Q := fun x i j => -hessianMatrix u x j i + ∑ a : Fin n,
      (T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
        hessianMatrix u x i a * ∑ b : Fin n, hessianMatrix u x j b *
          hessianMatrix W (gradient u x) b a)
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j : Fin n,
      Q x i j - (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
        (∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)) -
        (∑ a : Fin n, J x i j a * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) =
      -hessianMatrix u x i j +
        (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
        (R x * (Matrix.of fun a b => T x i a b) * R x *
          (Matrix.of fun a b => T x j a b)).trace := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let R := fun x => (hessianMatrix u x)⁻¹
  let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
  have hrow₀ := ae_inverse_hessian_row_divergence_of_weak_derivative hu hG hF hdet T hInv
  have hrows : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ b : Fin n, (∑ a : Fin n, D x a b a) =
        -(∑ a : Fin n, R x b a *
          fderiv ℝ (fun y => -u y + W (gradient u y)) x (e a)) :=
    ae_all_iff.mpr (fun b => (hrow₀ b).2)
  have hchain := ae_fderiv_mongeAmpere_exponent hu hG (hW.of_le one_le_two)
  have hsymm := ae_weak_third_derivative_symm hu hG (fun k i j => (hT k i j).1)
  filter_upwards [hrows, hchain, hsymm, hdet, hG.ae_differentiableAt (μ := volume)]
    with x hrow hc hs hd hx
  intro i j
  have hH : (hessianMatrix u x)ᵀ = hessianMatrix u x := by
    have hh := hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx
    ext a b
    simpa only [Matrix.transpose_apply, star_trivial] using hh.apply a b
  have hWsym : (hessianMatrix W (gradient u x))ᵀ = hessianMatrix W (gradient u x) := by
    ext a b
    exact BakryEmery.bilinearIteratedFDerivTwo_symm hW (gradient u x) (e b) (e a)
  have hRH : R x * hessianMatrix u x = 1 := by
    apply Matrix.nonsing_inv_mul
    apply isUnit_iff_ne_zero.mpr
    rw [hd]
    exact Real.exp_ne_zero _
  have hrow' (b : Fin n) : (∑ a : Fin n, D x a b a) =
      -(∑ a : Fin n, R x b a *
        (-fderiv ℝ u x (e a) + ∑ c : Fin n, hessianMatrix u x a c *
          fderiv ℝ W (gradient u x) (e c))) := by
    rw [hrow b]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [hc a]
  exact sum_weak_hessian_divergence_minus_drift_eq
    (R x) (hessianMatrix u x) (hessianMatrix W (gradient u x))
    (fun k => Matrix.of fun a b => T x k a b) hH hWsym hRH hs
    (fun a => fderiv ℝ u x (e a))
    (fun a => fderiv ℝ W (gradient u x) (e a)) hrow' i j



/-- Closed C1 multiplication by exp(-u) in a compact-test divergence identity. -/
private theorem integral_exp_neg_flux_of_unweighted {n : ℕ}
    {u c : EuclideanSpace ℝ (Fin n) → ℝ}
    {J : EuclideanSpace ℝ (Fin n) → Fin n → ℝ}
    (hu : ContDiff ℝ 1 u)
    (hJ : ∀ a : Fin n, LocallyIntegrable (fun x => J x a)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hc : LocallyIntegrable c (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hId : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ x, ∑ a : Fin n, J x a *
        fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ a)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, c x * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    LocallyIntegrable
      (fun x => Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x a *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let weight := fun x => Real.exp (-u x)
  have hweight : ContDiff ℝ 1 weight := hu.neg.exp
  have hdu (a : Fin n) : Continuous (fun x => fderiv ℝ u x (e a)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  let d := fun x => ∑ a : Fin n, J x a * fderiv ℝ u x (e a)
  have hd : LocallyIntegrable d (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_finsetSum Finset.univ (fun a _ => (hJ a).mul_continuous (hdu a))
  refine ⟨?_, ?_⟩
  · change LocallyIntegrable (fun x => weight x * (c x - d x)) volume
    simpa only [Pi.sub_apply] using
      LocallyIntegrable.continuous_mul hweight.continuous (hc.sub hd)
  · intro ψ hψ hψc
    let A := fun x => weight x * (∑ a : Fin n, J x a * fderiv ℝ ψ x (e a))
    let B := fun x => weight x * ψ x * d x
    let E := fun x => c x * (weight x * ψ x)
    have hdψ (a : Fin n) : Continuous (fun x => fderiv ℝ ψ x (e a)) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdψc (a : Fin n) : HasCompactSupport (fun x => fderiv ℝ ψ x (e a)) :=
      hψc.fderiv_apply ℝ (e a)
    have hAi (a : Fin n) : Integrable (fun x => weight x * (J x a * fderiv ℝ ψ x (e a)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      have hi := (hJ a).integrable_smul_left_of_hasCompactSupport
        (hweight.continuous.mul (hdψ a)) ((hdψc a).mul_left)
      convert hi using 1
      funext x
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    have hA : Integrable A (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [A, Finset.mul_sum] using
        integrable_finsetSum Finset.univ (fun a _ => hAi a)
    have hB : Integrable B (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [B, smul_eq_mul, Pi.mul_apply] using
        hd.integrable_smul_left_of_hasCompactSupport
          (hweight.continuous.mul hψ.continuous) hψc.mul_left
    have hE : Integrable E (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      have hi := hc.integrable_smul_left_of_hasCompactSupport
        (hweight.continuous.mul hψ.continuous) hψc.mul_left
      simpa only [E, smul_eq_mul, Pi.mul_apply, mul_comm] using hi
    have hderiv (x : EuclideanSpace ℝ (Fin n)) (a : Fin n) :
        fderiv ℝ (fun y => weight y * ψ y) x (e a) =
          weight x * fderiv ℝ ψ x (e a) - weight x * ψ x * fderiv ℝ u x (e a) := by
      have hux := (hu.differentiable one_ne_zero).differentiableAt (x := x)
      have hψx := (hψ.differentiable one_ne_zero).differentiableAt (x := x)
      have he := ((hux.hasFDerivAt.neg.exp).mul hψx.hasFDerivAt).fderiv
      change fderiv ℝ (fun y => Real.exp (-u y) * ψ y) x (e a) = _
      change fderiv ℝ (fun y => Real.exp (-u y) * ψ y) x = _ at he
      rw [he]
      simp only [_root_.add_apply, _root_.smul_apply,
        _root_.neg_apply, smul_eq_mul, Pi.neg_apply]
      dsimp [weight]
      ring
    have hleft (x : EuclideanSpace ℝ (Fin n)) :
        (∑ a : Fin n, J x a * fderiv ℝ (fun y => weight y * ψ y) x (e a)) =
          A x - B x := by
      simp only [hderiv]
      calc
        _ = ∑ a : Fin n, (weight x * (J x a * fderiv ℝ ψ x (e a)) -
            (weight x * ψ x) * (J x a * fderiv ℝ u x (e a))) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hid := hId (fun y => weight y * ψ y) (hweight.mul hψ) hψc.mul_left
    have hleftfun :
        (fun x => ∑ a : Fin n, J x a * fderiv ℝ (fun y => weight y * ψ y) x (e a)) =
          (fun x => A x - B x) := funext hleft
    have hab : (∫ x, A x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) -
        (∫ x, B x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, E x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      change (∫ x, ∑ a : Fin n, J x a *
        fderiv ℝ (fun y => weight y * ψ y) x (e a)) = -(∫ x, E x) at hid
      rw [hleftfun, integral_sub hA hB] at hid
      exact hid
    have hrhs : (fun x => weight x * (c x - d x) * ψ x) =
        (fun x => E x - B x) := by
      funext x
      dsimp [E, B]
      ring
    change (∫ x, A x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, weight x * (c x - d x) * ψ x)
    rw [hrhs, integral_sub hE hB]
    linarith only [hab]


set_option maxHeartbeats 1200000 in
/-- Weighted weak Hessian evolution (weak Letwin (2.6)): the flux `J` is compact-local L2, the curvature
and Gram forcing `E = -H + H ∇²W(∇u) H + tr(H⁻¹Tᵢ H⁻¹Tⱼ)` and `e^{-u} E` are locally integrable, and
`∫ e^{-u} Σₐ Jᵢⱼₐ ∂ₐψ = -∫ e^{-u} Eᵢⱼ ψ` for every compactly supported C1 `ψ`. -/
theorem integral_exp_neg_hessian_flux_eq_curvature_gram {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst : ∀ i : Fin n,
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
          -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
          ∑ a : Fin n, hessianMatrix u x i a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  dsimp only
  intro i j
  let R := fun x => (hessianMatrix u x)⁻¹
  let D := fun x k b a =>
    -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
  let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
  let Q := fun x i j => -hessianMatrix u x j i + ∑ a : Fin n,
    (T x j i a * fderiv ℝ W (gradient u x)
        (EuclideanSpace.basisFun (Fin n) ℝ a) +
      hessianMatrix u x i a * ∑ b : Fin n, hessianMatrix u x j b *
        hessianMatrix W (gradient u x) b a)
  let C := fun x i j => Q x i j -
    (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
  let E := fun x i j => -hessianMatrix u x i j +
    (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
  have hQall :
      ∀ i j : Fin n,
        HasWeakDerivAlong
            (fun x => ((hessianMatrix u x)⁻¹ *
              (Matrix.of fun a b => T x i a b)).trace)
            (fun x => Q x i j)
            (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => Q x i j) 2
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro i j
    obtain ⟨hweak, hlocal⟩ :=
      hasWeakDerivAlong_mongeAmpere_first_rhs hu hL hG hW T hT i j
    have htrace :
        (fun x =>
          -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
            ∑ a : Fin n, hessianMatrix u x i a *
              fderiv ℝ W (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ a)) =ᵐ[volume]
        (fun x =>
          ((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x i a b)).trace) := by
      filter_upwards [hFirst i] with x hx
      exact hx.symm
    refine ⟨?_, ?_⟩
    · simpa only [Q] using
        hweak.congr_ae htrace (Filter.Eventually.of_forall fun _ => rfl)
    · simpa only [Q] using hlocal
  have hcf1 :=
    integral_weak_hessian_flux_eq_trace_derivative hu hG T hT hInv Q hQall
  have hJmem :
      ∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    simpa only [J, R] using (hcf1 i j).1
  have hClocal :
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [C, D, Q, R] using (hcf1 i j).2.1
  have hJlocal (a : Fin n) :
      LocallyIntegrable (fun x => J x i j a)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [locallyIntegrable_iff]
    intro K hK
    have hfinite : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) := by
      rw [isFiniteMeasure_restrict]
      exact ne_of_lt hK.measure_lt_top
    exact @MemLp.integrable _ _ _ _ _ _ 2 (by norm_num) _
      hfinite (hJmem a K hK)
  have hdu (a : Fin n) :
      Continuous (fun x => fderiv ℝ u x
        (EuclideanSpace.basisFun (Fin n) ℝ a)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hJdu :
      LocallyIntegrable
        (fun x => ∑ a : Fin n, J x i j a *
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    locallyIntegrable_finsetSum Finset.univ
      (fun a _ => (hJlocal a).mul_continuous (hdu a))
  have hae :=
    ae_hessian_flux_forcing_minus_drift hu hG hW hF hdet T hT hInv
  have hAE :
      (fun x =>
        C x i j -
          ∑ a : Fin n, J x i j a *
            fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) =ᵐ[volume]
        (fun x => E x i j) := by
    filter_upwards [hae] with x hx
    simpa only [C, D, J, Q, E, R] using hx i j
  have hElocal :
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hClocal.sub hJdu).congr hAE
  have hweighted :=
    integral_exp_neg_flux_of_unweighted hu hJlocal hClocal
      (fun φ hφ hφc => by
        simpa only [C, D, Q, R] using (hcf1 i j).2.2 φ hφ hφc)
  have hEweighted :
      LocallyIntegrable
        (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hweightedAE :
        (fun x => Real.exp (-u x) *
          (C x i j -
            ∑ a : Fin n, J x i j a *
              fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a))) =ᵐ[volume]
          (fun x => Real.exp (-u x) * E x i j) := by
      filter_upwards [hAE] with x hx
      rw [hx]
    exact hweighted.1.congr hweightedAE
  have hfinal :
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) *
          (∑ a : Fin n, J x i j a *
            fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    intro ψ hψ hψc
    have hid := hweighted.2 ψ hψ hψc
    have hright :
        (fun x => Real.exp (-u x) *
          (C x i j -
            ∑ a : Fin n, J x i j a *
              fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) * ψ x) =ᵐ[volume]
          (fun x => Real.exp (-u x) * E x i j * ψ x) := by
      filter_upwards [hAE] with x hx
      rw [hx]
    rw [integral_congr_ae hright] at hid
    exact hid
  exact ⟨hJmem, hElocal, hEweighted, hfinal⟩

end FunctionalInequalities.Analysis
end WeightedWeakHessianEvolution


section BoundedWeightedHessianTesting
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology
namespace FunctionalInequalities.Analysis

private theorem compact_local_memLp_two_continuous_mul {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hχ : Continuous χ) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => χ x * f x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  intro S hS
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hχ.continuousOn
  have htop : MemLp χ (⊤ : ENNReal)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    memLp_top_of_bound hχ.measurable.aestronglyMeasurable.restrict C
      (ae_restrict_of_forall_mem hS.measurableSet hC)
  exact (hf S hS).mul' htop

/-- The weighted weak Hessian evolution identity extended to a bounded compactly supported test `η` whose
coordinate weak derivatives are compactly supported and globally L2, with both sides integrable. -/
theorem integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst : ∀ i : Fin n,
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
          -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
          ∑ a : Fin n, hessianMatrix u x i a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ b : Fin n, HasWeakDerivAlong η (a b) (EuclideanSpace.basisFun (Fin n) ℝ b))
    (hac : ∀ b : Fin n, HasCompactSupport (a b))
    (ha2 : ∀ b : Fin n, MemLp (a b) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ b : Fin n, Integrable
        (fun x => Real.exp (-u x) * J x i j b * a b x)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * η x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * a b x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * η x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  let R := fun x => (hessianMatrix u x)⁻¹
  let J := fun x i j b => ∑ c : Fin n, R x c b * T x c i j
  let E := fun x i j => -hessianMatrix u x i j +
    (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
    (R x * (Matrix.of fun b c => T x i b c) * R x *
      (Matrix.of fun b c => T x j b c)).trace
  let wgt := fun x => Real.exp (-u x)
  have hdata := integral_exp_neg_hessian_flux_eq_curvature_gram
    hu hL hG hW hF hdet T hT hInv hFirst
  change ∀ i j : Fin n, _
  intro i j
  have hwgt : Continuous wgt := Real.continuous_exp.comp hu.continuous.neg
  have hJw (b : Fin n) : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => wgt x * J x i j b) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    compact_local_memLp_two_continuous_mul ((hdata i j).1 b) hwgt
  have hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, ∑ b : Fin n, (wgt x * J x i j b) *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, (wgt x * E x i j) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    intro ψ hψ hψc
    calc
      _ = ∫ x, wgt x * (∑ b : Fin n, J x i j b *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ b))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          simp only [wgt, J, R, Finset.mul_sum, Finset.sum_mul, mul_assoc])
      _ = _ := (hdata i j).2.2.2 ψ hψ hψc
  have ht := integral_flux_eq_neg_forcing_of_bounded_weak_test
    hJw (hdata i j).2.2.1 hId hη hbound hηc hweak hac ha2
  refine ⟨ht.1, ht.2.1, ?_⟩
  calc
    _ = ∫ x, ∑ b : Fin n, (wgt x * J x i j b) * a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [wgt, J, R, Finset.mul_sum, Finset.sum_mul, mul_assoc])
    _ = _ := ht.2.2

end FunctionalInequalities.Analysis
end BoundedWeightedHessianTesting
