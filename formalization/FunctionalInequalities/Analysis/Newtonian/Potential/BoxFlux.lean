module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Divergence theorem on Euclidean coordinate boxes

For `F : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1)) → ℝ` with every component globally `C¹` and a
nondegenerate box `a ≤ b`:

* `integral_closedBox_sum_fderiv_eq_faces`: the integral of `∑ᵢ ∂ᵢ Fᵢ` over the closed box
  `{x | ∀ i, a i ≤ x i ≤ b i}` equals the sum over `i` of the face integrals of `Fᵢ` at `x i = b i`
  minus those at `x i = a i`, each face parametrised by `Fin.insertNth` over `Icc (a ∘ i.succAbove)
  (b ∘ i.succAbove)`; integrability is derived from continuity of the derivative;
* `openBox_ae_eq_closedBox`: the open and closed boxes differ by a null set;
* `integral_openBox_sum_fderiv_eq_faces`: the same identity on the open box.

This transports Mathlib's divergence theorem on `Fin (k+1) → ℝ` to `EuclideanSpace ℝ (Fin (k+1))`.
It supplies the verified instance (coordinate boxes) of the domains "for which the divergence
theorem holds" in Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7), Lemma 4.2, equation (4.9), pp. 55–56. Only boxes in dimension
`k + 1 ≥ 1` are treated; no general Lipschitz or `C¹` domain is covered.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set

namespace FunctionalInequalities.Analysis

/-- A concrete Euclidean box divergence identity, with integrability derived from C1. -/
theorem integral_closedBox_sum_fderiv_eq_faces {k : ℕ} (a b : Fin (k + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i)) :
    (∫ x in {x : EuclideanSpace ℝ (Fin (k + 1)) | ∀ i, a i ≤ x i ∧ x i ≤ b i},
        ∑ i : Fin (k + 1), fderiv ℝ (F i) x (EuclideanSpace.basisFun (Fin (k + 1)) ℝ i)) =
      ∑ i : Fin (k + 1),
        ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            F i (WithLp.toLp 2 (i.insertNth (b i) y))) -
          ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            F i (WithLp.toLp 2 (i.insertNth (a i) y))) := by
  let : Preorder (EuclideanSpace ℝ (Fin (k + 1))) := Preorder.lift (fun x => x.ofLp)
  let eL := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (k + 1) => ℝ)
  let a' : EuclideanSpace ℝ (Fin (k + 1)) := WithLp.toLp 2 a
  let b' : EuclideanSpace ℝ (Fin (k + 1)) := WithLp.toLp 2 b
  have hord (x y : EuclideanSpace ℝ (Fin (k + 1))) : eL x ≤ eL y ↔ x ≤ y := Iff.rfl
  have hvol : MeasurePreserving eL volume volume := PiLp.volume_preserving_ofLp (Fin (k + 1))
  have hbox : Icc a' b' = eL ⁻¹' Icc a b := by rfl
  have hbox' : Icc a' b' = {x : EuclideanSpace ℝ (Fin (k + 1)) | ∀ i, a i ≤ x i ∧ x i ≤ b i} := by
    ext x
    change ((∀ i, a i ≤ x i) ∧ ∀ i, x i ≤ b i) ↔ ∀ i, a i ≤ x i ∧ x i ≤ b i
    exact forall_and.symm
  have hK : IsCompact (Icc a' b') := by
    rw [hbox]
    exact eL.toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hbasis (i : Fin (k + 1)) :
    eL.symm (Pi.single i 1) = EuclideanSpace.basisFun (Fin (k + 1)) ℝ i := by
    ext j
    simp [eL]
  have hc :
    Continuous
      (fun x : EuclideanSpace ℝ (Fin (k + 1)) =>
        ∑ i : Fin (k + 1), fderiv ℝ (F i) x (EuclideanSpace.basisFun (Fin (k + 1)) ℝ i)) := by
    apply continuous_finsetSum
    intro i _
    exact ((hF i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hi :
    IntegrableOn
      (fun x : EuclideanSpace ℝ (Fin (k + 1)) =>
        ∑ i : Fin (k + 1), fderiv ℝ (F i) x (EuclideanSpace.basisFun (Fin (k + 1)) ℝ i))
      (Icc a' b') volume :=
    hc.continuousOn.integrableOn_compact hK
  have h :=
    integral_divergence_of_hasFDerivAt_off_countable_of_equiv eL hord hvol F
      (fun i => fderiv ℝ (F i)) (∅ : Set (EuclideanSpace ℝ (Fin (k + 1)))) countable_empty a' b'
      hab (fun i => (hF i).continuous.continuousOn)
      (fun x _ i => ((hF i).differentiable one_ne_zero x).hasFDerivAt)
      (fun x => ∑ i : Fin (k + 1), fderiv ℝ (F i) x (EuclideanSpace.basisFun (Fin (k + 1)) ℝ i))
      (fun x => by simp only [hbasis]) hi
  have heLa : eL a' = a := rfl
  have heLb : eL b' = b := rfl
  have heSymm (y : Fin (k + 1) → ℝ) : eL.symm y = WithLp.toLp 2 y := rfl
  simpa only [hbox', heLa, heLb, heSymm] using h

/-- The actual Euclidean open/closed boxes differ only by a null boundary. -/
theorem openBox_ae_eq_closedBox {k : ℕ} (a b : Fin (k + 1) → ℝ) :
    {x : EuclideanSpace ℝ (Fin (k + 1)) | ∀ i, a i < x i ∧ x i < b i} =ᵐ[volume]
      {x | ∀ i, a i ≤ x i ∧ x i ≤ b i} := by
  have hp : (Set.pi univ fun i => Ioo (a i) (b i)) =ᵐ[volume] Icc a b := by
    simpa only [volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ => volume) (f := a) (g := b))
  have h := (PiLp.volume_preserving_ofLp (Fin (k + 1))).quasiMeasurePreserving.ae hp
  filter_upwards [h] with x hx
  change (x.ofLp ∈ Set.pi univ (fun i => Ioo (a i) (b i))) = (x.ofLp ∈ Icc a b) at hx
  change (∀ i, a i < x i ∧ x i < b i) = (∀ i, a i ≤ x i ∧ x i ≤ b i)
  simpa only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Set.mem_Icc, Pi.le_def,
    forall_and] using hx

/-- The Euclidean box divergence identity on the open box. -/
theorem integral_openBox_sum_fderiv_eq_faces {k : ℕ} (a b : Fin (k + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i)) :
    (∫ x in {x : EuclideanSpace ℝ (Fin (k + 1)) | ∀ i, a i < x i ∧ x i < b i},
        ∑ i : Fin (k + 1), fderiv ℝ (F i) x (EuclideanSpace.basisFun (Fin (k + 1)) ℝ i)) =
      ∑ i : Fin (k + 1),
        ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            F i (WithLp.toLp 2 (i.insertNth (b i) y))) -
          ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            F i (WithLp.toLp 2 (i.insertNth (a i) y))) := by
  rw [setIntegral_congr_set (openBox_ae_eq_closedBox a b)]
  exact integral_closedBox_sum_fderiv_eq_faces a b hab F hF

end FunctionalInequalities.Analysis
