import FunctionalInequalities.Analysis.Matrix.CompactEllipticity
import FunctionalInequalities.Analysis.Matrix.AveragedInverse

/-!
# Ellipticity of segment-averaged inverse coefficients

Supporting Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16, pp. 463–464, whose linearized equation must be
uniformly elliptic to apply the interior Schauder estimate, Theorem 6.2, pp. 90–92.

`exists_uniform_averagedInverse_ellipticity`: if `H` is continuous on a compact set `s` with
positive definite values, there are `a, b > 0` such that for all `x, x + d ∈ s` and all `ξ`,
`a ‖ξ‖² ≤ Σᵢⱼ averagedInverse H d x i j ξᵢ ξⱼ ≤ b ‖ξ‖²`. These are the same coefficients as in
`logDet_quotient_eq_averagedInverse`; the constants are chosen before the endpoints, the
displacement, any scalar step and the vector. The proof applies
`exists_uniform_quadratic_bounds` to the inverses of the matrix segments over
`(s × s) × [0, 1]` and integrates in the segment parameter.

No Hölder or third-derivative premise is used, and no Schauder estimate is asserted.
-/
noncomputable section
namespace FunctionalInequalities.Analysis
open Set MeasureTheory Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]

private def matrixSegment (A B : Matrix ι ι ℝ) (θ : ℝ) : Matrix ι ι ℝ :=
  (1-θ) • A+θ • B

private def inverseMatrixSegment (A B : Matrix ι ι ℝ) (θ : ℝ) : Matrix ι ι ℝ :=
  (matrixSegment A B θ)⁻¹

omit [Fintype ι] [DecidableEq ι] in
private theorem matrixSegment_posDef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {θ : ℝ} (hθ : θ ∈ Icc 0 1) :
    ((1-θ) • A+θ • B).PosDef := by
  by_cases hz : θ = 0
  · simpa only [hz,sub_zero,one_smul,zero_smul,add_zero] using hA
  by_cases ho : θ = 1
  · simpa only [ho,sub_self,zero_smul,one_smul,zero_add] using hB
  exact (hA.smul (sub_pos.mpr (lt_of_le_of_ne hθ.2 ho))).add
    (hB.smul (lt_of_le_of_ne hθ.1 (Ne.symm hz)))

private theorem continuousOn_inverseMatrixSegment {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ContinuousOn (inverseMatrixSegment A B) (Icc (0 : ℝ) 1) := by
  have hc : Continuous (matrixSegment A B) := by unfold matrixSegment; fun_prop
  intro θ hθ
  exact ((continuousAt_matrix_inv (matrixSegment A B θ) (by
    simpa only [matrixSegment,Ring.inverse_eq_inv'] using continuousAt_inv₀
      (matrixSegment_posDef hA hB hθ).det_pos.ne')).comp
        (f := matrixSegment A B) hc.continuousAt).continuousWithinAt

private theorem integral_quadratic {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (ξ : EuclideanSpace ℝ ι) :
    IntervalIntegrable (fun θ : ℝ => ∑ i, ∑ j,
      inverseMatrixSegment A B θ i j * ξ i * ξ j) volume 0 1 ∧
    (∫ θ in (0 : ℝ)..1, ∑ i, ∑ j, inverseMatrixSegment A B θ i j * ξ i * ξ j) =
      ∑ i, ∑ j, (∫ θ in (0 : ℝ)..1, inverseMatrixSegment A B θ i j) * ξ i * ξ j := by
  have hi (i j : ι) : IntervalIntegrable (fun θ : ℝ => inverseMatrixSegment A B θ i j)
      volume 0 1 := by
    have he : Continuous (fun D : Matrix ι ι ℝ => D i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact (he.comp_continuousOn (continuousOn_inverseMatrixSegment hA hB)).intervalIntegrable_of_Icc
      zero_le_one
  have hm (i j : ι) := ((hi i j).mul_const (ξ i)).mul_const (ξ j)
  have hr (i : ι) : IntervalIntegrable (fun θ : ℝ => ∑ j,
      inverseMatrixSegment A B θ i j * ξ i * ξ j) volume 0 1 := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hm i j) using 1 <;> try rfl
    funext θ
    simp only [Finset.sum_apply]
  have hq : IntervalIntegrable (fun θ : ℝ => ∑ i, ∑ j,
      inverseMatrixSegment A B θ i j * ξ i * ξ j) volume 0 1 := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hr i) using 1 <;> try rfl
    funext θ
    simp only [Finset.sum_apply]
  refine ⟨hq,?_⟩
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (f := fun i θ => ∑ j, inverseMatrixSegment A B θ i j*ξ i*ξ j) (fun i _ => hr i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (f := fun j θ => inverseMatrixSegment A B θ i j*ξ i*ξ j) (fun j _ => hm i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]

/-- Uniform positive quadratic lower and upper bounds for the averaged-inverse coefficients of the
log-determinant finite-difference equation. The constants precede all endpoint, displacement and
vector choices; norms are Euclidean and the zero vector is included. -/
theorem exists_uniform_averagedInverse_ellipticity [NormedAddCommGroup E]
    (H : E → Matrix ι ι ℝ) {s : Set E} (hs : IsCompact s)
    (hH : ContinuousOn H s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ (d x : E), x ∈ s → x+d ∈ s →
      ∀ ξ : EuclideanSpace ℝ ι,
        a*‖ξ‖^2 ≤ (∑ i, ∑ j, averagedInverse H d x i j * ξ i * ξ j) ∧
        (∑ i, ∑ j, averagedInverse H d x i j * ξ i * ξ j) ≤ b*‖ξ‖^2 := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let P : s → Matrix ι ι ℝ := fun x => H x
  have hP : Continuous P := hH.domRestrict
  let M : (s × s) × Icc (0 : ℝ) 1 → Matrix ι ι ℝ :=
    fun z => matrixSegment (P z.1.1) (P z.1.2) z.2
  have hM : Continuous M := by unfold M matrixSegment; fun_prop
  have hp (z : (s × s) × Icc (0 : ℝ) 1) : (M z).PosDef :=
    matrixSegment_posDef (hpos z.1.1 z.1.1.property) (hpos z.1.2 z.1.2.property) z.2.property
  have hI : Continuous (fun z => (M z)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (continuousAt_matrix_inv (M z) (by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hp z).det_pos.ne')).comp
        (f := M) hM.continuousAt
  obtain ⟨a,b,ha,hb,hbound⟩ := exists_uniform_quadratic_bounds
    (fun z => (M z)⁻¹) hI (fun z => (hp z).inv)
  refine ⟨a,b,ha,hb,?_⟩
  intro d x hx hxd ξ
  have hq := integral_quadratic (hpos x hx) (hpos (x+d) hxd) ξ
  have heq : (∫ θ in (0 : ℝ)..1, ∑ i, ∑ j,
      inverseMatrixSegment (H x) (H (x+d)) θ i j * ξ i * ξ j) =
      ∑ i, ∑ j, averagedInverse H d x i j * ξ i * ξ j := by
    simpa only [inverseMatrixSegment,matrixSegment,averagedInverse] using hq.2
  have he (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :=
    hbound ((⟨x,hx⟩,⟨x+d,hxd⟩),⟨θ,hθ⟩) ξ
  have hlo := intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => a*‖ξ‖^2) volume 0 1)
    hq.1 (fun θ hθ => (he θ hθ).1)
  have hup := intervalIntegral.integral_mono_on zero_le_one hq.1
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => b*‖ξ‖^2) volume 0 1)
    (fun θ hθ => (he θ hθ).2)
  rw [heq] at hlo hup
  exact ⟨by simpa using hlo,by simpa using hup⟩

end FunctionalInequalities.Analysis
