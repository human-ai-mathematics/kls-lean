import FunctionalInequalities.Analysis.Matrix.LogDet.Segment
import FunctionalInequalities.Analysis.Matrix.InverseHolder

/-!
# Segment-averaged inverses and log-determinant finite differences

Supporting Gilbarg–Trudinger, Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16, pp. 463–464, for
equations `log det H(x) + u(x) = F(x)`. The coefficient `averagedInverse H d x` is the integral of
the inverse along the matrix segment from `H x` to `H (x + d)`.

* `logDet_quotient_eq_averagedInverse`: the exact finite-difference equation with these SAME
  coefficients;
* `exists_pair_inverse_cap`: one inverse-entry cap for all endpoint pairs in a compact set, chosen
  before the endpoints, the interpolation parameter and the displacement;
* `exists_uniform_averagedInverse_holder`: a uniform Hölder constant of the same coefficients, chosen
  before the displacement and the inner set;
* `abs_averagedInverse_le`: the coefficient inherits the cap.

No third derivative, ellipticity lower bound, Schauder estimate or bootstrap conclusion is asserted.
-/

noncomputable section
namespace FunctionalInequalities.Analysis
open Set MeasureTheory
open scoped NNReal BigOperators Matrix.Norms.Elementwise ComplexOrder

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual averaged inverse of the segment between the values of `H` at `x` and `x + d`. -/
def averagedInverse (H : E → Matrix ι ι ℝ) (d : E) [Add E] (x : E) (i j : ι) : ℝ :=
  ∫ θ in (0 : ℝ)..1, ((1-θ) • H x + θ • H (x+d))⁻¹ i j

/-- Exact finite-difference equation, with the same explicit coefficients.
`q` is the scalar denominator; the caller supplies `d = q • v`. The identity
also holds at zero denominator using Lean's total division, but consumers
of a classical difference quotient must separately require `q ≠ 0`. -/
theorem logDet_quotient_eq_averagedInverse [Add E] {H : E → Matrix ι ι ℝ} {u F : E → ℝ}
    (x d : E) (q : ℝ) (h0 : (H x).PosDef) (h1 : (H (x+d)).PosDef)
    (he0 : Real.log (H x).det + u x = F x)
    (he1 : Real.log (H (x+d)).det + u (x+d) = F (x+d)) :
    (∑ i, ∑ j, averagedInverse H d x i j * ((H (x+d) - H x) j i / q)) +
      (u (x+d) - u x) / q = (F (x+d) - F x) / q := by
  have hlog := log_det_sub_eq_sum_averaged_inverse_of_posDef h0 h1
  have hseg (θ : ℝ) : H x + θ • (H (x+d) - H x) =
      (1-θ) • H x + θ • H (x+d) := by module
  simp_rw [hseg] at hlog
  have he : (∑ i, ∑ j, averagedInverse H d x i j * (H (x+d) - H x) j i) +
      (u (x+d) - u x) = F (x+d) - F x := by
    change (∑ i, ∑ j, (∫ θ in (0 : ℝ)..1,
      ((1-θ) • H x + θ • H (x+d))⁻¹ i j) * (H (x+d)-H x) j i) + _ = _
    linarith
  calc
    _ = ((∑ i, ∑ j, averagedInverse H d x i j * (H (x+d)-H x) j i) +
        (u (x+d)-u x)) / q := by
      rw [add_div, Finset.sum_div]
      refine congrArg (· + (u (x+d) - u x) / q) (Finset.sum_congr rfl fun i _ => ?_)
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => (mul_div_assoc _ _ _).symm
    _ = _ := congrArg (fun z : ℝ => z/q) he

section UniformBounds
variable [NormedAddCommGroup E]

/-- One inverse cap for all endpoint pairs in a compact set. It is chosen
before either endpoint, interpolation parameter or displacement. -/
theorem exists_pair_inverse_cap (H : E → Matrix ι ι ℝ) {s : Set E}
    (hs : IsCompact s) (hH : ContinuousOn H s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    ∃ L : ℝ≥0, 0 < L ∧ ∀ x ∈ s, ∀ y ∈ s, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ i j,
      |((1-θ) • H x + θ • H y)⁻¹ i j| ≤ L := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let P : s × s → Matrix ι ι ℝ := fun z => H z.1
  let Q : s × s → Matrix ι ι ℝ := fun z => H z.2
  have hc : Continuous (fun x : s => H x) := hH.domRestrict
  obtain ⟨L,hL,hb⟩ := exists_uniform_inverse_entry_bound_on_compact P Q
    (hc.comp continuous_fst) (hc.comp continuous_snd)
    (fun z => hpos z.1 z.1.property) (fun z => hpos z.2 z.2.property)
  exact ⟨L,hL,fun x hx y hy θ hθ i j => hb θ hθ (⟨x,hx⟩,⟨y,hy⟩) i j⟩

/-- Uniform Hölder control of the *same* finite-difference coefficients.
The cap and Hölder constant are chosen before the displacement and the
inner set, and therefore do not deteriorate as a scalar step tends to zero.
Only containment of both endpoint sets in the fixed compact set is needed. -/
theorem exists_uniform_averagedInverse_holder
    (H : E → Matrix ι ι ℝ) {s : Set E} (hs : IsCompact s)
    (C r : ℝ≥0) (hr : 0 < r)
    (hH : ∀ i j, HolderOnWith C r (fun x => H x i j) s)
    (hpos : ∀ x ∈ s, (H x).PosDef) :
    ∃ L : ℝ≥0, 0 < L ∧
      (∀ x ∈ s, ∀ y ∈ s, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ i j,
        |((1-θ) • H x + θ • H y)⁻¹ i j| ≤ L) ∧
      ∀ (d : E) (a : Set E), a ⊆ s → (∀ x ∈ a, x+d ∈ s) → ∀ i j,
        HolderOnWith ((Fintype.card ι : ℝ≥0)^2*L^2*C) r
          (fun x => averagedInverse H d x i j) a := by
  have hc : ContinuousOn H s := continuousOn_pi.mpr fun i =>
    continuousOn_pi.mpr fun j => (hH i j).continuousOn hr
  obtain ⟨L,hL,hcap⟩ := exists_pair_inverse_cap H hs hc hpos
  refine ⟨L,hL,hcap,?_⟩
  intro d a ha hshift i j
  let P : a → Matrix ι ι ℝ := fun x => H x
  let Q : a → Matrix ι ι ℝ := fun x => H (x+d)
  have hP (k l : ι) : HolderWith C r (fun x : a => P x k l) := by
    intro x y
    exact hH k l x (ha x.property) y (ha y.property)
  have hQ (k l : ι) : HolderWith C r (fun x : a => Q x k l) := by
    intro x y
    have hh := hH k l (x+d) (hshift x x.property) (y+d) (hshift y y.property)
    simpa only [edist_add_right, Subtype.edist_eq] using hh
  have hU (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (x : a) :
      IsUnit ((1-θ) • P x + θ • Q x) := by
    have hp := hpos x (ha x.property)
    have hq := hpos (x+d) (hshift x x.property)
    by_cases hz : θ = 0
    · simpa only [hz, sub_zero, one_smul, zero_smul, add_zero] using hp.isUnit
    by_cases ho : θ = 1
    · simpa only [ho, sub_self, zero_smul, one_smul, zero_add] using hq.isUnit
    exact ((hp.smul (sub_pos.mpr (lt_of_le_of_ne hθ.2 ho))).add
      (hq.smul (lt_of_le_of_ne hθ.1 (Ne.symm hz)))).isUnit
  have hB (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (x : a) (k l : ι) :
      |((1-θ) • P x + θ • Q x)⁻¹ k l| ≤ L :=
    hcap x (ha x.property) (x+d) (hshift x x.property) θ hθ k l
  exact HolderWith.restrict_iff.mp
    (holderWith_averaged_inverse_entries P Q C r L hP hQ hU hB i j)


/-- The actual averaged coefficient inherits the cap on every integrand. -/
theorem abs_averagedInverse_le {H : E → Matrix ι ι ℝ} {s : Set E} {L : ℝ≥0}
    (hcap : ∀ x ∈ s, ∀ y ∈ s, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ i j,
      |((1-θ) • H x + θ • H y)⁻¹ i j| ≤ L)
    {x d : E} (hx : x ∈ s) (hd : x+d ∈ s) (i j : ι) :
    |averagedInverse H d x i j| ≤ L := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := (L : ℝ))
    (f := fun θ : ℝ => ((1-θ) • H x + θ • H (x+d))⁻¹ i j) (fun θ hθ => by
      have hθ' : θ ∈ Icc (0 : ℝ) 1 := by
        simp only [uIoc_of_le zero_le_one] at hθ
        exact Ioc_subset_Icc_self hθ
      simpa only [Real.norm_eq_abs] using hcap x hx (x+d) hd θ hθ' i j)
  simpa only [averagedInverse, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

end UniformBounds

end FunctionalInequalities.Analysis
