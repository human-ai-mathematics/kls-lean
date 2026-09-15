import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The divergence of a vector field

Base layer for the Gauss–Green theorem of the relative-perimeter chain: the divergence
`div F x = tr (DF x)`, together with the rank-one trace computation that turns the vector-field
form of Gauss–Green into its scalar-test form.  Every statement here is proved and uses only the
standard axioms; the module contains no `sorry`.

`divergence_smul_const` is the bridge: for a fixed vector `v`, the field `F x = η x • v` has
`div F = ⟪∇η, v⟫`, because the derivative `D F x = (Dη x) ⊗ v` is a rank-one map whose trace is
`Dη x v`.  Taking `F = η • v` in the vector-field Gauss–Green identity and using `integral_inner`
in both integrals gives the scalar-test identity `∫_U ∇η = ∫_{∂U} η ν`.  The definition moved here
from `KLS/WIP/AnalyticPrerequisites.lean`, which keeps only the unfinished obligations.

`traceLM` presents `divergence` as the composition of the continuous linear functional
`M ↦ tr M` on `V →L[ℝ] V` with `x ↦ DF x`.  That is what gives `continuous_divergence`,
`hasCompactSupport_divergence` and the additivity `divergence_finset_sum` over a finite family —
the three facts a partition-of-unity argument needs in order to split a divergence integral into
finitely many local pieces.
-/

noncomputable section

namespace FunctionalInequalities.Analysis

universe u

section Divergence

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The divergence `div F x = tr (DF x)` of a vector field, as the trace of its Fréchet
derivative; zero where `F` is not differentiable. -/
def divergence (F : V → V) (x : V) : ℝ :=
  LinearMap.trace ℝ V (fderiv ℝ F x).toLinearMap

/-- A function vanishing outside its support has vanishing derivative there.  Moved down from
`Analysis/SubgraphDivergence.lean`, which still uses it, so that the support lemmas of the
divergence can live next to the definition. -/
theorem fderiv_eq_zero_of_notMem_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : V → E} {x : V} (hx : x ∉ tsupport F) : fderiv ℝ F x = 0 := by
  have heq : F =ᶠ[nhds x] fun _ => (0 : E) := by
    filter_upwards [(isOpen_compl_iff.mpr (isClosed_tsupport F)).mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [heq.fderiv_eq]
  simp

end Divergence

section RankOne

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The trace of the rank-one map `w ↦ φ w • v` is `φ v`. -/
theorem trace_smulRight (φ : V →ₗ[ℝ] ℝ) (v : V) :
    LinearMap.trace ℝ V (LinearMap.smulRight φ v) = φ v := by
  have hrank : LinearMap.smulRight φ v = dualTensorHom ℝ V V (φ ⊗ₜ[ℝ] v) := by
    ext w
    simp [dualTensorHom_apply]
  rw [hrank, LinearMap.trace_eq_contract_apply, contractLeft_apply]

/-- The divergence of `x ↦ η x • v` for a constant vector `v` is the directional derivative of `η`
along `v`.  This is the identity that reduces the scalar-test form of Gauss–Green to the
vector-field form. -/
theorem divergence_smul_const {η : V → ℝ} {x : V} (hη : DifferentiableAt ℝ η x) (v : V) :
    divergence (fun y => η y • v) x = fderiv ℝ η x v := by
  have hd : HasFDerivAt (fun y => η y • v) ((fderiv ℝ η x).smulRight v) x :=
    HasFDerivAt.smul_const hη.hasFDerivAt v
  rw [divergence, hd.fderiv]
  have hcoe : ((fderiv ℝ η x).smulRight v : V →L[ℝ] V).toLinearMap
      = LinearMap.smulRight (fderiv ℝ η x).toLinearMap v := by
    ext w; simp
  rw [hcoe, trace_smulRight]
  rfl

end RankOne

/-! ### The divergence as a continuous functional of the derivative -/

section Trace

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The trace as a linear functional on the continuous endomorphisms of `V`.  On a
finite-dimensional space it is automatically continuous (`continuous_traceLM`), which is what
makes `divergence F` continuous for a `C¹` field. -/
def traceLM : (V →L[ℝ] V) →ₗ[ℝ] ℝ where
  toFun M := LinearMap.trace ℝ V M.toLinearMap
  map_add' M M' := by
    have h : ((M + M' : V →L[ℝ] V)).toLinearMap = M.toLinearMap + M'.toLinearMap := rfl
    rw [h, map_add]
  map_smul' c M := by
    have h : ((c • M : V →L[ℝ] V)).toLinearMap = c • M.toLinearMap := rfl
    rw [h, map_smul]
    rfl

omit [FiniteDimensional ℝ V] in
theorem traceLM_apply (M : V →L[ℝ] V) : traceLM M = LinearMap.trace ℝ V M.toLinearMap := rfl

theorem continuous_traceLM : Continuous (traceLM (V := V)) :=
  LinearMap.continuous_of_finiteDimensional (traceLM (V := V))

omit [FiniteDimensional ℝ V] in
theorem divergence_eq_traceLM (F : V → V) (x : V) : divergence F x = traceLM (fderiv ℝ F x) := rfl

/-- The divergence of a `C¹` vector field is continuous. -/
theorem continuous_divergence {F : V → V} (hF : ContDiff ℝ 1 F) : Continuous (divergence F) :=
  continuous_traceLM.comp (hF.continuous_fderiv one_ne_zero)

omit [FiniteDimensional ℝ V] in
/-- A field vanishing on a neighbourhood of `x` has vanishing divergence at `x`. -/
theorem divergence_eq_zero_of_notMem_tsupport {F : V → V} {x : V} (hx : x ∉ tsupport F) :
    divergence F x = 0 := by
  rw [divergence, fderiv_eq_zero_of_notMem_tsupport hx]
  simp

omit [FiniteDimensional ℝ V] in
/-- The divergence of a compactly supported field is compactly supported. -/
theorem hasCompactSupport_divergence {F : V → V} (hF : HasCompactSupport F) :
    HasCompactSupport (divergence F) :=
  HasCompactSupport.intro hF fun _ hx => divergence_eq_zero_of_notMem_tsupport hx

omit [FiniteDimensional ℝ V] in
/-- The divergence is additive over a finite family of fields differentiable at the point. -/
theorem divergence_finset_sum {γ : Type*} (s : Finset γ) {G : γ → V → V} {x : V}
    (hG : ∀ i ∈ s, DifferentiableAt ℝ (G i) x) :
    divergence (fun y => ∑ i ∈ s, G i y) x = ∑ i ∈ s, divergence (G i) x := by
  have heq : (∑ i ∈ s, G i) = fun y => ∑ i ∈ s, G i y := by
    funext y; simp
  have hd : HasFDerivAt (fun y => ∑ i ∈ s, G i y) (∑ i ∈ s, fderiv ℝ (G i) x) x := by
    rw [← heq]
    exact HasFDerivAt.sum fun i hi => (hG i hi).hasFDerivAt
  rw [divergence_eq_traceLM, hd.fderiv, map_sum]
  rfl

end Trace

end FunctionalInequalities.Analysis
