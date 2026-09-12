import FunctionalInequalities.KLS.ConditionalFiber
import FunctionalInequalities.Energy.LocalSlope.Gradient
import FunctionalInequalities.Poincare.LocalSlope.Basic
import FunctionalInequalities.L2.MeanVariance
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Conditional-fiber comparison with an explicit input constant

Source: Blueprint `lem:conditional-fiber-energy-comparison`. Read `FiberBound`, then
`energy_le_of_fiberBound` (the displayed inequality `D_{μ,ρ}(f) ≤ κ∫‖∇f‖²dμ<∞`) and
`literatureConstant_le_of_fiberBound` (the "Hence ... implies" conclusion `C_P^lit(μ) ≤ κC`).

The private lemmas are of three kinds. Isometry transport moves `Poincare.LocalSlope.Holds`
across a measure-preserving isometric equivalence, so that `Intrinsic.constant` of a law with
full affine support is the infimum of its own coordinate constants. Full-support criteria cover
an absolutely continuous law (Haar null proper affine subspaces) and a real law with nonzero
variance. The analytic core identifies the local slope of a line slice with the absolute
directional derivative at differentiability points, pushes Rademacher's null set through the
disintegration, and combines the fiber bound with Tonelli and the frame identity.

No ledger, certificate, or Blueprint `\leanok` claim is made by this module.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.KLS.ConditionalFiber

section IsometryTransport

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] [FiniteDimensional ℝ Y]

omit [InnerProductSpace ℝ X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [FiniteDimensional ℝ X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] [FiniteDimensional ℝ Y] in
/-- The local slope of a composite with an isometric equivalence is the slope at the image. -/
private theorem localSlope_apply_comp_isometryEquiv (e : X ≃ᵢ Y) (h : Y → ℝ) (x : X) :
    Energy.LocalSlope.apply (h ∘ e) x = Energy.LocalSlope.apply h (e x) := by
  unfold Energy.LocalSlope.apply
  refine iInf_congr fun r ↦ iInf_congr fun _ ↦ ?_
  have hsurj := e.surjective.iSup_comp fun y : Y ↦
    ⨆ (_ : dist y (e x) < r), ENNReal.ofReal (dist (h y) (h (e x)) / dist y (e x))
  rw [← hsurj]
  simp only [Function.comp_apply, e.dist_eq]

omit [InnerProductSpace ℝ X] [CompleteSpace X] [SecondCountableTopology X]
  [FiniteDimensional ℝ X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [SecondCountableTopology Y] [FiniteDimensional ℝ Y] in
/-- Local-slope energy is transported by a measure-preserving isometric equivalence. -/
private theorem localSlope_energy_comp_isometryEquiv (e : X ≃ᵢ Y) {ν : ProbabilityMeasure X}
    {ν' : ProbabilityMeasure Y} (hmp : MeasurePreserving e (ν : Measure X) (ν' : Measure Y))
    (h : Y → ℝ) :
    Energy.LocalSlope.energy ν' h = Energy.LocalSlope.energy ν (h ∘ e) := by
  have hemb : MeasurableEmbedding e := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  unfold Energy.LocalSlope.energy
  rw [← hmp.lintegral_comp_emb hemb]
  refine lintegral_congr fun x ↦ ?_
  rw [localSlope_apply_comp_isometryEquiv]

/-- Extended variance is transported by a measure-preserving measurable embedding. -/
private theorem evariance_comp_measurePreserving {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {T : α → β}
    (hT : MeasurePreserving T μ ν) (hTe : MeasurableEmbedding T) (h : β → ℝ) :
    evariance (h ∘ T) μ = evariance h ν := by
  unfold evariance
  have h1 : ∫ x, (h ∘ T) x ∂μ = ∫ y, h y ∂ν := hT.integral_comp hTe h
  rw [h1]
  exact hT.lintegral_comp_emb hTe fun y ↦ ‖h y - ∫ y, h y ∂ν‖ₑ ^ 2

omit [InnerProductSpace ℝ X] [CompleteSpace X] [SecondCountableTopology X]
  [FiniteDimensional ℝ X] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [SecondCountableTopology Y] [FiniteDimensional ℝ Y] in
/-- A local-slope Poincaré bound pulls back along a measure-preserving isometric equivalence. -/
private theorem holds_of_isometryEquiv (e : X ≃ᵢ Y) {ν : ProbabilityMeasure X}
    {ν' : ProbabilityMeasure Y} (hmp : MeasurePreserving e (ν : Measure X) (ν' : Measure Y))
    {C : NNReal} (h : Poincare.LocalSlope.Holds ν' C) : Poincare.LocalSlope.Holds ν C := by
  intro g hg
  have hemb : MeasurableEmbedding e := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hmp' : MeasurePreserving e.symm (ν' : Measure Y) (ν : Measure X) :=
    MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv hmp
  have hcomp : (g ∘ e.symm) ∘ e = g := by
    funext x
    simp only [Function.comp_apply, IsometryEquiv.symm_apply_apply]
  have hadm : Energy.LocalSlope.Admissible ν' (g ∘ e.symm) := by
    refine ⟨hg.locallyLipschitz.comp e.symm.isometry.lipschitz.locallyLipschitz,
      hg.memLp_two.comp_measurePreserving hmp', ?_⟩
    rw [localSlope_energy_comp_isometryEquiv e hmp, hcomp]
    exact hg.finite_energy
  have hb := h _ hadm
  rwa [localSlope_energy_comp_isometryEquiv e hmp, hcomp,
    ← evariance_comp_measurePreserving hmp hemb, hcomp] at hb

end IsometryTransport

section FullAffineSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Intrinsic reconstruction is onto when the affine support is the whole space. -/
private theorem surjective_intrinsicReconstruct (ν : ProbabilityMeasure E)
    (h : Probability.affineSupport ν = ⊤) :
    Function.Surjective (Probability.reconstruct ν) := by
  intro x
  have hx : x ∈ Probability.affineSupport ν := by
    rw [h]
    exact AffineSubspace.mem_top ℝ E x
  refine ⟨(Probability.coordinateEquiv ν).symm ⟨x, hx⟩, ?_⟩
  show (((Probability.coordinateEquiv ν) ((Probability.coordinateEquiv ν).symm ⟨x, hx⟩) :
    Probability.affineSupport ν) : E) = x
  rw [AffineIsometryEquiv.apply_symm_apply]

/-- Intrinsic reconstruction as an isometric equivalence, for full affine support. -/
private def intrinsicIsometryEquiv (ν : ProbabilityMeasure E)
    (h : Probability.affineSupport ν = ⊤) :
    (Probability.affineSupport ν).direction ≃ᵢ E where
  toEquiv := Equiv.ofBijective (Probability.reconstruct ν)
    ⟨(Probability.reconstruct ν).injective, surjective_intrinsicReconstruct ν h⟩
  isometry_toFun := (Probability.reconstruct ν).isometry

omit [CompleteSpace E] in
/-- For full affine support, coordinate and intrinsic local-slope bounds coincide. -/
private theorem holds_iff_intrinsicMeasure (ν : ProbabilityMeasure E)
    (h : Probability.affineSupport ν = ⊤) (C : NNReal) :
    Poincare.LocalSlope.Holds ν C ↔
      Poincare.LocalSlope.Holds (Probability.intrinsicMeasure ν) C := by
  let e := intrinsicIsometryEquiv ν h
  have hmp : MeasurePreserving e (Probability.intrinsicMeasure ν : Measure _) (ν : Measure E) :=
    Probability.measurePreserving_reconstruct ν
  constructor
  · intro hC
    exact holds_of_isometryEquiv e hmp hC
  · intro hC
    exact holds_of_isometryEquiv e.symm
      (MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv hmp) hC

omit [CompleteSpace E] in
/-- For full affine support, the literature constant is the coordinate infimum. -/
private theorem intrinsic_constant_eq_iInf (ν : ProbabilityMeasure E)
    (h : Probability.affineSupport ν = ⊤) :
    Poincare.LocalSlope.Intrinsic.constant ν =
      ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds ν C}, (C.1 : ENNReal) := by
  unfold Poincare.LocalSlope.Intrinsic.constant
  apply le_antisymm
  · exact le_iInf fun C ↦
      iInf_le_of_le ⟨C.1, (holds_iff_intrinsicMeasure ν h C.1).1 C.2⟩ le_rfl
  · exact le_iInf fun C ↦
      iInf_le_of_le ⟨C.1, (holds_iff_intrinsicMeasure ν h C.1).2 C.2⟩ le_rfl

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] in
/-- A finite upper bound for the coordinate infimum is valid for every single admissible test. -/
private theorem evariance_le_mul_energy_of_iInf_le (ν : ProbabilityMeasure E) {B : ENNReal}
    (hB : B ≠ ⊤)
    (hle : ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds ν C}, (C.1 : ENNReal) ≤ B)
    {g : E → ℝ} (hg : Energy.LocalSlope.Admissible ν g) :
    evariance g (ν : Measure E) ≤ B * Energy.LocalSlope.energy ν g := by
  have : Nonempty {C : NNReal // Poincare.LocalSlope.Holds ν C} := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    rw [iInf_of_empty] at hle
    exact hB (top_le_iff.mp hle)
  calc evariance g (ν : Measure E)
      ≤ ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds ν C},
          (C.1 : ENNReal) * Energy.LocalSlope.energy ν g := le_iInf fun C ↦ C.2 g hg
    _ = (⨅ C : {C : NNReal // Poincare.LocalSlope.Holds ν C}, (C.1 : ENNReal)) *
          Energy.LocalSlope.energy ν g :=
        (ENNReal.iInf_mul fun htop _ ↦ absurd htop hg.finite_energy).symm
    _ ≤ B * Energy.LocalSlope.energy ν g := mul_le_mul_left hle _

omit [CompleteSpace E] in
/-- An absolutely continuous law has full affine support: proper affine subspaces are Haar null. -/
theorem affineSupport_eq_top_of_absolutelyContinuous (μ : ProbabilityMeasure E)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m) :
    Probability.affineSupport μ = ⊤ := by
  by_contra hne
  have h0 : (μ : Measure E) (Probability.affineSupport μ : Set E) = 0 :=
    hac (Measure.addHaar_affineSubspace m _ hne)
  have h1 := measure_add_measure_compl (μ := (μ : Measure E))
    (Probability.measurableSet_affineSupport μ)
  rw [h0, Probability.measure_compl_affineSupport μ, measure_univ] at h1
  simp at h1

/-- A real law with nonzero variance has full affine support. -/
private theorem affineSupport_eq_top_of_evariance_ne_zero (ν : ProbabilityMeasure ℝ)
    (h : evariance id (ν : Measure ℝ) ≠ 0) : Probability.affineSupport ν = ⊤ := by
  by_contra hne
  have hnon : ((Probability.affineSupport ν : AffineSubspace ℝ ℝ) : Set ℝ).Nonempty :=
    ⟨_, (Probability.origin ν).2⟩
  have hdir : (Probability.affineSupport ν).direction ≠ ⊤ := fun htop ↦
    hne ((AffineSubspace.direction_eq_top_iff_of_nonempty hnon).1 htop)
  have hbot : (Probability.affineSupport ν).direction = ⊥ := by
    have hlt := Submodule.finrank_lt hdir
    rw [Module.finrank_self, Nat.lt_one_iff] at hlt
    exact Submodule.finrank_eq_zero.1 hlt
  have hconst : ∀ x ∈ Probability.affineSupport ν, x = Probability.supportPoint ν := by
    intro x hx
    have hmem := AffineSubspace.vsub_mem_direction hx (Probability.origin ν).2
    rw [hbot, Submodule.mem_bot, vsub_eq_sub, sub_eq_zero] at hmem
    exact hmem
  have hae : (id : ℝ → ℝ) =ᵐ[(ν : Measure ℝ)] fun _ ↦ Probability.supportPoint ν := by
    filter_upwards [Probability.ae_mem_affineSupport ν] with x hx
    exact hconst x hx
  refine h ?_
  rw [evariance_congr hae]
  simp [evariance]

end FullAffineSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

section LineSlice

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] in
/-- Reconstruction along a unit direction is `1`-Lipschitz in the scalar coordinate. -/
private theorem lipschitzWith_reconstruct (b : Direction E × E) :
    LipschitzWith 1 (reconstruct b) := by
  refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
  simp only [reconstruct, dist_eq_norm, NNReal.coe_one, one_mul, add_sub_add_left_eq_sub,
    ← sub_smul, norm_smul, b.1.2, mul_one, le_refl]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] in
/-- The line slice of a differentiable point has the directional derivative as derivative. -/
private theorem hasDerivAt_comp_reconstruct {f : E → ℝ} {b : Direction E × E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (reconstruct b t)) :
    HasDerivAt (fun s ↦ f (reconstruct b s)) (fderiv ℝ f (reconstruct b t) b.1.1) t := by
  have h1 : HasDerivAt (reconstruct b) b.1.1 t := by
    unfold reconstruct
    simpa using ((hasDerivAt_id t).smul_const b.1.1).const_add b.2
  exact hf.hasFDerivAt.comp_hasDerivAt t h1

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] in
/-- At a differentiable point, the local slope of the line slice is the absolute directional
derivative. -/
private theorem localSlope_apply_comp_reconstruct {f : E → ℝ} {b : Direction E × E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (reconstruct b t)) :
    Energy.LocalSlope.apply (fun s ↦ f (reconstruct b s)) t =
      ENNReal.ofReal |fderiv ℝ f (reconstruct b t) b.1.1| := by
  have hd := hasDerivAt_comp_reconstruct hf
  rw [Energy.LocalSlope.apply_eq_norm_gradient _ _ hd.differentiableAt,
    hd.hasGradientAt.gradient]
  simp [Real.norm_eq_abs]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- The directional derivative is the inner product of the direction with the gradient. -/
private theorem fderiv_apply_eq_inner_gradient (f : E → ℝ) (x θ : E) :
    fderiv ℝ f x θ = inner ℝ θ (gradient f x) := by
  show fderiv ℝ f x θ = inner ℝ θ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

/-- The squared directional derivative `⟪θ, ∇f(z + tθ)⟫²`, as a function of the joint fiber
coordinate `((θ, z), t)`. -/
private def directionalIntegrand (f : E → ℝ) (q : (Direction E × E) × ℝ) : ENNReal :=
  ENNReal.ofReal (inner ℝ q.1.1.1 (gradient f (reconstruct q.1 q.2)) ^ 2)

omit [FiniteDimensional ℝ E] in
private theorem measurable_directionalIntegrand (f : E → ℝ) :
    Measurable (directionalIntegrand f) := by
  unfold directionalIntegrand
  have h1 : Measurable fun q : (Direction E × E) × ℝ ↦ gradient f (reconstruct q.1 q.2) :=
    (Energy.Euclidean.LipschitzApproximation.measurable_gradient f).comp measurable_reconstruct
  have h2 : Measurable fun q : (Direction E × E) × ℝ ↦ (q.1.1.1 : E) := by fun_prop
  exact ENNReal.measurable_ofReal.comp ((h2.inner h1).pow_const 2)

end LineSlice

section Disintegration

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A measurable almost-sure property of `μ` holds along almost every conditional fiber. -/
private theorem ae_ae_reconstruct (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    {P : E → Prop} (hP : MeasurableSet {x | P x}) (hμ : ∀ᵐ x ∂(μ : Measure E), P x) :
    ∀ᵐ b ∂baseLaw μ ρ, ∀ᵐ t ∂kernel μ ρ b, P (reconstruct b t) := by
  have hS : MeasurableSet {q : (Direction E × E) × ℝ | P (reconstruct q.1 q.2)} :=
    measurable_reconstruct hP
  have hjoint : ∀ᵐ q ∂jointLaw μ ρ, P (reconstruct q.1 q.2) := by
    rw [jointLaw, ae_map_iff measurable_coordinates.aemeasurable hS]
    simp only [reconstruct_coordinates]
    rw [ae_iff]
    have hN : MeasurableSet {x : E | ¬ P x} := hP.compl
    have : ((ρ : Measure (Direction E)).prod (μ : Measure E)) {p | ¬ P p.2} =
        ((ρ : Measure (Direction E)).prod (μ : Measure E)).snd {x | ¬ P x} :=
      (Measure.snd_apply hN).symm
    rw [this, Measure.snd_prod]
    exact ae_iff.1 hμ
  rw [← compProd_baseLaw_kernel] at hjoint
  exact Measure.ae_ae_of_ae_compProd hjoint

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A square-integrable Borel test is square integrable along almost every conditional fiber. -/
private theorem ae_memLp_comp_reconstruct (μ : ProbabilityMeasure E)
    (ρ : ProbabilityMeasure (Direction E)) {f : E → ℝ} (hfm : Measurable f)
    (hf₂ : MemLp f 2 (μ : Measure E)) :
    ∀ᵐ b ∂baseLaw μ ρ, MemLp (fun t ↦ f (reconstruct b t)) 2 (kernel μ ρ b) := by
  have hmeas : Measurable (fun q : (Direction E × E) × ℝ ↦ ‖f (reconstruct q.1 q.2)‖ₑ ^ (2 : ℝ)) :=
    (hfm.comp measurable_reconstruct).enorm.pow_const _
  have hfin : ∫⁻ b, ∫⁻ t, ‖f (reconstruct b t)‖ₑ ^ (2 : ℝ) ∂kernel μ ρ b ∂baseLaw μ ρ < ⊤ := by
    rw [← Measure.lintegral_compProd hmeas, compProd_baseLaw_kernel, jointLaw,
      lintegral_map hmeas measurable_coordinates]
    simp only [reconstruct_coordinates]
    have hFm : Measurable fun p : Direction E × E ↦ ‖f p.2‖ₑ ^ (2 : ℝ) :=
      (hfm.comp measurable_snd).enorm.pow_const _
    rw [lintegral_prod_symm _ hFm.aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (f := f) (μ := (μ : Measure E))
      (p := 2) two_ne_zero ENNReal.ofNat_ne_top).1 hf₂.2
    simpa using h
  have hm : Measurable fun b ↦ ∫⁻ t, ‖f (reconstruct b t)‖ₑ ^ (2 : ℝ) ∂kernel μ ρ b :=
    Measurable.lintegral_kernel_prod_right' hmeas
  filter_upwards [ae_lt_top hm hfin.ne] with b hb
  refine ⟨(hfm.comp (measurable_reconstruct_left b)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simpa using hb

end Disintegration

/-- The Blueprint's fiber hypothesis: for almost every nondegenerate conditional fiber, the
literature Poincaré constant of the (one-dimensional) fiber law is at most `κ` times the fiber's
own scalar variance `Var_{μ_{θ,z}}(T)`. Degenerate fibers are unconstrained, matching `energyAt`'s
convention of contributing zero there. -/
def FiberBound (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) (κ : NNReal) :
    Prop :=
  ∀ᵐ b ∂baseLaw μ ρ, Nondegenerate (kernel μ ρ) b →
    Poincare.LocalSlope.Intrinsic.constant
        (⟨kernel μ ρ b, inferInstance⟩ : ProbabilityMeasure ℝ) ≤
      (κ : ENNReal) * evariance id (kernel μ ρ b)

/-- Every admissible-frame, locally Lipschitz, finite-gradient-energy test compares to the
conditional-fiber energy with factor `κ`, given the fiber hypothesis: this is the displayed
inequality `D_{μ,ρ}(f) ≤ κ∫‖∇f‖²dμ<∞` of the Blueprint lemma. -/
theorem energy_le_of_fiberBound (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (hρ : Admissible μ ρ) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (hac : (μ : Measure E) ≪ m) {κ : NNReal} (hfiber : FiberBound μ ρ κ)
    {f : E → ℝ} (hf : Energy.LocalSlope.Admissible μ f) :
    energy μ ρ f ≤ (κ : ENNReal) * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤ := by
  classical
  set d : ENNReal := (Module.finrank ℝ E : ENNReal) with hd
  have hfm : Measurable f := hf.locallyLipschitz.continuous.measurable
  -- Rademacher on the ambient law.
  have hdiff : ∀ᵐ x ∂(μ : Measure E), DifferentiableAt ℝ f x :=
    hac.ae_le (Energy.Euclidean.LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
      hf.locallyLipschitz m)
  -- Tonelli: the iterated fiber integral of the squared directional derivative.
  have hF : ∀ p : Direction E × E, directionalIntegrand f (coordinates p) =
      ENNReal.ofReal (inner ℝ p.1.1 (gradient f p.2) ^ 2) := by
    intro p
    show ENNReal.ofReal
      (inner ℝ p.1.1 (gradient f (reconstruct (coordinates p).1 (coordinates p).2)) ^ 2) = _
    rw [reconstruct_coordinates]
  have hθ : Measurable fun p : Direction E × E ↦ (p.1.1 : E) := by fun_prop
  have hg : Measurable fun p : Direction E × E ↦ gradient f p.2 :=
    (Energy.Euclidean.LipschitzApproximation.measurable_gradient f).comp measurable_snd
  have hFm : Measurable fun p : Direction E × E ↦
      ENNReal.ofReal (inner ℝ p.1.1 (gradient f p.2) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hθ.inner hg).pow_const 2)
  have hI : ∫⁻ b, ∫⁻ t, directionalIntegrand f (b, t) ∂kernel μ ρ b ∂baseLaw μ ρ =
      ∫⁻ x, ∫⁻ θ, ENNReal.ofReal (inner ℝ θ.1 (gradient f x) ^ 2)
        ∂(ρ : Measure (Direction E)) ∂(μ : Measure E) := by
    rw [← Measure.lintegral_compProd (measurable_directionalIntegrand f),
      compProd_baseLaw_kernel, jointLaw,
      lintegral_map (measurable_directionalIntegrand f) measurable_coordinates]
    simp only [hF]
    exact lintegral_prod_symm _ hFm.aemeasurable
  -- The frame identity at a fixed point.
  have hframe : ∀ x : E, d * ∫⁻ θ, ENNReal.ofReal (inner ℝ θ.1 (gradient f x) ^ 2)
      ∂(ρ : Measure (Direction E)) = ENNReal.ofReal ‖gradient f x‖ ^ 2 := by
    intro x
    set u := gradient f x
    have hint : Integrable (fun θ : Direction E ↦ inner ℝ θ.1 u * inner ℝ θ.1 u)
        (ρ : Measure (Direction E)) := by
      refine Integrable.of_bound ?_ (‖u‖ * ‖u‖) (Filter.Eventually.of_forall fun θ ↦ ?_)
      · exact ((continuous_subtype_val.inner continuous_const).mul
          (continuous_subtype_val.inner continuous_const)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        have h1 : |inner ℝ θ.1 u| ≤ ‖u‖ := by
          calc |inner ℝ θ.1 u| ≤ ‖θ.1‖ * ‖u‖ := abs_real_inner_le_norm _ _
            _ = ‖u‖ := by rw [θ.2, one_mul]
        exact mul_le_mul h1 h1 (abs_nonneg _) (norm_nonneg _)
    have hnn : 0 ≤ᵐ[(ρ : Measure (Direction E))]
        fun θ : Direction E ↦ inner ℝ θ.1 u * inner ℝ θ.1 u :=
      Filter.Eventually.of_forall fun θ ↦ mul_self_nonneg _
    have hlin : ∫⁻ θ, ENNReal.ofReal (inner ℝ θ.1 u ^ 2) ∂(ρ : Measure (Direction E)) =
        ENNReal.ofReal (∫ θ, inner ℝ θ.1 u * inner ℝ θ.1 u ∂(ρ : Measure (Direction E))) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
      simp only [sq]
    rw [hlin, hd, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      hρ.frame_identity u u, real_inner_self_eq_norm_sq, ENNReal.ofReal_pow (norm_nonneg _)]
  -- Finiteness of the total directional integral.
  have hItot : ∫⁻ b, ∫⁻ t, directionalIntegrand f (b, t) ∂kernel μ ρ b ∂baseLaw μ ρ ≠ ⊤ := by
    have h1 : (1 : ENNReal) ≤ d := by
      rw [hd]
      exact_mod_cast hρ.positive_dimension
    refine ne_top_of_le_ne_top
      (b := ∫⁻ x, ENNReal.ofReal ‖gradient f x‖ ^ 2 ∂(μ : Measure E)) ?_ ?_
    · rw [← Energy.LocalSlope.energy_eq_lintegral_gradient μ m hac f hf.locallyLipschitz]
      exact hf.finite_energy
    · rw [hI]
      refine lintegral_mono fun x ↦ ?_
      rw [← hframe x]
      exact le_mul_of_one_le_left zero_le h1
  -- The fiberwise bound, almost everywhere in the base point.
  have hslice_diff : ∀ᵐ b ∂baseLaw μ ρ, ∀ᵐ t ∂kernel μ ρ b,
      DifferentiableAt ℝ f (reconstruct b t) :=
    ae_ae_reconstruct μ ρ (measurableSet_of_differentiableAt ℝ f) hdiff
  have hslice_L2 := ae_memLp_comp_reconstruct μ ρ hfm hf.memLp_two
  have hslice_fin : ∀ᵐ b ∂baseLaw μ ρ,
      ∫⁻ t, directionalIntegrand f (b, t) ∂kernel μ ρ b ≠ ⊤ := by
    have hm : Measurable fun b ↦ ∫⁻ t, directionalIntegrand f (b, t) ∂kernel μ ρ b :=
      Measurable.lintegral_kernel_prod_right' (measurable_directionalIntegrand f)
    filter_upwards [ae_lt_top hm hItot] with b hb
    exact hb.ne
  have hfiberwise : ∀ᵐ b ∂baseLaw μ ρ, energyAt (kernel μ ρ) b f ≤
      (κ : ENNReal) * ∫⁻ t, directionalIntegrand f (b, t) ∂kernel μ ρ b := by
    filter_upwards [hfiber, hslice_diff, hslice_L2, hslice_fin] with b hb hdiffb hL2b hfinb
    by_cases hnd : Nondegenerate (kernel μ ρ) b
    · set ν : ProbabilityMeasure ℝ := ⟨kernel μ ρ b, inferInstance⟩ with hν
      have henergy : Energy.LocalSlope.energy ν (fun t ↦ f (reconstruct b t)) =
          ∫⁻ t, directionalIntegrand f (b, t) ∂kernel μ ρ b := by
        unfold Energy.LocalSlope.energy
        refine lintegral_congr_ae ?_
        filter_upwards [hdiffb] with t ht
        rw [localSlope_apply_comp_reconstruct ht, fderiv_apply_eq_inner_gradient]
        simp only [directionalIntegrand]
        rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      have hadm : Energy.LocalSlope.Admissible ν (fun t ↦ f (reconstruct b t)) :=
        ⟨hf.locallyLipschitz.comp (lipschitzWith_reconstruct b).locallyLipschitz, hL2b,
          by rw [henergy]; exact hfinb⟩
      have hV : evariance id (kernel μ ρ b) ≠ ⊤ := (evariance_lt_top hnd.2.1).ne
      have htop : (κ : ENNReal) * evariance id (kernel μ ρ b) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top hV
      have hconst : ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds ν C}, (C.1 : ENNReal) ≤
          (κ : ENNReal) * evariance id (kernel μ ρ b) :=
        (intrinsic_constant_eq_iInf ν
          (affineSupport_eq_top_of_evariance_ne_zero ν hnd.2.2)).symm.trans_le (hb hnd)
      have hineq := evariance_le_mul_energy_of_iInf_le ν htop hconst hadm
      rw [henergy] at hineq
      unfold energyAt
      rw [if_pos hnd, ENNReal.div_le_iff hnd.2.2 hV]
      calc evariance (fun t ↦ f (reconstruct b t)) (kernel μ ρ b)
          ≤ (κ : ENNReal) * evariance id (kernel μ ρ b) *
            ∫⁻ t, directionalIntegrand f (b, t) ∂kernel μ ρ b := hineq
        _ = (κ : ENNReal) * (∫⁻ t, directionalIntegrand f (b, t) ∂kernel μ ρ b) *
            evariance id (kernel μ ρ b) := by ring
    · unfold energyAt
      rw [if_neg hnd]
      exact zero_le
  -- Assemble.
  have hmain : energy μ ρ f ≤ (κ : ENNReal) * Energy.LocalSlope.energy μ f := by
    calc energy μ ρ f = d * ∫⁻ b, energyAt (kernel μ ρ) b f ∂baseLaw μ ρ := rfl
      _ ≤ d * ∫⁻ b, (κ : ENNReal) * ∫⁻ t, directionalIntegrand f (b, t) ∂kernel μ ρ b
            ∂baseLaw μ ρ := mul_le_mul_right (lintegral_mono_ae hfiberwise) _
      _ = (κ : ENNReal) *
            (d * ∫⁻ b, ∫⁻ t, directionalIntegrand f (b, t) ∂kernel μ ρ b ∂baseLaw μ ρ) := by
          rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
          ring
      _ = (κ : ENNReal) * ∫⁻ x, d * ∫⁻ θ, ENNReal.ofReal (inner ℝ θ.1 (gradient f x) ^ 2)
            ∂(ρ : Measure (Direction E)) ∂(μ : Measure E) := by
          rw [hI, lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
      _ = (κ : ENNReal) * ∫⁻ x, ENNReal.ofReal ‖gradient f x‖ ^ 2 ∂(μ : Measure E) := by
          simp only [hframe]
      _ = (κ : ENNReal) * Energy.LocalSlope.energy μ f := by
          rw [Energy.LocalSlope.energy_eq_lintegral_gradient μ m hac f hf.locallyLipschitz]
  exact ⟨hmain, ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hf.finite_energy) hmain⟩

/-- The Blueprint's "Hence": given the fiber hypothesis, a finite form-gap bound
`Var_μ(f) ≤ C·D_{μ,ρ}(f)` on the maximal finite conditional-fiber domain transfers to the bound
`C_P^lit(μ) ≤ κC` on the literature Poincaré constant of `μ` itself. -/
theorem literatureConstant_le_of_fiberBound
    (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m)
    {κ : NNReal} (hfiber : FiberBound μ ρ κ)
    {C : NNReal}
    (hform : ∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (κ : ENNReal) * (C : ENNReal) := by
  have htop : Probability.affineSupport μ = ⊤ :=
    affineSupport_eq_top_of_absolutelyContinuous μ m hac
  have hholds : Poincare.LocalSlope.Holds μ (κ * C) := by
    intro f hf
    obtain ⟨hle, hne⟩ := energy_le_of_fiberBound μ ρ hρ m hac hfiber hf
    have hfm : Measurable f := hf.locallyLipschitz.continuous.measurable
    have hmem : hf.memLp_two.toLp f ∈ domain μ ρ := by
      show form μ ρ _ ≠ ⊤
      rw [form_toLp μ ρ f hfm hf.memLp_two]
      exact hne
    have hform' := hform _ hmem
    rw [form_toLp μ ρ f hfm hf.memLp_two, L2.variance_toLp] at hform'
    have hvar : ((ProbabilityTheory.variance f (μ : Measure E)).toNNReal : ENNReal) =
        evariance f (μ : Measure E) := ofReal_variance hf.memLp_two
    rw [hvar] at hform'
    calc evariance f (μ : Measure E) ≤ (C : ENNReal) * energy μ ρ f := hform'
      _ ≤ (C : ENNReal) * ((κ : ENNReal) * Energy.LocalSlope.energy μ f) :=
          mul_le_mul_right hle _
      _ = ((κ * C : NNReal) : ENNReal) * Energy.LocalSlope.energy μ f := by
          push_cast
          ring
  unfold Poincare.LocalSlope.Intrinsic.constant
  exact iInf_le_of_le ⟨κ * C, (holds_iff_intrinsicMeasure μ htop _).1 hholds⟩
    (ENNReal.coe_mul κ C).le

end FunctionalInequalities.KLS.ConditionalFiber
