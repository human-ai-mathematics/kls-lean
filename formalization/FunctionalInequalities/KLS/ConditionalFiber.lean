import FunctionalInequalities.Probability.Moments
import FunctionalInequalities.Probability.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.Moments.Variance

/-!
# Conditional-fiber energy: construction and proved well-definedness contracts

Source: Blueprint `def:conditional-fiber-form`, with the pinned conditional-frame route.
Read `Admissible`, `jointLaw`, `energyAt`, `energy`, `form`, and then the well-definedness theorems.
One disintegration of the joint law of `((θ, z), T)` gives joint measurability in `(θ, z)`.
We use an ordinary product base `Direction E × E`; nonorthogonal base points contribute zero.

The integral and the chosen-representative L² function are implemented, and the six
well-definedness contracts (iterated base integral, a.e. finite conditional second moment, joint
measurability, version independence, representative independence and the L² identification) are
fully proved.
No closedness, Markov property, frame bound, Poincare inequality or KLS result is asserted.
An admissible frame has positive dimension; there is no zero-dimensional sphere probability.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.KLS.ConditionalFiber

variable (E : Type*) [NormedAddCommGroup E]

/-- Unit directions, with their Borel subtype structure. -/
abbrev Direction := {θ : E // ‖θ‖ = 1}

variable {E} [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Antipodal map used to state that a direction law is even. -/
def antipode (θ : Direction E) : Direction E := ⟨-θ.1, by simp [θ.2]⟩

/-- The hypotheses of the Blueprint definition. The bilinear identity expresses
`d ∫ θ θᵀ dρ = I` without choosing a matrix basis. -/
structure Admissible (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) : Prop where
  positive_dimension : 0 < Module.finrank ℝ E
  memLp_two : MemLp id 2 (μ : Measure E)
  even : Measure.map antipode (ρ : Measure (Direction E)) = (ρ : Measure (Direction E))
  frame_identity : ∀ u v : E,
    (Module.finrank ℝ E : ℝ) *
      (∫ θ, inner ℝ θ.1 u * inner ℝ θ.1 v ∂(ρ : Measure (Direction E))) = inner ℝ u v

/-- Joint coordinates `((θ, P_{θ⊥} x), ⟨x, θ⟩)`, in a fixed product base space. -/
def coordinates (p : Direction E × E) : (Direction E × E) × ℝ :=
  ((p.1, p.2 - (inner ℝ p.2 p.1.1) • p.1.1), inner ℝ p.2 p.1.1)

/-- Reconstruct an ambient point from its base and scalar fiber coordinate. -/
def reconstruct (b : Direction E × E) (t : ℝ) : E := b.2 + t • b.1.1

/-- The joint coordinate map is measurable. -/
theorem measurable_coordinates : Measurable (coordinates (E := E)) := by
  unfold coordinates
  fun_prop

/-- The pushforward of `ρ ⊗ μ` by the joint coordinate map. -/
def jointLaw (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) :
    Measure ((Direction E × E) × ℝ) :=
  ((ρ : Measure (Direction E)).prod (μ : Measure E)).map coordinates

instance instIsProbabilityMeasureJointLaw (μ : ProbabilityMeasure E)
    (ρ : ProbabilityMeasure (Direction E)) : IsProbabilityMeasure (jointLaw μ ρ) :=
  Measure.isProbabilityMeasure_map measurable_coordinates.aemeasurable

/-- Joint base law of `(θ, z)`, supported on `z ⟂ θ` almost everywhere. -/
def baseLaw (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) :
    Measure (Direction E × E) := (jointLaw μ ρ).fst

instance instIsProbabilityMeasureBaseLaw (μ : ProbabilityMeasure E)
    (ρ : ProbabilityMeasure (Direction E)) : IsProbabilityMeasure (baseLaw μ ρ) :=
  inferInstanceAs (IsProbabilityMeasure (jointLaw μ ρ).fst)

/-- A jointly measurable Markov conditional kernel obtained from Mathlib disintegration. -/
def kernel (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) :
    Kernel (Direction E × E) ℝ := (jointLaw μ ρ).condKernel

instance instIsMarkovKernel (μ : ProbabilityMeasure E)
    (ρ : ProbabilityMeasure (Direction E)) : IsMarkovKernel (kernel μ ρ) :=
  inferInstanceAs (IsMarkovKernel (jointLaw μ ρ).condKernel)

/-- A nondegenerate conditional fiber has an orthogonal base point, finite scalar second moment
and nonzero variance. These three conditions are part of this predicate's contract.
Since conditional kernels are probability kernels, `MemLp` rules out infinite variance. -/
def Nondegenerate (κ : Kernel (Direction E × E) ℝ) (b : Direction E × E) : Prop :=
  inner ℝ b.2 b.1.1 = 0 ∧ MemLp id 2 (κ b) ∧ evariance id (κ b) ≠ 0

/-- Extended normalized fiber variance. Exceptional, infinite-second-moment and
zero-variance fibers contribute zero explicitly, before any division. -/
def energyAt (κ : Kernel (Direction E × E) ℝ) (b : Direction E × E)
    (f : E → ℝ) : ENNReal := by
  classical
  exact if Nondegenerate κ b then
    evariance (fun t ↦ f (reconstruct b t)) (κ b) / evariance id (κ b) else 0

/-- Formula with a supplied conditional version; the disintegration premise belongs to
the version-independence contract below, not to this total integral expression. -/
def energyWithKernel (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (κ : Kernel (Direction E × E) ℝ) (f : E → ℝ) : ENNReal :=
  (Module.finrank ℝ E : ENNReal) * ∫⁻ b, energyAt κ b f ∂baseLaw μ ρ

/-- The conditional-fiber energy of a concrete Borel representative, using the chosen kernel. -/
def energy (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) (f : E → ℝ) :
    ENNReal := energyWithKernel μ ρ (kernel μ ρ) f

/-- The chosen-representative function on L² classes. `Lp` supplies a strongly measurable
representative. Agreement with every Borel representative is the draft `form_toLp` contract. -/
def form (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (f : Lp ℝ 2 (μ : Measure E)) : ENNReal := energy μ ρ f

/-- Maximal finite domain of the chosen-representative function. No closed-form assertion. -/
def domain (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) :
    Set (Lp ℝ 2 (μ : Measure E)) := {f | form μ ρ f ≠ ⊤}

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Reconstruction inverts the joint coordinates: the base point and the scalar coordinate
of `(θ, x)` recombine to `x`. -/
theorem reconstruct_coordinates (p : Direction E × E) :
    reconstruct (coordinates p).1 (coordinates p).2 = p.2 := by
  simp [reconstruct, coordinates]

/-- Reconstruction is jointly measurable in the base point and the scalar coordinate. -/
theorem measurable_reconstruct :
    Measurable (fun q : (Direction E × E) × ℝ ↦ reconstruct q.1 q.2) := by
  unfold reconstruct
  fun_prop

omit [SecondCountableTopology E] in
/-- Along a fixed base point, reconstruction is a measurable function of the scalar. -/
theorem measurable_reconstruct_left (b : Direction E × E) : Measurable (reconstruct b) := by
  unfold reconstruct
  fun_prop

/-- The base projection `(θ, x) ↦ (θ, P_{θ⊥} x)`; it is the first coordinate map. -/
def baseMap (p : Direction E × E) : Direction E × E :=
  (p.1, p.2 - (inner ℝ p.2 p.1.1) • p.1.1)

private theorem measurable_baseMap : Measurable (baseMap (E := E)) := by
  unfold baseMap
  fun_prop

/-- The base law is the pushforward of `ρ ⊗ μ` by the base projection. -/
theorem baseLaw_eq_map (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) :
    baseLaw μ ρ = ((ρ : Measure (Direction E)).prod (μ : Measure E)).map baseMap := by
  unfold baseLaw jointLaw Measure.fst
  rw [Measure.map_map measurable_fst measurable_coordinates]
  rfl

/-- The disintegration identity for the chosen kernel, in the module's own names. -/
theorem compProd_baseLaw_kernel (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) :
    baseLaw μ ρ ⊗ₘ kernel μ ρ = jointLaw μ ρ :=
  Measure.disintegrate (jointLaw μ ρ) (jointLaw μ ρ).condKernel

/-- The joint-base integral is the iterated integral over directions and projected laws.
This connects the fixed product base to the Blueprint's varying orthogonal fibers. -/
theorem lintegral_baseLaw (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (F : Direction E × E → ENNReal) (hF : Measurable F) :
    (∫⁻ b, F b ∂baseLaw μ ρ) =
      ∫⁻ θ, ∫⁻ z, F (θ, z)
        ∂((μ : Measure E).map (fun x ↦ x - inner ℝ x θ.1 • θ.1))
        ∂(ρ : Measure (Direction E)) := by
  rw [baseLaw_eq_map, lintegral_map hF measurable_baseMap,
    lintegral_prod (fun a ↦ F (baseMap a)) (hF.comp measurable_baseMap).aemeasurable]
  refine lintegral_congr fun θ ↦ ?_
  rw [lintegral_map (f := fun z ↦ F (θ, z)) (hF.comp measurable_prodMk_left) (by fun_prop)]
  rfl

/-- Finite global second moment makes infinite conditional second moments a null case. -/
theorem ae_memLp_id (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (hμ : MemLp id 2 (μ : Measure E)) :
    ∀ᵐ b ∂baseLaw μ ρ, MemLp (id : ℝ → ℝ) 2 (kernel μ ρ b) := by
  have hmeas : Measurable (fun q : (Direction E × E) × ℝ ↦ ‖q.2‖ₑ ^ (2 : ℝ)) := by fun_prop
  have hfin : ∫⁻ b, ∫⁻ t, ‖t‖ₑ ^ (2 : ℝ) ∂kernel μ ρ b ∂baseLaw μ ρ < ⊤ := by
    rw [← Measure.lintegral_compProd hmeas, compProd_baseLaw_kernel, jointLaw,
      lintegral_map hmeas measurable_coordinates]
    calc ∫⁻ p, ‖(coordinates p).2‖ₑ ^ (2 : ℝ) ∂((ρ : Measure (Direction E)).prod (μ : Measure E))
        ≤ ∫⁻ p : Direction E × E, ‖p.2‖ₑ ^ (2 : ℝ)
            ∂((ρ : Measure (Direction E)).prod (μ : Measure E)) := by
          refine lintegral_mono fun p ↦ ?_
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [← ofReal_norm, ← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          calc ‖(coordinates p).2‖ = |inner ℝ p.2 p.1.1| := Real.norm_eq_abs _
            _ ≤ ‖p.2‖ * ‖p.1.1‖ := abs_real_inner_le_norm _ _
            _ = ‖p.2‖ := by rw [p.1.2, mul_one]
      _ = ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ : Measure E) := by
          rw [lintegral_prod _ (by fun_prop)]
          simp
      _ < ⊤ := (Probability.memLp_id_two_iff_lintegral_enorm_rpow_lt_top (μ : Measure E)).1 hμ
  have hm : Measurable fun b ↦ ∫⁻ t, ‖t‖ₑ ^ (2 : ℝ) ∂kernel μ ρ b :=
    Measurable.lintegral_kernel_prod_right' hmeas
  filter_upwards [ae_lt_top hm hfin.ne] with b hb
  exact (Probability.memLp_id_two_iff_lintegral_enorm_rpow_lt_top _).2 hb

/-- For a Borel test, the guarded normalized variance is jointly measurable. -/
theorem measurable_energyAt (κ : Kernel (Direction E × E) ℝ) [IsMarkovKernel κ]
    (f : E → ℝ) (hf : Measurable f) : Measurable (fun b ↦ energyAt κ b f) := by
  have hrec : Measurable (fun q : (Direction E × E) × ℝ ↦ f (reconstruct q.1 q.2)) :=
    hf.comp measurable_reconstruct
  have hmean : Measurable fun b ↦ ∫ t, f (reconstruct b t) ∂κ b :=
    hrec.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hvar : Measurable fun b ↦ evariance (fun t ↦ f (reconstruct b t)) (κ b) := by
    simp only [evariance]
    exact Measurable.lintegral_kernel_prod_right'
      (f := fun q : (Direction E × E) × ℝ ↦
        ‖f (reconstruct q.1 q.2) - ∫ t, f (reconstruct q.1 t) ∂κ q.1‖ₑ ^ 2)
      ((hrec.sub (hmean.comp measurable_fst)).enorm.pow_const _)
  have hsnd : StronglyMeasurable (fun q : (Direction E × E) × ℝ ↦ q.2) :=
    measurable_snd.stronglyMeasurable
  have hmean_id : Measurable fun b ↦ ∫ t, t ∂κ b :=
    hsnd.integral_kernel_prod_right'.measurable
  have hvar_id : Measurable fun b ↦ evariance id (κ b) := by
    simp only [evariance, id_eq]
    exact Measurable.lintegral_kernel_prod_right'
      (f := fun q : (Direction E × E) × ℝ ↦ ‖q.2 - ∫ t, t ∂κ q.1‖ₑ ^ 2)
      ((measurable_snd.sub (hmean_id.comp measurable_fst)).enorm.pow_const _)
  have hsecond : Measurable fun b ↦ ∫⁻ t, ‖t‖ₑ ^ (2 : ℝ) ∂κ b :=
    Measurable.lintegral_kernel_prod_right'
      (f := fun q : (Direction E × E) × ℝ ↦ ‖q.2‖ₑ ^ (2 : ℝ)) (by fun_prop)
  have hgood : MeasurableSet {b | Nondegenerate κ b} := by
    have e : {b | Nondegenerate κ b} = {b : Direction E × E | inner ℝ b.2 b.1.1 = 0} ∩
        ({b | ∫⁻ t, ‖t‖ₑ ^ (2 : ℝ) ∂κ b < ⊤} ∩ {b | evariance id (κ b) ≠ 0}) := by
      ext b
      simp only [Nondegenerate, Set.mem_ofPred_eq, Set.mem_inter_iff, Probability.memLp_id_two_iff_lintegral_enorm_rpow_lt_top]
    rw [e]
    refine (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      ((measurableSet_lt hsecond measurable_const).inter ?_)
    exact (hvar_id (measurableSet_singleton 0)).compl
  unfold energyAt
  exact Measurable.ite hgood (hvar.div hvar_id) measurable_const

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The fiber energy depends on the kernel only through its value at the base point. -/
theorem energyAt_congr_kernel {κ κ' : Kernel (Direction E × E) ℝ} {b : Direction E × E}
    (h : κ b = κ' b) (f : E → ℝ) : energyAt κ b f = energyAt κ' b f := by
  unfold energyAt Nondegenerate
  rw [h]

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The fiber energy depends on the test only through its class along the fiber. -/
theorem energyAt_congr_ae {κ : Kernel (Direction E × E) ℝ} {b : Direction E × E}
    {f g : E → ℝ}
    (h : (fun t ↦ f (reconstruct b t)) =ᵐ[κ b] (fun t ↦ g (reconstruct b t))) :
    energyAt κ b f = energyAt κ b g := by
  simp only [energyAt, evariance_congr h]

/-- Every Markov version of the same joint disintegration gives the same energy. -/
theorem energyWithKernel_eq_energy (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (κ : Kernel (Direction E × E) ℝ) [IsMarkovKernel κ]
    (hκ : baseLaw μ ρ ⊗ₘ κ = jointLaw μ ρ) (f : E → ℝ) :
    energyWithKernel μ ρ κ f = energy μ ρ f := by
  have huniq : ∀ᵐ b ∂(jointLaw μ ρ).fst, κ b = (jointLaw μ ρ).condKernel b :=
    ProbabilityTheory.eq_condKernel_of_measure_eq_compProd κ hκ.symm
  unfold energy energyWithKernel
  congr 1
  exact lintegral_congr_ae (huniq.mono fun b hb ↦ energyAt_congr_kernel hb f)

/-- Two Borel tests equal `μ`-a.e. agree along almost every conditional fiber. -/
theorem ae_restrict_congr (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g) (hfg : f =ᵐ[(μ : Measure E)] g) :
    ∀ᵐ b ∂baseLaw μ ρ,
      (fun t ↦ f (reconstruct b t)) =ᵐ[kernel μ ρ b] (fun t ↦ g (reconstruct b t)) := by
  have hS : MeasurableSet
      {q : (Direction E × E) × ℝ | f (reconstruct q.1 q.2) = g (reconstruct q.1 q.2)} :=
    measurableSet_eq_fun (hf.comp measurable_reconstruct) (hg.comp measurable_reconstruct)
  have hjoint : ∀ᵐ q ∂jointLaw μ ρ, f (reconstruct q.1 q.2) = g (reconstruct q.1 q.2) := by
    rw [jointLaw, ae_map_iff measurable_coordinates.aemeasurable hS]
    simp only [reconstruct_coordinates]
    rw [ae_iff]
    have hN : MeasurableSet {x : E | ¬ f x = g x} := (measurableSet_eq_fun hf hg).compl
    have : ((ρ : Measure (Direction E)).prod (μ : Measure E)) {p | ¬ f p.2 = g p.2} =
        ((ρ : Measure (Direction E)).prod (μ : Measure E)).snd {x | ¬ f x = g x} :=
      (Measure.snd_apply hN).symm
    rw [this, Measure.snd_prod]
    exact ae_iff.1 hfg
  rw [← compProd_baseLaw_kernel] at hjoint
  exact Measure.ae_ae_of_ae_compProd hjoint

/-- The formula is independent of the Borel representative of an L² class. -/
theorem energy_congr_ae (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (f g : E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (_hf₂ : MemLp f 2 (μ : Measure E)) (_hg₂ : MemLp g 2 (μ : Measure E))
    (hfg : f =ᵐ[(μ : Measure E)] g) : energy μ ρ f = energy μ ρ g := by
  unfold energy energyWithKernel
  congr 1
  exact lintegral_congr_ae ((ae_restrict_congr μ ρ hf hg hfg).mono fun b hb ↦ energyAt_congr_ae hb)

/-- The chosen-representative L² function agrees with the Blueprint formula. -/
theorem form_toLp (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (f : E → ℝ) (hf : Measurable f) (hf₂ : MemLp f 2 (μ : Measure E)) :
    form μ ρ (hf₂.toLp f) = energy μ ρ f :=
  energy_congr_ae μ ρ _ f (Lp.stronglyMeasurable _).measurable hf (Lp.memLp _) hf₂
    hf₂.coeFn_toLp

end FunctionalInequalities.KLS.ConditionalFiber
