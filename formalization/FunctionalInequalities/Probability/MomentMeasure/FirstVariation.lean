module

public import FunctionalInequalities.Probability.MomentMeasure.Basic
public import FunctionalInequalities.Analysis.Convex.Legendre.Variation.Derivative
public import FunctionalInequalities.Analysis.Convex.Subgradient.Measure
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# First variation of the CEK functional for extended-real potentials

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), proof of Theorem 2, (42)–(44), for
an arbitrary
lower semicontinuous primal `φ` whose conjugate `ψ = φ*` may take the value `+∞`.

* Moment measure of an extended-real potential `ofPotential dx ψ`: total mass `mass dx ψ`
  (`ofPotential_univ`) and the
  integral formula `∫ g d(ofPotential dx ψ) = ∫ e^{-ψ} g(∇ψ) dx` (`integral_ofPotential`).
* A convex potential with nonzero exponential mass has an effective domain with nonempty interior
  (`interior_domain_nonempty_of_mass_ne_zero`).
* Normalization: subtracting a real constant `b` multiplies the density, the mass and, for a Borel
  convex potential,
  the moment measure by `e^b` (`density_sub_const`, `mass_sub_const`, `ofPotential_sub_const`).
* Integrated first variation (42): for a bounded continuous `b`,
  `t ↦ ∫ exp(-(φ + t b)*)` is differentiable at `0` with derivative `∫ b d(ofPotential dx φ*)`
  (`hasDerivAt_mass_legendre_add_smul`). The effective domain of `φ*` is convex, so its frontier is
  Lebesgue-null, and
  `φ*` is differentiable almost everywhere on its interior; outside the domain all perturbed
  densities vanish.
* Euler–Lagrange equation (44): a lower semicontinuous maximizer `φ` of `I_μ` over all
  `PotentialIntegrable`
  competitors with `∫ exp(-φ*) = 1` has `μ` as the moment measure of `φ*`
  (`ofPotential_legendre_eq_of_maximizer`).

No essential continuity, finiteness of `φ*` or bounded support is assumed or concluded.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Probability.MomentMeasure

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
open FunctionalInequalities.Analysis

variable {E : Type*}

section Algebra

private theorem proper_add_smul {φ : E → EReal} (hφ : ProperPotential φ) (b : E → ℝ) (t : ℝ) :
    ProperPotential (fun z => φ z + ((t * b z : ℝ) : EReal)) := by
  obtain ⟨hbot, w, hw⟩ := hφ
  refine ⟨fun z h => ?_, w, EReal.add_ne_top hw (EReal.coe_ne_top _)⟩
  rw [EReal.add_eq_bot_iff] at h
  rcases h with h | h
  · exact hbot z h
  · exact EReal.coe_ne_bot _ h

private theorem add_smul_add_smul_neg (φ : E → EReal) (b : E → ℝ) (t : ℝ) :
    (fun z => φ z + ((t * b z : ℝ) : EReal) + ((-t * b z : ℝ) : EReal)) = φ := by
  funext z
  rw [add_assoc, ← EReal.coe_add, show t * b z + -t * b z = 0 by ring, EReal.coe_zero, add_zero]

private theorem add_smul_zero (φ : E → EReal) (b : E → ℝ) :
    (fun z => φ z + (((0 : ℝ) * b z : ℝ) : EReal)) = φ := by
  funext z
  rw [zero_mul, EReal.coe_zero, add_zero]

end Algebra

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Conjugate

private theorem exp_neg_eq_ofReal {e : EReal} (htop : e ≠ ⊤) (hbot : e ≠ ⊥) :
    EReal.exp (-e) = ENNReal.ofReal (Real.exp (-e.toReal)) := by
  lift e to ℝ using ⟨htop, hbot⟩
  rw [← EReal.coe_neg, EReal.exp_coe, EReal.toReal_coe]

/--
Pointwise comparison of the perturbed conjugate density: `e^{-(φ + t b)*} ≤ e^{|t| M} e^{-φ*}`. -/
private theorem density_legendre_add_smul_le {φ : E → EReal} (hφ : ProperPotential φ)
    {b : E → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z, |b z| ≤ M) (t : ℝ) (x : E) :
    density (legendre (fun z => φ z + ((t * b z : ℝ) : EReal))) x ≤
      ENNReal.ofReal (Real.exp (|t| * M)) * density (legendre φ) x := by
  by_cases hx : legendre φ x = ⊤
  · have ht : legendre (fun z => φ z + ((t * b z : ℝ) : EReal)) x = ⊤ := by
      by_contra h
      exact ((legendre_add_smul_ne_top_iff hφ hM0 hM t x).mp h) hx
    rw [density, ht, EReal.neg_top, EReal.exp_bot]
    exact zero_le
  · obtain ⟨htop, hbot, hc⟩ := legendre_bounded_perturbation_finite_curve φ hφ x hx b M hM0 hM t
    rw [density, density, exp_neg_eq_ofReal htop hbot,
      exp_neg_eq_ofReal hx (legendre_ne_bot φ hφ x), ← ENNReal.ofReal_mul (Real.exp_pos _).le, ←
      Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp hc).1
    linarith

end Conjugate

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section MomentMeasure

/--
The gradient of the real part of an extended-real potential is Borel measurable, for every `ψ`. -/
theorem measurable_gradient_toReal (ψ : E → EReal) :
    Measurable (gradient fun x => (ψ x).toReal) := by
  change
    Measurable
      (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun x => (ψ x).toReal) x))
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ _)

/-- Values of the moment measure on Borel sets. -/
theorem ofPotential_apply (dx : Measure E) (ψ : E → EReal) {s : Set E} (hs : MeasurableSet s) :
    ofPotential dx ψ s = weightedMeasure dx ψ ((gradient fun x => (ψ x).toReal) ⁻¹' s) :=
  Measure.map_apply (measurable_gradient_toReal ψ) hs

/-- The total mass of the moment measure is the exponential mass `∫ exp(-ψ) dx`. -/
theorem ofPotential_univ (dx : Measure E) (ψ : E → EReal) : ofPotential dx ψ univ = mass dx ψ := by
  rw [ofPotential_apply dx ψ MeasurableSet.univ, preimage_univ, weightedMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, mass]

/-- The moment measure is finite when the exponential mass is finite. -/
theorem isFiniteMeasure_ofPotential (dx : Measure E) (ψ : E → EReal) (h : mass dx ψ ≠ ⊤) :
    IsFiniteMeasure (ofPotential dx ψ) :=
  ⟨by rw [ofPotential_univ]; exact lt_top_iff_ne_top.mpr h⟩

/--
**Integral against the moment measure**: for a Borel potential `ψ` that never takes `⊥` and a Borel
real `g`,
`∫ g d(ofPotential dx ψ) = ∫ e^{-ψ(x)} g(∇ψ(x)) dx` (both sides are `0` when not integrable). -/
theorem integral_ofPotential (dx : Measure E) {ψ : E → EReal} (hψ : Measurable ψ)
    (hbot : ∀ x, ψ x ≠ ⊥) {g : E → ℝ} (hg : Measurable g) :
    ∫ y, g y ∂ofPotential dx ψ =
      ∫ x, (density ψ x).toReal * g (gradient (fun x => (ψ x).toReal) x) ∂dx := by
  rw [ofPotential,
    integral_map (measurable_gradient_toReal ψ).aemeasurable hg.aestronglyMeasurable,
    weightedMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ (f := density ψ)
      (EReal.measurable_exp.comp hψ.neg).aemeasurable]
  · simp only [smul_eq_mul]
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [density, EReal.exp_lt_top_iff, lt_top_iff_ne_top]
    intro h
    exact hbot x (EReal.neg_eq_top_iff.mp h)

end MomentMeasure

section DomainMeasure

/--
A convex potential whose exponential mass is nonzero has an effective domain with nonempty interior:
otherwise
the convex domain lies in its Lebesgue-null frontier and `exp(-ψ)` vanishes almost everywhere. -/
theorem interior_domain_nonempty_of_mass_ne_zero (dx : Measure E) [dx.IsAddHaarMeasure]
    {ψ : E → EReal} (hψ : ConvexPotential ψ) (h : mass dx ψ ≠ 0) :
    (interior {x | ψ x ≠ ⊤}).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  apply h
  have hsub : {x | ψ x ≠ ⊤} ⊆ frontier {x | ψ x ≠ ⊤} := fun x hx =>
    ⟨subset_closure hx, by rw [hne]; exact notMem_empty x⟩
  have hD0 : dx {x | ψ x ≠ ⊤} = 0 :=
    measure_mono_null hsub (hψ.convex_domain.addHaar_frontier dx)
  have hz : density ψ =ᵐ[dx] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hD0] with x hx
    have hx' : ψ x = ⊤ := by simpa using hx
    simp [density, hx']
  rw [mass, lintegral_congr_ae hz]
  simp

end DomainMeasure

section Normalization

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] in
/--
Subtracting a real constant from the potential multiplies the density: `e^{-(ψ - b)} = e^b e^{-ψ}`,
including the
values `ψ = ±∞`. -/
theorem density_sub_const (ψ : E → EReal) (b : ℝ) (x : E) :
    density (fun y => ψ y - (b : EReal)) x = ENNReal.ofReal (Real.exp b) * density ψ x := by
  have hneg : -(ψ x - (b : EReal)) = -ψ x + (b : EReal) := by
    induction ψ x using EReal.rec with
    | bot => simp
    | top => simp
    | coe r =>
      rw [← EReal.coe_sub, ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add]; congr 1;
      ring
  rw [density, density, hneg, EReal.exp_add, EReal.exp_coe, mul_comm]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Subtracting a real constant `b` from the potential multiplies the exponential mass by `e^b`. -/
theorem mass_sub_const (dx : Measure E) (ψ : E → EReal) (b : ℝ) :
    mass dx (fun y => ψ y - (b : EReal)) = ENNReal.ofReal (Real.exp b) * mass dx ψ := by
  rw [mass, mass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr fun x => density_sub_const ψ b x

/--
**Normalization of the moment measure**: for a Borel convex potential `ψ` and an additive Haar
measure `dx`,
subtracting a real constant `b` scales the moment measure by `e^b`. The real parts of `ψ - b` and
`ψ` differ by `b` on
the interior of the effective domain, whose complement in the domain is the Lebesgue-null frontier.
-/
theorem ofPotential_sub_const (dx : Measure E) [dx.IsAddHaarMeasure] {ψ : E → EReal}
    (hψ : ConvexPotential ψ) (hm : Measurable ψ) (b : ℝ) :
    ofPotential dx (fun y => ψ y - (b : EReal)) =
      ENNReal.ofReal (Real.exp b) • ofPotential dx ψ := by
  set D : Set E := {x | ψ x ≠ ⊤} with hD
  have hdens : density (fun y => ψ y - (b : EReal)) = ENNReal.ofReal (Real.exp b) • density ψ :=
    funext fun x => density_sub_const ψ b x
  have hW :
    weightedMeasure dx (fun y => ψ y - (b : EReal)) =
      ENNReal.ofReal (Real.exp b) • weightedMeasure dx ψ := by
    rw [weightedMeasure, weightedMeasure, hdens, withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  have hdm : Measurable (density ψ) := EReal.measurable_exp.comp hm.neg
  have hWD : ∀ᵐ x ∂weightedMeasure dx ψ, x ∈ D := by
    rw [ae_iff, weightedMeasure, withDensity_apply_eq_zero' hdm.aemeasurable]
    convert measure_empty (μ := dx)
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, not_not, mem_empty_iff_false, iff_false, not_and]
    intro hx htop
    apply hx
    rw [density, htop, EReal.neg_top, EReal.exp_bot]
  have hWfr : ∀ᵐ x ∂weightedMeasure dx ψ, x ∉ frontier D :=
    withDensity_absolutelyContinuous dx (density ψ)
      (measure_eq_zero_iff_ae_notMem.mp (hψ.convex_domain.addHaar_frontier dx))
  have hgrad :
    (gradient fun y => (ψ y - (b : EReal)).toReal) =ᵐ[weightedMeasure dx ψ]
      gradient fun y => (ψ y).toReal := by
    filter_upwards [hWD, hWfr] with x hx hxf
    have hxint : x ∈ interior D := by
      by_contra hni
      exact hxf ⟨subset_closure hx, hni⟩
    have hloc : (fun y => (ψ y - (b : EReal)).toReal) =ᶠ[𝓝 x] fun y => (ψ y).toReal - b := by
      filter_upwards [isOpen_interior.mem_nhds hxint] with y hy
      rw [EReal.toReal_sub (interior_subset hy) (hψ.1 y) (EReal.coe_ne_top b)
          (EReal.coe_ne_bot b),
        EReal.toReal_coe]
    unfold gradient
    rw [hloc.fderiv_eq, fderiv_sub_const]
  rw [ofPotential, ofPotential, hW,
    Measure.map_smul _ (measurable_gradient_toReal fun y => ψ y - (b : EReal)).aemeasurable,
    Measure.map_congr hgrad]

end Normalization

section Perturbation

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Two-sided comparison of the exponential masses of `(φ + t b)*` and `φ*`. -/
private theorem mass_legendre_add_smul_bounds (dx : Measure E) {φ : E → EReal}
    (hφ : ProperPotential φ) {b : E → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z, |b z| ≤ M) (t : ℝ) :
    mass dx (legendre (fun z => φ z + ((t * b z : ℝ) : EReal))) ≤
        ENNReal.ofReal (Real.exp (|t| * M)) * mass dx (legendre φ) ∧
      mass dx (legendre φ) ≤
        ENNReal.ofReal (Real.exp (|t| * M)) *
          mass dx (legendre (fun z => φ z + ((t * b z : ℝ) : EReal))) := by
  constructor
  · rw [mass, mass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun x => density_legendre_add_smul_le hφ hM0 hM t x
  · rw [mass, mass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    have h := density_legendre_add_smul_le (proper_add_smul hφ b t) hM0 hM (-t) x
    rw [abs_neg] at h
    have hfun : (fun z => φ z + ((t * b z : ℝ) : EReal) + ((-t * b z : ℝ) : EReal)) = φ :=
      add_smul_add_smul_neg φ b t
    simp only [hfun] at h
    exact h

/--
**Integrated first variation of the conjugate partition function** (Cordero-Erausquin–Klartag
arXiv:1304.0630v1, proof of Theorem 2, (42); Berman–Berndtsson arXiv:1207.6128v1, Lemma 2.7): let
`φ` be proper and
lower semicontinuous with `∫ exp(-φ*) dx < ∞` (`dx` an additive Haar measure; `φ*` may be `+∞`), and
let `b` be
continuous with `|b| ≤ M`. Then `t ↦ ∫ exp(-(φ + t b)*) dx` (real part of the mass) is
differentiable at `0` with
derivative `∫ b d(ofPotential dx φ*) = ∫ exp(-φ*) b(∇φ*) dx`. -/
theorem hasDerivAt_mass_legendre_add_smul (dx : Measure E) [dx.IsAddHaarMeasure] {φ : E → EReal}
    (hφ : ProperPotential φ) (hlsc : LowerSemicontinuous φ) (hmass : mass dx (legendre φ) ≠ ⊤)
    {b : E → ℝ} (hb : Continuous b) {M : ℝ} (hM : ∀ z, |b z| ≤ M) :
    HasDerivAt (fun t : ℝ => (mass dx (legendre fun z => φ z + ((t * b z : ℝ) : EReal))).toReal)
      (∫ y, b y ∂ofPotential dx (legendre φ)) 0 := by
  classical
  have hM0 : 0 ≤ M := (abs_nonneg (b 0)).trans (hM 0)
  have hfin : ∃ x, φ x ≠ ⊤ := hφ.2
  let ψr : E → ℝ := fun x => (legendre φ x).toReal
  let D : Set E := {x | legendre φ x ≠ ⊤}
  let F : ℝ → E → ℝ := fun t x =>
    (density (legendre fun z => φ z + ((t * b z : ℝ) : EReal)) x).toReal
  let F' : E → ℝ := fun x => (density (legendre φ) x).toReal * b (gradient ψr x)
  let bound : E → ℝ := fun x => M * Real.exp M * (density (legendre φ) x).toReal
  have hF0 : F 0 = fun x => (density (legendre φ) x).toReal := by
    funext x
    simp only [F, add_smul_zero]
  have hdens_fin : ∀ x, legendre φ x ≠ ⊤ → (density (legendre φ) x).toReal = Real.exp (-ψr x) := by
    intro x hx
    rw [density, exp_neg_eq_ofReal hx (legendre_ne_bot φ hφ x),
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hF_fin :
    ∀ x,
      legendre φ x ≠ ⊤ →
        ∀ t, F t x = Real.exp (-(legendre (fun z => φ z + ((t * b z : ℝ) : EReal)) x).toReal) := by
    intro x hx t
    have htop := (legendre_add_smul_ne_top_iff hφ hM0 hM t x).mpr hx
    simp only [F]
    rw [density, exp_neg_eq_ofReal htop (legendre_ne_bot _ (proper_add_smul hφ b t) x),
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hF_top : ∀ x, legendre φ x = ⊤ → ∀ t, F t x = 0 := by
    intro x hx t
    have ht : legendre (fun z => φ z + ((t * b z : ℝ) : EReal)) x = ⊤ := by
      by_contra h
      exact ((legendre_add_smul_ne_top_iff hφ hM0 hM t x).mp h) hx
    simp only [F]
    rw [density, ht, EReal.neg_top, EReal.exp_bot, ENNReal.toReal_zero]
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) dx :=
    Filter.Eventually.of_forall fun t =>
      (measurable_density_legendre _).ennreal_toReal.aestronglyMeasurable
  have hdens_int : Integrable (fun x => (density (legendre φ) x).toReal) dx :=
    integrable_toReal_of_lintegral_ne_top (measurable_density_legendre φ).aemeasurable hmass
  have hF_int : Integrable (F 0) dx := by
    rw [hF0]
    exact hdens_int
  have hψr_meas : Measurable ψr := (lowerSemicontinuous_legendre φ).measurable.ereal_toReal
  have hF'_meas : AEStronglyMeasurable F' dx :=
    ((measurable_density_legendre φ).ennreal_toReal.mul
        (hb.measurable.comp (measurable_gradient_toReal (legendre φ)))).aestronglyMeasurable
  have hbound_nonneg : ∀ x, 0 ≤ bound x := fun x =>
    mul_nonneg (mul_nonneg hM0 (Real.exp_pos M).le) ENNReal.toReal_nonneg
  have hbound_int : Integrable bound dx := by
    simpa only [bound] using hdens_int.const_mul (M * Real.exp M)
  have h_lipsch : ∀ᵐ x ∂dx, LipschitzOnWith (Real.nnabs (bound x)) (F · x) (ball (0 : ℝ) 1) := by
    refine
      Filter.Eventually.of_forall fun x => LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    have hcoef : (↑(Real.nnabs (bound x)) : ℝ) = bound x := by
      rw [Real.nnabs_of_nonneg (hbound_nonneg x), Real.coe_toNNReal _ (hbound_nonneg x)]
    rw [hcoef]
    by_cases hx : legendre φ x = ⊤
    · rw [hF_top x hx u, hF_top x hx v, dist_self]
      exact mul_nonneg (hbound_nonneg x) dist_nonneg
    let P : ℝ → ℝ := fun t => (legendre (fun z => φ z + ((t * b z : ℝ) : EReal)) x).toReal
    let A : ℝ := ψr x
    have hu_abs : |u| ≤ 1 := by
      have hu' : dist u 0 < 1 := hu
      simpa [Real.dist_eq] using hu'.le
    have hv_abs : |v| ≤ 1 := by
      have hv' : dist v 0 < 1 := hv
      simpa [Real.dist_eq] using hv'.le
    have hu_curve := legendre_bounded_perturbation_finite_curve φ hφ x hx b M hM0 hM u
    have hv_curve := legendre_bounded_perturbation_finite_curve φ hφ x hx b M hM0 hM v
    have huv_curve :=
      legendre_bounded_perturbation_finite_curve (fun z => φ z + ((v * b z : ℝ) : EReal))
        (proper_add_smul hφ b v) x hv_curve.1 b M hM0 hM (u - v)
    have hfun :
      (fun z : E => φ z + ((v * b z : ℝ) : EReal) + (((u - v) * b z : ℝ) : EReal)) =
        (fun z : E => φ z + ((u * b z : ℝ) : EReal)) := by
      funext z
      rw [add_assoc, ← EReal.coe_add]
      congr 2
      ring
    have hdiff : |P u - P v| ≤ M * |u - v| := by
      have h := huv_curve.2.2
      change
        |(legendre (fun z : E => φ z + ((v * b z : ℝ) : EReal) + (((u - v) * b z : ℝ) : EReal))
                  x).toReal -
              P v| ≤
          |u - v| * M at h
      rw [hfun] at h
      simpa [P, mul_comm] using h
    have hu_shift : |P u - A| ≤ M := by
      calc
        |P u - A| ≤ |u| * M := hu_curve.2.2
        _ ≤ 1 * M := mul_le_mul_of_nonneg_right hu_abs hM0
        _ = M := one_mul M
    have hv_shift : |P v - A| ≤ M := by
      calc
        |P v - A| ≤ |v| * M := hv_curve.2.2
        _ ≤ 1 * M := mul_le_mul_of_nonneg_right hv_abs hM0
        _ = M := one_mul M
    have hu_neg_mem : -P u ∈ Icc (-(A + M)) (-(A - M)) := by
      rcases abs_le.mp hu_shift with ⟨hlo, hhi⟩
      constructor <;> linarith
    have hv_neg_mem : -P v ∈ Icc (-(A + M)) (-(A - M)) := by
      rcases abs_le.mp hv_shift with ⟨hlo, hhi⟩
      constructor <;> linarith
    have hexp :=
      (convex_Icc (-(A + M)) (-(A - M))).norm_image_sub_le_of_norm_deriv_le
        (fun y _ => (Real.hasDerivAt_exp y).differentiableAt)
        (fun y hy => by
          rw [Real.deriv_exp, Real.norm_eq_abs, Real.abs_exp]
          exact Real.exp_le_exp.2 hy.2)
        hu_neg_mem hv_neg_mem
    have hexp' : |Real.exp (-P u) - Real.exp (-P v)| ≤ Real.exp (-(A - M)) * |P u - P v| := by
      calc
        |Real.exp (-P u) - Real.exp (-P v)| = ‖Real.exp (-P v) - Real.exp (-P u)‖ := by
          rw [Real.norm_eq_abs, abs_sub_comm]
        _ ≤ Real.exp (-(A - M)) * ‖-P v - -P u‖ := hexp
        _ = Real.exp (-(A - M)) * |P u - P v| := by
          rw [show -P v - -P u = P u - P v by ring, Real.norm_eq_abs]
    have hcoeff : Real.exp (-(A - M)) = Real.exp (-A) * Real.exp M := by
      rw [show -(A - M) = -A + M by ring, Real.exp_add]
    calc
      dist (F u x) (F v x) = |Real.exp (-P u) - Real.exp (-P v)| := by
        rw [hF_fin x hx u, hF_fin x hx v, Real.dist_eq]
      _ ≤ Real.exp (-(A - M)) * |P u - P v| := hexp'
      _ ≤ Real.exp (-(A - M)) * (M * |u - v|) :=
        mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
      _ = bound x * dist u v := by
        rw [hcoeff, Real.dist_eq]
        simp only [bound, hdens_fin x hx, A]
        ring
  have hconv : ConvexPotential (legendre φ) := convexPotential_legendre φ hfin
  have hae_diff : ∀ᵐ x ∂dx, x ∈ interior D → DifferentiableAt ℝ ψr x :=
    FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen dx isOpen_interior
      (hconv.convexOn_toReal.subset interior_subset hconv.convex_domain.interior)
  have hae_front : ∀ᵐ x ∂dx, x ∉ frontier D :=
    measure_eq_zero_iff_ae_notMem.mp (hconv.convex_domain.addHaar_frontier dx)
  have h_diff : ∀ᵐ x ∂dx, HasDerivAt (F · x) (F' x) 0 := by
    filter_upwards [hae_diff, hae_front] with x hxd hxf
    by_cases hx : legendre φ x = ⊤
    · have hzero : (F · x) = fun _ => (0 : ℝ) := funext fun t => hF_top x hx t
      have hF'0 : F' x = 0 := by simp [F', density, hx]
      rw [hzero, hF'0]
      exact hasDerivAt_const _ _
    have hxint : x ∈ interior D := by
      by_contra hni
      exact hxf ⟨subset_closure hx, hni⟩
    have hv :=
      hasDerivAt_legendre_add_smul_of_dualDifferentiable φ hφ hlsc x hxint (hxd hxint) b hb
        ⟨M, by rintro _ ⟨z, rfl⟩; exact hM z⟩
    have hfun :
      (F · x) = fun t =>
        Real.exp (-(legendre (fun z => φ z + ((t * b z : ℝ) : EReal)) x).toReal) :=
      funext fun t => hF_fin x hx t
    rw [hfun]
    have h3 := hv.neg.exp
    simp only [Pi.neg_apply, neg_neg, zero_mul, EReal.coe_zero, add_zero] at h3
    exact h3.congr_deriv (by simp only [F']; rw [hdens_fin x hx])
  have hresult :=
    hasDerivAt_integral_of_dominated_loc_of_lip (F := F) (F' := F') (bound := bound) (x₀ :=
      (0 : ℝ)) (s := ball (0 : ℝ) 1) (ball_mem_nhds (0 : ℝ) zero_lt_one) hF_meas hF_int hF'_meas
      h_lipsch hbound_int h_diff
  have hmassF :
    (fun t : ℝ => (mass dx (legendre fun z => φ z + ((t * b z : ℝ) : EReal))).toReal) = fun t =>
      ∫ x, F t x ∂dx := by
    funext t
    rw [mass, ← integral_toReal (measurable_density_legendre _).aemeasurable]
    refine Filter.Eventually.of_forall fun x => ?_
    rw [density, EReal.exp_lt_top_iff, lt_top_iff_ne_top]
    intro h
    exact legendre_ne_bot _ (proper_add_smul hφ b t) x (EReal.neg_eq_top_iff.mp h)
  rw [hmassF,
    integral_ofPotential dx (lowerSemicontinuous_legendre φ).measurable (legendre_ne_bot φ hφ)
      hb.measurable]
  exact hresult.2

end Perturbation

section EulerLagrange

/--
**Euler–Lagrange equation for the CEK functional** (Cordero-Erausquin–Klartag arXiv:1304.0630v1,
proof of
Theorem 2, (43)–(44)): let `μ ≠ 0` be finite and `dx` an additive Haar measure. If a lower
semicontinuous
`PotentialIntegrable` potential `φ` with `∫ exp(-φ*) dx = 1` maximizes `I_μ(f) = log ∫ exp(-f*) dx -
∫ f dμ` over all
`PotentialIntegrable` competitors, then `μ` is the moment measure of the (possibly infinite-valued)
conjugate `φ*`.
Each bounded continuous `b` gives the competitor `φ + t b`; differentiating at `t = 0` gives
`∫ b d(ofPotential dx φ*) = ∫ b dμ`. -/
theorem ofPotential_legendre_eq_of_maximizer (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsFiniteMeasure μ] (hμ : μ ≠ 0) {φ : E → EReal} (hlsc : LowerSemicontinuous φ)
    (hφ : PotentialIntegrable φ μ) (hmass : mass dx (legendre φ) = 1)
    (hmax :
      ∀ f : E → EReal,
        PotentialIntegrable f μ → variationalFunctional dx μ f ≤ variationalFunctional dx μ φ) :
    ofPotential dx (legendre φ) = μ := by
  classical
  have hproper : ProperPotential φ := by
    have : NeZero μ := ⟨hμ⟩
    exact ⟨hφ.1, hφ.2.1.exists⟩
  have : IsFiniteMeasure (ofPotential dx (legendre φ)) :=
    isFiniteMeasure_ofPotential dx _ (by rw [hmass]; exact ENNReal.one_ne_top)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro b
  have hb : Continuous (b : E → ℝ) := b.continuous
  have hM : ∀ z, |b z| ≤ ‖b‖ := fun z => by
    simpa only [Real.norm_eq_abs] using b.norm_coe_le_norm z
  set A : ℝ := ∫ z, (φ z).toReal ∂μ with hA
  set B : ℝ := ∫ z, b z ∂μ with hB
  have hreal :
    ∀ t : ℝ, ∀ᵐ z ∂μ, (φ z + ((t * b z : ℝ) : EReal)).toReal = (φ z).toReal + t * b z := by
    intro t
    filter_upwards [hφ.2.1] with z hz
    rw [EReal.toReal_add hz (hφ.1 z) (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe]
  have hbint : ∀ t : ℝ, Integrable (fun z => t * b z) μ := fun t => (b.integrable μ).const_mul t
  have hpot : ∀ t : ℝ, PotentialIntegrable (fun z => φ z + ((t * b z : ℝ) : EReal)) μ := by
    intro t
    refine ⟨fun z hz => ?_, ?_, ?_⟩
    · rw [EReal.add_eq_bot_iff] at hz
      rcases hz with hz | hz
      · exact hφ.1 z hz
      · exact EReal.coe_ne_bot _ hz
    · filter_upwards [hφ.2.1] with z hz
      exact EReal.add_ne_top hz (EReal.coe_ne_top _)
    · exact
        (hφ.2.2.add (hbint t)).congr
          (by
            filter_upwards [hreal t] with z hz
            exact hz.symm)
  have hIntq : ∀ t : ℝ, ∫ z, (φ z + ((t * b z : ℝ) : EReal)).toReal ∂μ = A + t * B := by
    intro t
    rw [integral_congr_ae (hreal t), integral_add hφ.2.2 (hbint t), integral_const_mul]
  let Z : ℝ → ℝ := fun t => (mass dx (legendre fun z => φ z + ((t * b z : ℝ) : EReal))).toReal
  have hbounds := mass_legendre_add_smul_bounds dx hproper (norm_nonneg b) hM
  have hZne0 : ∀ t : ℝ, mass dx (legendre fun z => φ z + ((t * b z : ℝ) : EReal)) ≠ 0 := by
    intro t h
    have h' := (hbounds t).2
    rw [h, mul_zero, hmass] at h'
    exact one_ne_zero (le_zero_iff.mp h')
  have hZnetop : ∀ t : ℝ, mass dx (legendre fun z => φ z + ((t * b z : ℝ) : EReal)) ≠ ⊤ :=
    fun t =>
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by rw [hmass]; exact ENNReal.one_ne_top))
      (hbounds t).1
  have hJt :
    ∀ t : ℝ,
      variationalFunctional dx μ (fun z => φ z + ((t * b z : ℝ) : EReal)) =
        ((Real.log (Z t) - (A + t * B) : ℝ) : EReal) := by
    intro t
    rw [variationalFunctional, ENNReal.log_pos_real (hZne0 t) (hZnetop t), hIntq t, ←
      EReal.coe_sub]
  have hJ : variationalFunctional dx μ φ = ((-A : ℝ) : EReal) := by
    rw [variationalFunctional, hmass, ENNReal.log_one, zero_sub, EReal.coe_neg]
  have hZ0 : Z 0 = 1 := by
    change (mass dx (legendre fun z => φ z + (((0 : ℝ) * b z : ℝ) : EReal))).toReal = 1
    rw [add_smul_zero, hmass, ENNReal.toReal_one]
  have hmax0 : IsLocalMax (fun t => Real.log (Z t) - t * B) 0 := by
    refine IsMaxOn.isLocalMax (fun t _ => ?_) Filter.univ_mem
    have hi := hmax _ (hpot t)
    rw [hJt t, hJ] at hi
    have hi' := EReal.coe_le_coe_iff.mp hi
    show Real.log (Z t) - t * B ≤ Real.log (Z 0) - 0 * B
    rw [hZ0, Real.log_one]
    linarith
  have hderiv : HasDerivAt Z (∫ y, b y ∂ofPotential dx (legendre φ)) 0 :=
    hasDerivAt_mass_legendre_add_smul dx hproper hlsc (by rw [hmass]; exact ENNReal.one_ne_top)
      hb hM
  have hlog := hderiv.log (by rw [hZ0]; exact one_ne_zero)
  have hmul : HasDerivAt (fun t : ℝ => t * B) B 0 := by
    simpa only [one_mul, id] using (hasDerivAt_id (0 : ℝ)).mul_const B
  have h0 := hmax0.hasDerivAt_eq_zero (hlog.sub hmul)
  rw [hZ0, div_one] at h0
  linarith

end EulerLagrange

end FunctionalInequalities.Probability.MomentMeasure
