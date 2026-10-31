module

public import FunctionalInequalities.KLS.CEK.MaximizerContinuity
public import FunctionalInequalities.KLS.CEK.VariationalMaximum
public import FunctionalInequalities.Probability.MomentMeasure.FirstVariation

/-!
# CEK Theorem 2: existence of a convex potential for every centered full-dimensional finite measure

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Theorem 2, existence part: for a
finite Borel
measure `μ ≠ 0` on a finite-dimensional inner-product space with finite first moment, barycenter `0`
and not supported
in a proper linear subspace, and for an additive Haar measure `dx`, there is a convex essentially
continuous
`ψ : E → ℝ ∪ {+∞}` (CEK Definition 2) whose effective domain has nonempty interior, with `∫ exp(-ψ)
dx = μ(E)` and
moment measure `μ`, i.e. `(∇ψ)_# (exp(-ψ) dx) = μ` (`exists_ofPotential_eq_essentiallyContinuous`;
`exists_ofPotential_eq` keeps only lower semicontinuity).

The potential is the conjugate of the Proposition 12 maximizer (`exists_variational_maximum`,
applied to `μ / μ(E)`),
identified by the Euler–Lagrange equation (`ofPotential_legendre_eq_of_maximizer`, CEK (43)–(44)),
essentially
continuous by Proposition 10 (`essentiallyContinuous_legendre_of_maximizer`), and shifted by `log
μ(E)`. Uniqueness up
to translation is not provided here.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.KLS.CEK

open MeasureTheory Set
open scoped ENNReal
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
**CEK Theorem 2, existence for probability measures** (Cordero-Erausquin–Klartag arXiv:1304.0630v1,
Proposition 12
and (43)–(44)): for a probability measure `μ` with finite first moment, barycenter `0` and not
supported in a proper
linear subspace, and an additive Haar measure `dx`, the conjugate `ψ = φ*` of a lower semicontinuous
Proposition 12
maximizer `φ` is a convex lower semicontinuous potential with `∫ exp(-ψ) dx = 1` and moment measure
`μ`. -/
theorem exists_ofPotential_eq_of_probability (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsProbabilityMeasure μ] (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ φ : E → EReal,
      ConvexPotential φ ∧
        LowerSemicontinuous φ ∧
          PotentialIntegrable φ μ ∧
            ConvexPotential (legendre φ) ∧
              mass dx (legendre φ) = 1 ∧ ofPotential dx (legendre φ) = μ := by
  obtain ⟨φ, hc, hlsc, hpot, hmass, hmax⟩ := exists_variational_maximum dx μ hsub hfirst hbar
  have hμ : μ ≠ 0 := IsProbabilityMeasure.ne_zero μ
  have hfin : ∃ x, φ x ≠ ⊤ := by
    have : NeZero μ := ⟨hμ⟩
    exact hpot.2.1.exists
  exact
    ⟨φ, hc, hlsc, hpot, convexPotential_legendre φ hfin, hmass,
      ofPotential_legendre_eq_of_maximizer dx μ hμ hlsc hpot hmass hmax⟩

/-- **CEK Theorem 2, existence with essential continuity, for probability measures**
(Cordero-Erausquin–Klartag arXiv:1304.0630v1, Proposition 12, (43)–(44) and Proposition 10): for a
probability
measure `μ` with finite first moment, barycenter `0` and not supported in a proper linear subspace,
and an additive
Haar measure `dx`, the conjugate `ψ = φ*` of a lower semicontinuous Proposition 12 maximizer `φ` is
a convex
essentially continuous potential with `∫ exp(-ψ) dx = 1` and moment measure `μ`. -/
theorem exists_ofPotential_eq_essentiallyContinuous_of_probability (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ φ : E → EReal,
      ConvexPotential φ ∧
        LowerSemicontinuous φ ∧
          PotentialIntegrable φ μ ∧
            ConvexPotential (legendre φ) ∧
              EssentiallyContinuous (legendre φ) ∧
                mass dx (legendre φ) = 1 ∧ ofPotential dx (legendre φ) = μ := by
  obtain ⟨φ, hc, hlsc, hpot, hmass, hmax⟩ := exists_variational_maximum dx μ hsub hfirst hbar
  have hμ : μ ≠ 0 := IsProbabilityMeasure.ne_zero μ
  have hfin : ∃ x, φ x ≠ ⊤ := by
    have : NeZero μ := ⟨hμ⟩
    exact hpot.2.1.exists
  exact
    ⟨φ, hc, hlsc, hpot, convexPotential_legendre φ hfin,
      essentiallyContinuous_legendre_of_maximizer dx μ hfirst hc hpot hmass fun f _ hf =>
        hmax f hf,
      hmass, ofPotential_legendre_eq_of_maximizer dx μ hμ hlsc hpot hmass hmax⟩

/--
**CEK Theorem 2, existence** (Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 2, existence
part): let `dx`
be an additive Haar measure and `μ ≠ 0` a finite Borel measure with finite first moment, barycenter
`0` and not
supported in a proper linear subspace (`μ(Vᶜ) = 0` forces `V = ⊤`). Then there is a convex
essentially continuous
`ψ : E → EReal` (never `-∞`; CEK Definition 2) whose effective domain `{ψ < +∞}` has nonempty
interior, with
`∫ exp(-ψ) dx = μ(E)` and moment measure `μ`: `(∇ψ)_# (exp(-ψ) dx) = μ` (`ofPotential dx ψ = μ`). -/
theorem exists_ofPotential_eq_essentiallyContinuous (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsFiniteMeasure μ] (hμ : μ ≠ 0) (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ ψ : E → EReal,
      ConvexPotential ψ ∧
        EssentiallyContinuous ψ ∧
          (interior {x | ψ x ≠ ⊤}).Nonempty ∧ mass dx ψ = μ univ ∧ ofPotential dx ψ = μ := by
  set c : ℝ≥0∞ := μ univ with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (Measure.measure_univ_ne_zero).mpr hμ
  have hctop : c ≠ ⊤ := measure_ne_top μ univ
  set ν : Measure E := c⁻¹ • μ with hν
  have hνprob : IsProbabilityMeasure ν :=
    ⟨by rw [hν, Measure.smul_apply, smul_eq_mul, ← hc, ENNReal.inv_mul_cancel hc0 hctop]⟩
  have hνsub : ∀ V : Submodule ℝ E, ν (V : Set E)ᶜ = 0 → V = ⊤ := by
    intro V hV
    apply hsub V
    rw [hν, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hV
    rcases hV with h | h
    · exact absurd h (ENNReal.inv_ne_zero.mpr hctop)
    · exact h
  have hνfirst : Integrable (fun x : E => x) ν :=
    hfirst.smul_measure (ENNReal.inv_ne_top.mpr hc0)
  have hνbar : ∫ x, x ∂ν = 0 := by rw [hν, integral_smul_measure, hbar, smul_zero]
  obtain ⟨φ, _hφc, _hlsc, _hpot, hconv, hess, hmass, hmom⟩ :=
    exists_ofPotential_eq_essentiallyContinuous_of_probability dx ν hνsub hνfirst hνbar
  set b : ℝ := Real.log c.toReal with hb
  have hexp : ENNReal.ofReal (Real.exp b) = c := by
    rw [hb, Real.exp_log (ENNReal.toReal_pos hc0 hctop), ENNReal.ofReal_toReal hctop]
  have hψleg : (fun y => legendre φ y - (b : EReal)) = legendre (affineSubtract φ 0 (-b)) := by
    funext y
    rw [legendre_affineSubtract, add_zero, sub_eq_add_neg, EReal.coe_neg]
  have hψconv : ConvexPotential (fun y => legendre φ y - (b : EReal)) := by
    refine ⟨fun y h => ?_, ?_⟩
    · change legendre φ y - (b : EReal) = ⊥ at h
      rw [sub_eq_add_neg, ← EReal.coe_neg, EReal.add_eq_bot_iff] at h
      rcases h with h | h
      · exact hconv.1 y h
      · exact EReal.coe_ne_bot _ h
    · rw [hψleg]
      exact convex_epigraph_legendre _
  have hψlsc : LowerSemicontinuous (fun y => legendre φ y - (b : EReal)) := by
    rw [hψleg]
    exact lowerSemicontinuous_legendre _
  have hdom : {y | legendre φ y - (b : EReal) ≠ ⊤} = {y | legendre φ y ≠ ⊤} := by
    ext y
    change legendre φ y - (b : EReal) ≠ ⊤ ↔ legendre φ y ≠ ⊤
    induction legendre φ y with
    | bot => simp
    | top => simp
    | coe r =>
      exact
        ⟨fun _ => EReal.coe_ne_top r, fun _ => by
          rw [← EReal.coe_sub];
          exact EReal.coe_ne_top _⟩
  have hψess : EssentiallyContinuous (fun y => legendre φ y - (b : EReal)) := by
    rw [hψconv.essentiallyContinuous_iff, hdom]
    exact ⟨hψlsc, (hconv.essentiallyContinuous_iff.mp hess).2⟩
  have hmassψ : mass dx (fun y => legendre φ y - (b : EReal)) = c := by
    rw [mass_sub_const, hmass, mul_one, hexp]
  refine ⟨fun y => legendre φ y - (b : EReal), hψconv, hψess, ?_, hmassψ, ?_⟩
  · exact interior_domain_nonempty_of_mass_ne_zero dx hψconv (by rw [hmassψ]; exact hc0)
  · rw [ofPotential_sub_const dx hconv (lowerSemicontinuous_legendre φ).measurable, hmom, hexp,
      hν, smul_smul, ENNReal.mul_inv_cancel hc0 hctop, one_smul]

/--
**CEK Theorem 2, existence** (Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 2, existence
part, recording
lower semicontinuity instead of essential continuity): let `dx` be an additive Haar measure and `μ ≠
0` a finite Borel
measure with finite first moment, barycenter `0` and not supported in a proper linear subspace
(`μ(Vᶜ) = 0` forces
`V = ⊤`). Then there is a convex lower semicontinuous `ψ : E → EReal` (never `-∞`) whose effective
domain `{ψ < +∞}`
has nonempty interior, with `∫ exp(-ψ) dx = μ(E)` and moment measure `μ`: `(∇ψ)_# (exp(-ψ) dx) = μ`
(`ofPotential dx ψ = μ`). See `exists_ofPotential_eq_essentiallyContinuous` for the essentially
continuous form. -/
theorem exists_ofPotential_eq (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ ψ : E → EReal,
      ConvexPotential ψ ∧
        LowerSemicontinuous ψ ∧
          (interior {x | ψ x ≠ ⊤}).Nonempty ∧ mass dx ψ = μ univ ∧ ofPotential dx ψ = μ := by
  obtain ⟨ψ, hconv, hess, hint, hmass, hmom⟩ :=
    exists_ofPotential_eq_essentiallyContinuous dx μ hμ hsub hfirst hbar
  exact ⟨ψ, hconv, hess.1, hint, hmass, hmom⟩

end FunctionalInequalities.KLS.CEK
