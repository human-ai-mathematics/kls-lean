# 2026-09-11 — Prompt for proof session: replace the sorry placeholders in `KLS/LogConcave/ConditionalFiber.lean` with proofs

The following prompt can be directly copied to another model/session. Preceding note: Statement skeleton and infrastructure verification see
[`2026-09-11-conditional-fiber-twelve-bound-statement.md`](2026-09-11-conditional-fiber-twelve-bound-statement.md);
The upstream comparison lemma has been registered as certification ([registration record](2026-09-11-conditional-fiber-energy-comparison-registration.md)).

---

```
Repository: /Users/lyuyuwei/Documents/ChatGPT/KLS (Lean 4 / Mathlib v4.33.0, Mathlib submission
db584cd6d46c92f209a44c0f1c829460d327499d; Lake root directory formalization/)

Task: Fill in the only sorry statement in formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean:

  theorem ae_conditionalFiber_logConcave (hμ : LogConcave μ) (hρ : Admissible μ ρ)
      (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m) :
      ∀ᵐ b ∂baseLaw μ ρ, LogConcave (⟨kernel μ ρ b, inferInstance⟩ : ProbabilityMeasure ℝ)

This is the analysis content of the Blueprint node cor:conditional-fiber-twelve-bound (formalization/blueprint/src/chapters/50-kls-routes.tex, "Log-concave conditional fibers" inference block) proof segment: "Fubini disintegration of the log-concave density gives
conditional densities proportional to t ↦ ρ_μ(z+tθ) wherever the normalizing slice integral is finite and positive.
These densities are log-concave. The remaining fibers are null." The remaining five theorems in this file have been derived from this lemma together with two already certified inputs (lem:conditional-fiber-energy-comparison, thm:one-dimensional-logconcave-poincare). Do not alter them.

First read:
- research/decisions/2026-09-11-conditional-fiber-twelve-bound-statement.md (statement design, sentence-by-sentence alignment, three infrastructure gaps)
- formalization/FunctionalInequalities/KLS/ConditionalFiber.lean (jointLaw, baseLaw, kernel := (jointLaw μ ρ).condKernel,
  coordinates, reconstruct, baseMap, compProd_baseLaw_kernel, energyWithKernel_eq_energy —— the latter demonstrates
  the usage of "constructing a Markov kernel κ satisfying baseLaw ⊗ₘ κ = jointLaw ⇒ κ = kernel a.e."
- formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean (private lemma
  affineSupport_eq_top_of_absolutelyContinuous, ae_ae_reconstruct, ae_memLp_comp_reconstruct can be copied as written)
- formalization/FunctionalInequalities/KLS/Definitions.lean (LogConcave: compact set version),
  ProbabilityTheory.eq_condKernel_of_measure_eq_compProd κ hκ.symm)
- formalization/FunctionalInequalities/KLS/LogConcave/BorellRepresentation.lean (five fields of IsBorellDensity:
  KLS/LogConcave/Borel.lean (BorelLogConcave, innerMeasure, LogConcave.borel_iff)
  measurable, nonneg, upperSemicontinuous, logConcave, withDensity_eq;
  LogConcave.exists_isBorellDensity_of_interior_support_nonempty hlc m hint hac;
  convex_pos, concaveOn_log, pos_of_mem_interior_support)
- formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean's
  interior_support_nonempty_of_affineSupport_eq_top (derived from hac, the affine support is ⊤, hence the interior of support is nonempty)
- formalization/FunctionalInequalities/KLS/LogConcave/Line/Density.lean (LineDensity, exists_lineDensity:
  Note that the current repository only has "log-concave law ⇒ log-concave density", without the converse direction)


Rules:
1. Do not modify ae_conditionalFiber_logConcave and the other five theorems in the same file regarding their types. If unprovable, do not change the types; document the obstacle in the report and retain sorry.
2. New infrastructure required allows creation of new files (see suggested path below), permits writing public lemmas in new files; do not modify existing declarations in shared files (e.g., if it is necessary to change the private lemma from EnergyComparison.lean to public, only removal of private and addition of a docstring is allowed, without changing types).
Naming follows research/naming.md (short names without namespace duplication; log-concave consequences placed in KLS.LogConcave using hμ. point notation).
3. Do not register: do not add to formalization/FunctionalInequalities.lean, lakefile's Solutions root, research/a-series/ledger.yaml, research/check_blueprint.py's CERTIFICATES, research/tasks.json, Blueprint's \lean{}/\leanok.
Do not git commit, do not git push. Decision records are only appended (new entries).
   research/decisions/2026-09-1X-conditional-fiber-twelve-bound-proofs.md).
4. Compilation (in formalization/): after generating olean for a new file via lake build FunctionalInequalities.<module name>,
     lake env lean FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean
   goal: no errors, no "declaration uses 'sorry'", no warnings such as unusedSectionVars; after completion, for each new file and this file run lake env lean -DwarningAsError=true <file>
   and for ae_conditionalFiber_logConcave and conditionalFiber_literatureConstant_le_four_mul #print axioms, only propext / Classical.choice / Quot.sound are allowed.
5. If the local lake reports `external command 'git' exited with code 1`: prepend to PATH the directory containing the wrapper script for `exec /Library/Developer/CommandLineTools/usr/bin/git "$@"`, and set
   GIT_EXEC_PATH=/Library/Developer/CommandLineTools/usr/libexec/git-core,
   GIT_TEMPLATE_DIR=/Library/Developer/CommandLineTools/usr/share/git-core/templates. Do not modify repository content or system git configuration.

Suggested route (three sub-obligations, potentially split into three new files; A and B are independent, and C uses both):

## Sub-obligation A: One-dimensional "log-concave density ⇒ log-concave law on compact sets"
Suggested files formalization/FunctionalInequalities/Probability/Line/BrunnMinkowski.lean (general utilities) and formalization/FunctionalInequalities/KLS/LogConcave/Line/OfDensity.lean (log-concave conclusion). The pinned Mathlib lacks
Brunn–Minkowski or Prékopa–Leindler (all "Minkowski" grep results are gauge functionals).

A1. One-dimensional Brunn–Minkowski (for compact sets): K L : Set ℝ non-empty compact ⇒ volume (K + L) ≥ volume K + volume L
    (Set.add i.e. Minkowski sum, or written as {z | ∃ x ∈ K, ∃ y ∈ L, z = x + y}).
    Proof: a := sSup K, b := sInf L (IsCompact.sSup_mem / sInf_mem); (K + {b}) ∪ ({a} + L) ⊆ K + L,
    the intersection of the two pieces contains only a + b (K + b ≤ a + b ≤ a + L), so volume (K+L) ≥ volume (K+{b}) + volume ({a}+L) − volume {a+b}
    = volume K + volume L (measure_union_add_inter, Real.volume_singleton, translation invariance
    measure_preimage_add / Measure.IsAddRightInvariant).
A2. One-dimensional Prékopa–Leindler (lintegral version): f g h : ℝ → ENNReal measurable, t ∈ (0,1),
    ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y) ⇒ (∫⁻ f) ^ t * (∫⁻ g) ^ (1 - t) ≤ ∫⁻ h.
    Proof: first handle the degenerate branches where ∫⁻ f or ∫⁻ g is 0 or ⊤; then normalize to ∫⁻ f = ∫⁻ g = 1 (homogeneity:
    f/‖f‖, g/‖g‖, h/(‖f‖^t‖g‖^{1−t}) still satisfies the assumptions). The cake formula lintegral_eq_lintegral_meas_lt
    (Mathlib/MeasureTheory/Integral/Layercake.lean) writes the three integrals as ∫⁻ s in Ioi 0, volume {x | s < ·};
    for each s > 0, {h > s} ⊇ t • {f > s} + (1 − t) • {g > s} (if f x > s, g y > s then
    h(tx+(1−t)y) ≥ s^t s^{1−t} = s; note that when using the strict inequality version, adjustments are needed for s < f x ⇒ … omitted),
    apply A1 on inner regular approximations by compact subsets (Real.volume is InnerRegular: MeasurableSet.measure_eq_iSup_isCompact
    or Measure.InnerRegular), obtain volume {h>s} ≥ t·volume{f>s} + (1−t)·volume{g>s} (scaling: Real.volume_smul / Measure.addHaar_smul), integrate to get ∫⁻ h ≥ t·1 + (1−t)·1 = 1 = 1^t·1^{1−t}.
A3. Conclusion: ν : ProbabilityMeasure ℝ, p : ℝ → ℝ satisfies IsBorellDensity ν volume p ⇒ LogConcave ν.
    Proof: for compact sets K₀ K₁ and t, take f := 1_{K₀}·ofReal∘p, g := 1_{K₁}·ofReal∘p,
    h := 1_{tK₀+(1−t)K₁}·ofReal∘p; IsBorellDensity.logConcave gives pointwise assumption (x ∈ K₀, y ∈ K₁ ⇒
    tx+(1−t)y ∈ the convex combination set), A2 gives ∫⁻ h ≥ (∫⁻ f)^t (∫⁻ g)^{1−t}, then use withDensity_eq to replace the three integrals with ν measure (withDensity_apply, lintegral_indicator). The convex combination set {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t•x+(1−t)•y} is compact (KLS.LogConcave.isCompact_combination in Borel.lean) hence measurable.

## Sub-obligation B: Explicit decomposition kernel along a line
Suggested file formalization/FunctionalInequalities/KLS/ConditionalFiber/SliceKernel.lean (namespace KLS.ConditionalFiber).
Given a density p : E → ℝ (measurable, non-negative), define:
  sliceMass p b := ∫⁻ t, ENNReal.ofReal (p (reconstruct b t))            -- Z(θ,z)
  sliceKernel p : Kernel (Direction E × E) ℝ :=
    On {b | 0 < sliceMass p b ∧ sliceMass p b < ⊤}
      (volume.withDensity fun t ↦ ENNReal.ofReal (p (reconstruct b t))) divided by sliceMass p b
       (Kernel.withDensity (Kernel.const _ volume) (fun b t ↦ ofReal (p (reconstruct b t)) / sliceMass p b),
       The integrand is measurable with respect to (b,t): measurable_reconstruct, '), Measurable.lintegral_kernel_prod_right
    Otherwise Kernel.const _ (Measure.dirac 0) ( Kernel.piecewise , measurable set).
  Proof IsMarkovKernel (good set with mass Z/Z = 1: lintegral_div_const / ENNReal.div_self).
B1. Key identity: IsBorellDensity μ m p (or simply m.withDensity (ofReal ∘ p) = μ) ⇒
    baseLaw μ ρ ⊗ₘ sliceKernel p = jointLaw μ ρ.
    Proof: Measure.ext_of_lintegral or compare for measurable set s. Right-hand side = ∫⁻ θ ∫⁻ x 1_s(coordinates (θ,x)) ofReal(p x) dm dρ
    (jointLaw definition, lintegral_map, withDensity, lintegral_prod). For fixed θ, the Fubini along the line:
    m is Haar, (z,t) ↦ z + t•θ is a continuous linear equivalence T_θ of (θ⊥ × ℝ) ≃L[ℝ] E
     (Submodule.prodEquivOfIsCompl (ℝ∙θ)ᗮ (ℝ∙θ) + equivalence with one-dimensional subspaces and ℝ, or direct hand-writing
     LinearEquiv again LinearEquiv.toContinuousLinearEquiv, so map T_θ (m_θ.prod volume) is also Haar
    (ContinuousLinearEquiv.isAddHaarMeasure_map), differs from m by a constant c_θ (Measure.isAddLeftInvariant_eq_smul /
    addHaarMeasure_unique). Thus ∫⁻ x, G x dm = c_θ ∫⁻ z ∫⁻ t, G (z + t•θ) dt dm_θ.
    Take G x := 1_s((θ, x − ⟪x,θ⟫θ), ⟪x,θ⟫) ofReal(p x); for z ∈ θ⊥, the coordinates (θ, z + tθ) = ((θ,z),t)
    (z ⊥ θ, ‖θ‖ = 1), we obtain the right-hand side = ∫⁻ θ c_θ ∫⁻ z ∫⁻ t 1_s((θ,z),t) ofReal(p(z+tθ)) dt dm_θ dρ.
    left = ∫⁻ b, sliceKernel p b (Prod.mk b ⁻¹' s) dbaseLaw (Measure.compProd_apply); baseLaw = map baseMap (ρ.prod μ)
    (baseLaw_eq_map), similarly, Fubini gives the baseLaw's θ-section a density c_θ·Z(θ,z) (with respect to m_θ), thus
    Left = ∫⁻ θ c_θ ∫⁻ z Z(θ,z) · [Z(θ,z)⁻¹ ∫⁻ t 1_s ofReal(p(z+tθ)) dt] dm_θ dρ, pointwise equal to the right-hand side on good sets;
    Bad set {Z = 0} ∪ {Z = ⊤}: at Z = 0, the integrand functions on both sides are 0; the z for Z = ⊤ is an m_θ-nullable set
    (∫⁻ Z dm_θ · c_θ = 1 finite, ae_lt_top). c_θ is identical on both sides, so no computation is needed.
    If the T_θ and m_θ depending on θ are too heavy, an alternative route can be taken: perform the above calculations only for each fixed θ (after θ is fixed,
    m_θ := any Haar on (ℝ∙θ)ᗮ, if Measure.addHaar), outer integral_prod first fixes θ;
    lintegral_baseLaw already gives baseLaw integral = ∫⁻ θ ∫⁻ z F(θ,z) d(map (x ↦ x − ⟪x,θ⟫θ) μ) dρ,
    Thus it suffices to prove for each θ that "the projection law map (x ↦ x − ⟨x,θ⟩θ) μ has density c_θ Z(θ,·) with respect to m_θ" and
    ∫⁻ x G x dm = c_θ ∫⁻ z ∫⁻ t G(z+tθ) dt dm_θ" two lines, do not make c_θ, m_θ into measurable objects with respect to θ.
B2. By B1 and ProbabilityTheory.eq_condKernel_of_measure_eq_compProd (sliceKernel p) hκ.symm we get
    ∀ᵐ b ∂baseLaw μ ρ, sliceKernel p b = kernel μ ρ b (verbatim copy the usage of energyWithKernel_eq_energy,
    (jointLaw μ ρ).fst is defined as baseLaw μ ρ).
B3. Good set almost everywhere: ∀ᵐ b ∂baseLaw, 0 < sliceMass p b ∧ sliceMass p b < ⊤ (Z = ⊤ null-measure equal to B1;
    the baseLaw mass of the set of base points with Z = 0 equals ∫⁻ 1_{Z=0} · Z = 0).

## Sub-obligation C: Assemble ae_conditionalFiber_logConcave
1. hac + hμ ⇒ affine support is ⊤ (private lemma affineSupport_eq_top_of_absolutelyContinuous of EnergyComparison.lean, copy or omit private) ⇒ interior support is nonempty (interior_support_nonempty_of_affineSupport_eq_top) ⇒
take p such that IsBorellDensity μ m p (exists_isBorellDensity_of_interior_support_nonempty).
2. For b on a good set, sliceKernel p b is a probability measure on ℝ with density t ↦ ofReal(p(z + tθ)) / Z with respect to volume;
  it is a Borel density: measurable, non-negative, upper semicontinuous (p upper semicontinuous ∘ continuous affine), log-concave (IsBorellDensity.logConcave along affine lines
  t•(z+xθ) + (1−t)•(z+yθ) = z + (tx + (1−t)y)θ, divided by constant Z preserves), withDensity_eq by definition.
  By sub-obligation A3, LogConcave (sliceKernel p b).
3. filter_upwards [B2, B3] transfers the conclusion to kernel μ ρ b (Subtype equality using ext of ProbabilityMeasure / direct rw measure equality).

Gaps and hints:
- The combinatorial set definition for LogConcave is {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y}, on ℝ, where t • x = t * x (smul_eq_mul).
- In ENNReal, the zero_le parameter is implicit (written exact zero_le); mul_le_mul_left'/right' no longer exist; use mul_le_mul_left / mul_le_mul_right instead (note the current Mathlib version's convention for left/right: mul_le_mul_right (h : b ≤ c) a : a * b ≤ a * c).
- ⟨kernel μ ρ b, inferInstance⟩ : the toMeasure of ProbabilityMeasure ℝ is simply kernel μ ρ b (Subtype.val reduction), a.e. equal kernels can be replaced with congrArg/Subtype.ext.
- The non-degeneracy condition does not need to be proven here: FiberBound only imposes constraints on non-degenerate fibers, and conditionalFiber_fiberBound_four is already implemented. This lemma only requires a.e. log-concave.
- If the subtask A's Prékopa–Leindler is too long, first write A2 as an independent lemma about measurable functions with ENNReal values and use sorry as a placeholder, run through the assembly of B and C first, then return to fill in A2; report each subtask's completion status clearly.

List the following for the completed report: completion/status of each sub-obligation, new files and their public declarations, key Mathlib API used,
if any statement you suspect is incorrect (missing premises, wrong direction, etc.) provide a specific counterexample, and "where should these new lemmas be placed in a shared file".
```
