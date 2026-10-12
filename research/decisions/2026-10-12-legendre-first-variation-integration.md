# Legendre first variation (CEK (42), pointwise): canonical integration

Date: 2026-10-12. Controller: Codex thread `01a12de4-2412-7082-ae33-15b1c3502420` (the new Goal: Letwin v1 Theorem 2.5 →
Theorem 1.2 with constant 8 → BKL v1 Lemma 4.2 / Theorems 4.1 / 1.1 / KLS). Integrator: the sole reviewed Claude conversation,
writer window AF.

## Integration

**Input.** Root-revalidated, previously reviewed strong-API constructions
(`build/reviews/2026-10-12-bkl-letwin-t25-continuation/goal-20261012T0647/revalidated-legendre-variation/`).
- 12 literal modules, 58 owned constants, all with standard axioms.
- All 12 modules kernel-replayed.
- The shared `Analysis/Convex/{Legendre,AffineMaximum}.lean` are byte-equal.
- No proof body was written by Root.

**Placement:**
- **`Analysis/Extremum.lean`.** Finite maxima of upper semicontinuous `EReal` functions with linear decay.
- **Family directory `Analysis/Convex/LegendreVariation/` (`Attainment`, `Perturbation`, `Derivative`).**
  - The family rule of `research/naming.md` forbids three `Legendre*` basenames.
  - A `Convex/Legendre/` directory would move `Legendre.lean` and all its importers.
- **Audit `research/audits/BKL/LetwinLegendreVariationAudit.lean`.** The real clients.

**Name changes.**
- `KLSConstruction.API.FirstVariation.conjugate_maximizer_eq_gradient` → `FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient`.
- The audit namespace `KLSConstruction.API.FirstVariation.BoundaryClient` → `DirectVariationBoundaryClient`.
- Full map: `research/api-migration/2026-10-12-legendre-variation-promotion-map.json`. No aliases.

**Text changes.**
- Proof bodies are verbatim, except the one reference to `conjugate_maximizer_eq_gradient`.
- The production import of the whole `Mathlib.Tactic` was dropped. The strict compiles needed nothing more, and the
  compiled terms did not change.

**Comparison.** Pure compiled, all 58 constants: equal in kind, ordered universes, type and value under the explicit map.
40 are RAW-equal; 18 are equal after replacing only the module component of hygiene labels.

**Evidence:** `build/reviews/2026-10-12-bkl-letwin-t25-continuation/goal-20261012T0647/claude-af-legendre-variation-integration-v1/`.

**Not provided:** the pointwise first variation is a moment-map prerequisite, not the moment map. The integral first
variation / Euler–Lagrange for a source law, the gradient push-forward, source regularity, CEK Theorem 2 (essential
continuity, uniqueness), Letwin Theorems 2.5 and 1.2, BKL and KLS remain open. No lemma-map relation, coverage or
certificate changes.

## Superseded live text (verbatim)

The source modules' module docstrings, which claimed "one intentional construction hole", were stale: the revalidated
sources have no hole, with standard axiom closure and kernel replay. They were replaced by honest module docstrings. The
current-state HANDOFF clauses below still asked for receipts that now exist. Quoted in code blocks; links inert.

Source module `USCAttainmentFixed`:

```text
/-!
# Frozen actual extended-real USC attainment target

Generic compactness infrastructure for BB arXiv:1207.6128v1 Lemma2.7/Appendix6
and CEK arXiv:1304.0630v1 first variation. The linear decay is actual input
of this generic unit, to be derived from dual interior in the CEK application.
One construction hole remains; this scratch theorem is not certified.
-/
```

Source module `CoerciveTiltFixed`:

```text
/-!
# Frozen coercive tilt construction target

Generic growth infrastructure for BB arXiv:1207.6128v1 Lemma 2.7 / Appendix 6
and CEK arXiv:1304.0630v1 first variation. This scratch statement has one
intentional construction hole and is not a completed proof.
-/
```

Source module `TiltedObjectiveFixed`:

```text
/-!
# Frozen tilted-objective data adapter

Application interface supporting Berman--Berndtsson, arXiv:1207.6128v1,
Lemma 2.7 / Appendix 6, and Cordero-Erausquin--Klartag,
arXiv:1304.0630v1, first variation.

This scratch statement has one intentional construction hole. It packages actual
extended-real objective data and does not assert attainment or a maximizer.
-/
```

Source module `ActualArgmax`:

```text
/-!
# Frozen actual Legendre argmax interface

Generic attainment infrastructure for Berman--Berndtsson,
arXiv:1207.6128v1, Lemma 2.7 / Appendix 6, and
Cordero-Erausquin--Klartag, arXiv:1304.0630v1, first variation.

This scratch interface has one intentional construction hole. It does not
import or assume the pending tilted-objective data adapter.
-/
```

Source module `LegendreBoundedPerturbationFixed`:

```text
/-!
# Frozen bounded perturbation of the actual extended-real conjugate

Supporting infrastructure for BB arXiv:1207.6128v1 Lemma2.7/Appendix6
and CEK arXiv:1304.0630v1 equation42. Entire EReal sup is retained,
including infinity. One intentional construction hole remains.
-/
```

Source module `LegendreFiniteCurveFixed`:

```text
/-!
A supporting finite-curve interface for the direct first-variation route.
It packages only consequences of genuine bounded perturbation data.
-/
```

Source module `LegendreNearMaxFixed`:

```text
/-!
# Near-maximizer stability from dual differentiability

Supporting route for Berman--Berndtsson, arXiv:1207.6128v1, Lemma 2.7 and
Appendix 6, and Cordero-Erausquin--Klartag, arXiv:1304.0630v1, equation (42).
This pure interface has one intentional construction hole.
-/
```

Source module `LegendreVariationFixed`:

```text
/-!
# Direct first variation of the actual Legendre transform

Source target: Berman--Berndtsson, arXiv:1207.6128v1, Lemma 2.7
(second point) and Appendix 6; Cordero-Erausquin--Klartag,
arXiv:1304.0630v1, equation (42).

This frozen interface has one intentional construction hole. It states the
actual extended-real perturbation and does not take a maximizing family,
a derivative formula, or a real-valued surrogate as input.
-/
```

Source module `VariationClients (header comment)`:

```text
/- Compile only against Root's terminal accepted-source candidate; no prototype hole import. -/
```

`HANDOFF.md` — Letwin Theorem 2.5 extension step:

```text
Letwin Theorem 2.5 extension step (2026-10-12, working tree; it needs its own matching full local receipt): `symmetric_trace_integral_extension` in the new `Analysis/Matrix/Integral.lean` derives, for any measure and any measurable positive semidefinite matrix field, the bound `∫ tr(BHBH) dν ≤ 2 tr(B²)` with its integrability for every symmetric `B` from the same bound for every positive semidefinite `A`, a named hypothesis (Blueprint `lem:letwin-symmetric-integral`, audit `BKL/LetwinSymmetricIntegralAudit.lean` with an actual two-point law). The source positive semidefinite bound, the moment map of the source law and its application, and Letwin Theorem 2.5 itself remain open (the scalar Brascamp–Lieb inequality for a given potential is recorded below); Letwin T25 stays partial.
```

`HANDOFF.md` — Letwin Lemma A.6 support:

```text
Letwin Lemma A.6 support (2026-10-12, working tree; it needs its own matching full local receipt): in the new `KLS/LogConcave/HeatSemigroup/Range.lean`, the images of compactly supported smooth functions under the ordinary weighted diffusion operator are dense in the mean-zero classes of `L²(ν)` for a log-concave `ν = m.tilted(−U)` with `C¹` `U` (`centered_mem_closure_compactSmoothDiffusionImage`; Blueprint `lem:letwin-centered-range`; audit `BKL/LetwinCenteredRangeAudit.lean` with the actual Gaussian law). It is finite-energy Brascamp–Lieb infrastructure for the ordinary weighted diffusion of a `C¹` potential. The given-potential scalar Brascamp–Lieb inequality is recorded below; applying Lemma A.6 to the actual source-law moment map, and Letwin Theorem 2.5, remain open; Letwin LA6 is partial.
```

`HANDOFF.md` — Further Letwin Lemma A.6 supports:

```text
Further Letwin Lemma A.6 supports (2026-10-12, working tree; they need their own matching full local receipt): compactly supported coercivity of the ordinary weighted diffusion, `∫ ∇²U(∇u, ∇u) dμ ≤ ∫ (ℒu)² dμ` with both integrability conclusions (`compact_ordinary_diffusion_coercivity` in `Analysis/BakryEmery/Curvature.lean`), and the inverse-quadratic Young inequality for positive definite matrices (`inverse_quadratic_young` in `Analysis/Matrix/Positivity.lean`); Blueprint `lem:letwin-finite-energy-supports`, audit `BKL/LetwinFiniteEnergyAudit.lean`. They concern the ordinary weighted Laplacian (coercivity for `C²` `U`), not the inverse-Hessian operator. The given-potential scalar Brascamp–Lieb inequality is recorded below; applying Lemma A.6 to the actual source-law moment map remains open.
```

`HANDOFF.md` — Letwin:

```text
Letwin (2.8) for Theorem 2.5 (2026-10-12, working tree; same receipt condition): in the new `Analysis/BakryEmery/HessianTrace.lean`, the pointwise identity `L tr(BHBH) = 2 tr(BHB·LH) + 2 Σ φ^{ab} tr(B∂_aH B∂_bH)` holds for smooth `φ`, any `V` and every constant real `B`, with no PSD, commutation or Monge–Ampère premise (`hessianInverseOperator_trace_stdHessianMatrix_sq`; Blueprint `lem:letwin-hessian-trace`; audit `BKL/LetwinHessianTraceAudit.lean` with the nonconstant quartic `x⁴/12 + x²/2`). The given-potential Monge–Ampère substitution and pointwise (2.10) are recorded below; noncompact A.4/A.5 consumption for the trace, the tensor comparison and the source positive-semidefinite trace estimate remain open; Letwin T25 and LA6 stay partial.
```

`HANDOFF.md` — Bounded-source primal:

```text
Bounded-source primal (2026-10-12, working tree; it needs its own matching full local receipt): for an isotropic probability law with `‖y‖ ≤ L` almost everywhere, the CEK Proposition 12 maximiser capped to the `L`-ball gives a finite conjugate `ψ`, convex and `L`-Lipschitz, with `∫ e^{−ψ} = 1` and `e^{−ψ}dx` a probability (`bounded_source_lipschitz_primal` in the new `KLS/CEK/BoundedPrimal.lean`, generic geometry in `Analysis/Convex/BoundedConjugate.lean`; Blueprint `lem:cek-bounded-primal`; audit `BKL/LetwinBoundedPrimalAudit.lean` with the uniform law on `[-√3, √3]`). It is a weak normalized primal: the Euler–Lagrange identification, the gradient push-forward, source smoothness, a positive definite Hessian, the gradient diffeomorphism and the Monge–Ampère equation remain open, as do CEK Theorem 2 and Letwin Theorem 2.5.
```

`HANDOFF.md` — Letwin Lemma A.6 for a given potential:

```text
Letwin Lemma A.6 for a given potential (2026-10-12, working tree; it needs its own matching full local receipt): in the new `KLS/LogConcave/BrascampLieb.lean`, for a log-concave `ν = m.tilted(−U)` with everywhere positive definite Hessian and `C¹` `f ∈ L²(ν)`, `Var f ≤ ∫ ⟪∇f, H⁻¹∇f⟫ dν` — for `C²` `U` with integrable energy (`scalar_brascamp_lieb_finite_energy`) and, with the right side in `[0, ∞]` and no energy premise, for `C^∞` `U` (`scalar_brascamp_lieb_extended_energy`, bounded tests included); the energy facts are in the new `Analysis/BakryEmery/InverseHessianEnergy.lean` (Blueprint `thm:letwin-scalar-brascamp-lieb`, `lem:letwin-inverse-hessian-energy`; audit `BKL/LetwinScalarBrascampLiebAudit.lean`, equality for the standard Gaussian law). The potential is given: the source moment map, its Euler–Lagrange identification, push-forward and regularity, hence A.6 for the source law and Letwin Theorem 2.5, remain open; Letwin LA6 is partial.
```

`HANDOFF.md` — Letwin:

```text
Letwin (2.9)–(2.10) for a given potential (2026-10-12, working tree; it needs its own matching full local receipt): in `Analysis/BakryEmery/HessianTrace.lean` (section `MongeAmpereTrace`), for smooth `φ` with positive definite Hessian satisfying the zero-order Monge–Ampère relation, `V` smooth only near `closure K ⊇ range ∇φ`, (2.9) and (2.10) hold for every constant `B` (`traceGenerator_210_on_range`); for open `K`, `V` convex on `K` and PSD `B` the three remainders are nonnegative, so `L tr(BHBH) + 2 tr(BHBH) ≥ 0` pointwise (`traceGeneratorCondition_on_range`; Blueprint `lem:letwin-ma-trace-210`; matrix support in `Analysis/Matrix/Positivity.lean`; audit `BKL/LetwinMongeAmpereTraceAudit.lean` with a nonconstant interval potential). This pointwise condition is not yet integrated: A.4–A.5 for this trace function, the tensor comparison and the source trace bound, the source-law moment map and Letwin Theorem 2.5 remain open.
```
