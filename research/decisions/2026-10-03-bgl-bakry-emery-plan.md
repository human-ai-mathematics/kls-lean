# Bakry–Émery `C_P ≤ 1/ρ`: four-hour plan (2026-10-03)

The owner supplied Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators*
(Grundlehren 348, Springer 2014), and asked for a four-hour task after pushing `b5ba50c`.

## Target

BGL Corollary 4.8.2 (p. 212): if `dμ = e^{-W} dx` is a probability measure on `ℝⁿ` with a smooth
`W` and `∇∇W ≥ ρ Id`, `ρ > 0`, then `μ` satisfies `P(1/ρ)`, i.e. `Var_μ(f) ≤ (1/ρ) ∫ |∇f|² dμ`.
The book derives it from Proposition 4.8.1 (`P(1/ρ)` under `CD(ρ, ∞)`), whose semigroup proof is
Proposition 4.8.3 (`P(C)` iff `E(f) ≤ C ∫ (Lf)² dμ` on `D(L)`), using ergodicity `P_∞ f = ∫ f dμ`.

## Starting point (audit of the repository)

Everything in `KLS/LogConcave/HeatSemigroup/` and `Analysis/BakryEmery/` is at curvature `0`:
- the pointwise Bochner identity `gammaTwo_eq_hessianSqStdBasis_add` holds for every `C²` potential;
- `P_t = exp(-t T̄†T̄)` exists, with its generator identified on `C_c^∞` and `C_c^∞` an operator core;
- the energy derivative of `‖P_t f‖²` is proved;
- there is no `ρ`, no ergodicity, and no lemma that `T̄ h = 0` forces `h` to be constant.

## Steps (statements by Claude, proofs by the GPT worker, local commits only)

1. Source: pin BGL 2014 Chapter 4 and add its lemma map (46 numbered statements), with existing
   declarations mapped. Other chapters are out of scope for this map.
2. Curvature layer, `Analysis/BakryEmery/Curvature.lean`:
   - `Hess U ≥ ρ ≥ 0` implies `U` convex;
   - pointwise `Γ₂(f) ≥ ρ Γ(f)`;
   - `∫ Γ₂(f) dμ = ∫ (ℒf)² dμ` on `C_c³`, hence `ρ ∫ Γ(f) ≤ ∫ (ℒf)²`.
3. Operator level, in `KLS/LogConcave/HeatSemigroup/`: `ρ ‖T̄ y‖² ≤ ‖A y‖²` on all of `D(A)`, via the
   existing operator core.
4. Semigroup level:
   - energy decay `‖T̄ P_t g‖² ≤ e^{-2ρt} ‖T̄ g‖²`;
   - the finite-time variance bound `Var(g) - Var(P_t g) ≤ (1 - e^{-2ρt})/ρ · ‖T̄ g‖²`.
5. Out of scope tonight: ergodicity (`Var(P_t g) → 0`, equivalently `ker T̄ = constants`), which
   turns step 4 into Corollary 4.8.2. Proposed route: a Poincaré inequality on cubes from the proved
   one-dimensional log-concave bound and finite tensorization, then local constancy.

## Placement plan

- Step 2: owner `Analysis/BakryEmery` (generic diffusion calculus on a finite-dimensional inner
  product space, potential `U`, measure `m.tilted (-U)`). Create `Curvature.lean`; imports `Bochner`
  and `IntegratedBochner`. It adds API and changes no existing statement.
- Steps 3–4: owner `KLS/LogConcave/HeatSemigroup` (the log-concave heat semigroup model, hypothesis
  bundle `hν hi hνU hU hconv`). Create `Curvature.lean` there; imports `Decay`, `InteriorRegularity`
  and `Analysis/BakryEmery/Curvature`. The curvature hypothesis is
  `∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v`.
- Validation: independent recheck of every statement, then the full local verifier before each
  Lean commit.

## Log

- Step 1 done: BGL 2014 Chapter 4 lemma map (46 numbered statements; main target Corollary 4.8.2),
  drafted by an agent from the extracted text and reviewed by Claude. An independent GPT reading
  of the chapter listed the same 46 statements. Mapped declarations, all partial: Proposition 4.1.1
  (Gaussian P(1) on smooth tests; covariance clause in dimension one only), Proposition 4.3.1
  (tensorization for the Euclidean carré du champ), Theorem 4.2.5 ((i) ⇒ (ii) in the heat model),
  Theorem 4.6.3 (dimension one), Theorem 4.7.2 ((ii) and (iv) at ρ = 0). The proposed contraction
  principle matches were rejected: coordinate projections and scalings are not Proposition 4.4.4.
  Extraction uncertainties are flagged in the item notes (Proposition 4.4.2, Remarks 4.2.4 and 4.7.4,
  Proposition 4.5.5, Corollary 4.10.9). All 24 register diagrams render (Mermaid 11).
- Driver finding: the proof driver compared only theorem headers. During this block the worker
  replaced the section variable `(m : Measure E) [m.IsAddHaarMeasure]` with
  `{m : Measure E} [IsProbabilityMeasure m]`, which would have made the integrated statements
  vacuous for a Haar measure. Claude restored the line; the two helper proofs accepted under it
  compile unchanged with the original line. The driver now rejects any change to
  `variable`/`omit`/`include`/`namespace`/`section` lines.
- Audit of the modules committed on 2026-10-03 for the same issue. Extra directives found:
  `set_option maxHeartbeats 800000 in` (`Analysis/MatrixTrace.lean`) and two `open` lines
  (`Analysis/Majorization.lean`), both harmless. The worker also added `include d` in
  `KLS/LogConcave/Line/DensityBound.lean` (applies to `mem_interior_support_of_measureReal_Ioi`) and
  in `KLS/LogConcave/Line/CheegerVariance.lean` (applies to `measure_Iio_eq_ofReal_cdf`,
  `thickening_Iic_quotient_eq` and `LineDensity.inv_minkowskiConstant_sq_le_three_mul_evariance`).
  These helpers are in the `LineDensity` namespace, and Claude's statements omitted the density
  `d`; without it they are false (two atoms). Their docstrings already describe laws with a
  density, so `include d` repairs Claude's statements rather than changing the intended meaning. The
  paper-level theorems all take `d` (or `LogConcave` plus nonempty interior) explicitly, and the
  lemma-map relations are unchanged.
- Step 2 done: `Analysis/BakryEmery/Curvature.lean` (8 statements by Claude, 4 of them split out
  after failed rounds). `∇∇U ≥ ρ ≥ 0` gives convexity; pointwise `ρ Γ(f) ≤ Γ₂(f)`; for
  `μ = m.tilted (-U)` and compactly supported `C³` functions `f`, `∫ Γ₂(f) dμ = ∫ (ℒf)² dμ` and
  `ρ ∫ Γ(f) dμ ≤ ∫ (ℒf)² dμ`. Proofs by the GPT worker. Claude restored a section variable the
  worker had changed (see above), one docstring, and added three `omit … in` lines for unused
  instances.
- Step 4, abstract part, done: `Analysis/Semigroup/Generated/Curvature.lean` (8 statements by
  Claude). For `T` closed and densely defined with `ρ ‖T y‖² ≤ ‖A y‖²` on `D(A)`:
  `‖T (P_t f)‖² ≤ e^{-2ρt} ‖T f‖²` on `D(T)`, and, for `ρ > 0`,
  `‖f‖² - ‖P_t f‖² ≤ (1 - e^{-2ρt})/ρ · ‖T f‖²`. The Grönwall and derivative steps were split out
  after failed rounds. On `ℝ` the worker needed the `HasDerivAt.fun_mul`/`fun_neg` forms; the `mul`
  and `neg` forms with `simpa`/`convert` hit an instance mismatch. Claude added two missing
  Mathlib imports to the statement file, removed a redundant nested `section` that repeated the
  same variables, and removed a dead `ring`.
- Steps 3–4, heat-semigroup part, done: `KLS/LogConcave/HeatSemigroup/Curvature.lean` (8 statements
  by Claude). It proves:
  - the curvature bound `ρ ‖T̄ y‖² ≤ ‖A y‖²`, first on `C_c^∞` and then on `D(A)` via the operator
    core;
  - centering identities in `D(T̄)`;
  - the finite-time bound `Var(u) - Var(P_t u) ≤ (1 - e^{-2ρt})/ρ · ‖T̄ u‖²`;
  - `gap ⇒ C_P ≤ C`;
  - `literatureConstant_le_inv_of_tendsto`: with `∇∇U ≥ ρ > 0` **and the ergodicity hypothesis**
    `Var(P_t u) → 0`, `C_P(ν) ≤ 1/ρ`.

  Proofs by the GPT worker. Claude patched three mechanical errors in otherwise correct candidates
  (a `3 ≤ ∞` cast, an unqualified lemma name, a `const_smul` rewrite) and spliced one correct proof
  that the driver had mangled while splicing a fragment. The driver now compares directives as
  multisets and strips headers from returned fragments. The BGL map marks Proposition 4.8.1 and
  Corollary 4.8.2 partial (◐).
- Remaining for Corollary 4.8.2 itself: ergodicity in this model, i.e. `T̄ h = 0` implies `h`
  constant (equivalently `Var(P_t u) → 0`). Proposed route: a Poincaré inequality on cubes from the
  proved one-dimensional log-concave bound and finite tensorization, then local constancy of `h`
  on every cube (the density of `ν` is bounded below on compact sets).
- 2026-10-03/04 (two eight-hour windows, uncommitted): ergodicity is proved in the model and the
  corollary follows. The abstract step `P_t g → 0` for `g ⊥ ker T` is in
  `Generated/Convergence.lean`. The kernel route was taken instead of cube Poincaré:
  - zero weak gradient ⇒ a.e. constant, by differentiating translates under the integral and a
    Fubini argument (`Energy/Euclidean/ZeroGradient.lean`);
  - the weak gradient of `D(T̄)` and `T̄ h = 0 ⇒ h = mean` (`WeightedGradient/Kernel.lean`);
  - `ker T̄` = constants, `Var(P_t u) → 0`, `Var(u) ≤ ρ⁻¹‖T̄u‖²` on `D(T̄)`, and `C_P ≤ 1/ρ` without
    `herg`, in `HeatSemigroup/Curvature.lean`;
  - the `volume.tilted (-W)` form, with log-concavity and full support from `Density/Tilted.lean`.
  Statements by Claude, proofs by the GPT worker, with logged mechanical patches. Records:
  [window 1](../handoffs/2026-10-03-eight-hour-bgl-ergodicity.md),
  [window 2](../handoffs/2026-10-03-renewed-eight-hour-bgl-ergodicity.md),
  [certificate candidate](2026-10-04-bgl-corollary-4-8-2-candidate.md) (not registered).
