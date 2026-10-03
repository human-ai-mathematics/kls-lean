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
