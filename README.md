# kls-lean

Lean formalization of functional inequalities and the published literature around the
Kannan–Lovász–Simonovits (KLS) conjecture. Work is selected by source paper and target theorem.
Lean and Mathlib are pinned to **v4.33.0**. Public interfaces may still change; see the
[lifecycle](research/ledger-schema.md#lifecycle) and the [naming guide](research/naming.md).

## Statement

`KLS.Conjecture` asks for one finite constant `C` such that `C_P^lit(μ) ≤ C ‖Cov_μ‖_op` for every
log-concave probability law `μ` with finite second moment on every finite-dimensional Euclidean
space, where `C_P^lit` is the intrinsic local-slope Poincaré constant. See the
[statement](formalization/FunctionalInequalities/KLS/Statement.lean) and the
[open target](formalization/FunctionalInequalities/KLS/Target.lean): `KLS.kls` is the library's
one intentional `sorry` and lies outside every certificate import closure.
**Dimension-free KLS remains open.**

## What is proved

There are **30 registered Lean certificates**, plus proved auxiliary results. Highlights:

- the one-dimensional upper bound `C_P^lit ≤ 4 Var` for log-concave laws on the line;
- finite Poincaré tensorization and the sharp one-dimensional Gaussian constant;
- scalar and vector weighted coarea (C¹, Lipschitz, locally Lipschitz) and sharp scalar Sard;
- canonical energy `E^can = 2 Ch` for every Borel probability law; the weighted-gradient heat
  semigroup with its Markov and positive-time smoothing properties; the Bakry–Émery `Γ`/`Γ₂`
  calculus with `Γ₂ ≥ 0` for smooth convex potentials; ergodicity of the heat semigroup
  (`ker T̄` = constants);
- the Bakry–Émery bound `C_P ≤ 1/ρ` for `e^{-W} dx` with `W ∈ C²`, `∇∇W ≥ ρ > 0`
  (Bakry–Gentil–Ledoux Corollary 4.8.2, in a reviewed stronger form) is certified as a paper
  target;
- both numerical Cheeger–Buser comparisons `C_P^lit ≤ 4 Ψ²` and `Ψ² ≤ π C_P^lit` for every
  finite-dimensional log-concave law, including degenerate affine supports;
- metric BV relaxation and Minkowski recovery; Ambrosio–Di Marino–Gigli Theorem 3.6 (relaxed
  Minkowski content equals the Definition 3.3 perimeter, for measures finite on bounded sets) is
  certified as a paper target.
- Bizeul–Klartag–Lehec (arXiv:2610.05474v1) **Theorem 3.1** (the Taylor-coefficient criterion:
  `C_P(μ) ≤ K R²` for centered regular log-concave `μ` with `Cov μ ≤ Id` and `|T_d f| ≤ R^d ‖f‖₂`) is
  certified in the source form (`thm:bkl-taylor-criterion`), proved through the operator domain of
  the generator with an approximate first eigenfunction; Lemma 2.2 and the Section 3 lemmas
  (Lemmas 3.2–3.4, 3.6, 3.8, 3.9, Corollaries 3.5, 3.7) are formalized for these iterates. The
  paper's main Theorem 1.1 is **not** proved: Theorem 4.1 (Eldan localization) and the Letwin bound it
  uses remain open. The deterministic grouping of the drift expansion (74), `2m κ_m + 2 L_m` with `L_m` from (72), and the
  covariance step `Cov(|M|^{1/2} X) = |M|` of the proof of Letwin's Theorem 1.2 are formalized; the stochastic Lemma 4.3
  and Letwin's Theorem 1.2 are not. Letwin's Lemma A.4 is formalized for every potential in
  its source class (the moment-map properties are hypotheses; cutoffs for every real `R ≥ 1` with `‖Lχ_R‖_{L¹(ν)} ≤ C/R`),
  Lemma A.5 for given cutoffs, and both are applied to the uniform law on `(−√3, √3)` with the nonconstant test
  function `tanh²(√3y/2)`; the moment map itself and Letwin's Theorem 2.5 are not. The Section 2 regular approximation is complete in conditional form: Gaussian
  smoothing produces regular potentials (`δ ≤ ∇² ≤ 2s + δ`, polynomial growth of all derivatives through
  the Gaussian posterior and quantitative Borell moments), the two-step laws converge to the law with
  their means, second moments and covariances, regular laws center and whiten to isotropic regular
  laws, a Poincaré bound for isotropic regular laws transfers through the covariance norm, and the
  weak-limit passage gives: a bound for isotropic regular laws on `ℝⁿ` implies the bound for every
  isotropic log-concave law. Combined with the p. 30 reduction, Theorem 1.1 is formalized
  **conditionally on Theorem 4.1**: under its universal cumulant bounds, every isotropic log-concave
  law in every finite dimension has `C_P ≤ 2·C_{3.1}·K` and the KLS conjecture follows
  (`KLS.conjecture_of_cumulantBound`). This carries no certificate; `KLS.kls` stays open. Letwin's
  Stein-kernel supports (Definition 2.6, A.7, Lemma 2.9, the mean-Hessian identity of Lemma 2.3 for a
  given potential) are formalized; the Gaussian has the identity kernel, while the moment-map kernel of
  an arbitrary law and Letwin's Theorems 1.1–1.2 remain open.
- Bizeul–Klartag–Lehec **Proposition 7.1** (suspension: a `(d+1)`-cumulant bound `CumulantBound d b` for
  all isotropic log-concave laws implies `‖T_d f‖²_HS ≤ 2 b (d!)⁻² ‖f‖₂²` for every centered
  isotropic regular log-concave `μ` on `ℝⁿ` and every `f ∈ L²(μ)`, all dimensions) is certified in the source form
  (`prop:bkl-suspension`): the joint law of the Laplace-noise suspension, its density (109),
  log-concavity (110), isotropy, the mixed-cumulant identities (111)–(112), the Hilbert–Schmidt
  step, the `β → ∞` limit and the affine-orthogonal decomposition are formalized. Theorem 4.1 is
  stated conditionally (cumulant envelope) and remains open.
- Cordero-Erausquin–Klartag (*Moment measures*): **Proposition 12** (a convex lower semicontinuous potential with
  Legendre mass one maximizes the variational functional over every admissible competitor, for centered full-span
  probability measures with finite first moment), **Lemma 16** for finite measures and **Lemma 17** with the
  interior-hull condition as an explicit hypothesis. Lemma 15's constant, essential continuity and Theorem 2
  (existence and uniqueness of moment potentials) remain open.

## What is not proved

- Any published high-dimensional KLS bound (KLS 1995, Eldan, Lee–Vempala, Chen, Klartag–Lehec,
  Klartag, Letwin) or the stochastic-localization machinery they use, including the October 2026
  preprints claiming the dimension-free bound (Bizeul–Klartag–Lehec, Song–Zhang).
- Any complete paper other than Ambrosio–Di Marino–Gigli (Theorem 3.6) and Bakry–Gentil–Ledoux
  (Corollary 4.8.2 only; the book's general Markov-triple framework is not formalized).
  A paper is covered only when its main theorem is stated faithfully in Lean, proved without
  nonstandard axioms, and certified for that exact statement. Supporting lemmas, restricted cases
  and conditional reductions do not count.
- General RCD comparisons, nonproper locally Lipschitz BV variants and nonconvex support transfer.

## Where to look

| Entry | Contents |
| --- | --- |
| [Literature register](research/progress/LITERATURE.md) | **Primary progress view**: paper versions, target theorems, Lean statements, status, certificates |
| [Progress hub](research/progress/README.md) | Literature priorities, literature map, exploratory route diagrams |
| [Node register](research/progress/STATUS.md) | Blueprint statements, provenance and certificate mappings |
| [Current handoff](HANDOFF.md) | Verified baseline, current scope and next step |
| [Formalization guide](formalization/README.md) · [Blueprint](formalization/blueprint/README.md) | Library layout, builds, theorem map |
| [Ledger](research/a-series/ledger.yaml) · [Certificates](solutions/README.md) | Certified nodes and their Lean entry points |
| [Workflow](research/workflow.md) · [Verification](research/verification.md) | Task selection, module placement, verification and CI rules |
| [Decision records](research/decisions/) | Dated history, including earlier handoffs |

## Verify

From the repository root:

```bash
(cd formalization && lake build)
python3 research/check_ledger.py
python3 research/verify.py
python3 research/progress/update.py --check
```

`research/verify.py` is the full local verifier: build, strict audit clients, transitive axiom
audit of every local declaration except `KLS.kls`, kernel replay, statement baselines and
metadata checks. Remote CI runs its Lean-only scope (`--lean-only`) on manual dispatch
(`gh workflow run lean.yml`) or a pushed `milestone/**` tag; ordinary pushes do not trigger it.
[Run 37516844384](https://github.com/human-ai-mathematics/kls-lean/actions/runs/37516844384)
passed for commit `36e7c78`; it does not certify later commits or prove KLS.
