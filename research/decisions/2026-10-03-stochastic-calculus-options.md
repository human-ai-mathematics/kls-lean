# Stochastic calculus for the priority-4 papers: options

Date: 2026-10-03. Status: evidence prepared overnight for an owner decision; **nothing is adopted**.
Sources were cloned into a scratch directory and inspected; none was built against this repository.
The pins were re-checked: StochLean `e6741e1` uses `leanprover/lean4:v4.33.0` and Mathlib `db584cd`
(identical to ours), contains Itô-formula modules under
`StochLean/Probability/Process/Semimartingale/Ito/` and no `sorry`. The Eldan 2013 and Chen 2021 lemma
maps (`research/progress/LITERATURE.md`) list the stochastic ingredients each proof uses.

---
Our pin: Lean `v4.33.0`, Mathlib `db584cd` (tag v4.33.0, 2026-08-10). The repo has no stochastic code. Everything below comes from shallow clones and the GitHub API; nothing external was built locally.

## 1. Sources

| Source @ SHA (date) | Toolchain / Mathlib | Provides | Missing |
|---|---|---|---|
| **Mathlib** `db584cd` | ours | `Probability/BrownianMotion/Basic.lean`: predicates `IsPreBrownianReal` and `IsBrownianReal` (real-valued). `Process/{Stopping,Predictable,LocalProperty,Kolmogorov}.lean`: stopping times, predictable σ-algebra, localizing sequences, the Kolmogorov *condition*. Discrete-time martingale theorems. | No proof that BM exists, no ℝⁿ BM, no stochastic integral, QV, Itô formula or SDE |
| **RemyDegenne/brownian-motion** `0d5b6eb` (09-22), 62★ | `v4.33.0-rc1` / `0434c03` (07-24, **242 behind**) | Real BM constructed (Kolmogorov extension and Kolmogorov–Chentsov); simple integral; Doob–Meyer; local martingales. 29k lines, 25 `sorry`s | Stochastic integral only *specified* (`IsStochasticIntegral`); Itô formula not started; no ℝⁿ, no SDE |
| **formal-applied-math/formal-mathfin** `f085fd5` (10-02), 37★ | `v4.33.0-rc1` / `0434c03` | 1-D L² Itô integral on [0,T]; Itô formula for f(t,B_t) with f in C³; scalar Lipschitz SDE, only when T·L_b+√T·L_σ<1 | No ℝⁿ, no general semimartingale Itô formula, no localization |
| **cgarryZA/LevyStochCalc** `984dbf0` (09-30), 1★ | `v4.32.0` / `81a5d25` (07-13, **470 behind**), plus brownian-motion and MathFin | d-dim BM; L² Itô integral; **ℝⁿ SDE, time-dependent globally Lipschitz coefficients, all horizons** (`Ito/PicardWellPosed.lean`); vector Itô formula with bounded f′,f″. 155k lines, 0 `sorry` | No locally Lipschitz coefficients or explosion time; three-repo dependency chain |
| **FredericaBernkastel1/Stochastic-Process-lean-lib ("StochLean")** `e6741e1` (09-17), 0★ | **`v4.33.0` / `db584cd`, identical to ours**; Mathlib only | Protter Ch. I–III, by their ledger: semimartingale integral, brackets, **C² Itô formula on ℝⁿ for càdlàg semimartingales** (`ito_finiteCoordinates_continuous_bracket`), stochastic exponential, multidimensional Lévy characterization, Girsanov/Novikov, continuous-time Doob. 197k lines. CI build passes; audit step fails only on a stale name | **No SDEs.** Single unknown maintainer, about 3 weeks old, likely machine-generated, unreviewed |
| xiyin137/stochasticpde-itocalculus; savarin/lean-stochastic-calculus | Mathlib 6140 behind; 1242 ahead | Scalar Itô formula / Girsanov | Not usable at our pin |

## 2. What Eldan's scheme needs, and who has it

| Need | Mathlib | Degenne | mathfin | LevyStochCalc | StochLean |
|---|---|---|---|---|---|
| ℝⁿ BM | ✗ | 1-D | 1-D | ✓ | ✓ |
| Vector Itô integral | ✗ | spec only | 1-D | ✓ L² | ✓ |
| Localized C² Itô formula on ℝⁿ | ✗ | ✗ | ✗ | bounded derivatives only | ✓ |
| Locally Lipschitz SDE up to a stopping time | ✗ | ✗ | ✗ | global Lipschitz only | ✗ |
| Covariance-process estimates | ✗ | ✗ | ✗ | ✗ | ✗ |

No project provides:
- locally Lipschitz SDEs;
- matrix Itô calculus for A_t and A_t^{-1/2};
- the true-martingale property of F_t(x);
- every estimate specific to KLS.

The target paper decides the scope:
- **Eldan 2013 as stated** has diffusion depending on the state, so it needs all of the above.
- **The Lee–Vempala / Chen variant** (C_t = I) reduces to dc_t = dW_t + a(t,c_t)dt. The diffusion is constant, so the equation can be solved path by path as an ODE (Mathlib's Picard–Lindelöf). The drift is globally Lipschitz for compactly supported laws. It then needs only a vector Itô formula for W+∫b ds, plus the estimates.

## 3. Options

**A. Build here.**
- Port BM existence, then build the vector integral, a localized Itô formula and SDEs. The comparable projects needed 30k–200k lines.
- Estimate: months for Eldan 2013; 3–6 weeks for the C_t = I route if BM is imported.
- Risk: high scope, but no dependency drift.

**B. Depend on an external project.**
- *StochLean*:
  - It needs no Mathlib bump and is the only one with a full Itô formula.
  - It adds about 1.6k modules to every build and CI run.
  - Bus factor 1; its statements are unaudited; its own CI audit is red, though the build passes.
  - Adoption takes days. SDEs still have to be built here.
- *LevyStochCalc*:
  - It has the right SDE layer.
  - It would force a Mathlib downgrade of 470 commits, or a port forward of 155k lines; only piecewise vendoring is realistic.
- *Degenne / mathfin*: 242 behind us, so expect API breakage once Lake compiles them against our pin. They add little beyond 1-D.

**C. Contribute to Degenne's brownian-motion and wait.**
- It is the most credible project and the route into Mathlib.
- But its integral is unconstructed, and it has no ℝⁿ BM and no SDE plans.
- Likely available in Mathlib in 2027 or later. Risk to our timeline: very high.

## 4. Recommendation

A hybrid of B and A, with a decision gate:
1. Fix the target paper first (Eldan 2013 or Lee–Vempala 2024).
2. In a scratch worktree, pin StochLean `e6741e1`. Build it against `db584cd`, and audit the axioms and statement fidelity of the BM, integral and Itô declarations. Adopt it as a dependency only if that audit passes; otherwise vendor the audited modules under Apache-2.0 with attribution.
3. Build the SDE layer here, using LevyStochCalc's Bielecki and gluing proofs as a reference.
4. Upstream generic pieces to Degenne's project opportunistically.

Do not adopt LevyStochCalc or mathfin as dependencies.
