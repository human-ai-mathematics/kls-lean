# Palomar entry: dimension-free KLS bound

This contained Lake project is the Palomar submission surface for one registry entry:

| File | Role |
|---|---|
| [`Challenge.lean`](Challenge.lean) | Trusted statement. Imports only Mathlib. Inlines the pinned OpenAI ordinary definitions (`OAI.LeanBlast.KLS.*`) and the locally Lipschitz definitions `KLSOpenAI.LocallyLipschitzBound` and `KLSOpenAI.LocallyLipschitzStatement`, then states `KLSOpenAI.kls : OAI.LeanBlast.KLS.KLSStatement` and `KLSOpenAI.kls_locallyLipschitz : KLSOpenAI.LocallyLipschitzStatement`, each with a deliberate `sorry`. |
| [`Solution.lean`](Solution.lean) | Imports the OpenAI model and `KLSOpenAI.Target`; declares nothing. |
| [`comparator.json`](comparator.json) | Compares both `KLSOpenAI.kls` and `KLSOpenAI.kls_locallyLipschitz`; no `definition_names` holes, so every ordinary definition in the statements is compared by body. Axioms: `propext`, `Quot.sound`, `Classical.choice`. |
| [`formalization.yaml`](formalization.yaml) | Palomar v0.4 metadata for this entry. |
| [`STATEMENT-CORRESPONDENCE.md`](STATEMENT-CORRESPONDENCE.md) | Row-by-row correspondence with the pinned OpenAI model and the Formal Conjectures statement. |
| [`lakefile.toml`](lakefile.toml), [`lake-manifest.json`](lake-manifest.json), [`lean-toolchain`](lean-toolchain) | Lean `v4.35.0`, Mathlib `v4.35.0` (`56a005855ea17e0b0958f73ec801ae140b0a1679`) with its exact pinned closure, and the repository's `formalization` and `integrations/openai` packages as path dependencies. |

## What is claimed

Both statements choose one positive real constant `C` before the dimension `n ≥ 1` and the
measurable probability density on `ℝⁿ`, which is log-concave on its positive support and whose
law is isotropic (integrable coordinates and products, zero mean, Kronecker second moments).

- `KLSOpenAI.kls`, the pinned OpenAI form: `Var(f) ≤ C · ∫ ‖∇f‖²` for every `C^∞` compactly
  supported real test `f`.
- `KLSOpenAI.kls_locallyLipschitz` (proposed for a new version, not registered), a
  density-coordinate formulation of Bizeul–Klartag–Lehec arXiv:2610.05474v1 Theorem 1.1: for
  every locally Lipschitz `f` in `L²`,
  `ENNReal.ofReal Var(f) ≤ ENNReal.ofReal C · ∫⁻ ‖∇f‖²`. The variance is the ordinary centered
  square integral; the energy is an extended nonnegative integral and may be infinite, so no
  finite-energy premise is imposed.

Not claimed: the original convex-body isoperimetric formulation, dimension zero in this density
form, a numerical value of `C`, or the paper's uncut Eldan construction. The library theorem
`FunctionalInequalities.KLS.kls` is a stronger covariance-normalized statement;
`KLSOpenAI.of_conjecture` and `KLSOpenAI.locallyLipschitz_of_conjecture` convert it to these forms.

Registered version 1 (`PALOMAR-2026-11-01-000014`) covers only `KLSOpenAI.kls`. The locally
Lipschitz endpoint is local work prepared for a new version; it is not registered.

## Review boundaries

- **Statement (human-auditable):** `Challenge.lean` only. Its `OAI` definitions are the OpenAI
  model at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, unchanged except for the module header,
  `public import Mathlib` and `@[expose] public section`; see `../openai/UPSTREAM.json`. The two
  `KLSOpenAI` definitions are new project code that add the locally Lipschitz statement on top
  of that model; they are not OpenAI material.
- **Proof (for machine checking):** everything imported by `Solution.lean`: the bridge in
  `../openai/KLSOpenAI`, the library in `../../formalization`, and the vendored
  stochastic-calculus libraries with their recorded local adaptations.
- **AI involvement:** substantial throughout the proof development and in preparing this
  project; see `formalization.yaml` and the repository's root `formalization.yaml`.
- **Human review:** as stated in `formalization.yaml`; not independent peer review.

## Checking

Prepare the pinned caches with `python3 research/cache_mathlib.py --project all`. In this
directory, `lake build Challenge Solution` builds both modules; the Challenge reports its two
deliberate `sorry` placeholders. From the repository root,
`python3 research/comparator.py --target palomar --mode compile` strictly builds the Solution
and its axiom client and reports `COMPILED_CLIENT_ONLY`; it does not judge the
Challenge/Solution comparison. `--mode development` runs the actual bundled judge with NanoDa
on macOS, without the sandbox. Linux `--mode sandbox`, official preflight and registry
acceptance are separate evidence. The complete library acceptance
command is `python3 research/verify.py`; all receipts bind their own exact source inputs.


The repository workflow `.github/workflows/palomar-preflight.yml` runs Palomar's official
reusable verifier (`PalomarRegistry/PalomarSubmission` at
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`) on manual dispatch only. Its result is advisory and
is neither a submission nor a registration. Submission uses
<https://submit.palomar-registry.org/> with the repository, an immutable commit and the path
`integrations/palomar/comparator.json`.
