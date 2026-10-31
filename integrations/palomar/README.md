# Palomar entry: dimension-free KLS bound

This contained Lake project is the Palomar submission surface for one registry entry:

| File | Role |
|---|---|
| [`Challenge.lean`](Challenge.lean) | Trusted statement. Imports only Mathlib. Inlines the pinned OpenAI ordinary definitions (`OAI.LeanBlast.KLS.*`) and states `KLSOpenAI.kls : OAI.LeanBlast.KLS.KLSStatement` with the single deliberate `sorry`. |
| [`Solution.lean`](Solution.lean) | Imports the OpenAI model and `KLSOpenAI.Target`; declares nothing. |
| [`comparator.json`](comparator.json) | Compares `KLSOpenAI.kls`; no `definition_names` holes, so every ordinary definition in the statement is compared by body. Axioms: `propext`, `Quot.sound`, `Classical.choice`. |
| [`formalization.yaml`](formalization.yaml) | Palomar v0.4 metadata for this entry. |
| [`STATEMENT-CORRESPONDENCE.md`](STATEMENT-CORRESPONDENCE.md) | Row-by-row correspondence with the pinned OpenAI model and the Formal Conjectures statement. |
| [`lakefile.toml`](lakefile.toml), [`lake-manifest.json`](lake-manifest.json), [`lean-toolchain`](lean-toolchain) | Lean `v4.35.0`, Mathlib `v4.35.0` (`56a005855ea17e0b0958f73ec801ae140b0a1679`) with its exact pinned closure, and the repository's `formalization` and `integrations/openai` packages as path dependencies. |

## What is claimed

One positive real constant `C`, chosen before the dimension, such that for every `n ≥ 1`, every
measurable probability density on `ℝⁿ` that is log-concave on its positive support and whose law
is isotropic (integrable coordinates and products, zero mean, Kronecker second moments), and every
`C^∞` compactly supported real test `f`, `Var(f) ≤ C · ∫ ‖∇f‖²`.

Not claimed: the locally Lipschitz `L²` test class of Bizeul–Klartag–Lehec Theorem 1.1, the
original convex-body isoperimetric formulation, a numerical value of `C`, or the paper's uncut
Eldan construction. The library theorem `FunctionalInequalities.KLS.kls` is a stronger
covariance-normalized statement; `KLSOpenAI.of_conjecture` converts it to this form.

## Review boundaries

- **Statement (human-auditable):** `Challenge.lean` only. Its definitions are the OpenAI model
  at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, unchanged except for the module header,
  `public import Mathlib` and `@[expose] public section`; see `../openai/UPSTREAM.json`.
- **Proof (for machine checking):** everything imported by `Solution.lean`: the bridge in
  `../openai/KLSOpenAI`, the library in `../../formalization`, and the vendored
  stochastic-calculus libraries with their recorded local adaptations.
- **AI involvement:** substantial throughout the proof development and in preparing this
  project; see `formalization.yaml` and the repository's root `formalization.yaml`.
- **Human review:** as stated in `formalization.yaml`; not independent peer review.

## Checking

Prepare the pinned caches with `python3 research/cache_mathlib.py --project all`. From the
repository root, run `python3 research/comparator.py --target palomar --mode compile` for
strict statement/solution compilation and `--mode development` for the actual bundled judge
with NanoDa on macOS. Development mode is unsandboxed. Linux `--mode sandbox`, official
preflight and registry acceptance are separate evidence. The complete library acceptance
command is `python3 research/verify.py`; all receipts bind their own exact source inputs.


The repository workflow `.github/workflows/palomar-preflight.yml` runs Palomar's official
reusable verifier (`PalomarRegistry/PalomarSubmission` at
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`) on manual dispatch only. Its result is advisory and
is neither a submission nor a registration. Submission uses
<https://submit.palomar-registry.org/> with the repository, an immutable commit and the path
`integrations/palomar/comparator.json`.
