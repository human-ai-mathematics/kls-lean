# Statement correspondence

Correspondence between this Palomar challenge, the pinned OpenAI model and the prepared Formal
Conjectures statement. Two separate kinds of evidence apply:

- **Compiled same-pin statement equivalence (Formal Conjectures toolchain, Lean v4.33.1).** The
  client [`formal-conjectures/StatementCorrespondence.lean.in`](formal-conjectures/StatementCorrespondence.lean.in)
  copies the ordinary `OAI` definition block and the two `KLSOpenAI` locally Lipschitz
  definitions of `Challenge.lean` byte for byte into the Formal Conjectures checkout at `b6939a3a`
  with [`formal-conjectures/FC_CONTRIBUTION.patch`](formal-conjectures/FC_CONTRIBUTION.patch)
  applied. It proves `KLSOpenAI.LocallyLipschitzStatement ↔` the Formal Conjectures proposition
  without using the Formal Conjectures placeholder proof; reproduction steps are in
  [`formal-conjectures/README.md`](formal-conjectures/README.md). This is a statement check, not
  a proof of KLS.
- **Lean v4.35.0 Comparator check of `Challenge.lean` against `Solution.lean`** for both
  `KLSOpenAI.kls` and `KLSOpenAI.kls_locallyLipschitz`. Its run receipt records the actual judged
  bytes and mode; the official Palomar full preflight additionally needs a public final commit.

| Object | Pinned OpenAI model (`adc7f1241b42e322a6451854ab7e4b4c146bf78a:lean/OAI/Analysis/KLS/Model.lean`) | [`Challenge.lean`](Challenge.lean) | Formal Conjectures statement (`KannanLovaszSimonovits`, base `b6939a3a`) |
|---|---|---|---|
| Space | `OAI.LeanBlast.KLS.Space n := EuclideanSpace ℝ (Fin n)` | identical | `Space` |
| Density measure | `densityMeasure ρ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))` | identical | `densityMeasure` |
| Log-concave density | `IsLogConcaveDensity`: nonnegative, measurable, probability, `ConcaveOn` of `log ρ` on `{0 < ρ}` | identical | `IsLogConcaveDensity` |
| Isotropy | `IsIsotropic`: coordinate and product integrability, zero mean, Kronecker second moments | identical | `IsIsotropic` |
| Expectation / variance | `expectation`, `variance` (centered square) | identical | same names |
| Smooth test class and bound | `IsTestFunction f := ContDiff ℝ ∞ f ∧ HasCompactSupport f`; `PoincareBound` with real `dirichletEnergy` | identical | not used |
| Smooth statement | `KLSStatement` | `theorem KLSOpenAI.kls : OAI.LeanBlast.KLS.KLSStatement` (deliberate `sorry`) | not stated |
| Locally Lipschitz test class | — | premises `LocallyLipschitz f` and `MemLp f 2 μ` in `KLSOpenAI.LocallyLipschitzBound` | `IsTestFunction μ f := LocallyLipschitz f ∧ MemLp f 2 μ` |
| Gradient energy | — | `∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂μ`, may be `⊤` | `dirichletEnergy μ f`, the definitionally corresponding `lintegral` after unfolding |
| Locally Lipschitz bound | — | `LocallyLipschitzBound μ C`: `ENNReal.ofReal (variance μ f) ≤ ENNReal.ofReal C * energy` | `PoincareBound μ C`, the corresponding inequality after unfolding |
| Locally Lipschitz statement | — | `LocallyLipschitzStatement := ∃ C : ℝ, 0 < C ∧ ∀ n, 1 ≤ n → ∀ ρ, IsLogConcaveDensity ρ → IsIsotropic (densityMeasure ρ) → LocallyLipschitzBound (densityMeasure ρ) C`; `theorem KLSOpenAI.kls_locallyLipschitz` (deliberate `sorry`) | `kannan_lovasz_simonovits` states the unfolded proposition |

The `OAI` block of `Challenge.lean` is byte-identical to the module-adapted model file
`integrations/openai/OAI/Analysis/KLS/Model.lean`, whose only differences from the upstream bytes are the
module header, `public import Mathlib` and `@[expose] public section` (recorded in
`integrations/openai/UPSTREAM.json`). The two locally Lipschitz definitions have the same bodies
as those in `integrations/openai/KLSOpenAI/LocallyLipschitz.lean`; they are new project code, not
part of the OpenAI model. Comparator compares every
ordinary definition in both statements by body: `comparator.json` has no `definition_names`.

Scope: `KLSOpenAI.kls_locallyLipschitz` is a density-coordinate formulation of
Bizeul–Klartag–Lehec arXiv:2610.05474v1 Theorem 1.1, for isotropic log-concave probability
densities on `ℝⁿ`, `n ≥ 1`, with the paper's locally
Lipschitz `L²` test class. The variance is the ordinary centered square integral, and the
squared-gradient energy is an extended nonnegative integral; infinite energy is allowed rather than
excluded by a premise. `KLSOpenAI.kls` is the unchanged OpenAI smooth compactly supported form.
The library theorem `FunctionalInequalities.KLS.kls` is a stronger covariance-normalized statement
that implies both through `KLSOpenAI.of_conjecture` and `KLSOpenAI.locallyLipschitz_of_conjecture`.

Registered Palomar version 1 (`PALOMAR-2026-11-01-000014`) covers only `KLSOpenAI.kls`. It does
not certify the locally Lipschitz statement, so the Formal Conjectures statement carries no
`formal_proof` annotation until a version that includes `KLSOpenAI.kls_locallyLipschitz` is
registered. The [official full preflight](https://github.com/human-ai-mathematics/kls-lean/actions/runs/41430632501)
passed for both endpoints at `ed8da44bf8637d31bfd352d22a8a59a3a4445bf2`; it does not replace registration.
The locally Lipschitz statement and its five tests are published in [Formal Conjectures PR #7712](https://github.com/google-deepmind/formal-conjectures/pull/7712),
currently at `98067de1693653eec73b644e64a17b35477ede78`.
