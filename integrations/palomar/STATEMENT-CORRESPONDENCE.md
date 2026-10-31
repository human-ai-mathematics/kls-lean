# Statement correspondence

Correspondence between this Palomar challenge, the pinned OpenAI model and the prepared Formal
Conjectures statement. Two separate kinds of evidence apply:

- **Compiled same-pin statement equivalence (Formal Conjectures toolchain, Lean v4.33.1).** The
  client [`formal-conjectures/StatementCorrespondence.lean.in`](formal-conjectures/StatementCorrespondence.lean.in)
  copies the ordinary definition block of `Challenge.lean` into the Formal Conjectures checkout at
  `b6939a3a` with [`formal-conjectures/FC_CONTRIBUTION.patch`](formal-conjectures/FC_CONTRIBUTION.patch)
  applied and proves `KLSStatement ↔` the Formal Conjectures proposition; reproduction steps are in
  [`formal-conjectures/README.md`](formal-conjectures/README.md). This is a statement check, not a
  proof of KLS.
- **Lean v4.35.0 Comparator check of `Challenge.lean` against `Solution.lean`.** Its run receipt
  records the actual judged bytes and mode; the official Palomar full preflight additionally
  needs a public final commit.

| Object | Pinned OpenAI model (`adc7f1241b42e322a6451854ab7e4b4c146bf78a:lean/OAI/Analysis/KLS/Model.lean`) | [`Challenge.lean`](Challenge.lean) | Formal Conjectures candidate (`KannanLovaszSimonovits`, base `b6939a3a`) |
|---|---|---|---|
| Space | `OAI.LeanBlast.KLS.Space n := EuclideanSpace ℝ (Fin n)` | identical | `Space` |
| Density measure | `densityMeasure ρ := volume.withDensity (fun x => ENNReal.ofReal (ρ x))` | identical | `densityMeasure` |
| Log-concave density | `IsLogConcaveDensity`: nonnegative, measurable, probability, `ConcaveOn` of `log ρ` on `{0 < ρ}` | identical | `IsLogConcaveDensity` |
| Isotropy | `IsIsotropic`: coordinate and product integrability, zero mean, Kronecker second moments | identical | `IsIsotropic` |
| Expectation / variance / energy | `expectation`, `variance` (centered square), `dirichletEnergy` (`∫ ‖gradient f‖²`) | identical | same names |
| Test class | `IsTestFunction f := ContDiff ℝ ∞ f ∧ HasCompactSupport f` | identical | `IsTestFunction` |
| Poincaré bound | `PoincareBound μ C := ∀ f, IsTestFunction f → variance μ f ≤ C * dirichletEnergy μ f` | identical | `PoincareBound` |
| Main statement | `KLSStatement := ∃ C : ℝ, 0 < C ∧ ∀ n, 1 ≤ n → ∀ ρ, IsLogConcaveDensity ρ → IsIsotropic (densityMeasure ρ) → PoincareBound (densityMeasure ρ) C` | `theorem KLSOpenAI.kls : OAI.LeanBlast.KLS.KLSStatement` (deliberate `sorry`) | `kannan_lovasz_simonovits` states the unfolded proposition |

The `OAI` block of `Challenge.lean` is byte-identical to the module-adapted model file
`integrations/openai/OAI/Analysis/KLS/Model.lean`, whose only differences from the upstream bytes are the
module header, `public import Mathlib` and `@[expose] public section` (recorded in
`integrations/openai/UPSTREAM.json`). Comparator compares every ordinary definition in the
statement by body: `comparator.json` has no `definition_names`.

Scope: Bizeul–Klartag–Lehec arXiv:2610.05474v1 Theorem 1.1 implies this smooth compactly supported
test formulation. No formal equivalence with their locally Lipschitz `L²` test class is claimed.
The library theorem `FunctionalInequalities.KLS.kls` is a stronger covariance-normalized statement
that implies `KLSStatement` through `KLSOpenAI.of_conjecture`.

The Formal Conjectures `formal_proof` annotation needs a real registered Palomar entry and is not
part of this repository.
