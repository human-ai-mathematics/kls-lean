# KLS bridge to the OpenAI statement

This separate Lean project derives the exact OpenAI
`OAI.LeanBlast.KLS.KLSStatement`, and its extension to the locally Lipschitz `L²` test
class of Bizeul–Klartag–Lehec Theorem 1.1, from the existing covariance-normalized
`FunctionalInequalities.KLS.Conjecture`. It is an independent Lake project within
the same repository, using `../../formalization` as a relative path dependency
with Lean 4.35.0. Checking out a Git revision fixes both the bridge and its KLS source.

- [OAI/Analysis/KLS/Model.lean](OAI/Analysis/KLS/Model.lean) is the file from
  [openai/math at adc7f124](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/KLS/Model.lean)
  with only the Lean module-system header adaptation: a leading `module` line,
  `public import Mathlib` instead of `import Mathlib`, and `@[expose] public section`
  before `namespace OAI`. The original namespace, definitions, hypotheses and test
  functions are otherwise byte-for-byte unchanged. This file comes from OpenAI's
  Apache-2.0 repository; see [LICENSE](LICENSE). [UPSTREAM.json](UPSTREAM.json) records
  the source pin, the original file's SHA-256, the exact transformation and the local SHA-256.
- [KLSOpenAI/Bridge.lean](KLSOpenAI/Bridge.lean) proves `KLSOpenAI.of_conjecture`
  without importing the KLS proof. Measurable log-concave densities are converted
  directly using Prékopa–Leindler; upper semicontinuity is not assumed. Coordinate
  moments give vector isotropy, and `smoothTest_holds_of_localSlope_le_covariance`, shared
  with the locally Lipschitz bridge, turns a covariance-normalized constant into a smooth
  compactly supported Poincaré constant in every dimension. Those tests have the required
  integrability. A nonnegative universal constant `C` becomes `C + 1`.
- [KLSOpenAI/LocallyLipschitz.lean](KLSOpenAI/LocallyLipschitz.lean) is new project code,
  not part of the OpenAI model. It defines `LocallyLipschitzStatement`, a density-coordinate
  formulation of arXiv:2610.05474v1, Theorem 1.1, on the unchanged OpenAI density and isotropy
  definitions: one positive constant before every dimension `n ≥ 1`
  and density, and every locally Lipschitz `f` in `L²` satisfies
  `ENNReal.ofReal (variance μ f) ≤ ENNReal.ofReal C * ∫⁻ ‖∇f‖²`. The energy is an extended
  nonnegative integral and may be infinite; no finite-energy or extra density premise is
  imposed. The theorem `completeSpace_space` (not an instance) gives the completeness argument
  of `gradient` a stable named term, so the definition elaborates identically in the Palomar
  challenge. `locallyLipschitz_of_conjecture` derives the statement without importing the KLS proof:
  for absolutely continuous laws the library equates smooth-test and local-slope Poincaré
  bounds, and identifies the local-slope energy of a locally Lipschitz function with
  its squared-gradient `lintegral`.
- [KLSOpenAI/Target.lean](KLSOpenAI/Target.lean) proves `KLSOpenAI.kls` and
  `KLSOpenAI.kls_locallyLipschitz` by applying these bridges to the KLS library's
  existing theorem.
- [Check.lean](Check.lean) consumes the original endpoint as ordinary variance and
  gradient integrals, and the locally Lipschitz endpoint as an extended-real inequality
  with the `lintegral` energy, each with one positive constant for every dimension `n ≥ 1`.

The closed endpoints use the KLS library's Bizeul–Klartag–Lehec proof. This bridge
adds no numerical constant and does not change the KLS library, its proof scope,
or its certificate statuses. It is separate from the ongoing Mathlib contribution
preparation. [formalization.yaml](formalization.yaml) separately credits the substantive
proof and the upstream statement. [Comparator inputs](research/comparator/config.json)
compare the original `KLSOpenAI.kls` and conditional `KLSOpenAI.of_conjecture` against a
challenge importing the upstream model and the KLS proposition, with no proof import.
The locally Lipschitz endpoint is compared by the
[Palomar configuration](../palomar/comparator.json), together with `KLSOpenAI.kls`.
Both endpoints are registered in
[Palomar version 2](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-01-000014&version=2)
at `e60bc39b18ef691263c66e2dba8d64726f18060d`. See the
[Palomar submission guide](../palomar/README.md) for their scope and verification evidence.

From the repository root, first prepare and build the substantive KLS library:

```sh
python3 research/cache_mathlib.py --project all
lake -d formalization build
```

Then build and check this package:

```sh
cd integrations/openai
lake build
lake build Check
lake env lean -DwarningAsError=true Check.lean
lake env lean -DwarningAsError=true research/audits/ImportBoundary.lean
lake env lean -DwarningAsError=true research/audits/Declarations.lean
```

The cache command prepares and checks both Lake packages' Mathlib caches. The bridge
may have its own dependency checkout, so preparing only `formalization/` does not
ensure its cache is populated. Use `--project openai` for just the bridge, or
`--project all --check` to inspect both without fetching.

The committed manifest retains the root library's exact third-party pins. Local
development may reuse their compiled caches; its receipts record that trust scope.
The package is checked separately from the root library's default build and full
verifier. The two audit clients check that neither conditional bridge imports a closed
KLS endpoint, and audit all declarations, including private and generated ones, in the
model, both bridges, target and ordinary-integral client. Raw
attempts and receipts stay in ignored `build/` directories. The upstream model is
independently checkable against the source pin and SHA-256 in `UPSTREAM.json`: reversing the
recorded module-header transformation reproduces the original upstream bytes, and the
Comparator runner checks both the original and the local hash.

After building as above (see [the runner guide](../../research/audits/KLS/Comparator/README.md)),
run from the repository root:

```sh
python3 research/comparator.py --target openai --mode development
```

This runs the Lean v4.35.0 toolchain-bundled `lake comparator` without its sandbox
(`--inadvisably-no-sandbox`), including exported-statement comparison, standard-axiom checks
and Lean kernel replay. Linux with bubblewrap (`bwrap`) is required for `--mode sandbox`. The
modes and their receipt statuses are distinct; this configuration enables no external proof
kernel. Logs and source-bound receipts stay under the repository's ignored `build/comparator/`
directory.

The substantive library's initial roadmap was organized by Nicolas (nbrosse), and
its early foundational work and proof development followed that roadmap. ChatGPT
helped organize literature and proof approaches. The root
[formalization metadata](../../formalization.yaml) records substantial AI involvement,
the maintainer's review of key statements and the separate Claude/GPT review passes.
The [current review checklist](../../research/progress/public-interface-review.md) records
the maintainer's 2026-10-26 report of personally reviewing the OpenAI statement and
bridge conversion proof. Upstream stochastic-analysis interfaces remain outside
that reported personal review, as do the locally Lipschitz definitions and bridge added on
2026-11-02, which have had agent-assisted Claude, GPT and Codex review only. The later
2026-11-02 style revision, comprising the shared smooth-bound conversion, the reorganized
`of_conjecture` proof and `completeSpace_space`, likewise has agent-assisted review only and is
not covered by the 2026-10-26 personal review.
The bridge imports the substantive proof; its OpenAI model (header-adapted only) retains its
original authorship and license.
