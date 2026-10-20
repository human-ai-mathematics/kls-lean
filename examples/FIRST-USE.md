# Call KLS from a separate Lake project

This walkthrough builds [KlsApplications.lean](KlsApplications.lean) as a client in a new
directory outside the repository. It uses a local path dependency so it can exercise changes
before they are committed. The library and its existing compiled modules stay in the original
checkout; pinned third-party compiled caches remain trusted. This is an integration check,
not pristine-Git acceptance or a new mathematical certificate.

Install Git and Elan first. From the KLS repository root, create the client directory:

```bash
kls_repo="$(pwd -P)"
kls_client="$(mktemp -d "${TMPDIR:-/tmp}/kls-first-use.XXXXXX")"
cp "$kls_repo/formalization/lean-toolchain" "$kls_client/lean-toolchain"
cp "$kls_repo/examples/KlsApplications.lean" "$kls_client/KlsApplications.lean"
cd "$kls_client"
```

In that directory, create `lakefile.toml` with the following content. Replace the absolute
`path` with the path to your checkout's `formalization/` directory; the repository root is not
the Lake package root.

```toml
name = "kls-first-use"
version = "0.1.0"
defaultTargets = ["KlsApplications"]

[[require]]
name = "functional-inequalities"
path = "/absolute/path/to/KLS/formalization"

[[lean_lib]]
name = "KlsApplications"
```

Fetch the pinned dependencies and prepare Mathlib before building. Commands below run in the
new client directory. Its first `lake update` still fetches transitive Git dependencies even
though the primary dependency is a local path. Preseed the current Mathlib tag with a shallow
clone to avoid fetching its full Git history; Lake still checks out the revision recorded in
the library's manifest. The current `v4.33.0` tag resolves to
`db584cd6d46c92f209a44c0f1c829460d327499d`. Use the matching tag if the library pin changes.
The environment variable suppresses Mathlib's automatic update-time cache request so the
explicit cache command has a visible scope.

```bash
cd "$kls_client"
mkdir -p .lake/packages
git clone --depth 1 --branch v4.33.0 \
  https://github.com/leanprover-community/mathlib4.git .lake/packages/mathlib
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib
lake build KlsApplications
lake env lean -DwarningAsError=true KlsApplications.lean
```

The pinned library includes aggregate `Mathlib` imports. Preparing only the direct imports
visible in the small client can therefore miss the library's closure and cause a long Mathlib
source build. Preserve `lake-manifest.json` to retain the resolved dependency revisions.
For a committed Git dependency, use the `git`, `rev` and `subDir` configuration in the
[examples guide](README.md#connect-a-separate-lake-project), selecting the revision you intend
to consume. The new local example itself is available only after its containing revision is
committed; copying it into this client does not make it part of an earlier Git revision.

## Read and adapt the client

| Entry | What to supply | Result |
| --- | --- | --- |
| `covariance_bound` | A dimension and a log-concave probability law | A smooth-test bound proportional to the covariance operator norm |
| `variance_bound` | Additionally a smooth L² function and integrability of its squared gradient | The real variance inequality |
| `isotropic_bound` | Additionally isotropy | The universal bound without a covariance factor |
| `gaussian_convolution_bound` | Additionally a nonnegative variance `t` | The bound `C + t` after adding `sqrt(t) G` |

Read the `∃ C, ∀ n μ, …` quantifier order literally: select the same universal constant for
every dimension and law. The example does not extract a numerical value for it. Gaussian
variance is `t`, while the scaling applied to a standard Gaussian is `sqrt(t)`; zero is allowed.

`KLS.kls` bounds an `ENNReal` intrinsic local-slope constant. For a real variance inequality,
follow the example's proved comparison to `Poincare.SmoothTest.Holds` and retain the test's
L² and energy hypotheses. `NNReal` holds finite nonnegative constants; `ENNReal` can be infinite.
Keep the ambient/intrinsic and energy distinctions in the [library design guide](../LEAN_DESIGN.md).

When Lean cannot infer the measure type in a norm, integral or convolution, write the full
coercion `(μ : Measure (EuclideanSpace ℝ (Fin n)))`. A placeholder `(μ : Measure _)` can leave
the carrier or measurable-space instance unresolved. This explicit annotation is used throughout
the checked client.

Use the [API directory](../formalization/API.md) to find other operations. Search several
keywords, such as `constant convolution`, in any order; expand a result to copy its defining
import and inspect its complete type and source documentation.
