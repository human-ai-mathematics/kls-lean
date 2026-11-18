# Formal Conjectures statement inputs

Validation inputs for the prepared Formal Conjectures contribution that states the locally
Lipschitz KLS proposition of [`../Challenge.lean`](../Challenge.lean). They are not a second proof
library or theorem API of this repository, and nothing here is built by this repository's Lake
packages.

| File | Content |
|---|---|
| [`FC_CONTRIBUTION.patch`](FC_CONTRIBUTION.patch) | Two new files. `FormalConjectures/Randomstrasse/KLS.lean`: the ordinary OpenAI density and isotropy definitions in namespace `KannanLovaszSimonovits`, the locally Lipschitz `L²` test class with extended gradient energy, the main statement `kannan_lovasz_simonovits` (a deliberate `sorry` statement placeholder) and five short sanity tests: the zero test, an absolute coordinate (nonsmooth, not compactly supported), infinite energy, and the variance of zero and of a coordinate. `FormalConjectures/Randomstrasse/README.md`: the collection index, linking [Randomstrasse 101](https://randomstrasse101.math.ethz.ch/) and listing Problem 30 as solved. |
| [`StatementCorrespondence.lean.in`](StatementCorrespondence.lean.in) | Correspondence client: the exact `OAI` definition block and the `KLSOpenAI` block of `Challenge.lean` (carrier-completeness theorem and the two locally Lipschitz definitions), a check that the type of `kannan_lovasz_simonovits` is definitionally the proposition `Statement`, and `palomar_iff_fc : KLSOpenAI.LocallyLipschitzStatement ↔ Statement`. The `.lean.in` extension keeps it out of this repository's Lean sources. |
| [`check_statement_correspondence.py`](check_statement_correspondence.py) | Local reproduction command for an external checkout. Requires only the Python standard library. |

## Reproduce

1. Check out `google-deepmind/formal-conjectures` at
   `b6939a3a0d89e5f999fa8c6483a6ef646c1e2923` (toolchain `leanprover/lean4:v4.33.1`) and fetch its
   Mathlib cache.
2. From that checkout, apply [`FC_CONTRIBUTION.patch`](FC_CONTRIBUTION.patch) with `git apply`.
3. Strictly build the module with `lake --wfail build FormalConjectures.Randomstrasse.KLS`.
4. From this repository, run
   `python3 integrations/palomar/formal-conjectures/check_statement_correspondence.py <checkout>`.
   Both definition blocks from `Challenge.lean` must occur byte for byte exactly once in
   `StatementCorrespondence.lean.in`. The command then elaborates those client bytes from a
   temporary file with `lake env lean -DwarningAsError=true`. It checks that
   `palomar_iff_fc` depends only on `propext`, `Classical.choice` and `Quot.sound`.

A checkout of the published head `9bb8202ff1cd8c97d1c28619e56a8b643ae96de5`, built as in step 3,
is accepted in place of steps 1 and 2. The command checks the toolchain file, `HEAD`,
and the two contribution files against the patch with strict whitespace matching. It
uses `lake --wfail build --no-build` to check build freshness and reports the step 3
command if this check fails. It reads the checkout and its Git index, and writes the
client to a temporary directory. Lake manages its ignored `.lake` directory.

Step 4 proves equivalence between the Formal Conjectures proposition and the copied
Palomar definitions under Lean v4.33.1. The equivalence proof uses the proposition's type.
The cross-version link to the Lean v4.35.0 Palomar entry is that `Challenge.lean` contains the
same definition blocks byte for byte, which Palomar's Comparator then checks against
`Solution.lean`.
[Registered Palomar version 2](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-01-000014&version=2)
includes `KLSOpenAI.kls_locallyLipschitz` at source commit
`e60bc39b18ef691263c66e2dba8d64726f18060d`, so it supplies the matching proof record for the
Formal Conjectures `formal_proof` annotation. Version 1 covers only the smooth compactly
supported `KLSOpenAI.kls` and is not the proof link for the extended statement.
The contribution is published in [PR #7712](https://github.com/google-deepmind/formal-conjectures/pull/7712)
at `9bb8202ff1cd8c97d1c28619e56a8b643ae96de5`; its title and description use the extended test class.
The main theorem carries `formal_proof using lean4` pointing to version 2. A maintainer closed
the pull request on 2026-11-11 because a solved statement outside a problem collection is out of
scope, and reopened it on 2026-11-15 for the
[Randomstrasse 101](https://randomstrasse101.math.ethz.ch/) collection, where KLS is
[Problem 30](https://randomstrasse101.math.ethz.ch/posts/KLSConjecture/). That commit moves the
module from `FormalConjectures/Arxiv/2610.05474/KLS.lean` to the new `FormalConjectures/Randomstrasse`
directory and adds the directory README; only the module docstring changed from
`a8117f89a12bda93fa89abb8aba00a5817ffe9e6`, and the definitions, theorem statements and sanity
tests are identical. The local strict changed-module build and the statement-correspondence check
passed at that commit on Lean v4.33.1. On 2026-11-17, the upstream PR was open and still required
review. The CLA check passed. The [Lean build](https://github.com/google-deepmind/formal-conjectures/actions/runs/43829235068)
and [copyright check](https://github.com/google-deepmind/formal-conjectures/actions/runs/43829235105)
were awaiting maintainer approval to run. The [Palomar submission guide](../README.md) records
the registration and verification evidence.
