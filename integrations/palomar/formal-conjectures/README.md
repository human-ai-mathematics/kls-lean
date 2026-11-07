# Formal Conjectures statement inputs

Validation inputs for the prepared Formal Conjectures contribution that states the locally
Lipschitz KLS proposition of [`../Challenge.lean`](../Challenge.lean). They are not a second proof
library or theorem API of this repository, and nothing here is built by this repository's Lake
packages.

| File | Content |
|---|---|
| [`FC_CONTRIBUTION.patch`](FC_CONTRIBUTION.patch) | One new file, `FormalConjectures/Arxiv/2610.05474/KLS.lean`: the ordinary OpenAI density and isotropy definitions in namespace `KannanLovaszSimonovits`, the locally Lipschitz `L²` test class with extended gradient energy, the main statement `kannan_lovasz_simonovits` (a deliberate `sorry` statement placeholder) and five short sanity tests: the zero test, an absolute coordinate (nonsmooth, not compactly supported), infinite energy, and the variance of zero and of a coordinate. |
| [`StatementCorrespondence.lean.in`](StatementCorrespondence.lean.in) | Correspondence client: the exact `OAI` definition block and the `KLSOpenAI` block of `Challenge.lean` (carrier-completeness theorem and the two locally Lipschitz definitions), a check that the type of `kannan_lovasz_simonovits` is definitionally the proposition `Statement`, and `palomar_iff_fc : KLSOpenAI.LocallyLipschitzStatement ↔ Statement`. The `.lean.in` extension keeps it out of this repository's Lean sources. |

## Reproduce

1. Check out `google-deepmind/formal-conjectures` at
   `b6939a3a0d89e5f999fa8c6483a6ef646c1e2923` (toolchain `leanprover/lean4:v4.33.1`) and fetch its
   Mathlib cache.
2. Apply the patch: `git apply FC_CONTRIBUTION.patch`.
3. Strictly build the new file:
   `lake --wfail build FormalConjectures.Arxiv.«2610.05474».KLS`.
4. Copy `StatementCorrespondence.lean.in` to a scratch `.lean` file and run
   `lake env lean -DwarningAsError=true <scratch>.lean` from that checkout.
5. Check that both copied blocks are byte-identical to `Challenge.lean`: the text from
   `namespace OAI` through `end OAI`, and the text from `namespace KLSOpenAI` up to the docstring
   of `KLSOpenAI.kls`, must each occur exactly once in the scratch file.

Scope: step 4 is a same-pin source-copy equivalence check under the Formal Conjectures toolchain
(Lean v4.33.1). It shows that the Formal Conjectures proposition and the copied Palomar
definitions agree as statements, without citing the placeholder theorem; it does not prove KLS.
The cross-version link to the Lean v4.35.0 Palomar entry is that `Challenge.lean` contains the
same definition blocks byte for byte (step 5), which Palomar's Comparator then checks against
`Solution.lean`.
[Registered Palomar version 2](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-01-000014&version=2)
includes `KLSOpenAI.kls_locallyLipschitz` at source commit
`e60bc39b18ef691263c66e2dba8d64726f18060d`, so it supplies the matching proof record for the
Formal Conjectures `formal_proof` annotation. Version 1 covers only the smooth compactly
supported `KLSOpenAI.kls` and is not the proof link for the extended statement.
The contribution is published in [PR #7712](https://github.com/google-deepmind/formal-conjectures/pull/7712)
at `a8117f89a12bda93fa89abb8aba00a5817ffe9e6`; its title and description use the extended test class.
The main theorem carries `formal_proof using lean4` pointing to version 2. The strict
changed-module build and the statement-correspondence check passed at that commit on Lean
v4.33.1. Upstream review and merge remain pending. The
[Palomar submission guide](../README.md) records the registration and verification evidence.
