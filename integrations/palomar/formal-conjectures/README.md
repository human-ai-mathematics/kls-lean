# Formal Conjectures statement inputs

Validation inputs for the prepared Formal Conjectures contribution that states the same KLS
proposition as [`../Challenge.lean`](../Challenge.lean). They are not a second proof library or
theorem API of this repository, and nothing here is built by this repository's Lake packages.

| File | Content |
|---|---|
| [`FC_CONTRIBUTION.patch`](FC_CONTRIBUTION.patch) | One new file, `FormalConjectures/Arxiv/2610.05474/KLS.lean`: the ordinary OpenAI definitions in namespace `KannanLovaszSimonovits`, the main statement `kannan_lovasz_simonovits` (a deliberate `sorry` statement placeholder) and three sanity tests. |
| [`StatementCorrespondence.lean.in`](StatementCorrespondence.lean.in) | Correspondence client: the exact ordinary definition block of `Challenge.lean` (namespace `OAI.LeanBlast.KLS`), a check that the type of `kannan_lovasz_simonovits` is definitionally the proposition `Statement`, and `palomar_iff_fc : OAI.LeanBlast.KLS.KLSStatement ↔ Statement`. The `.lean.in` extension keeps it out of this repository's Lean sources. |

## Reproduce

1. Check out `google-deepmind/formal-conjectures` at
   `b6939a3a0d89e5f999fa8c6483a6ef646c1e2923` (toolchain `leanprover/lean4:v4.33.1`) and fetch its
   Mathlib cache.
2. Apply the patch: `git apply FC_CONTRIBUTION.patch`.
3. Strictly build the new file:
   `lake --wfail build FormalConjectures.Arxiv.«2610.05474».KLS`.
4. Copy `StatementCorrespondence.lean.in` to a scratch `.lean` file inside that checkout and run
   `lake env lean -DwarningAsError=true <scratch>.lean`.

Scope: step 4 is a same-pin source-copy equivalence check under the Formal Conjectures toolchain
(Lean v4.33.1). It shows that the Formal Conjectures proposition and the copied Palomar ordinary
definitions agree as statements; it does not prove KLS. The cross-version link to the Lean v4.35.0
Palomar entry is that `Challenge.lean` contains the same definition block byte for byte, which
Palomar's Comparator then checks against `Solution.lean`. The Formal Conjectures `formal_proof`
annotation needs a real registered Palomar entry and is not part of this patch.
