# Humanize2 Issue 2 Stage 4A Run 1

Date: 2026-09-01

## Run boundary

The valid Run 1 started from local preparation commit
`57dea887045379b9d1f2a1e7a74ff9dd4dd5d4d0` on branch `autoformalization-experiments`. It used
the fresh external root `/private/tmp/humanize2-kls-issue2-stage4a-run1`, whose dedicated
`CODEX_HOME` was authenticated directly through the user's ChatGPT subscription. No global or
earlier-stage credential or transcript was copied.

The runner reset the candidate to the pinned failing sentinel, rebuilt all five accepted `.olean`
dependencies from pinned source with Lean 4.33.0 and upstream Mathlib only, and passed the complete
44-file pin, hidden oracle, exact-workspace, immutable-dependency, compiler-failure, ordered-import,
Borel-surface, physical-isolation, forbidden-read, client-state, Codex app-server, and Humanize2
adapter preflights before the model call.

## Actor result

The `gpt-5.6-sol` actor at `high` effort used one session and one turn with zero descendants. It
read only the eight permitted text files and did not inspect any compiled dependency. It edited
only `CandidateStage4A.lean`.

The first complete implementation compiled with proof errors around the symmetric continuous-map
coercion, bounded real supremum, the Rayleigh numerator representation, and the centered covariance
variance bridge. Seven compiler-feedback repair iterations replaced an unavailable guessed bridge
with an explicit normalization proof, made the `reApplyInnerSelf` coercion explicit, commuted the
Riesz coordinate functional with the Bochner integral, and aligned the scalar covariance
integrand. The eighth exact `lean CandidateStage4A.lean` call exited zero with empty standard
output and standard error. The actor's final response reported eight repair iterations by counting
the initial implementation; the trace-visible sequence is eight compiler calls with seven
post-failure repairs.

Candidate SHA-256:

```text
233e0297d99e52467e4ef7533af76f2310b23400ed720228361d540ffa36a90d
```

The candidate has exactly the ordered two-import surface and eight frozen declarations. It adds
no global finite-dimensional, nontrivial, separability, probability, or stronger moment
assumption and no Stage 4B, eigenvalue, extended covariance, Euclidean, final-assembly, or other
KLS material.

## Independent mechanical verification

The candidate verifier recompiled the candidate silently with all five immutable accepted
dependency pairs and upstream Mathlib only. Its fail-closed source checks accepted exactly the two
ordered imports, exact Borel ambient block, sole `@[simp]` attribute, and eight declaration names.
The independent Lean surface checker accepted all eight exact declaration types. The hidden
eight-declaration `Poincare.lean` surface pin matched.

The complete-session trace audit returned `ok: true` with:

- one actor-root session and one actor turn;
- zero descendants or collaboration/reviewer activity;
- nineteen local `exec` tool calls and no other tool class;
- exactly thirteen actor-visible files;
- only `CandidateStage4A.lean` mutated;
- all five accepted source/compiled pairs still matching their pins; and
- no forbidden path, output, network command, client-state access, sandbox denial, or Seatbelt
  drift.

Compact trace-audit SHA-256:

```text
4619e0b269f591ffa7d4206aa06664bd4691a044161688e73116f7dfcffd90bc
```

Raw sessions, authentication, tokens, runtime state, generated `.olean` files, and the rendered
machine-specific Seatbelt profile remain external and uncommitted.

## Post-stop semantic comparison

The candidate has no semantic or new declaration-API difference from the frozen surface or the
corresponding production declarations. The exact experimental namespace remains an accepted API
difference. The direct covariance-module import is the separately accepted harness/API-surface
adjustment; it exposes the same pinned Mathlib `covarianceBilin` imported by production and has no
semantic content. Missing production docstrings are documentation-only.

All other differences are proof-only. The candidate uses simplification for the representation
lemma; explicit coercion and measure arguments for symmetry and positivity; an expanded Bochner-
integral proof of the variance identity; an explicit range-equivalence normalization proof of the
unit-sphere formula; and a nonzero-subtype nonemptiness split for the real supremum's
nonnegativity. These comparisons are review aids and do not amount to human acceptance.

## Status

Run 1 is a zero-diagnostic mechanical pass, not a human acceptance. The exact actor output is
preserved at
`experiments/humanize2_kls_issue2_staged/review/pending/CandidateStage4ARun1.lean`. It changes no
production Lean, dossier, certificate, review certification, ledger, manuscript, or mathematical
status. The next action is the sixteen-item human semantic/proof checklist. Stage 4B remains
blocked and unauthorized until an explicit human decision.
