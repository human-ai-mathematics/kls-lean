# Issue 2 Stage 4A actor prompt

Produce a compiling Lean implementation of the eight centered-covariance and real-Rayleigh-
maximum declarations in the frozen Stage 4A specification.

## Context

Your workspace is a deliberately isolated autoformalization fixture. Its exact file entries are:

1. `AGENTS.md`;
2. `TASK.md`;
3. `AcceptedStage1A.lean`;
4. `AcceptedStage1A.olean`;
5. `AcceptedStage1B.lean`;
6. `AcceptedStage1B.olean`;
7. `AcceptedStage2A.lean`;
8. `AcceptedStage2A.olean`;
9. `AcceptedStage2B.lean`;
10. `AcceptedStage2B.olean`;
11. `AcceptedStage3.lean`;
12. `AcceptedStage3.olean`; and
13. `CandidateStage4A.lean`.

Read the eight text files and do not inspect any compiled `.olean` dependency.

`TASK.md` is the complete frozen Stage 4A specification. The five accepted Lean sources and their
toolchain-matched compiled artifacts are read-only, human-accepted experimental dependencies. No
repository source, existing Issue 2 implementation, solution, certificate, review, ledger,
oracle, or later-stage artifact is available or needed.

## Required result

Edit only `CandidateStage4A.lean`. It must:

- use exactly these imports in this order, with no third import:

  ```lean
  import AcceptedStage3
  import Mathlib.Probability.Moments.CovarianceBilin
  ```
- continue namespace `Issue2Autoformalization.Stage1A` without redeclaring accepted material;
- implement exactly the eight declarations displayed in `TASK.md`;
- preserve every displayed binder, declaration type, hypothesis, expression, attribute, and
  right-hand side;
- use the centered bilinear form and preserve the zero-dimensional empty-supremum convention;
- add no unrequested public declaration, attribute, stronger assumption, or Stage 4B result; and
- compile with `lean CandidateStage4A.lean` at exit zero and with empty standard output and
  standard error.

After every edit, run exactly `lean CandidateStage4A.lean`. Use only actual Lean diagnostics to
repair imports, namespaces, types, binders, coercions, continuous-linear-map or Rayleigh-quotient
proof terms, or style findings until the command exits zero and its output is empty. A warning or
linter suggestion is a failed attempt even when Lean exits zero. Do not report success based on
inspection alone.

## Boundaries

- Work directly in this single actor session.
- Do not spawn a subagent, delegate, invoke collaboration, or act as a reviewer.
- Do not use web search, browser, plugins, MCP tools, or network commands.
- Do not access or name paths outside this workspace.
- Do not inspect Codex/Humanize client state, credentials, transcripts, or environment variables.
- Do not inspect any `.olean`, modify any accepted artifact, or create, rename, or delete files.
- Do not use `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `external`, `set_option`, `attribute`,
  or another proof/diagnostic escape hatch.
- Do not add finite-dimensionality, nontriviality, separability, a probability assumption, or a
  stronger moment condition.
- Do not change the required namespace or API, or formalize any Stage 4B spectral or extended-
  value result, Euclidean specialization, final Issue 2 theorem, or later layer.
- Do not add, remove, reorder, or replace either frozen import.
- Do not create a proof dossier or claim review, certification, production integration, or
  mathematical acceptance.

## Final response

When Lean exits zero with no diagnostic output, inspect `CandidateStage4A.lean` once more. Report
only:

1. that `lean CandidateStage4A.lean` exited zero and emitted no diagnostics;
2. the eight requested declaration names;
3. whether you added any assumption beyond `TASK.md` (the required answer is no);
4. the number of compiler-feedback repair iterations; and
5. any semantic or proof uncertainty that the human reviewer should examine.

Compilation is neither semantic acceptance nor proof certification. Stop after reporting; a human
reviewer makes the only accept/reject decision.
