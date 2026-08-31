# Issue 2 Stage 3 actor prompt

Produce a compiling Lean implementation of the five extended Rayleigh-quotient declarations in
the frozen Stage 3 specification.

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
10. `AcceptedStage2B.olean`; and
11. `CandidateStage3.lean`.

Read the seven text files and do not inspect any compiled `.olean` dependency.

`TASK.md` is the complete frozen Stage 3 specification. The four accepted Lean sources and their
toolchain-matched compiled artifacts are read-only, human-accepted experimental dependencies. No
repository source, existing Issue 2 implementation, solution, certificate, review, ledger,
oracle, or later-stage artifact is available or needed.

## Required result

Edit only `CandidateStage3.lean`. It must:

- import only `AcceptedStage2B`;
- continue namespace `Issue2Autoformalization.Stage1A` without redeclaring accepted material;
- implement exactly the five declarations displayed in `TASK.md`;
- preserve every displayed binder, declaration type, hypothesis, expression, and right-hand side;
- form the quotient in `ENNReal` after applying `ENNReal.ofReal` separately to variance and energy;
- cover the frozen zero-energy and no-finite-constant boundaries without a new assumption;
- add no unrequested public declaration, attribute, stronger assumption, or later-stage result;
  and
- compile with `lean CandidateStage3.lean` at exit zero and with empty standard output and standard
  error.

After every edit, run exactly `lean CandidateStage3.lean`. Use only actual Lean diagnostics to
repair imports, namespaces, types, binders, coercions, extended-real division, proof terms, or
style findings until the command exits zero and its output is empty. A warning or linter
suggestion is a failed attempt even when Lean exits zero. Do not report success based on inspection
alone.

## Boundaries

- Work directly in this single actor session.
- Do not spawn a subagent, delegate, invoke collaboration, or act as a reviewer.
- Do not use web search, browser, plugins, MCP tools, or network commands.
- Do not access or name paths outside this workspace.
- Do not inspect Codex/Humanize client state, credentials, transcripts, or environment variables.
- Do not inspect any `.olean`, modify any accepted artifact, or create, rename, or delete files.
- Do not use `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `external`, `set_option`, `attribute`,
  or another proof/diagnostic escape hatch.
- Do not add a probability, Borel, finite-dimensional, nontrivial, separability, centered-moment,
  or stronger ambient assumption.
- Do not change the required namespace or API, or formalize covariance, spectral, Euclidean, final
  Issue 2, or any later layer.
- Do not create a proof dossier or claim review, certification, production integration, or
  mathematical acceptance.

## Final response

When Lean exits zero with no diagnostic output, inspect `CandidateStage3.lean` once more. Report
only:

1. that `lean CandidateStage3.lean` exited zero and emitted no diagnostics;
2. the five requested declaration names;
3. whether you added any assumption beyond `TASK.md` (the required answer is no);
4. the number of compiler-feedback repair iterations; and
5. any semantic or proof uncertainty that the human reviewer should examine.

Compilation is neither semantic acceptance nor proof certification. Stop after reporting; a human
reviewer makes the only accept/reject decision.
