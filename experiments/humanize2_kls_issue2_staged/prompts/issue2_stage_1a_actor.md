# Issue 2 Stage 1A actor prompt

Produce a compiling Lean implementation of the three foundational Poincaré definitions in the
frozen Stage 1A specification.

## Context

Your workspace is a deliberately isolated autoformalization fixture. Read all and only:

1. `AGENTS.md`;
2. `TASK.md`; and
3. `CandidateStage1A.lean`.

`TASK.md` contains the complete frozen mathematical specification. No repository source, existing
Issue 2 implementation, solution, certificate, review, ledger, oracle, or later-stage artifact is
available or needed.

## Required result

Edit only `CandidateStage1A.lean`. It must:

- use namespace `Issue2Autoformalization.Stage1A`;
- retain the ambient real-Hilbert-space assumptions stated in `TASK.md`;
- define exactly the requested top-level declarations `IsAdmissible`, `dirichletEnergy`, and
  `HasPoincare`, plus only the structure-generated declarations required by `IsAdmissible`;
- name the three `IsAdmissible` fields exactly `smooth'`, `memLp_two`, and `energy_integrable`;
- implement all fields and formulas literally from the frozen specification;
- use Mathlib's `gradient`, `MemLp`, `Integrable`, `IsProbabilityMeasure`, and `variance` notions;
- contain no additional public mathematical declaration; and
- compile successfully with the command `lean CandidateStage1A.lean`.

Use only these imports, which the reset fixture supplies:

- `Mathlib.Analysis.Calculus.ContDiff.Basic`;
- `Mathlib.Analysis.Calculus.Gradient.Basic`;
- `Mathlib.Probability.Moments.Variance`.

Do not add an import whose name starts with `FunctionalInequalities` or `Solutions`.

After every edit, run exactly `lean CandidateStage1A.lean`. Use the actual Lean diagnostics to
repair imports, namespaces, types, binders, or syntax until the command exits zero. Do not report
success based on inspection alone.

## Boundaries

- Work directly in this single actor session.
- Do not spawn a subagent, delegate, invoke collaboration, or act as a reviewer.
- Do not use web search, browser, plugins, MCP tools, or network commands.
- Do not access or name paths outside this workspace.
- Do not inspect Codex/Humanize client state, credentials, transcripts, or environment variables.
- Do not use `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `external`, or a custom unsound escape
  hatch.
- Do not add stronger assumptions, change the required namespace or names, or formalize a later
  stage.
- Do not create, rename, or delete files.

## Final response

When Lean exits zero, inspect the file once more. Report only:

1. that `lean CandidateStage1A.lean` exited zero;
2. the three requested top-level declarations produced;
3. whether you added any assumption beyond `TASK.md` (the required answer is no); and
4. any semantic uncertainty that the human reviewer should examine.

Compilation is not semantic acceptance. Stop after reporting; a human reviewer makes the only
accept/reject decision.
