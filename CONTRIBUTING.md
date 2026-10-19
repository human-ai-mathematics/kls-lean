# Contributing

Start with the [library design](LEAN_DESIGN.md), [calling examples](examples/README.md)
and [formalization guide](formalization/README.md). The [paper register](research/progress/LITERATURE.md)
owns theorem scope and coverage; Lean declarations define the actual interfaces.

## Mathematical changes

Identify the paper, pinned version and theorem before starting a proof. Preserve its
hypotheses, constants, normalization and dimension range. Distinguish a supporting lemma,
restricted counterpart, conditional implication and faithfully formalized main theorem.
Read the [placement workflow](research/workflow.md) and [naming rules](research/naming.md)
before adding modules or changing an API. Named parameters, binder order and explicitness
are part of that API. Keep generic tools in their existing mathematical owners.

Explain what changed and why, cite the mathematical source, and report the checks actually
run. AI-assisted development is welcome; review the resulting statements and proofs and
describe verification accurately. Agent review is not external human peer review.
Keep third-party licenses, attribution and modification notices with reused code.

## Local checks

Use the pinned Lean toolchain and dependency manifest. From the repository root:

```bash
python3 research/cache_mathlib.py
python3 research/check_ledger.py
python3 research/verify.py
```

The cache command includes an aggregate `import Mathlib` when present and checks the
complete required Mathlib module closure. `--check` checks existing caches without fetching.
The full verifier retains build, strict audit, axiom and kernel-replay logs; see the
[verification guide](research/verification.md) for trust boundaries and live progress.
Do not edit source or documentation during a full run: its receipt binds the whole snapshot.

Use change-appropriate checks during development. Documentation-only changes do not need
a Lean build. Proof, dependency and interface changes need the checks specified by the
[workflow](research/workflow.md). Keep generated progress views synchronized through
`research/progress/update.py` using the intended Git index; preserve unrelated local work.
Do not edit generated blocks directly.

## Reviews and releases

For a bug report, include the exact commit, pinned toolchain, a small reproducing import
or command, and the relevant log or failing gate. For a mathematical concern, include the
declaration and the source theorem being compared.

Remote Lean certification runs at meaningful milestones through manual dispatch or a
`milestone/**` tag. Routine pushes do not trigger it. Follow the
[release procedure](research/release.md); a successful old run does not certify a newer SHA.
Use the [citation metadata](CITATION.cff) and record the exact revision when reusing this work.
