# Synchronize upstream and verify the full manuscript build

- **Date:** 2026-08-27
- **Type:** repository integration and manuscript build
- **Scope:** upstream merge, `modules/kls/00-orientation.tex`, generated PDF QA
- **Mathematical effect:** none

## Problem

The Issue 2 Lean branch was based on `d354fdc` while `upstream/main` had advanced by five commits
through `abf4e0c`. The branch needed those repository and research-harness changes without losing
its Lean bootstrap. The full `main.tex` manuscript also needed a reproducible build and visual
inspection after integration.

## Decision

Fetch `upstream/main` and merge it into `codex/issue-2-linear-test-lower` with an ordinary merge,
recorded as `3cf3936`. Do not rebase, force-push, switch branches, or update the fork's `main`
branch. The merge was clean and retained the Issue 2 handoff, Lean bootstrap, and append-only
exploration record.

Compile the manuscript with `latexmk -pdf -outdir=build main.tex`, copy the deliverable to the
ignored path `output/pdf/main.pdf`, and render all 152 pages for visual inspection. The first
render exposed a clipped KLS architecture diagram on page 67. Constrain that existing TikZ
picture with `\resizebox{\linewidth}{!}{...}`; this changes only its rendered scale and leaves its
nodes, arrows, caption, labels, and mathematical content unchanged. The second render fits the
complete diagram inside the text block.

No ledger, claim status, proof dossier, or mathematical dependency changes as part of this
integration.

## Migration boundary and compatibility

The upstream merge adopts the split program ledgers at `research/a-series/ledger.yaml` and
`research/kls/ledger.yaml`, the current agent harness, and the append-only `research/decisions/`
classification. Existing Issue 2 work continues on the same feature branch. The generated PDF,
LaTeX build directory, UV environment, and rendered QA images remain local ignored artifacts.

The final LaTeX log retains two visually benign overfull-box warnings (the long A3 audit path and
one KLS history-table cell) plus pre-existing duplicate hyperlink-destination warnings for
`equation.188`. There are no undefined references or citations; the formerly clipped figure no
longer produces an overfull-box warning.

## Validation

- `latexmk -pdf -outdir=build main.tex` — passed; 152 pages, 1,293,637 bytes.
- `pdfinfo output/pdf/main.pdf` — passed; PDF 1.7, letter size, unencrypted, no suspect objects.
- Render all pages with `pdftoppm` and inspect thirteen contact sheets plus warning pages at
  original resolution — passed; no missing pages or remaining clipped content.
- `/usr/bin/python3 research/check_ledger.py` — passed; 2 ledgers, 176 nodes, 642 labels,
  0 errors.
- `uv run --with pyyaml python research/check_agents.py` — passed; 13 roles, 0 errors.
- `uv run --with pyyaml python -m unittest discover -s research/tests -p 'test_*.py'` — passed;
  42 tests.
- `cd formalization && lake build` — passed; 2,940 jobs.
- `cd experiments && uv run python -m finum selftest` — passed; 0 failures.
- `cd experiments && uv run pytest` — passed; 91 tests.
- `git diff --check` — passed.

The system `/usr/bin/python3` is version 3.9 and cannot import `tomllib`, while the Homebrew
Python 3.14 lacks PyYAML. Therefore the combined agent and unit-test checks use an isolated UV
environment with PyYAML rather than modifying either global interpreter.
