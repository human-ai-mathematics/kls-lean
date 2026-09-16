# KLS literature map through July 2026

The progress hub now includes a literature map alongside the existing research-route map.
The new register covers 27 selected sources: the principal general KLS-bound milestones,
the connected thin-shell and slicing developments, moment-measure/Stein-kernel foundations,
and analytic references with explicit local proof coverage. It is a curated map, not an
exhaustive bibliography or a new verification of all external proofs.

The July endpoint is pinned to Chen–Klartag `2607.23307v1` (25 July 2026) and Letwin
`2607.24164v1` (27 July 2026). Both are marked as preprints. Their main statements were
checked against the original arXiv HTML. Publication dates are distinguished from first
preprint and conference dates, particularly for Lee–Vempala and the 2025 thin-shell paper.
Primary-source links and theorem locators are stored per entry.

All general KLS bounds use the inverse-Cheeger convention `ψ = 1/h`, while `C_P` multiplies
the squared-gradient energy without a factor 1/2. Logarithmic exponents are converted using
the literature comparison `ψ²/π ≤ C_P ≤ 4ψ²`. Thus Letwin’s inverse-Cheeger exponent 1/4
means Poincaré exponent 1/2. The local Cheeger–Buser comparison remains unfinished. Neither
the sharp thin-shell theorem nor a result restricted to quadratic tests is called full KLS.

`research/progress/literature.json` is the editable inventory. The existing progress
generator now renders `LITERATURE.md`, `LITERATURE.mmd` and the hub’s literature block.
Local result links resolve against the same staged Blueprint records and auxiliary
assessments as the proof tree. A completed restricted result makes a paper only partially
covered; a publication or an upstream proof alone never gives local Lean credit. No paper
completion percentages are invented. Dashed literature edges are chronology or method
context, explicitly distinct from the proof tree’s prerequisite arrows.

The existing combined proof-route diagram and 19-row upstream approach register are
preserved. There are no Lean edits, certificate changes, new `leanok` markers or changes
to the Cheeger–Buser workstream. The book’s coefficient-4 attribution remains tied to the
previous source audit, with an explicit distinction between the recorded high-dimensional
statement and the independently proved one-dimensional local result.

Validation uses the generator drift check, seven progress tests including negative
publication/coverage tests, the existing 104 Python tests, Blueprint/Atlas checks and
local-link/preservation checks. Generation uses a disposable Git index for the intended
canonical inputs. Local audit evidence is stored in
`build/audit/literature-map-20260916/final.json`. This documentation/generator round does
not rerun Lean or replace the previous source-bound kernel receipt. No commit, push or
collaborator message is sent in this round.
