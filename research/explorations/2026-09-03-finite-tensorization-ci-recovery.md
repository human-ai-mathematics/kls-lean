# Finite tensorization publication: CI disk recovery

**Date:** 2026-09-03 (Asia/Shanghai).

The accepted mathematical commit `58d3c1c7c68e44e4df54dcaf694a739df67167e5` passed the local
and clean-checkout gates recorded in the finite-tensorization acceptance record. Its first
[push workflow](https://github.com/human-ai-mathematics/kls-lean/actions/runs/33762313810)
failed after 4m25s with runner `System.IO.IOException: No space left on device`. The ledger and
Python steps had succeeded. The runner failed while the composite Lean step was in progress;
GitHub could not supply that job's failed-step log. This is not a successful remote build and
does not establish whether the remote Lean build had finished.

The actual official [`leanprover/lean-action@v1` definition](https://github.com/leanprover/lean-action/blob/v1/action.yml)
was inspected. Its default GitHub
cache restores and saves the entire `.lake` directory, and `use-mathlib-cache: true` runs an
unrestricted `lake exe cache get`. Existing repository cache entries were approximately 2.5 GB
compressed each. The available logs do not establish exactly which substep exhausted storage;
the repair reduces both whole-directory archive overhead and the Mathlib artifact footprint.

The workflow now uses the official action to set up Lean with both automatic cache modes and
its internal build disabled. A separate step enumerates the direct `Mathlib.*` imports of the
local aggregate, reusable library, and solution files, then runs `lake exe cache get` on that
nonempty list. A final step still runs the complete default `lake build`. The ledger and Python
test steps are unchanged. No theorem, certificate, ledger statement, toolchain, dependency pin,
or proof-validation gate is changed.

The dependency-update hook is also disabled through `MATHLIB_NO_CACHE_ON_UPDATE=1`; the targeted
fetch supplies the cache explicitly. This setting is supported by the pinned Mathlib
`lakefile.lean`, lines 163–182. `Cache/Main.lean` documents module-root arguments and recursive
upstream retrieval. The root arguments must be Mathlib modules: `Cache/Hashing.lean` filters out
local project imports before traversing imports, so supplying only `FunctionalInequalities.lean`
or solution entry points would miss their indirect Mathlib dependencies.

At this revision the scan finds 13 direct Mathlib imports, covering all three solution entry
points and the aggregate. The cache is only a build optimization: every local declaration and
all default targets continue to be compiled. The final publication SHA and successful CI for
that exact revision are recorded in Issue #7 after the repaired workflow completes; the failed
run above remains part of the publication history.

Local validation parsed the workflow YAML, executed the exact embedded import scanner with its
subprocess call captured, and confirmed the 13 Mathlib roots and unchanged `lake build` step.
The pinned `lake exe cache lookup` accepted all 13 roots successfully. The ledger checker again
reported 3 proved nodes and zero errors; all 24 Python regression tests passed. No Lean source
or ledger data changed after the accepted mathematical commit.
