# Warning cleanup and semantic/mathematical review

Continue from the existing uncommitted library-wide API migration. Unified acceptance passed
before editing, with receipt `build/verification/20260908T142214.267284Z/report.json`.
No compilation error was reproduced, but there was one deprecation warning and nine warnings
about references to automatically generated auxiliary declarations.

## Fixes

- Replace the deprecated name with `Set.mem_ofPred_eq` in `KLS/LogConcave/Isotropic.lean`. Only the lemma used to simplify set membership changes; assumptions, conclusion, and proof route are unchanged.
- `research/verify.py` calls `Lean.collectAxioms` using exact names from the environment, the same transitive axiom collector as `#print axioms`. Retain all auxiliary declarations and the existing allowlist, without suppressing warnings or skipping declarations. Check existence before querying, so a missing name cannot appear axiom-free. Three Lean integration tests cover generated proof helpers, transitive nonstandard axioms, and missing declarations.
- Correct `local-apply` back to `local-slope` in comments in `KLS/Statement.lean` and `Poincare/LocalSlope/Basic.lean`; the L² condition for local-slope tests correctly references `Energy.LocalSlope.Admissible.memLp_two`.

## Semantic and mathematical checks

The 1085 types and definition closures re-extracted from the current compiled environment
agree with the previous migration. Full raw-expression output is byte-identical before and
after the fixes, without name, parameter, or universe normalization. Test classes, carriers,
assumptions, constants, normalization, and definition bodies are unchanged. The comparison
does not include theorem proof bodies, which are separately checked by compilation, axiom
audit, and kernel replay. Artifacts are in `build/warning-cleanup/`.

Manual review found no mathematical statement requiring changes in these boundaries:

- KLS's finite nonnegative constant is quantified before dimension and probability law. Energy is the integral of squared local slope in intrinsic affine coordinates, without a `1/2` factor; finite second moments are retained.
- Zero-energy tests are not excluded. Positive variance divided by zero energy is infinity; zero divided by zero is zero. The literature constant is infinite if no finite bound is valid. An empty approximation class gives infinite relaxation energy and does not imply a recovery sequence.
- Raw ambient gradient energy for a Dirac law can still depend on the representative. Intrinsic space and relaxation have not been replaced by raw ambient energy. Dimension zero, empty products, and degenerate Gaussians remain covered.
- The one-dimensional Gaussian optimum is variance `v`; whitening uses positive definite intrinsic covariance. Equivalence of affine, covariance, and isotropic formulations retains fixed finite `K` and a fixed universe; it does not prove existence of such a `K`.

After checking original evidence hashes and these source differences, refresh four
infrastructure source hashes. Statement golden files, ledger certification status,
mathematical interfaces, and third-party dependencies are unchanged in this round.

A separate `lake build` after the fixes passes without errors or warnings. Final full
acceptance reads `build/verification/latest.json` and checks it against the current source
snapshot, covering Python tests, statement golden files, declaration axiom audits, and kernel
replay of all 114 local modules. Replay trusts pinned third-party compiled dependencies;
it is not an independent clean-environment rebuild. Local working-tree edits only, no commit or push.
