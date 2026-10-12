# BKL independent target-check results

Date: 2026-10-12. This records a scoped local audit of the existing Theorem 3.1 and
Proposition 7.1 certificates. It adds no production theorem, certificate or paper coverage.

## Verdict and source fidelity

Within the [reviewed foundation boundary](2026-10-12-bkl-independent-target-checks.md), both
existing certificates satisfy the independently written source specifications. No mismatch
was found in the reviewed hypotheses, quantifier order, dimensional universality, Taylor
factorial, Hilbert–Schmidt norm or numerical coefficient. The Hilbert–Schmidt convention was also visually
checked on p. 8. This is a local source review and
Lean target-link check, not external peer review or an external comparator verdict.

| Target | Preserved contract | Result |
| --- | --- | --- |
| BKL v1 Theorem 3.1, p. 10 | One universal C > 0, centered regular law, Cov <= Id, R >= 1, every L2 f and d >= 1, T_d = (d!)^(-1) D^d F_f(0), Hilbert–Schmidt norm, C_P <= C R^2 | Independent specification link passed |
| BKL v1 Proposition 7.1, p. 28 | d >= 2, b > 0, cumulant energy R_(d+1) <= b Id for every isotropic log-concave law in every dimension, every L2 f, coefficient 2b/(d!)^2 | Independent specification link passed; universal input remains a hypothesis |

Normalized potential laws are identified with the paper density exp(-(V + log Z)); the
whole regularity contract survives the added constant. Both positive regularity bounds are
retained in the source specification. The production API's dimension-zero extension and
omission of explicit b > 0 in that dimension remain unchanged and are documented in the
source review. Intermediate proof restrictions (108) are not added to Proposition 7.1.
The Poincaré/log-concavity parameters are specialized to the existing reviewed definitions,
whose local closures are part of this pilot baseline; they are not independently rebuilt
from Mathlib by this pilot.

## Completed local checks

- The existing certificate source import closure was built: 168 local modules.
- The Mathlib-only specification compiled separately, followed by strict link compilation.
- Twelve bridge/target axiom reports contain only propext, Classical.choice and Quot.sound.
- The pilot snapshots 26 roots, 62 local declarations/types/definition bodies and 304 pinned
  external boundary leaves. Its reviewed golden was established explicitly, then matched
  on a separate check run without refresh.
- Lean kernel replay covered exactly the two existing certificate modules and the two new
  audit modules. This is not a replay of the full production library or a second kernel.
- Three mutated specifications compiled, then their links failed for the expected mathematical
  type errors: removing the factorial, changing 2b to b, and restricting the input to dimension 1.
  The rejection gate checks the expected diagnostics, not just a nonzero process exit.
- Six pilot Python regressions and nine existing statement-snapshot regressions passed.
- The original general statement baseline still matches its 26 local declarations and was
  not refreshed. Ledger, Blueprint and atlas structural checks passed; no new registration.

The final scoped receipt is
[20261012T063906.555442Z](../../build/reviews/2026-10-12-bkl-independent-targets/runs/20261012T063906.555442Z/report.json).
It records source hashes, compiler identity, dependency manifest, compiled artifact hashes,
logs, mutation outcomes and replay scope. Its source inputs were unchanged during the run;
it is evidence for that exact dirty source snapshot, not HEAD alone or later edits.
All intermediate diagnostics are retained in the same task's build directory.

## Reproduction and non-claims

See the [pilot guide](../audits/BKL/IndependentTargets/README.md) for the pinned PDF and command.
The pilot remains a separately invoked audit; the ordinary full verifier does not implicitly
run it. No existing proof, hypothesis or production API was changed. No commit, push, tag or
remote CI was performed.

This does not discharge Proposition 7.1's cumulant premise or prove BKL Theorem 4.1,
Theorem 1.1 or dimension-free KLS. Existing proof and coverage statuses remain unchanged.
