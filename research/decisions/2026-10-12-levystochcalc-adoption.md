# Adopt LevyStochCalc as vendored stochastic calculus

Date: 2026-10-12. Decided by the owner in the Claude session of 2026-10-11/12. This resolves the
open owner decision "build stochastic calculus here or build on external Lean efforts" and
supersedes the StochLean R0/R1 question: StochLean is not adopted (it has no SDE theorem), and its
review records remain historical evidence under `build/reviews/2026-10-07-bkl-continuous/`.

## Context

On 2026-10-11 the independent KLS500 development (github.com/HongruZhao/KLS500 at `c1a5099`) was
rebuilt from source in a scratch directory. Its stochastic-localization route constructs the
Eldan SDE with LevyStochCalc's Picard strong solutions, extended from globally to locally
Lipschitz coefficients by cutoffs on balls and gluing at exit times, and proves non-explosion.
LevyStochCalc (github.com/cgarryZA/LevyStochCalc) is a general Apache-2.0 library with
multidimensional Brownian motion, L² Itô integration, the vector Itô formula and strong SDE
solutions, no `axiom` declarations and no `sorry`-carrying LevyStochCalc declaration. Writing the
same infrastructure here would duplicate a reusable library. The KLS500 `KLS/` sources are not
adopted: they are specialized to ℝⁿ coordinates and serve as a route reference only.

## Decision and placement

- Owner: generic stochastic-calculus infrastructure, third-party, below every project family.
- Scope: the 196 LevyStochCalc modules of the KLS500 route and their exact import closure in the
  pinned dependencies: 39 BrownianMotion, 3 KolmogorovExtension4 and 1 MathFin modules (239).
- Destination: `formalization/vendor/{LevyStochCalc,BrownianMotion,MathFin,KolmogorovExtension4}/`,
  each with its upstream `LICENSE`; module paths and declaration names unchanged.
- Package design: four `lean_lib`s of the existing `functional-inequalities` Lake package, added to
  `defaultTargets`, with the upstream options `relaxedAutoImplicit = false` and
  `maxSynthPendingDepth = 3`. This differs from the separate vendored Lake package proposed for
  StochLean on 2026-10-08: the libraries share this package's toolchain, Mathlib pin and build
  directory, and the verifier treats them as local sources.
- Imports: no project module imports the vendored libraries yet; they import only Mathlib and
  each other.
- API impact: none on project declarations. Future BKL stochastic modules will import them from
  a dedicated probability family.
- Pins: LevyStochCalc `984dbf0b790031eac05d56fe5a84b65e15e1e932`; BrownianMotion
  `4d52fa776130a29d4ad7d6eda2035a919c0b4696`; KolmogorovExtension4
  `f33cbc388e5d444606dffa7eec507a26b62c15bb`; MathFin `784a8311f75a1519a23717856df9982bd6a9a370`
  (all upstream Lean v4.32.0, Mathlib `81a5d25`).
- Port: to Lean v4.33.0 and Mathlib `db584cd`; twelve files, +29/−35 proof lines plus a two-line
  modification notice each (Apache-2.0 §4(b)); exact diff in `formalization/vendor/port.patch`;
  no declaration renamed or restated, no option, axiom or `sorry` added. Details in
  `formalization/vendor/README.md`.

## Upstream holes and verification

The pinned BrownianMotion revision has four `sorry`s in
`StochasticIntegral/Quasimartingale/CadlagModification.lean`; exactly five vendored declarations
depend on them (listed in `VENDOR_UPSTREAM_SORRY`). A real audit of all 4789 vendored declarations
confirmed that no other vendored declaration does.

`research/verify.py` now:

- maps `formalization/vendor/<Root>/<Root>/…` sources to modules, discovers them in the source
  snapshot, builds them, and replays them with `leanchecker`;
- runs a `vendor-axiom-audit` gate: every vendored declaration has only the three standard
  axioms, except the five listed ones, each of which must be found among the audited vendored
  declarations and must still depend on `sorryAx`;
- runs the strict `local-declaration-audit` of every project-local declaration in both the full
  and the `--lean-only` verification (previously only `--lean-only`), so an unregistered local
  wrapper of a vendored hole fails; the allowlist never applies to local declarations and only the
  exact open target `KLS.kls` is excluded. The full mode keeps its statement golden, registered
  declaration and certificate gates;
- parses axiom reports exactly and fails closed. The generated audits (registered declarations,
  all local declarations) emit one JSON object per report (`AXIOM_REPORT {"name":…,"axioms":…}`),
  so any legal name, including primes, generated suffixes and `«…»` names with spaces or line
  breaks, is reported exactly, and a text report in such an audit is an error. Research audits
  keep `#print axioms`; their reports are parsed line-anchored up to the last quote on the name's
  line (Lean may break the line before the verdict), and verification fails unless every verdict in the output is parsed, so a name with a
  line break is rejected rather than skipped. Duplicate and missing reports are still rejected.

The first full run with the local audit (`20261011T180030.046722Z`) failed only on the old
`'([^']+)'` parser, which truncated primed names such as `foo'._simp_1_2`; its 8311 local reports
had no nonstandard axiom. An interim `'(\S+)'` parser (run `20261011T180651.519269Z`, stopped and not
accepted) would have skipped names containing spaces, and run `20261011T181945.249143Z` failed
its Python tests because the next pattern did not allow that line break; the independent review's
`«bad name»` and `«bad\nname»` probes are regression tests.

Tests in `research/tests/test_verify.py` (`VendorTests`) cover the module mapping, an isolated
listed hole, a vendored user of a listed hole, an unlisted vendored hole, a fixed or missing
listed name, a listed name outside the vendored roots, and an unregistered local wrapper of both a
fixture hole and the actual vendored hole. `AxiomAuditTests` and `ResearchAuditTests` cover primed,
generated and spaced names, structured reports, and the rejection of `«bad name»` and
`«bad\nname»` research audits. The CI Mathlib cache step includes vendored imports.

## Not claimed

Adding these libraries proves no SDE, Itô, martingale, non-explosion or BKL statement of this
project. The Eldan SDE (67) with locally Lipschitz coefficients, its non-explosion, (68)–(71),
Lemma 4.3, Theorem 4.1, unconditional Theorem 1.1 and `KLS.kls` remain open.

## Superseded handoff text

The following two open-owner-decision bullets of `HANDOFF.md` (as of commit `ad630b0`) are resolved
by this decision and are preserved verbatim:

- Decide whether to build stochastic calculus for Theorem 4.1 and priorities 5–6 here or build on external Lean efforts. The evidence and recommendation are in `research/decisions/2026-10-03-stochastic-calculus-options.md`.
- Decide whether the external stochastic closure, 339 StochLean modules at pin `e6741e18` and Apache-2.0 per the root audit, is adopted as a vendored separate Lake package or retained as evidence. The relevant records are `build/reviews/2026-10-07-bkl-continuous/reviews/STOCHASTIC-EXTERNAL-REUSE-SCHEME-20261008.md` and `build/reviews/2026-10-07-bkl-continuous/reviews/COEFFICIENT-SDE-MOMENTMAP-PROPOSALS-20261008.md`. The pinned closure has no SDE theorem; the Letwin moment-map producer remains out of reach at that pin and stays an explicit hypothesis.
