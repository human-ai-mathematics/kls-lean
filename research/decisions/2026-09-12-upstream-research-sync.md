# 2026-09-12 — Upstream research and literature synchronization

This round synchronizes research. It adds no Lean theorem, `sorry`, certificate, or proved node,
and changes no existing proof. The working tree was clean at the start; the four existing
boundary-interface proofs belong to earlier work.

## Sources and revisions

- The upstream repository is now named [kls-conjecture-search](https://github.com/human-ai-mathematics/kls-conjecture-search).
- Previous research pin: `8185e46ffb040e04fea076953e5bcaeb4157d71a` (2026-09-01).
- New research pin: `34b5fcd57fef17089e781616005fe6d3641bd11e` (2026-09-10), confirmed by a read-only query as `main` during this round.
- [Six-commit comparison](https://github.com/human-ai-mathematics/kls-conjecture-search/compare/8185e46ffb040e04fea076953e5bcaeb4157d71a...34b5fcd57fef17089e781616005fe6d3641bd11e): template migration, two research batches, manuscript and website improvements. Record dates are not merge dates.
- The ledger moved to `research/program/ledger.yaml`, and the search portfolio to `research/program/portfolio.yaml`.
- The local route source retains stable ID `kls-exploration`; repository URL, revision, ledger, and route-provenance paths are updated. Historical decisions and certificates retain their old revision sources.

The pinned mathematical modules, ledger, portfolio, bibliography, and two research summaries
were read. The [selected raw ledger records](../upstream/2026-09-12-kls-research.json) preserve
20 unmodified YAML records and the source ledger's SHA-256. This is a reviewable source excerpt,
not a second Lean ledger, and does not directly drive task scheduling. This round did not
independently re-audit the mathematics of every upstream proof document.

## Certification semantics

At this snapshot, upstream has 138 nodes: 86 `proved`, 46 `open`, 4 `defined`, and 2 `refuted`.
These counts cannot be compared directly with the 24 local Lean certificates: upstream includes
literature, natural-language proofs, and implications with hypotheses.

- `proofs.mode: agent` records upstream natural-language review, not Lean verification.
- Upstream `proved` with nonempty `assumes` means a conditional proposition has been proved. Local `prop:spectral-sufficiency` and `cor:cmh-recovery-sequence-suffices` remain `conditional`; the existing Blueprint/route dependencies retain their explicit open premises, without promotion to unconditional results.
- Preprint statements, upstream reviews, numerical experiments, and Lean certificates are different kinds of evidence.
- The four sufficient routes to KLS remain a logical OR. New exact models or short-time results do not create a new completed branch to KLS.

## Literature updates

Both papers are pinned to v1 and added to the Blueprint bibliography and route chapter.

| Source | Original statement | Local boundary |
| --- | --- | --- |
| [Chen–Klartag, 2607.23307v1](https://arxiv.org/abs/2607.23307v1) | Sharp thin-shell bound for isotropic log-concave laws: `Var(|X|²) ≤ 8n`; also a third-moment tensor bound | Not formalized in Lean; thin-shell alone does not solve KLS |
| [Letwin, 2607.24164v1](https://arxiv.org/abs/2607.24164v1) | Poincaré coefficient 2 for symmetric quadratic forms; `ψ_n ≤ C (log n)^(1/4)`, `n ≥ 2` | Not formalized in Lean; `1/4 ≤ ψ²/C_P ≤ π` yields `C_P ≤ C' sqrt(log n)`, not a dimension-free bound |

Do not copy Letwin's exponent for `ψ` directly to `C_P`, or describe the weaker upstream route
endpoint conditional on Letwin as a new best literature bound.

## Added research and remaining gaps

The [wave-four summary](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/34b5fcd57fef17089e781616005fe6d3641bd11e/research/explorations/2026-08-31-orchestrator-kls-angles-wave-w4.md)
and [wave-five mathematical summary](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/34b5fcd57fef17089e781616005fe6d3641bd11e/research/explorations/2026-09-06-orchestrator-kls-cone-lift-wave-w5.md)
provide proof and review paths; the latest ledger takes precedence over provisional statuses
from earlier waves.

| Route | Newly incorporated upstream records | Established scope | Still missing |
| --- | --- | --- | --- |
| Spectral localization | `lem:mm-restart-deweighting`, `lem:mm-smallgap-fourth-moment` | Restart deweighting and small-spectral-gap fourth-moment control using an existing dimension-dependent bound | Local foundations for stochastic processes, stopping times, eigenfunctions, and generators |
| Spectral localization | `lem:mm-stopped-window-source`, `prop:mm-window-occupation` | Short-time chain and `C_P ≤ C log² n`, **conditional on `thm:letwin-qcts`** | Occupation uniformly over positive times; KLS remains open |
| Screened localization | `prop:split-screened-supply` | Screened-supply estimate for the regular split class | Universal gate for arbitrary measures/cuts |
| CMH | `lem:cmh-linear-spectral-resolution` | Weak column equation and spectral resolution in the closed-form sense | General strong operator-domain conclusion; the `Tr Q ∈ L²` issue cannot be omitted |
| CMH | `lem:linear-sector-third-moment`, `cor:gate-zero-third-moment` | Stein-column energy decomposition into constant, directional third-moment, and orthogonal higher-order remainder terms | A matrix bound universally controlling the higher-order remainder |
| CMH | `conj:gate-zero-sharp` | Explicit conjecture `E[H Σ⁻¹ H] ≼ 2Σ` | Still a conjecture; exact models satisfying it do not promote its status |
| Exponential cones | `def:exponential-cone`, `prop:cone-moment-map`, `prop:cone-linear-sector`, `cor:cube-cone-gate-zero` | Explicit moment map/Stein kernel, axial value `1+n/β ≤ 2`, and cube-cone matrix bound | General gate zero, full CMH inequality, uniform recovery envelope |
| Conditional fibers | `lem:fiber-root-degree-two` | Root-frame quadratic quotient-space minimum `(m+2)(m+3)/(5m²) > 1/5` for `m ≥ 3` | Full `L²` spectral gap, cubic certificate, universal frame construction |

The 264 exact upstream cone samples are numerical/finite-model evidence, not a proof of a
universal inequality. The sharp linear sector of exponential cones is not the entire CMH
constant. The quadratic-polynomial result only excludes quadratic refuters in that bidual
framework; it cannot be generalized to a complete frame theorem.

## Subsequent formalization queue

These are scope proposals, not claims of infrastructure readiness. This round only adds
research-update notes to existing tasks, retaining their mathematical classification,
assumptions, and infrastructure status. Audit statements and dependencies before adding new
objects as formal Blueprint mathematical nodes.

1. **Continue the current perimeter chain.** Four outward-normal/boundary-integral interfaces are proved. First connect Gauss–Green and existing smooth approximation, then coarea, Sard, recovery sequences, and Cheeger-infimum comparison. These are existing formalization tasks.
2. **Assess `lem:fiber-root-degree-two` separately.** The original statement is in upstream `modules/kls/45-conditional-fiber-frame.tex`. Review the isotropic simplex, root frame, quadratic-polynomial quotient space, conditional-resampling normalization, and finite-dimensional spectral calculation. The existing fiber closed form is reusable, but those models must not be assumed to exist locally.
3. **Start CMH with a minimal definition dependency table.** Keep moment maps, canonical Stein kernels, closed generators, and weak column equations separate. Do not silently replace the upstream weak formulation with a strong-domain premise. Treat cone models as a separate calibration task.
4. **Treat stochastic localization as a larger independent work package.** Define processes and stopping times before the wave-four window chain. The Letwin input must be proved in Lean or retained as an explicit assumption; a source citation cannot serve as an axiom.

This round does not automatically create tasks, send Slack messages, commit, or push. New
research routes do not replace the perimeter proof already in progress.

## Verification scope of this round

Run Blueprint/Atlas structure checks, Python regression checks, full local verification, and
a build check of the updated Blueprint. The full verification receipt is
`build/verification/latest.json`; it binds the actual source snapshot, and this document does
not claim a pass in advance. The generated Atlas still schedules only existing local
mathematical nodes; upstream excerpts add neither `leanok` nor Lean certificates.
