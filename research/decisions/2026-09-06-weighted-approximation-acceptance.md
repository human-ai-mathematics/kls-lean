# Weighted smooth approximation: local acceptance and certificate registration

Date: 2026-09-06. The user agreed to “accept these proofs first, then prepare the constant-comparison
statements”. This record accepts the current four proofs of `lem:covariance-test-core-density`
and connects them to the existing acceptance workflow. Starting HEAD:
`70ca1c19c4d207a31716c2e589c0b096521a5490`, including earlier uncommitted work.
No commit/push, rewriting of historical decisions/explorations, or changes to prior staging.

## Source and scope review

Read the [statement handoff](2026-09-06-weighted-approximation-statements.md),
[proof-completion record](2026-09-06-weighted-approximation-proofs.md), Blueprint Appendix A,
and the four public declarations and implementations. Their signatures are unchanged, with
no added mathematical inputs. The implementation only removes three `beta_reduce` steps
confirmed ineffective by the current Lean linter; the linter is not disabled.

The main result still only requires g and B∇g in L²(ν), allowing degenerate B; ν is absolutely
continuous with respect to an arbitrary positively normalized Haar reference, including
dimension zero. Helpers retain compact support, the same Lipschitz constant, and arbitrary
closed intervals in bounded-L1. Integrability of the full squared gradient is not added to
the main conclusion's premises. Local slope, literature constants, and closed-operator
conclusions are outside this batch.

The implementation uses Rademacher, scaled cutoffs, nonnegative normalized kernels, and
dominated convergence. Convolution-gradient convergence uses the affine model at differentiable
points and kernel-derivative mass estimates; no additional weak-derivative construction from
the original written route is needed. This change of proof route preserves the target scope.

## Registration

- The unique `Solutions.LemCovarianceTestCoreDensity.certificate` in `solutions/LemCovarianceTestCoreDensity.lean` explicitly conjoins all four contracts, using the corresponding library theorem for each component. Retain checks of all four library declarations and add a transitive axiom guard for the certificate.
- Set the ledger node to `proved / checked_by: lean`, updating only obsolete draft wording and acceptance provenance; the original six nodes are unchanged. The existing Blueprint label `lem:covariance-test-core-density` carries the certificate link and `leanok`, without a new navigation node.
- Register the certificate in the existing explicit `check_blueprint.py` map, without changing the verification algorithm or weakening acceptance. The `tasks.json` mathematical classification remains `local_argument`; infrastructure becomes `available`, with implemented-library and certificate source hashes. Update TeX evidence hashes for the new certification anchors. No long-route status changes.
- Synchronize current guides to seven proof certificates, retaining the unproved literature-constant comparison and Borell-density input.

## Verified checks and final receipt

The four declarations' transitive axioms are locally confirmed to be exactly `propext`,
`Classical.choice`, and `Quot.sound`. Escape-marker scans of the entry point and local import
closure pass. After removing ineffective tactics and adding the certificate,
`lake build solutions.LemCovarianceTestCoreDensity` passes with 3032 jobs; the new certificate
guard passes. Ledger, Blueprint, and atlas checks pass: 7 proved ledger nodes, 7 certificates,
73 mathematical nodes, 86 navigation labels, 4 active routes, no dependency cycles.

After editing this record and the guides, run `python3 research/verify.py`. Its generated
`build/verification/<UTC timestamp>/report.json` records actual final outcomes, per-gate logs,
complete certificate printing, axiom coverage, local kernel replay, and source SHA256.
This record does not claim success of that full run in advance or write the generated final
source hash back into itself. Subsequent statements change the working tree: distinguish the
acceptance snapshot from later draft snapshots, and use each subsequent receipt's source hash
when verification is rerun.

Replay still trusts pinned third-party compiled imports; it is not an isolated source rebuild
or external independent check. No remote CI or publication was performed.
