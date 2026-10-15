# Documentation and accepted-proof checkpoint

Date: 2026-10-15. The owner requested documentation cleanup using the previous Numina/Kakeya
comparison and explicitly authorized one commit and push including already accepted proofs.

## Documentation ownership

The [earlier comparison and navigation decision](2026-10-12-progress-navigation.md) identified
source-step → Lean-declaration → module navigation, exact endpoint/hypothesis boundaries and
separation of current guides from history as useful practices. This checkpoint extends the
existing proof path instead of adding another theorem-status catalog or verification framework.

- Root README: short statement, proved/open boundary, navigation and verification.
- HANDOFF: current mathematical frontier, evidence, scratch state and next obligations.
- PROOF-PATH: four-stage source-to-Lean reading order and explicit remaining inputs.
- Literature register / Blueprint / ledger: existing scope, status and certificate authority.
- Dated decisions: superseded handoffs and integration history. The previous live handoff is
  archived in [pre-publication-handoff](2026-10-15-pre-publication-handoff.md).

Only relative link destinations are corrected in this checkpoint's seven previously uncommitted
handoff archives. Their prose, mathematical claims and historical verification boundaries stay
unchanged. Historical integration decisions are not rewritten as current status.

## Proof and evidence boundary

All canonical Lean source and audit-client changes included here are byte-identical to the
independently accepted snapshot `d7503d7e927870866a40e3b4f3c7b987b71351c048ab0a5235e83cf6b7d9e439`.
Its full receipt is `build/verification/20261015T004538.149290Z/report.json`: 287 passing gates,
273 research clients, 9,633 project-local declarations audited and 812 modules replayed.
Package acceptance records are retained under the ignored Goal control directory. No Lean
proof, module, declaration, assumption or constant is changed by the documentation cleanup.

The canonical frontier is the actual-source first weak Monge–Ampère identity (2.4), with every
R0 field and the same produced u, L, LF and T retained. The second evolution identity, Theorem
2.5, Letwin constant 8, unconditional BKL and KLS remain open. Paper coverage and 30 registered
certificates are unchanged. E3's accepted scratch proof and E4's interface preflight are excluded.

Before publication, regenerate progress through a temporary index, check the complete diagrams,
links, English prose and unchanged source hashes, then run a fresh full verifier for the frozen
post-cleanup snapshot with no temporary index. Retain the exact receipt and final publication
record under `build/reviews/2026-10-15-documentation-publication/`; the d750 receipt does not
certify the later metadata. Ordinary branch publication triggers no remote certification.
Unrelated `.cursor/` and `.clinerules/` configuration stays local.
