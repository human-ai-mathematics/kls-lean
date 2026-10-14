# Proof-path documentation checkpoint

Date: 2026-10-14. The owner prioritized a documentation cleanup, informed by the earlier comparison with Numina's Kakeya
formalization, followed by one commit and an ordinary push that also carries the independently accepted proof changes. Claude
wrote the documentation as the sole canonical documentation writer; Codex reviews, validates, stages, commits and pushes. No proof,
Lean declaration, certificate, coverage or node status changed.

## Rationale and reference

Numina's [Kakeya formalization](https://github.com/project-numina/kakeya-3d) keeps a short
[PROOF-PATH.md](https://github.com/project-numina/kakeya-3d/blob/main/PROOF-PATH.md) that walks a reader from the main theorem down
its proof path with explicit input boundaries, and a [formalization.yaml](https://github.com/project-numina/kakeya-3d/blob/main/formalization.yaml)
manifest of the formalized statement. KLS adopts only the first pattern: a navigation guide naming exact inputs. It does not add a
`formalization.yaml` or any second status database, because the structured paper register (`research/progress/literature.json`), the
Blueprint, the ledger and the scope-specific verification receipts already own status and evidence. No comparator, second kernel or
external checker coverage is claimed.

## Changes and placement

- New `research/progress/PROOF-PATH.md`: the owner's four-stage main line (Letwin constant 8, stochastic localization, BKL Theorem 4.1,
  KLS), the exact current input `LetwinCompactBound` (KLS/BKL/CompactReduction.lean) and its scope, the unproved frozen endpoint
  `letwinCompactBound`, the proved regular-class reduction with its retained premise, the conditional `theorem41`/
  `conjecture_of_letwinCompact` with their retained input, `KLS/Statement.lean` and the open `KLS/Target.lean`, a short list of proved
  supports and the next obligation (N11d). It links the generated registers as authoritative and introduces no status, count or edge.
- `formalization/blueprint/README.md` rewritten as a concise current guide (where live status is, TeX markers as recorded implementation markers that by
  themselves establish neither a `sorry`-free axiom closure nor a certificate, AND/OR structure, adapter and provenance metadata, workflow links, the unchanged build commands and
  output paths). Its full previous body, including the stale node count and route assessments, is archived in
  [2026-10-14-blueprint-guide-history](2026-10-14-blueprint-guide-history.md) with only relative links rebased. No Blueprint TeX or route
  semantics changed.
- `HANDOFF.md` archived byte for byte in [2026-10-14-pre-documentation-checkpoint-handoff](2026-10-14-pre-documentation-checkpoint-handoff.md)
  and rewritten: active Goal, roles, current supports and open obligations, the N11b full receipt and Codex canonical acceptance with
  their pre-checkpoint scope, and the checkpoint commit/push authorization.
- Root `README.md` and the non-generated navigation and dated paragraph of `research/progress/README.md` link the proof path; generated
  blocks, the complete diagram and the approach table are regenerated, not hand-edited.
- The Goal record `research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md` gains an updated current queue and a separate
  authorization update; its setup history and no-commit default are preserved.

## Navigation fixes from the final review

Per Codex's final navigation review: the non-generated "Scope of the diagram" item in `research/progress/README.md` no longer states a
manual certificate count (the stale "27") and links the authoritative certification ledger instead, keeping the isolated `KLS.kls`
target and certificate-closure boundary; the chronological handoff index now lists the historical
`2026-10-12-bkl-claude-controller-goal.md` (its own text, including "Status: active", is preserved as history) and notes that the
current controller and work are described only in the root HANDOFF; and the current authorization prose says "no separate release
beyond that ordinary push" instead of an unqualified "no publication" next to the authorized push. Historical no-publication
statements are unchanged. No certificate, Goal or proof status changed.

## Trust boundary

This checkpoint is documentation only. Lean sources, the ledger and certificates, node statuses and paper coverage are unchanged from
the snapshot covered by the passed full receipt `build/verification/20261014T080831.534453Z/report.json` and Codex's canonical
acceptance; those records do not cover the new documentation. Validation of the post-checkpoint snapshot is recorded by Codex in the
ignored checkpoint directory `build/reviews/2026-10-14-documentation-checkpoint/`. Dimension-free KLS, Letwin Theorem 1.2 and the active
compact constant-8 Goal remain open.
