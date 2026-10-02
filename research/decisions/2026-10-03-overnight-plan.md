# Overnight work plan (2026-10-03, about eight hours)

Requested by the owner before sleeping: prepare and carry out an eight-hour block. Rules for the
whole window:

- Local commits only. No push, no tag, no remote CI, no change to accepted certificates.
- Statements are written by Claude; proof bodies may come from the GPT worker
  (`gpt-5.6-luna`), and every candidate is checked locally: unchanged statements, no forbidden
  tokens, strict compilation and a standard-axiom report. Claude reviews accepted proofs before
  integration.
- Work only on sources available locally (`~/Desktop/KLS`); Bakry–Gentil–Ledoux stays blocked.
- Run the change-appropriate checks before each commit; run the full local verifier before
  committing Lean changes, on a frozen tree.

## Blocks

1. **De Ponti–Mondino Lemmas 3.2 and 3.3.** Finish the stepwise GPT proof of the fifteen fixed
   statements (eight helpers by Claude, three paper statements, four substitution lemmas),
   integrate `KLS/Geometry/Cheeger/BuserProfile.lean` into the library, update the De
   Ponti–Mondino lemma map, verify and commit.
2. **More lemma maps** from pinned arXiv sources: Ambrosio–Gigli–Savaré 2013, Eldan 2013 and
   Chen 2021, with numbering checked against the PDFs and Lean declarations mapped where they
   exist. An independent GPT reading checks each statement list.
3. **Stochastic-calculus assessment** (owner decision prepared, not taken): pin the current
   external Lean sources, check toolchain compatibility in an isolated directory, and list the
   interfaces the priority-4 papers need.
4. **Small documentation debt:** the stale "Buser half is not proved" docstring of the Cheeger
   inequality is a Lean edit and is handled with the next Lean commit.
5. **Wrap-up:** full local verifier, HANDOFF update and a morning report in this file.

## Stop conditions

A block that fails its checks is left uncommitted with a note below; later blocks continue.
Nothing is pushed.

## Log

- Block 2 done: lemma maps for AGS 2013 (38 items: 2 ✓, 3 ◐), Eldan 2013 (28 items, all ○) and
  Chen 2021 (19 items: 2 ◐), built from the arXiv LaTeX sources with numbering checked against the
  PDFs. Unnumbered claims are kept only where a Lean declaration states them. An independent GPT
  reading of each PDF listed the same numbered statements. All diagrams render (Mermaid 11).
- Block 3 done: [stochastic-calculus options](2026-10-03-stochastic-calculus-options.md),
  decision left to the owner.
- Block 4 prepared: the stale Buser docstrings in `KLS/Geometry/Cheeger/Inequality.lean` are fixed
  (docstrings only, pins refreshed); committed with the next verified Lean change.
- Block 2 extended: lemma maps for Lee–Vempala 2024 (arXiv v3, 59 items: 1 ⇑ for the quoted Cheeger
  inequality, which Lean proves without isotropy and with constant 4; 2 ◐), Klartag–Lehec 2022
  (28 items: 1 ✓, 7 ◐) and Klartag 2023 (19 items: 6 ◐). Lee–Vempala uses the C_t = I localization,
  relevant to the stochastic-calculus decision. All 22 diagrams render.
- Block 2 extended again: Jambulapati–Lee–Vempala 2022 (27 items: 1 ◐), Klartag–Lehec thin shell
  2025 (37 items, all ○) and Letwin 2026 (16 items: 1 ✓, 4 ◐). The Letwin main proof cites a bound
  `C_P ≤ C κ_n √log n` "by tracing" Klartag 2023 that the preprint does not prove (noted in the map).
  All 28 diagrams render.
- Block 2 extended again: Guan 2024 (11 items: 1 ⇑, the quoted Buser–Ledoux inequality with π in place
  of 9), Klartag–Lehec slicing 2025 (13 items) and Chen–Klartag 2026 (17 items). A filtering bug of mine
  had dropped appendix-numbered lemmas (`Lemma A.1` …) from Letwin 2026 in commit `53c23ed`; the map is
  restored from the agent's builder to all 23 items and the filter is fixed. All 34 diagrams render.
