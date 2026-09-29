# FirstOrderJet necessity round closeout

2026-09-16. Preserve all uncommitted changes present at the start of this round; no commit or push.
Starting HEAD and origin/main were both `dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`.
The earlier migration receipt `20260915T164547.132773Z` passed and covered 471 entries; the current inventory has 473 entries,
with snapshot `2e0e01c666cbbec14f684c0ded0d5e6130719c95fbf106c895c0dc399cc908ad`.
A file-by-file comparison found changes only in the FirstOrderJet module and client. All 67 existing infrastructure evidence entries were fresh.

## Proved content and scope

`Analysis.uniform_jet_remainder_of_contDiff`: in a finite-dimensional real normed space, if a globally C¹ function v
realizes both f and F on a compact set S, then for every ε > 0 there is a uniform δ > 0 such that
any x,y in S at distance less than δ satisfy `‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖`.
The proof uses uniform continuity of the derivative on the closed unit thickening of the compact set and a line-segment mean-value inequality.
It does not require S to be convex, to have interior points, or to be nonempty, nor does it require the space to have nonzero dimension.
This proves only **necessity of the L6 hypotheses, not L6 sufficiency/extension existence**.
The client contains a `#check` of the original L6 proposition, a restatement of necessity, the function's own jet, and a squared-function example on a closed ball.
The original module and client are preserved byte-for-byte; the four `#print axioms` checks allow only the three standard axioms.

## Closeout and verification

Added this round's decision and source evidence for the module and client, retaining older evidence entries and historical per-round JSON files.
Refreshed the current handoff, audit notes, task gaps, and progress diagram, marking L11 as formalized and moving the next step to L6.
The progress generator used a separate temporary Git index populated with the current canonical records; the real index was unchanged.

Strictly recompiled the module and all 20 clients (13 in research/audits and 7 existing clients in build/audit),
and compiled the three WIP files individually to check the 2/2/5 counts. The default build and root verification results are recorded in
`research/explorations/2026-09-16-first-order-jet.json`. The final exact receipt and snapshot-equality check are recorded in
`build/audit/first-order-jet/final-snapshot.json` to avoid a self-referential hash.
Clients intentionally reporting unclosed declarations may contain sorryAx; the new necessity theorem must not contain sorryAx.
The certificate count remains 24, and perimeter infrastructure remains missing. L6/L6a/L7/L12, Lipschitz coarea,
sharp finite-regularity Sard, the two Cheeger comparisons, and dimension-free KLS remain incomplete.
