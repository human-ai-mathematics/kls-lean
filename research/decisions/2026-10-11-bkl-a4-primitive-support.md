# Isolated Letwin A.4 tail-primitive support (2026-10-11)

Current controller independently accepted the exact Q3 tail primitive
`FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff`. For every smooth
nonnegative w vanishing off [0,3] and every R>0, the actual primitive
`q_R(t) = R^-1 integral_(t/R)^3 w` is smooth, has derivative `-R^-2 w(t/R)`, lies between
zero and `R^-1 integral_0^3 w`, and vanishes for `t >= 3R`.

The original proof was constructed by the actual `gpt-6-astra` response in Q3 v6. Its strict
rejection had exactly three unused-tactic errors. Codex created a separate candidate and removed
exactly those three redundancies: no new proof inference, import, option or statement change.
The original immutable packet and FAILED marker remain unchanged.

Independent evidence: `build/reviews/2026-10-11-bkl-a4-goal-setup/q3-lint-cleanup-v1/independent/VERIFICATION.json`.
Strict source compilation passed, literal frozen context was preserved, raw full types and universes
agree without normalization (type hash `5eb06cc62f83b2617701d7ea8c99e680db47f7f65567cd73c35fe1c4339b81e6`),
all eight actual proof values have standard axiom closure, and the new module
`Stage2ScalarPrimitive` was freshly kernel-replayed. Candidate source SHA-256:
`21912ed5a9555a8d8b32a8042be3f3bfde49cc0d419ce027f77c51025dab6b8a`.

This is an isolated supporting proof, not canonical adoption, source A.4/A.5 completion or a
paper certificate. The current scalar canonical candidate and real-parameter A.4 readiness were
assigned to the existing sole Claude integration conversation (Message70). B1 positivity is
an actual live one-response Astra request; fresh Q5 and E1 preflights retain failed histories.
Current authoritative checkpoints are in `build/reviews/2026-10-11-bkl-a4-goal-setup/STATE.json`.

The source-paper map, diagram and root summary remain correct at their existing partial/open
statuses: source A.4 is unfinished, and the scalar adoption still awaits a matching full local
receipt. No Blueprint/literature status is upgraded by this isolated proof. The real Git index
and production sources are preserved at this checkpoint; no commit, push, tag or remote CI.
