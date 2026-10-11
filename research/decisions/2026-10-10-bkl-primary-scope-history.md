# Superseded parallel-paper execution scope

Archived 2026-10-10 after the owner restored BKL as the primary target. The following fenced text preserves the former bytes and their original link context. It is historical scope and authorization, not current work instructions. No mathematical result or verification claim is changed.

## Previous handoff execution paragraph

```markdown
The active [parallel moment-map and Letwin goal](research/handoffs/2026-10-09-moment-map-letwin-parallel.md)
now follows the [API-first execution addendum](research/handoffs/2026-10-09-api-first-goal.md): Codex coordinates
and accepts; strong API models perform new proofs. Minimum model: GPT-5.6 Sol; no new Luna jobs.
Existing Codex proof workers remain at saved checkpoints. Construction skeletons stay outside production/certificates;
Claude retains reviewed production integration. The mathematical targets and acceptance gates are unchanged.
```

## Previous API-first goal addendum

```markdown
# Active goal: API-first execution addendum

Updated 2026-10-09 by the user's strategy amendment. This controls execution
of the existing active goal; it does not create a duplicate goal or mark the
unfinished mathematical objective complete. The Goal service currently exposes
status changes only, so its stored objective text cannot be edited by the
available tool. The newer user instruction takes precedence in execution.

## Revised goal wording

Formalize Cordero-Erausquin--Klartag, *Moment Measures*, arXiv:1304.0630v1
Theorem 2, for every nonzero finite Borel measure with finite first moments,
zero barycenter and full-dimensional support, including an essentially
continuous convex potential, the actual gradient pushforward and uniqueness
up to translation; and Letwin arXiv:2607.24164v1 Theorem 1.2 with the exact
dimension-independent quadratic-variance constant 8, including its genuine
regularity, analytic and approximation prerequisites.

Codex acts as the mathematical coordinator: choose dependency-ready tasks,
preserve pinned statements/hypotheses/constants/dimension, freeze interfaces,
dispatch API workers, inspect mathematical scope and perform final acceptance.
Move the proof construction previously assigned to Codex to strong models
through the existing API. Prefer GPT-6 Astra for difficult proofs, GPT-6.1 Sol
for general module construction, and GPT-5.6 Sol as the minimum model for
routine tasks. Use API Claude Opus 5.5 for selected critical independent
reviews. Do not use Luna or weaker fallback models for any new job.

Use compact local task contexts, saved diagnostics and checkpoints. No
duplicated construction or automatic return to expensive Codex proof loops.
Every accepted declaration needs faithful source scope, strict Lean flags,
actual proof values, only standard axiom closure, appropriate real consumers
and exact verification evidence. Keep `sorry` skeletons outside production
and certificate closures. A completed supporting or conditional result does
not finish a paper main theorem. Finish the original objective with exact
certificates and matching evidence; preserve unrelated work and staged content.
Commit, push, tags and remote CI still require separate user authorization.

## Transition checkpoint

- Three old Codex proof agents are interrupted; retain their files/handles and
  migrate unfinished units individually. No new Codex proof dispatch by default.
- Codex continuation `01a12091-ee35-7361-8a34-4cdfd64859c2` is idle with a completed
  Proposition 12 scratch candidate awaiting independent acceptance. Reuse it;
  do not spend API calls rebuilding that candidate.
- H3 and H5 bridge packages and the accepted CEK/Letwin supporting units retain
  their exact seals and claims. H3 needs independent acceptance; the smooth
  H2 producer remains open. The Letwin integrated bound/main theorem and CEK
  first variation, essential continuity and uniqueness remain open.
- Astra access was actually tested: HTTP 200, returned `gpt-6-astra`, expected
  `OK` reply, 16 reported tokens. This is connectivity evidence only. The old
  Sol HTTP 429 epoch remains historical; do not retry it blindly.
- Start with one frozen real API proof task, at most two proof attempts. Increase
  to two independent API workers after evidence of successful access/output.
  Rate/quota errors stop immediately. Provider/key bytes stay unchanged.
  The nonsecret default model is now GPT-6.1 Sol; task overrides select Astra
  or another allowed strong model, with no Luna fallback.

The 2026-10-09 full receipt for the adopted CEK support batch applies to its
exact pre-amendment snapshot. This amendment changes execution documentation,
not Lean proof status, paper coverage or the certificate ledger.
```

## Previous literature priority plan

```json
[
  {
    "rank": 1,
    "papers": [
      "BKL2026"
    ],
    "target": "Theorem 1.1 through Theorems 3.1 (certified, thm:bkl-taylor-criterion), 4.1 and Proposition 7.1 (certified in the source form, prop:bkl-suspension, conditional on its hypothesis CumulantBound): Section 3 is formalized by the operator route; Lemma 2.2, Lemma 3.6 (⇑), Corollary 3.7 (⇑), Lemmas 3.2–3.4, 3.8, 3.9 for the D(A) iterates (⇑), the regular-law adapter for (12), the complete Section 2 reduction to isotropic regular laws (regular approximation and weak-limit transfer) and the p. 30 reduction are formalized, so Theorem 1.1 is formalized conditionally on the Theorem 4.1 cumulant bounds (no certificate); Lemma 2.1 on 𝒜, (19), and Lemma 4.2 conditional on the Letwin bound are partial, restricted or conditional counterparts; Theorem 4.1 is stated conditionally (cumulant envelope) and open.",
    "next_step": "Current focus: Theorem 1.1 is now formalized conditionally on the universal cumulant bounds of Theorem 4.1 (KLS.conjecture_of_cumulantBound; no certificate, KLS.kls open). The remaining piece is Theorem 4.1 itself: the cumulant bounds via Eldan stochastic localization (Section 4; stochastic calculus decision pending) and the Letwin bound for Lemma 4.2 (Letwin Theorem 1.2 / 2.5; the moment-map Stein kernel for an arbitrary law, Lemma 2.2 / Proposition 2.8, is open — the Gaussian has the identity kernel and the mean-Hessian identity holds for a given potential). Lemma 2.1 on 𝒜 and (19) are not needed by the operator route. Active subgoal (2026-10-09): CEK Theorem 2 and Letwin Theorem 1.2 with the regularity bridge; CEK Lemma 16, Lemma 17 in geometric form and Proposition 12 attainment are formalized, while essential continuity, the Euler–Lagrange identification and Theorem 2 remain open."
  },
  {
    "rank": 2,
    "papers": [
      "BGL2014"
    ],
    "target": "Corollary 4.8.2 (strongly log-concave Bakry–Émery C_P ≤ 1/ρ) is certified as thm:bakry-emery-poincare and committed in 36e7c78 (remote run 37516844384 succeeded); select a separate Brascamp–Lieb source statement.",
    "next_step": "Pin a Brascamp–Lieb source theorem, its assumptions and normalization, and assess reuse of the heat-semigroup and Γ₂ interfaces before proof work."
  },
  {
    "rank": 3,
    "papers": [
      "KLS1995"
    ],
    "target": "Theorem 5.1, ψ(K) ≥ ln 2 / M₁(K) for convex bodies, through the needle reduction (Corollary 2.2, Lemma 2.6, Theorem 2.7). With the local Cheeger inequality it gives C_P ≲ E‖X − EX‖² for convex bodies.",
    "next_step": "Pin a proof of the cited localization lemma (Lovász–Simonovits 1993 or a modern account) and choose a Lean form for needles; keep the product denominator of (1.1) distinct from the min-denominator constant."
  },
  {
    "rank": 4,
    "papers": [
      "Milman2009"
    ],
    "target": "Concentration implies a Cheeger bound under the source convexity hypotheses.",
    "next_step": "Pin the main theorem and its concentration/curvature assumptions; compare its analytic inputs with the current finite-dimensional Cheeger–Buser API."
  },
  {
    "rank": 5,
    "papers": [
      "Eldan2013",
      "LeeVempala2024",
      "Chen2021",
      "KlartagLehec2022",
      "Klartag2023"
    ],
    "target": "Published stochastic-localization theorems and quantitative KLS bounds.",
    "next_step": "Reuse Mathlib probability foundations; build an isolated audited client of pinned external stochastic APIs before selecting the missing vector/matrix SDE bridges."
  },
  {
    "rank": 6,
    "papers": [
      "KlartagLehecThin2025",
      "ChenKlartag2026",
      "Letwin2026"
    ],
    "target": "Selected 2025–2026 thin-shell and quadratic-form results.",
    "next_step": "Retain exact preprint versions and assess moment-measure, stochastic and matrix-estimate dependencies; do not credit exploratory hypotheses as completed paper theorems."
  }
]
```
