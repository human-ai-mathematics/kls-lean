# BKL Stage 2 controller takeover

On 2026-10-10 the owner requested continuation of the established Codex coordination pattern and a new Goal. Controller `01a12661-eb02-7580-9fbd-e91e778454cf` takes over from the interrupted controller `01a123b5-2c39-72a2-951e-e4d148382678`; no unfinished prior objective is completed. Proof sources, certificate statuses and publication boundaries are unchanged. Baseline, exact request and runtime records are under `build/reviews/2026-10-10-bkl-controller-takeover/`.

## Superseded current-control wording

The following text is preserved verbatim as JSON strings; it records the earlier control state, not current authorization.

```json
[
  {
    "source": "research/handoffs/2026-10-10-bkl-staged-goals.md",
    "superseded": "The current controller is Codex chat `01a123b5-2c39-72a2-951e-e4d148382678`.\nIts Goal service was empty before the owner requested staged goals. The controller completed Stage 1 after the full requirement audit; Stage 2 is now active there."
  },
  {
    "source": "research/handoffs/2026-10-09-api-first-goal.md",
    "superseded": "The existing Goal service remains active; the available tool cannot rewrite its stored objective. The latest owner instruction and current scope file supersede the old parallel-paper wording for execution. No unfinished objective is marked complete and no duplicate goal is created."
  },
  {
    "source": "research/handoffs/2026-10-10-bkl-primary-scope.md",
    "superseded": "The existing Goal service is active. Its available tools allow status changes but cannot rewrite its stored objective text; that old parallel-paper wording is superseded for execution by this newer owner instruction. Do not mark the unfinished old objective complete or create a duplicate goal to change its text. This file and the current handoff govern the BKL-focused work queue."
  }
]
```

## Superseded priority wording

```json
{
  "source": "research/progress/literature.json, priorities[0].next_step",
  "superseded": "Next: Stage 2, Letwin Theorem 1.2 (Var ≤ 8‖M‖²_HS, the exact input of Lemma 4.2), pending until created. Stage 1 (BKL (74) grouped with (72); the covariance step of the proof of Letwin Theorem 1.2) is integrated and covered by the full local receipt 20261010T093056.948739Z. Owner scope (2026-10-10): BKL Theorem 1.1 is the primary objective. Discharge Theorem 4.1 through the original Eldan localization and the Section 4-6 cumulant-energy argument, and the cited Letwin Theorem 1.2 input for Lemma 4.2. Reuse the certified Theorem 3.1, conditional source Proposition 7.1 and regular-law reduction. Other papers are pursued only for referenced results and necessary prerequisites with an explicit BKL consumer; general CEK Theorem 2/uniqueness and full Letwin paper coverage are not standalone goals. Moment-potential, regularity, Stein, integration and approximation work must be tied to the required Letwin bound. Conditional assembly remains insufficient; KLS.kls stays open."
}
```
