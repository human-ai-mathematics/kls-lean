# 2026-09-12 — `thm:smooth-gradient-relaxation-two-cheeger`: metadata cleanup (no mathematical changes)

## Background

`python3 research/atlas.py ready` classified this node as `clarify_statement` because the Blueprint block carried `\notready`,
which takes precedence over the `mathematics` classification in `atlas.py`. However, the reasons for that marker had already been resolved in the
[statement record](2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md):

- Blueprint's own rules (`00-orientation-and-status.tex`) reserve `\notready` for "explicitly unresolved statement choices"
  and state: "An open proof or possible future API changes alone do not justify the marker".
- The original reasons were (i) the choice of Cheeger energy definition was unresolved; (ii) no literature source was available for comparing the two relaxations under singular measures.
  The statement record resolved (i): use the local-slope convention, state the `Lip_a` version as an explicit separate obligation, and reuse
  `def:intrinsic-affine-energy` for affine-support transport. Only (ii) remains, and it is an open **proof**.

## Decision

- `30-open-canonical-bridges.tex`: remove `\notready` from the theorem block; rewrite the following explanation to record the definition choices,
  the `Lip_a` version as a separate obligation, and the remaining open proof (recorded by the absence of `\leanok`). Development is in
  `Energy/WIP/Cheeger.lean`, without aggregate imports, certificates, or a freeze of public signatures.
- `research/tasks.json`: replace the obsolete `note` ("Resolve local-slope versus
  asymptotic-Lipschitz conventions and singular-measure scope before proof work") with the chosen conventions, the WIP module status
  (21 of 26 obligations proved; 5 `sorry` proofs reduce to two substantive singular-measure obligations,
  `LocalSlope.relaxation_eq_asymptoticLipschitz` and `SmoothGradient.relaxation_eq_localSlope`),
  and the completed absolutely continuous/log-concave scope.
- **Keep `mathematics` as `unknown`, without adding an `infrastructure` record.** Reasons follow below.
- No declarations or proofs in `Energy/WIP/Cheeger.lean` changed; no registration, commit, or push.

## Why “replace it with an actual infrastructure assessment” was not carried out

The validation rules in `research/verification.md` and `atlas.py` allow an `infrastructure` field **only** for `local_argument`,
`published`, and optionally `definition`. Other classifications produce an error
(`task ...: require exactly [...]`). Attaching an infrastructure assessment would therefore require first upgrading `unknown` to
`local_argument` or `published`.

But `local_argument` means "a proof plan or a written argument". For the **unconditional** singular-measure statement,
Blueprint explicitly reports no literature source, and the repository has no proof plan; only the absolutely continuous scope has a complete proof.
Upgrading to `local_argument` would assert that an argument exists for the open part, exceeding the evidence. `published` is likewise unjustified.

This round therefore keeps `unknown` and records the actual status in `note`, whose documented meaning is precisely "Mathematical scope,
review requirement or execution guidance". Dispatch accordingly changes from `clarify_statement` to `review`,
meaning that someone should determine the classification, consistent with the actual situation.

If the owner judges that the unconditional statement should be asserted to follow from a local argument, change the classification and add `infrastructure` then.
Alternatively, create a separate Blueprint node for the completed absolutely continuous/log-concave scope and register a certificate:
`KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` already has no `sorry` and covers all log-concave laws through the certified
`lem:logconcave-intrinsic-absolute-continuity`. Neither option was taken in this round.

## Checks

- `python3 research/check_blueprint.py`: 87 labels, 0 errors.
- `python3 research/atlas.py check`: 74 mathematical nodes, 23 certificates, acyclic.
- Node dispatch: `clarify_statement → review`, `statement_question: false`, no blockers.
- For `python3 research/check_ledger.py`, unit tests, `lake build`, and `research/verify.py`, see the final run of this round below.
