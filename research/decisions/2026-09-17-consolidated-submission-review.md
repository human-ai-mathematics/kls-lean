# Consolidated local submission review — 2026-09-17

This review consolidates the coarea and analytic-foundation updates since `34b9269`
into one local commit. Earlier dated implementation records remain historical snapshots,
including their statements that no commit was made in those rounds.

## Mathematical scope

- Scalar C¹, Lipschitz and locally Lipschitz weighted coarea are proved with normalized
  surface measure; the existing T1/T2/T3 entry points retain their stated scope.
- The Whitney construction extends compact first-order jets with exact ambient derivatives.
  It is not an arbitrary noncompact closed-set extension theorem.
- Vector-valued coarea is proved on the regular region. Slice measurability and nullity of
  almost every slice of the zero-derivative set are proved. Intermediate positive ranks
  remain a gap in the general formula.
- Rank stratification and kernel/right-inverse estimates discharge R1–R3. R4 is the next
  obligation; R0, R4–R10, N1 and N2 remain open. No additional KLS implication is asserted.
- The ledger still has 24 certificates. There are eight direct holes (1/2/5) in the three
  existing WIP modules. Sharp finite-regularity Sard, the two Cheeger comparison obligations,
  the five Energy identities and the dimension-free KLS bound remain open.

## Corrections made during review

1. The right-inverse audit overstated its degenerating-family example as ruling out a
   uniform kernel estimate near every failure of surjectivity. Its actual example concerns
   `t • id` near zero. Constant zero families satisfy the estimate, even for nonzero targets.
   Corrected both this comment and the constant-map comment; proof statements and bodies
   are unchanged.
2. The rank-deficient route file still said none of its obligations were proved. Marked that
   as the initial snapshot and linked the current R1–R3 results, without changing its
   `#check` propositions.
3. Updated the root status date and vector-coarea boundary. Added the separate vector
   extension to the combined progress diagram, with R4 highlighted. The four active KLS
   routes and the collaborator-owned Cheeger comparison remain distinct.

4. Corrected eight relative decision links in `research/verification.md` that repeated its
   parent directory. All 911 local Markdown targets in the changed documents resolve.

## Local validation

The current-source scan imported all local library and solution modules and inspected 3,166
elaborated declarations with `Lean.collectAxioms`. Exactly 12 declarations depend on `sorryAx`:
2 in `KLS.WIP.AnalyticPrerequisites`, 5 in `KLS.WIP.CheegerInfimum` and 5 in
`Energy.WIP.Cheeger`. None escape those modules. No local axiom, unsafe or partial declaration
was found. The proof bodies were unchanged by the review corrections.

The two coarea equality migrations were independently compared with `HEAD`: their elaborated
`pp.all` types are byte-identical before and after migration.

All 29 added or modified audit clients passed, with no warnings. Their three deliberate
`sorryAx` reports name the still-open `Analysis.sard`. The ledger and Blueprint structural
checks passed, as did the seven progress-generator tests. Progress views are regenerated
from the staged canonical records.

The final source snapshot must additionally pass `python3 research/verify.py`, including
statement-golden comparison, certificate axiom checking and all-local-module kernel replay,
before committing. Its machine receipt is stored under `build/verification/`, outside Git.
This is local verification with pinned third-party compiled imports trusted, not remote CI
or an independent checker of Mathlib. No push is part of this submission.
