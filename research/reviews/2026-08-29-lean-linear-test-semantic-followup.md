---
type: audit
date: "2026-08-29"
---

# Follow-up semantic audit of the Lean linear-test certificate

## Result

**PASS for the scoped semantic-alignment question.** Every blocking item in
`research/reviews/2026-08-29-lean-linear-test-independent-semantic-audit.md` is discharged by the
current manuscript, ledger, dossier, provenance convention, and Lean certificate. No residual
statement, hypothesis, normalization, extended-value, covariance-centering, or dimension-zero
mismatch was found for `lem:linear-test-lower`.

This remains a non-certifying `type: audit`: the word PASS here has no `checked_by: agent` proof
value and proposes no ledger certification delta. It records that the existing
`checked_by: lean` and `lean_solution: solutions/LemLinearTestLower.lean` binding is now
semantically supported.

## Sources reconstructed

The follow-up re-read the current versions of:

- `CLAUDE.md`, `.claude/agents/README.md`, `solutions/README.md`,
  `solutions/TEMPLATE.tex`, and `research/reviews/README.md`;
- `main.tex`, which includes `modules/01-definitions.tex` before
  `modules/02-results-toolkit.tex`;
- `modules/01-definitions.tex:17-29`, label `def:poincare`;
- `modules/02-results-toolkit.tex:108-126`, label `rem:rayleigh-lower-only`;
- `research/a-series/ledger.yaml:84-101`;
- `solutions/glm-linear-baselines.tex:5-89`;
- `formalization/FunctionalInequalities/Basic.lean`;
- `formalization/FunctionalInequalities/Poincare.lean`;
- `formalization/FunctionalInequalities/Project/LinearTestLower.lean`;
- `solutions/LemLinearTestLower.lean`; and
- the earlier HOLD audit in full.

No numerical result or prior author's narrative was used to bridge a mathematical step.

## Prior blockers rechecked

### Probability and finite second moment

The toolkit now assumes a probability measure on $\mathbb R^D$ with finite second moment at
`modules/02-results-toolkit.tex:110`. The ledger repeats that hypothesis at
`research/a-series/ledger.yaml:89`, and the dossier states it at
`solutions/glm-linear-baselines.tex:48-50`. In the node theorem these become
`IsProbabilityMeasure μ` and `MemLp id 2 μ` at `solutions/LemLinearTestLower.lean:18-20`.
For a standard Borel finite-dimensional Euclidean space, `MemLp id 2 μ` is exactly the
coordinate-free finite-second-moment condition; it also makes the centered covariance matrix
finite. The formal theorem's allowance of arbitrary probability measures, rather than only
density measures $e^{-U}dx$, is a harmless strengthening.

### Smooth $L^2$ finite-energy core

`modules/01-definitions.tex:19-27` now defines finite valid constants on smooth $L^2$ tests of
finite gradient energy and defines the optimal constant by the infimum of those finite candidates.
The toolkit uses the same class at `modules/02-results-toolkit.tex:110-112`; the ledger calls it the
“smooth L2 finite-energy” class; and the dossier defines admissibility explicitly at
`solutions/glm-linear-baselines.tex:50-52`.

This agrees with `IsAdmissible` at `Basic.lean:27-36`: `ContDiff ℝ ⊤`, `MemLp f 2 μ`, and
integrability of $\lVert\nabla f\rVert^2$. Smoothness supplies measurability, so finiteness of the
nonnegative gradient integral in the TeX statement has the same integrability content. No
closed-Sobolev-domain identification is used.

### Exact quotient boundary conventions

The toolkit at `modules/02-results-toolkit.tex:112-117`, ledger at
`research/a-series/ledger.yaml:89`, and dossier at
`solutions/glm-linear-baselines.tex:53-58` all state

$$
\frac00=0,\qquad \frac a0=+\infty\quad(a>0).
$$

This is precisely `poincareRayleighQuotient` at `Poincare.lean:80-83`, which maps numerator and
denominator separately to `ENNReal` before division. `Poincare.lean:85-116` proves the all-test
bound, the positive-energy real-quotient identity, and the positive-variance/zero-energy `⊤` case.
The dossier proof now handles positive energy, $0/0$, and positive variance over zero energy
separately at `solutions/glm-linear-baselines.tex:68-75`; constants are explicitly included.

### The no-finite-candidate case

The manuscript definition states $C_P\in[0,+\infty]$ and sets $C_P=+\infty$ when there is no
finite valid constant at `modules/01-definitions.tex:25-26`. The dossier uses the same range and
derives the zero-energy positive-variance case from the absence of a finite candidate at
`solutions/glm-linear-baselines.tex:50,69-75`. This matches the `ENNReal` infimum in
`Basic.lean:95-100` and the exact `⊤` equivalence in `Basic.lean:115-134`.

### Centered covariance

The toolkit says “centered covariance matrix” at `modules/02-results-toolkit.tex:117-120`; the
ledger says centered covariance; and the dossier identifies
$\operatorname{Var}_\pi\langle v,X\rangle=v^T\operatorname{Cov}_\pi v$ at
`solutions/glm-linear-baselines.tex:77-86`.

Lean constructs `centeredCovarianceOperator` from Mathlib's centered `covarianceBilin`, explicitly
not its uncentered `covarianceOperator`, at `Poincare.lean:120-156`. The quadratic-form equality
with linear-test variance is sufficient to identify the Euclidean operator with the usual centered
covariance matrix. `Poincare.lean:249-278` uses this same object in the fixed and optimal bounds.

### Dimension zero and the eigenvalue wording

The toolkit now defines the empty nonzero-direction supremum to be $0$ when $D=0$ and calls the
quantity an eigenvalue only for $D\ge1$ at `modules/02-results-toolkit.tex:118-120`. The ledger
contains the same convention, and the dossier states and uses it at
`solutions/glm-linear-baselines.tex:62-64,84-88`.

This agrees with `Poincare.lean:158-225`: the real nonzero-vector Rayleigh supremum is an actual
eigenvalue only under `Nontrivial E`, while the subsingleton value is proved to be zero. Thus the
certificate's quantification over every `D : ℕ` introduces no unstated natural-language case.

### Mixed per-node provenance

The shared dossier's active block at `solutions/glm-linear-baselines.tex:10-14` now records
separately:

- `lem:linear-test-lower`: `checked_by lean` with
  `lean_solution: solutions/LemLinearTestLower.lean`; and
- `thm:glm-fi`: `checked_by agent` with its 2026-08-25 proof review.

Lines 15-18 retain the shared analytic dossier's historical author/reviewer provenance without
obscuring current modes. This exactly matches the two ledger nodes at
`research/a-series/ledger.yaml:84-101` and the shared-dossier rule now documented in
`solutions/README.md:51-54,62-67` and `solutions/TEMPLATE.tex:19-20`.

### Sobolev and spectral-gap boundary

The certificate still makes no false equivalence claim. `Basic.lean:27-32` explicitly says that
identifying the selected core with a closed Sobolev or spectral-gap definition requires a separate
theorem. `modules/01-definitions.tex:27-28` states the reciprocal-gap sentence only under the
standard closed-Dirichlet-form identification. The repaired linear-test lemma and its proof use
only the finite-energy-core definition. No spectral-gap or form-closure step occurs in
`Project/LinearTestLower.lean:21-47` or `solutions/LemLinearTestLower.lean:17-27`.

## Proof-chain confirmation

The reusable Lean argument remains correct:

1. linear tests are smooth, $L^2$ under `MemLp id 2 μ`, and have energy $\lVert v\rVert^2$
   (`Poincare.lean:43-78`);
2. every admissible quotient is below every finite valid constant and hence below their `ENNReal`
   infimum (`Poincare.lean:80-116`, `Basic.lean:107-113`);
3. the centered covariance quadratic form is the variance of the linear test
   (`Poincare.lean:125-156`);
4. the nonzero-direction supremum is bounded by every finite Poincaré constant, with a separate
   subsingleton branch (`Poincare.lean:249-270`);
5. taking the infimum gives the optimal bound (`Poincare.lean:272-278`); and
6. the project and node-specific theorems conjoin exactly the two ledger clauses
   (`Project/LinearTestLower.lean:28-40`, `solutions/LemLinearTestLower.lean:18-27`).

No stated hypothesis is missing. `MemLp id 2 μ` is used by the covariance clause; the arbitrary
test clause is stronger than needed under that common theorem hypothesis. Finite dimensionality is
appropriate for interpreting the Rayleigh maximum as an eigenvalue when $D\ge1$.

## Fences, dependency closure, and citations

The node has no `bounded_by` or `depends_on` edges. There is therefore no unresolved obstruction,
conditional premise, or preprint dependency. The linear-test proof uses no research-level external
result. The Bakry--Émery and Otto--Villani citations in the shared dossier belong only to the
separate GLM theorem. The finite-dimensional Rayleigh API is proved in the pinned Mathlib
dependency and introduces no research-level citation debt.

## Validation

The follow-up independently reran:

```text
cd formalization && lake build
Build completed successfully (2946 jobs).

cd solutions && latexmk -pdf -outdir=<fresh external directory> glm-linear-baselines.tex
exit 0; 2-page PDF; only expected standalone cross-reference warnings remain.

latexmk -pdf -outdir=build main.tex
exit 0; 161-page PDF.

uv run --with pyyaml python research/check_ledger.py
2 ledger(s), 195 nodes, 675 labels. 0 error(s).

uv run --with pyyaml python research/check_ledger.py node lem:linear-test-lower
status: proved
solution: solutions/glm-linear-baselines.tex
lean_solution: solutions/LemLinearTestLower.lean
checked_by: lean

uv run --with pyyaml python -m unittest discover -s research/tests -p 'test_*.py'
Ran 44 tests ... OK

git diff --check
exit 0.
```

A source scan again found no `sorry`, `admit`, or custom `axiom` in the Lean implementation.

## Corrections

None. All repairs requested by the HOLD audit were found in the current artifacts and agree
mathematically.

## Exclusions

This audit does not certify:

- a closed-Sobolev-core or generator spectral-gap equivalence;
- Gaussian exactness or the mode-indicator statements adjacent to the manuscript remark;
- the separate `thm:glm-fi` proof, its approximation/closure argument, or its external citations;
- any numerical test-function search;
- a claim for infinite-second-moment measures; or
- any node other than `lem:linear-test-lower`.

No requested alignment step remained unverifiable.

## Handoff

```yaml
outcome: no-change
artifacts:
  - research/reviews/2026-08-29-lean-linear-test-semantic-followup.md
proposed_deltas:
  - none
next_role: orchestrator
next_prompt: |
  Retain the current proved node binding for lem:linear-test-lower: the repaired manuscript,
  ledger statement, analytic dossier, mixed per-node provenance header, and compiling node-specific
  Lean certificate now agree. This audit is non-certifying and requires no ledger delta. Preserve
  every earlier audit as append-only history.
```
