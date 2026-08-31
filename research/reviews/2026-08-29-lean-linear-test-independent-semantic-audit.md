---
type: audit
date: "2026-08-29"
---

# Independent semantic audit of the Lean linear-test certificate

## Result

**HOLD / revise.** The Lean theorem is internally sound and proves the intended finite-dimensional,
finite-second-moment, smooth finite-energy version of the linear-test lower bound. It does not,
however, literally match all active natural-language surfaces. The manuscript and ledger omit a
moment hypothesis, leave the zero-energy quotient underdefined, and do not state a dimension-zero
convention. The shared dossier also has one certification header for two nodes whose active checking
modes now differ.

This is a non-certifying `type: audit`. It proposes no proof-certification delta and does not alter
the earlier reports. In particular, it does not uphold the blanket no-mismatch conclusion in
`research/reviews/2026-08-29-lean-linear-test-semantic-alignment.md:115-121`.

## Scope and sources

The audit independently reconstructed the statement and proof from:

- `CLAUDE.md`, `.claude/agents/README.md`, `solutions/README.md`,
  `research/reviews/README.md`, and `research/ledger-schema.md`;
- `main.tex:57-64`, which includes the definition module before the toolkit module;
- `modules/01-definitions.tex:6-25`, especially `def:poincare`;
- `modules/02-results-toolkit.tex:105-117`, especially `rem:rayleigh-lower-only`;
- `research/a-series/ledger.yaml:84-92`, node `lem:linear-test-lower`;
- `solutions/glm-linear-baselines.tex:5-68`, especially `lem:sol-linear-test-lower`;
- `formalization/FunctionalInequalities/Basic.lean`;
- `formalization/FunctionalInequalities/Poincare.lean`;
- `formalization/FunctionalInequalities/Project/LinearTestLower.lean`;
- `solutions/LemLinearTestLower.lean`; and
- the earlier audit at
  `research/reviews/2026-08-29-lean-linear-test-semantic-alignment.md`.

No numerical artifact or author narrative was used as evidence.

## Checked Lean proof chain

The following steps check out.

1. `Basic.lean:33-36` defines an admissible test to be globally $C^\infty$, in $L^2(\mu)$,
   and to have integrable squared gradient. The last field prevents Mathlib's totalized real
   integral from turning a nonintegrable energy into zero.
2. `Basic.lean:39-60` uses exactly $\int\lVert\nabla f\rVert^2\,d\mu$ and proves pointwise and
   integrated equality with the squared operator norm of the Fréchet derivative.
3. `Basic.lean:62-68` uses the factor-one normalization
   $\operatorname{Var}_\mu(f)\le C\mathcal E_\mu(f)$, with $C\ge0$ and probability
   normalization. This agrees with `modules/01-definitions.tex:19-23`.
4. `Basic.lean:95-113` defines the optimal constant as the `ENNReal` infimum of all finite
   nonnegative valid constants. The direction of `le_optimalPoincareConstant` is correct: a lower
   bound on every finite candidate is a lower bound on the infimum. `Basic.lean:115-134` proves
   that the value is `⊤` exactly when there is no finite candidate.
5. `Poincare.lean:45-70` proves that $x\mapsto\langle v,x\rangle$ is admissible under
   `MemLp id 2 μ`, has gradient $v$, and has energy $\lVert v\rVert^2$ under probability
   normalization.
6. `Poincare.lean:82-116` maps variance and energy separately into `ENNReal` before division.
   Hence positive variance divided by zero energy is `⊤`, while $0/0=0$; at positive energy the
   quotient agrees with the ordinary real quotient. The proof covers zero energy without illicit
   cancellation.
7. `Poincare.lean:125-156` Riesz-represents Mathlib's centered `covarianceBilin`, not its
   uncentered object named `covarianceOperator`, and identifies the quadratic form with
   $\operatorname{Var}_\mu\langle v,X\rangle$ under `MemLp id 2 μ`.
8. `Poincare.lean:158-225` defines the real Rayleigh supremum over nonzero vectors, proves
   nonnegativity, identifies it with the unit-sphere covariance supremum, and proves it is an
   actual eigenvalue in nontrivial finite dimension. Mapping it with `ENNReal.ofReal` therefore
   does not truncate it. In dimension zero there is no eigenvalue; the implemented empty-supremum
   convention gives `lambdaMaxCovariance μ = 0`.
9. `Poincare.lean:249-278` applies the fixed-$C$ Poincaré inequality to every linear test,
   divides only by $\lVert v\rVert^2>0$ in the nonzero branch, handles the subsingleton branch
   separately, and then lower-bounds every finite valid candidate before taking the infimum.
10. `Project/LinearTestLower.lean:31-40` conjoins the all-admissible-test quotient bound and the
    covariance lower bound. `solutions/LemLinearTestLower.lean:18-27` specializes the theorem to
    `EuclideanSpace ℝ (Fin D)` and exposes the probability and finite-second-moment hypotheses.

No inequality is reversed, no covariance is uncentered, and no `ENNReal` boundary case used by the
certificate is mishandled.

## Hypothesis and quantifier accounting

The machine theorem uses:

- `D : ℕ` and the standard Borel Euclidean structure;
- `IsProbabilityMeasure μ`;
- `MemLp id 2 μ`, used to make every linear projection $L^2$ and to identify the centered
  covariance form with variance; in finite-dimensional Euclidean space this is the coordinate-free
  finite-second-moment hypothesis behind a finite covariance matrix;
- global smoothness, $L^2$ membership, and finite gradient energy for each arbitrary test; and
- finite dimensionality for the interpretation of the Rayleigh maximum as an actual eigenvalue
  when $D>0$.

The first conjunct does not logically need `MemLp id 2 μ`, but the node-specific theorem places
both conjuncts under the dossier's common finite-covariance hypothesis. Constants are included;
this is harmless only because the formal quotient explicitly fixes $0/0=0$. No density
$e^{-U}$, smooth potential, log-concavity, nondegeneracy of the covariance, or positive finite
Poincaré constant is used.

## Blocking statement-agreement findings

### 1. Finite covariance is not stated on every active surface

The dossier explicitly assumes a probability measure with finite covariance at
`solutions/glm-linear-baselines.tex:43-44`, matching `IsProbabilityMeasure μ` and
`MemLp id 2 μ` in `solutions/LemLinearTestLower.lean:18-20`. In contrast,
`modules/02-results-toolkit.tex:110-113` says “any test function” and “for every measure,” while
`research/a-series/ledger.yaml:89` records neither probability nor a finite-second-moment
hypothesis.

This is not cosmetic. In pinned Mathlib, the real variance of a non-$L^2$ function and
`covarianceBilin` outside `MemLp id 2` are totalized rather than interpreted as an infinite
classical covariance. The hypothesis is what makes the Lean covariance the manuscript's usual
finite centered covariance. The earlier audit's phrase “the node's stated finite-covariance scope”
at `research/reviews/2026-08-29-lean-linear-test-semantic-alignment.md:117-119` is therefore too
strong: the scope is stated in the dossier and Lean theorem, but only implicit or absent in the
manuscript and ledger.

### 2. The natural-language quotient has no exact zero-energy convention

`modules/02-results-toolkit.tex:110-111` and `research/a-series/ledger.yaml:89` quantify over
“any” test while printing a quotient, so constants already produce $0/0$. The dossier changes this
to “admissible nonconstant” and invokes a “usual extended-value convention” at
`solutions/glm-linear-baselines.tex:44-49`. For an arbitrary singular measure, global
nonconstancy still does not imply positive variance or positive $\mu$-energy, so that phrase does
not remove the boundary case.

Lean makes a definite and sound choice: $0/0=0$ and $a/0=+\infty$ for $a>0$. Because none of the
three natural-language statements specifies that choice, the formal theorem is a repair of an
ambiguity rather than a literal translation.

### 3. Dimension zero is an unstated extension

The certificate quantifies over every `D : ℕ`. At $D=0$ the nonzero-vector and unit-sphere index
types are empty, there is no actual covariance eigenvalue, and Lean assigns the supremal value
$0$. None of `modules/01-definitions.tex`, `modules/02-results-toolkit.tex`, the ledger sentence,
or the dossier states $D\ge1$ or defines $\lambda_{\max}$ of the $0\times0$ covariance to be zero.
The Lean result is correct under its explicit convention, but that convention is not yet source
semantics.

### 4. The extended optimal constant is explicit only in the dossier and Lean

The dossier places $C_P(\pi)$ in $[0,+\infty]$ and treats the $+\infty$ case at
`solutions/glm-linear-baselines.tex:43-44,65-67`. Lean gives the exact empty-candidate `⊤`
semantics. `modules/01-definitions.tex:17-25`, the toolkit remark, and the ledger sentence do not
state the no-finite-constant convention. The intended reading is standard, but the previous
audit's assertion that there is no extended-value mismatch is not literally established by the
active prose.

### 5. The shared dossier header does not express mixed active checking modes

`solutions/glm-linear-baselines.tex:6-14` enumerates both `lem:linear-test-lower` and
`thm:glm-fi` and supplies one global `checked_by: agent`, reviewer, and review. The ledger now has
`checked_by: lean` for the first node at `research/a-series/ledger.yaml:84-92`, while the second
node remains agent-certified at `research/a-series/ledger.yaml:94-101`.

The old agent provenance remains valid history and must not be erased, and the explicit
node-specific Lean artifact is structurally valid. Nevertheless, the solution-level header format
described by `solutions/README.md` does not currently distinguish the two active per-node checking
modes. The production checker validates node enumeration but does not detect this presentation
ambiguity. Per-node provenance in the shared header, or separate dossiers, is required for an
unambiguous current record.

## Fences, dependencies, and citation debt

The node has no `bounded_by` edge, so there is no obstruction fence to discharge. It has no
`depends_on` edge and no unresolved or preprint dependency. The linear-test proof uses no
research-level external result: the Bakry--Émery and Otto--Villani citations earlier in the shared
dossier belong to the separate GLM theorem. The finite-dimensional Rayleigh result used here is a
proved theorem in the pinned Mathlib dependency, not an assumed numerical or literature input.

## Validation

The independent checks produced:

```text
cd formalization && lake build
Build completed successfully (2946 jobs).

cd solutions && latexmk -pdf -outdir=<fresh external directory> glm-linear-baselines.tex
exit 0; the remaining unresolved cross-references are the expected standalone-subfile warnings.

uv run --with pyyaml python research/check_ledger.py
2 ledger(s), 195 nodes, 675 labels. 0 error(s).

uv run --with pyyaml python research/check_ledger.py node lem:linear-test-lower
status: proved
solution: solutions/glm-linear-baselines.tex
lean_solution: solutions/LemLinearTestLower.lean
checked_by: lean

uv run --with pyyaml python -m unittest discover -s research/tests -p 'test_*.py'
Ran 44 tests ... OK
```

A source scan found no `sorry`, `admit`, or custom `axiom` in the Lean implementation. An
independent `#print axioms` probe of the semantic bridges, covariance bound, project theorem, and
node certificate reported only `propext`, `Classical.choice`, and `Quot.sound`. Small compiled
probes also confirmed $0/0=0$, nonzero divided by zero is `⊤`, and
`lambdaMaxCovariance = 0` on `Fin 0`. These checks support internal formal correctness; they do not
repair statement disagreement.

## Required corrections

1. In `solutions/glm-linear-baselines.tex:43-68`, define the admissible class and the exact
   extended quotient. Either state the undivided inequality for every admissible test and restrict
   quotient notation to positive energy, or explicitly adopt the Lean conventions $0/0=0$ and
   $a/0=+\infty$ for $a>0$. State either $D\ge1$ or the $D=0$ value
   $\lambda_{\max}(\operatorname{Cov}_\pi):=0$.
2. Through the manuscript owner, align `modules/02-results-toolkit.tex:110-113` with the dossier:
   say probability measure on $\mathbb R^D$ with finite second moment, use the same admissible-test
   and extended-quotient conventions, say centered covariance, and state the dimension-zero
   convention or $D\ge1$.
3. Through the sole ledger orchestrator, make `research/a-series/ledger.yaml:89` a concise version
   of exactly that repaired statement. A green structural check alone is insufficient.
4. Make the no-finite-Poincaré-constant convention explicit where the manuscript defines the
   optimal constant, without claiming that this Lean development proves the separate spectral-gap
   sentence at `modules/01-definitions.tex:24`.
5. In `solutions/glm-linear-baselines.tex:6-14`, preserve the historical agent review but express
   current checking mode per covered node (including the node-specific Lean artifact), or split the
   shared dossier. Do not rewrite the historical proof review.
6. Preserve the earlier 2026-08-29 audit as append-only history. After the repairs compile and the
   orchestrator has synchronized manuscript and ledger, run a new independent semantic audit; do
   not amend an old audit into a pass.

Until then, the current `checked_by: lean` transition should be held rather than treated as having
earned literal semantic alignment. This audit itself supplies no ledger certification delta.

## Exclusions

Nothing here checks or certifies:

- equivalence of the smooth finite-energy core with a closed Sobolev Dirichlet-form domain;
- equality of `optimalPoincareConstant` with the reciprocal of a separately defined generator
  spectral gap;
- the dossier's statement that the optimal constant is the supremum of all Rayleigh quotients;
- Gaussian exactness, mode-indicator bottleneck bounds, or any numerical test-function search;
- `thm:glm-fi`, Bakry--Émery, Otto--Villani, or any other node in the shared dossier; or
- a coordinate-matrix equality theorem beyond the proved centered quadratic-form identity.

## Handoff

```yaml
outcome: revise
artifacts:
  - research/reviews/2026-08-29-lean-linear-test-independent-semantic-audit.md
proposed_deltas:
  - none
next_role: prover
next_prompt: |
  Repair solutions/glm-linear-baselines.tex:43-68 by stating the finite-second-moment probability
  hypothesis, defining the admissible smooth L2 finite-energy class and exact zero-energy quotient
  convention, and either assuming D>=1 or defining the D=0 covariance maximum as zero. Preserve
  the +infinity optimal-constant case and the centered covariance calculation. At
  solutions/glm-linear-baselines.tex:6-14, preserve historical agent provenance while expressing
  current certification per node, including the node-specific Lean artifact for
  lem:linear-test-lower and agent review for thm:glm-fi. Do not edit any existing review. Return
  exact manuscript proposals for modules/01-definitions.tex:17-25 and
  modules/02-results-toolkit.tex:108-117; the manuscript owner applies them. Return an exact ledger
  statement proposal for research/a-series/ledger.yaml:89; only the orchestrator applies it. Do
  not claim smooth-core/Sobolev or spectral-gap equivalence. Recompile the dossier and Lean target,
  then request a new cold semantic audit in a new append-only report.
```
