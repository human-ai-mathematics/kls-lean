# Lean Poincaré semantic contract

**Date:** 2026-08-27 (Asia/Taipei)

**Branch:** `codex/issue-2-linear-test-lower`

**Ledger node:** `lem:linear-test-lower`

**Scope:** Phase C semantic repair only. No ledger edit, node certificate, covariance theorem, or
claim of Lean certification is made here.

## Why the first interface was insufficient

The initial `Basic.lean` used an arbitrary almost-everywhere Fréchet-derivative witness and a
real-valued energy built from that witness. It was formally sound, but three semantic bridges
needed by the manuscript were not definitions or theorems:

1. the manuscript quantifies over smooth $L^2$ functions, while the Lean predicate only required
   almost-everywhere differentiability;
2. the manuscript writes $\|\nabla f\|^2$, while Lean used the operator norm of an externally
   supplied derivative field; and
3. only finite real candidate constants existed, so the optimal value in $[0,+\infty]$ and the
   no-finite-constant case were not represented.

The relevant natural-language sources are
`modules/01-definitions.tex` (`def:poincare`),
`modules/02-results-toolkit.tex` (`rem:rayleigh-lower-only`), and the complete elementary proof in
`solutions/glm-linear-baselines.tex` (`lem:sol-linear-test-lower`). No research-level external
theorem is used by this basic vocabulary or by the linear-test argument. The
Bakry--Émery/Bakry--Gentil--Ledoux and Otto--Villani citations in the same dossier support the
separate Gaussian-prior GLM upper bound, not `lem:linear-test-lower`.

## Repaired contract

`FunctionalInequalities.IsAdmissible μ f` now records:

- `ContDiff ℝ ⊤ f`, the selected Lean meaning of a $C^\infty$ function;
- `MemLp f 2 μ`; and
- integrability of $x\mapsto\|\nabla f(x)\|^2$.

The last field makes the real-valued Bochner energy honest: Mathlib's integral is totalized on a
nonintegrable function, so omitting the field could silently turn an undefined/infinite energy
into zero. This module therefore uses the conventional finite-energy smooth core. It does not yet
claim a theorem identifying that core with a closed Sobolev-domain or spectral-gap definition.

The ambient space is now a complete real inner-product space. This is the hypothesis under which
Mathlib's Riesz map gives a canonical `gradient`. The theorem
`norm_fderiv_eq_norm_gradient` uses `toDual_gradient` and the isometry
`InnerProductSpace.toDual`; `dirichletEnergy_eq_fderiv` integrates the resulting pointwise norm
identity. Thus later Fréchet-derivative calculations can be used without changing the
manuscript-facing energy.

`HasPoincare μ C` still takes a finite candidate `C : ℝ`, explicitly requires `0 ≤ C`, and uses a
real inequality. The new `optimalPoincareConstant μ : ENNReal` is

```lean
⨅ C : {C : NNReal // HasPoincare μ (C : ℝ)}, (C.1 : ENNReal)
```

This direction is deliberate. `optimalPoincareConstant_le` gives that the infimum is below each
valid finite constant, while `le_optimalPoincareConstant` proves a lower bound by checking every
valid finite constant. If no finite constant exists, the indexing subtype is empty and the
infimum is `⊤`; `optimalPoincareConstant_eq_top_iff` records the exact equivalence. This avoids
the easy error of reversing an `sInf`/`iInf` inequality.

## Mathlib API findings and rejected probe forms

The final module uses:

- `Mathlib.Analysis.Calculus.ContDiff.Basic` for `ContDiff ℝ ⊤`;
- `Mathlib.Analysis.Calculus.Gradient.Basic` for `gradient`, `toDual_gradient`, and the Riesz
  isometry;
- `Mathlib.Probability.Moments.Variance` for `variance`, `MemLp`, probability measures, and the
  integral stack; and
- the complete-lattice `iInf` API plus `NNReal`/`ENNReal` coercions for the optimal constant.

The temporary semantic probe also recorded several dead ends:

- under these minimal imports, the pretty notation `∞` and `ℝ≥0∞` did not parse in the intended
  positions; `⊤` and the type name `ENNReal` are robust;
- the natural field names `smooth` and `contDiff` caused parser conflicts in the structure probe;
  `smooth'` compiled;
- the required integral congruence theorem is `integral_congr_ae`, not `integral_congr`; and
- rewriting under the integral lambda required first changing the pointwise goal so the
  gradient/Fréchet norm theorem matched syntactically.

## Validation

The following checks passed on the pinned Lean/mathlib `v4.33.0` project:

```text
cd formalization && lake env lean /private/tmp/kls-semantic-probe.lean
cd formalization && lake env lean FunctionalInequalities/Basic.lean
cd formalization && lake env lean FunctionalInequalities.lean
cd formalization && lake build
cd formalization && lake env lean /private/tmp/kls-basic-axioms.lean
uv run --with pyyaml python research/check_ledger.py
uv run --with pyyaml python -m unittest discover -s research/tests -p 'test_*.py'
rg -n '\bsorry\b|\badmit\b' formalization/FunctionalInequalities/Basic.lean \
  formalization/FunctionalInequalities.lean
git diff --check
```

The build completed all 2,942 jobs. The axiom audit reported only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorry` or `admit` occurs. The structural ledger check
reported 2 ledgers, 176 nodes, 642 labels, and 0 errors, and all 42 control-plane tests passed.

The first axiom-probe run intentionally remains part of the attempt record: it imported the old
cached `.olean` and therefore could not see the newly added declarations. Running `lake build`
refreshed the module artifact, after which the same probe passed.

## Remaining boundary

This repair stabilizes the reusable semantic layer but proves none of the target's covariance
content. The next proof step is to show that each linear projection belongs to this exact smooth
finite-energy core and has gradient energy $\|v\|^2$, under the target's finite-second-moment and
Borel hypotheses. A later semantic audit must still compare the resulting optimal constant with
any Sobolev-closure or spectral-gap formulation before claiming those formulations are Lean
equivalent.
