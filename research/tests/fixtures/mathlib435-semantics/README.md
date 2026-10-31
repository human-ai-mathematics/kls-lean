# Mathlib v4.35 semantic-compatibility fixture

Validation input for the Lean/Mathlib v4.35.0 migration (owner: upstream-semantic compatibility
checks). It is not a library module, certificate or public API; the `.lean.in` extension keeps it
out of the repository's Lean sources.

[`SemanticPrimitives.lean.in`](SemanticPrimitives.lean.in) imports only Mathlib leaves and proves:

- `memLp_iff_baseline`: for every exponent `p` (including `0` and `∞`), v4.35 `MemLp f p μ` is
  equivalent to a.e. strong measurability together with finiteness of `baselineNorm`, the v4.33
  `eLpNorm` formula rebuilt from the unchanged primitives `eLpNorm'` and `eLpNormEssSup`;
- `gradient_measurable`: on a finite-dimensional real inner product space with its Borel
  σ-algebra, the gradient of an arbitrary real function is measurable;
- `potential_gradient_aemeasurable`: hence `gradient fun x => (ψ x).toReal` is a.e. measurable for an
  arbitrary `EReal`-valued potential `ψ` and any measure;

and prints the axioms of each (expected: `propext`, `Classical.choice`, `Quot.sound`).

Reproduce from `formalization/` after preparing the Mathlib cache: copy the file to a scratch
`.lean` path and run `lake env lean -DwarningAsError=true <scratch>.lean`.

Scope: primitive semantics only. It explains why the `MemLp` change preserves meaning and why the
measurable branches of the new `eLpNorm` and `Measure.map` apply to the project's gradient maps;
it does not certify any project endpoint or public interface.

## `LegacyInfinityNorm.lean.in` (Lean v4.33 correspondence)

Checked at the Formal Conjectures pin (toolchain `leanprover/lean4:v4.33.1`, Mathlib of that
checkout, whose `eLpNorm` definition is byte-identical to this project's previous Mathlib): it proves
the old formula `eLpNorm f ∞ μ = eLpNormEssSup f μ` for every real `f`, and that the original
statement of `eLpNorm_inverse_eq_inv_essInf` is equivalent to the explicit `eLpNormEssSup` form now
used in `Analysis/LpExponent.lean`. Reproduce inside that checkout: copy to a scratch `.lean` file and
run `lake env lean -DwarningAsError=true <scratch>.lean`. Scope: statement correspondence for this
one representation change; it is not a KLS theorem or a v4.35 norm identity.

## `ProbabilityMapBranch.lean.in` (Lean v4.35, `ProbabilityMeasure.map`)

Mathlib-only, for arbitrary measurable spaces: for an a.e.-measurable `f`, the underlying measure of
v4.35 `mu.map f` is exactly the a.e.-measurable branch of `Measure.map` (the branch the v4.33
`ProbabilityMeasure.map mu hf` used), and its value on measurable sets is unchanged. Reproduce from
`formalization/` as above. Scope: justifies the E4 call-site representation change (same function,
existing measurability witnesses kept); it says nothing about non-measurable maps and does not
certify any project declaration.

## `CadlagMeaning.lean.in` (Lean v4.35, càdlàg predicates)

Mathlib-only: the literal body of the previously vendored `IsRightContinuous` and the two fields of the
previously vendored `IsCadlag` (`right_continuous`, `left_limit`), restated under fresh audit-only names,
are equivalent to Mathlib v4.35 `IsRightContinuous` / `IsCadlag` (fields `isRightContinuous`,
`tendsto_nhdsLT`) for an arbitrary topological domain with a preorder and an arbitrary topological
codomain, with no further assumptions (axioms: `propext`, `Quot.sound`). Reproduce from
`integrations/openai/` (whose Mathlib cache contains `Mathlib.Topology.Order.Cadlag`) as above. Scope:
predicate meaning only; it does not certify field names, the `continuous_comp` argument order or any
other API row of the vendored module.

## `CadlagOldSignatures.lean.in` (Lean v4.35, E11 old-signature clients)

Imports Mathlib `Topology.Order.Cadlag` and the vendored `BrownianMotion.StochasticIntegral.Cadlag`.
For each of the 31 vendored declarations that E11 removed (29 now owned by Mathlib, plus the two old
projections `IsCadlag.right_continuous` / `IsCadlag.left_limit`) it states the old v4.33 signature as an
`example` — original binders, binder order and argument order, real scalar with `ContinuousSMul ℝ E` for
`const_smul` / `fun_const_smul`, no added hypotheses — and proves it from the Mathlib constant (new
argument order); `IsRightContinuous` and `IsCadlag` themselves are stated as equivalences. It adds no
declarations. Reproduce from `integrations/openai/` as above. Scope: shows the old API is recoverable
from Mathlib; it does not certify any project declaration.

## Hessian complete-type migration guard

`HessianOldTypes.json` and `HessianOldTypesEquality.lean.in` retain the seven old complete
types used to review the four hash-literal updates in `HessianIncrementAudit`.
[The extraction and trust-boundary review](HessianOldTypesReview.json) records the exact
input digest, pins, supported AST subset and old owned instance lineage.
Copy the template to an ignored `.lean` file, set `KLS_OLD_EXPRESSIONS` to the absolute
path of `HessianOldTypes.json`, and run `lake env lean -DwarningAsError=true <copy>.lean`
from `formalization`. Require exit zero, seven `KERNEL_TYPE_EQUAL` lines and
`SEVEN_LEGACY_TYPES_CHECKED`. Malformed array arities, missing/wrong names, failed type
comparisons or kernel errors fail the client. These extracted old-cache inputs do not
supply fresh old-source certification or global equivalence of imported Mathlib semantics.
