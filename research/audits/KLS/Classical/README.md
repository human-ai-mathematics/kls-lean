# Classical KLS specification gate

This gate checks that the proved `FunctionalInequalities.KLS.kls` and BKL Theorem 1.1 yield the classical
formulations of the KLS conjecture. The formulations are written independently, with Mathlib only.
[Specification.lean.in](Specification.lean.in) states three formulations without any project definition:

| Statement | Formulation |
| --- | --- |
| `CovarianceNormalizedSmoothKls` | One `C > 0` for all dimensions and all log-concave probability laws (compact-set Borell inequality): every smooth `L²` test with integrable squared gradient has `Var f ≤ C ‖Cov μ‖_op ∫ ‖∇f‖²`, with Mathlib's covariance Riesz operator |
| `IsotropicLocallyLipschitzKls` | One `C > 0` for all dimensions and all log-concave laws with raw mean zero and identity second moments: every locally Lipschitz `L²` function has `Var f ≤ C ∫ ‖∇f‖²` (extended real; the energy may be infinite) |
| `UniformConvexBodyKls` | The same inequality for the normalized Lebesgue law of every compact convex body of positive volume, with its density written literally and the same raw isotropy equations (mean zero, identity second moments) |

[Client.lean.in](Client.lean.in) proves the three statements from the library:
- `RawLogConcave ↔ KLS.LogConcave` holds by `Iff.rfl`;
- isotropy is derived from the raw moment equations;
- `KLS.kls` gives the covariance form;
- `KLS.BKL.Localization.exists_isotropicBound` gives the locally Lipschitz form;
- the uniform convex-body law is proved log-concave before use.

Both templates are byte copies of the second independent review's sources. Their SHA-256 values are pinned in
[config.json](config.json), which also names the review record of their provenance and semantic review.

## Gate

`research/verify.py` runs [check.py](check.py) as the `classical-kls` gate after the research-audit sweep, in the full and
`--lean-only` modes, with the filtered fresh view of the run. The gate:

1. checks both templates against their pins (a change needs re-review and an explicit config update; nothing is refreshed
   automatically);
2. checks, after removing nested comments and strings:
   - the specification imports Mathlib only, names no project declaration, and uses no `sorry`, `axiom`, `opaque`,
     `unsafe` or metaprogramming escape;
   - the client imports only the specification, project modules and `Lean`;
3. compiles the specification to an `.olean` and then the client, both with `-DwarningAsError=true`;
4. requires exactly the four configured axiom reports, each with only `propext`, `Classical.choice` and `Quot.sound`;
5. replays both runtime modules with `leanchecker`;
6. applies three mutations, each of which makes a statement false:
   - dropping log-concavity;
   - dropping the gradient energy;
   - a strict inequality.

   Each mutated specification must compile, and the unchanged client must then fail with that mutation's configured
   elaboration error in the client file: `Application type mismatch`, `Type mismatch`, or a `change` that is not
   definitionally equal to the target, as calibrated from the first preserved run. Linter, warning-as-error, syntax,
   import, unknown-name, tool and resource failures never count.

Its summary is the `classical_kls` field of the receipt. To run it by hand from the repository root with the receipt's
search path:

```bash
python3 research/audits/KLS/Classical/check.py --root . --lean LEAN --lean-path PATH --out build/classical-kls-manual
```

## Trust boundary

The gate checks source compilation and the client's consumption of the library. It relies on Lean, its kernel replay and
the pinned compiled Mathlib imports. It is not an independent kernel, not a rebuild of Mathlib or every dependency, and not
an automatic certification that the Lean statements match the English formulations: that reading is the reviewed
correspondence summarised in the statement table above and named in `config.json`.

## Public entry review

The isotropic client calls `KLS.BKL.Localization.exists_isotropicBound` for BKL Theorem 1.1.
The client pin accepts precisely the replacement of the former source-numbered callee by
that name. Its elaborated type, universal constant order, positivity, dimension range and
client argument/proof text are retained. The Mathlib-only specification and its pin, expected
axiom reports, mutation definitions and calibrated rejection kinds are unchanged. The checker
must still compile and replay the specification/client and reject all three mutations.
