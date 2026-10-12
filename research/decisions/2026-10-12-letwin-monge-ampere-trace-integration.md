# Letwin (2.9)–(2.10) and the pointwise generator condition for a given potential

Date: 2026-10-12. Controller: Codex thread `01a12de4-2412-7082-ae33-15b1c3502420` (continuing the owner-authorized Goal).
Integrator: the sole reviewed Claude conversation, sequenced writer window AE (after AD; last proof batch of the cycle).

## Integration

Input: strong-API candidate `api-trace-monge-ampere-210-v3/candidate.lean` (gpt-6-astra, high; SHA-256 `de34b430…`; 35
constants, 30 authored and 5 generated). Strict compile, complete type/universe/axiom audit, candidate and TraceSupport
kernel replay and independent semantic review passed. The inventory field `fullname` was normalized as metadata only.
Its scratch import is a byte copy of the AB-adopted trace candidate; its references map to the AB names.

**Placement:**
- **Matrix tools: `Analysis/Matrix/Positivity.lean`.** `sum_entry_mul_nonneg`, `trace_mul_nonneg` and
  `traceGram_posSemidef`, in the candidate's variable context.
- **Monge–Ampère trace results: `Analysis/BakryEmery/HessianTrace.lean`, section `MongeAmpereTrace`.**
  - Fields `stdHessianConjugate` and `stdThirdGram`.
  - (2.9) as `stdHessianMatrixGenerator_apply_on_range` and `…_eq_on_range`, and (2.10) as
    `traceGenerator_210_on_range`.
  - The positivity facts, the three nonnegative remainders and `traceGeneratorCondition_on_range`.
- **Audit `research/audits/BKL/LetwinMongeAmpereTraceAudit.lean`.** The explicit interval-potential client and its
  helper `generator_const`.
- **Text changes.** Blocks are verbatim. The only text map replaces the candidate's `candidate*`/`actual*` names (code
  only).

**Comparison.** Pure compiled, all 35 constants: equal in kind, ordered universes, type and value under the explicit map.
- **Module map.** The module component of hygiene labels is replaced.
- **Renamed declarations.** For these, the exact hygiene-context map `h = (hash #[declId]).toUInt32` is applied.
- **`stdThirdGram.eq_1`.** This equation lemma is generated in the audit but carries the binder labels of its
  definition's module.
- **TraceSupport references.** Equal to the AB owners, with the private-rule closure mapped.
- **Old API.** The old Positivity constants and the AB comparisons are unchanged.

**Evidence:** `build/reviews/2026-10-12-bkl-letwin-t25-continuation/claude-ae-ma-trace-integration-v1/`.

**Not provided:** the potential and the local `V` are given. The pointwise condition is not integrated (A.4–A.5 for this
trace function). Also open: the tensor comparison (2.12) with the mean Hessian, the source trace bound, the moment map of
an arbitrary source law (existence, Euler–Lagrange, push-forward, regularity), Letwin Theorems 2.5 and 1.2, BKL and KLS.
Letwin T25 stays partial; no paper coverage or certificate count changes.
