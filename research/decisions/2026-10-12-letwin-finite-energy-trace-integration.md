# Letwin Lemma A.6 finite-energy supports and the trace identity (2.8)

Date: 2026-10-12. Controller: Codex thread `01a12de4-2412-7082-ae33-15b1c3502420` (continuing the owner-authorized Goal).
Integrator: the sole reviewed Claude conversation, sequenced writer window AB (after AA).

## Integration

Inputs (strong-API candidates, gpt-6-astra, high; each independently strict-compiled, type/universe/axiom-audited,
kernel-replayed and semantically reviewed):

| Candidate | SHA-256 | Declarations |
| --- | --- | --- |
| `api-finite-energy-bl-compiler-v6` | `cadc3b6c…` | 4 |
| `api-trace-nonconstant-client-v10` | `b37b32bf…` | 24 |

**Finite-energy supports.**
- **`compact_ordinary_diffusion_coercivity`** extends `Analysis/BakryEmery/Curvature.lean`, with its private
  compact Hessian-square integrability helper. For `μ = m.tilted (−U)`, `U` of class `C²` and `u` smooth with
  compact support, `∫ ∇²U(∇u, ∇u) dμ ≤ ∫ (ℒu)² dμ`, with both integrability conclusions, for the ordinary weighted
  Laplacian.
- **`inverse_quadratic_young`** extends `Analysis/Matrix/Positivity.lean`: `2 v·w ≤ v·H⁻¹v + w·Hw` for positive
  definite real `H` over any finite index type.
- **Placement.** Both are in reopened namespace blocks with the candidate's verbatim variable context. That
  context is unused by the statements, but it fixes the accepted universe name `u_2` of `inverse_quadratic_young`
  and the hygiene counters.
- **Client.** The `Fin 2` client is in `research/audits/BKL/LetwinFiniteEnergyAudit.lean`.

**Trace identity (2.8).**
- **Module.** The new `Analysis/BakryEmery/HessianTrace.lean` holds `StdBasisIndex`, `stdHessianMatrix`,
  `stdHessianMatrixDeriv`, `stdHessianMatrixGenerator`, the theorem
  `hessianInverseOperator_trace_stdHessianMatrix_sq` and seven private operator rules.
- **Name map.** The candidate placeholder names `candidateN/H/T/LH`, `traceProductGenerator` and `candidate_*`
  are replaced by an explicit map, the only change to the proof text.
- **Client.** The quartic client is in `research/audits/BKL/LetwinHessianTraceAudit.lean`.

**Comparison** (pure compiled, all 28 candidate constants):
- **Finite-energy.**
  - Kinds and ordered universes are equal.
  - Types and values are equal after replacing only the module component of hygiene labels, with one exception:
    the proof value of `compact_ordinary_diffusion_coercivity` uses a different proof of the `Prop` instance
    `IsOrderedModule ℝ ℝ`. The candidate's `instIsOrderedModule` comes from `Mathlib.Algebra.Order.Star.Basic`, in
    its larger import set; canonical uses `IsStrictOrderedModule.toIsOrderedModule`.
  - The values are equal once that single instance subterm is replaced on both sides.
- **Trace identity.**
  - Equal under the module map plus the declaration-context hash map. Lean names each declaration's hygiene
    context `<module>.<h>._hygCtx` with `h = (hash #[declId]).toUInt32`, so the name map determines `h` exactly.
  - Client constants are equal under the module map alone.

**Evidence:** `build/reviews/2026-10-12-bkl-letwin-t25-continuation/claude-ab-diffusion-trace-integration-v1/`.

**Not formalized:** Brascamp–Lieb itself, Lemma A.6, the substitution of Lemma 2.4, (2.10), the tensor comparison and the
trace bound of Theorem 2.5, the moment map, Letwin Theorems 2.5 and 1.2, BKL and KLS remain open. Letwin LA6 and T25 are
partial; paper coverage and certificate counts are unchanged.
