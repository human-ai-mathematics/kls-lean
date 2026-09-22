# The heat-flow test class `ψ = P_s φ` for the weak `Γ₂` inequality

2026-09-22, after the interior-regularity round (`2026-09-22-interior-regularity.md`). The task
of this round is to extend the unconditional heat-flow weak `Γ₂` inequality
`HeatSemigroup.integral_mul_weakGamma_apply_nonneg` from nonnegative `C_c^∞` test functions to
`ψ = P_s φ`, `φ ∈ C_c^∞` nonnegative, `s > 0`, so that the `Γ` time interpolation can use it. It
preserves all earlier work, makes no commit or push and does not upgrade Lean/Mathlib.

## 1. Placement plan (recorded before editing)

| Item | Object and role | Destination | Decision |
| --- | --- | --- | --- |
| `H0` Markov bounds for `ψ = P_s φ`: `ψ ≥ 0` a.e., `|ψ| ≤ sup|φ|` a.e., `ψ ∈ D(A)`, `A ψ = P_s (A [φ])`, `|A ψ| ≤ sup|ℒφ|` a.e. | properties of the concrete heat semigroup on smooth data | `KLS/LogConcave/HeatSemigroup/TestClass.lean` | **create**: `Markov.lean` owns the abstract Markov properties, `Domain.lean` the domain statements; the smooth-datum specialisation with `L∞` bounds is a new responsibility that both `Γ₂` frontends consume |
| `H1` integrability of `∫ (Aψ) Γ(T̄F, T̄F)` and `∫ ψ Γ(T̄F, T̄(AF))` for `F ∈ D(A)`, `AF ∈ D(T̄)` | pairing of an a.e. bounded class with an `L¹` weak `Γ` | same module | uses `WeakGamma.integrable_mul` |
| `H2` the weak `Γ₂` inequality with **every** a.e. nonnegative test `ψ ∈ D(A)` for smooth compactly supported `F = [f]` | substantive theorem, the pointwise `Γ₂ ≥ 0` in integrated form with a general test | same module | uses symmetry of `A` and `adjointComp_toLp_eq` |
| `H3` transfer along **second-order** graph convergence `T̄[fₙ] → T̄F`, `T̄(A[fₙ]) → T̄(AF)` for a bounded test with bounded `Aψ` | transfer theorem with explicit convergence hypotheses, in the pattern of `GammaTwo.lean` | same module | uses `WeakGamma.tendsto_integral_mul` |

Dependency direction: `TestClass → {GammaTwo, Markov}`; no cycle. No existing statement is
changed. Validation: strict compilation of the new module and of a new audit
`research/audits/BakryEmeryHeatTestClassAudit.lean`, axiom audit, default `lake build`, root
`research/verify.py` on the final snapshot.

## 2. Takeover plan and incoming evidence

The incoming `TestClass.lean` contains four strictly compiled order/Markov lemmas only;
H0's generator bound, H1, H2, H3 and the requested arbitrary-input heat theorem were absent.
The incoming source hashes and patch are saved under `build/audit/heat-test-class-takeover/`.
Continue in the existing owning module, without renaming existing declarations: prove the
bounded generator and integrability interfaces, then the nonnegative generator-domain test
inequality on smooth compactly supported data. A two-field limit theorem is an explicitly
conditional intermediate, not completion of the heat-test extension. In particular, the
first-order operator core does not supply convergence of the gradients of the generator images.
Validation includes strict source/client compilation, axiom reports and a final source receipt.

## 3. Delivered results and remaining target

**The full round target is not complete.** The incoming four lemmas now form part of a
12-theorem module. The takeover adds:

- `ae_abs_adjointComp_operator_le`: essential bounds on `Af` are preserved under heat flow,
  using generator commutation. This permits arbitrary weights.
- `exists_bounds_operator_toLp`: for a smooth compactly supported initial test and a `C¹`
  potential in the current model, both `P_s φ` and `A(P_s φ)` have essential bounds uniform in
  every `s ≥ 0`. These bounds are proved, not assumed. No convexity of the potential is added.
- `integrable_operator_toLp_weakGamma`: both target integrands are integrable for arbitrary
  `L²` vector fields. This applies in particular to `T̄(P_r g)` and `T̄(A(P_r g))`, using the
  already proved positive-time domain statements. Integrability does not prove the inequality.
- `integral_adjointComp_mul_toLp_eq`: generator symmetry against a smooth compactly supported
  function, with the sign `A = -ℒ`, without differentiating a representative of the test.
- `integral_gammaTwo_nonneg_of_mem_domain` and
  `integral_weakGamma_nonneg_of_mem_domain`: integrated Bochner for **smooth compactly supported
  data** and **every nonnegative test in `D(A)`**, without a compact-support or smoothness
  assumption on that test. Products are integrable because the smooth factors are in `L²`.
- `integral_weakGamma_nonneg_of_mem_domain_of_tendsto`: transfer when **both** gradient fields
  converge in `L²`, for bounded tests with bounded generator image. This theorem retains those
  explicit convergence hypotheses and is not an unconditional heat-data theorem.
- `integral_weakGamma_operator_test_nonneg`: the smooth-data inequality with the actual evolved
  test `P_s φ`, including `s = 0`. Nonnegativity of the test follows from the Markov property.

The new independent audit tests essential-bound preservation, both actual integrands,
the negative generator sign, the new inequality on the actual closed-gradient fields of
smooth data, and the zero initial test. It prints axioms for all 12 public library theorems
and all five clients.

## 4. Why the remaining limit is not an existing core theorem

For arbitrary `F = P_r g`, the two-field transfer would be finished by constructing smooth
compactly supported `f_n` and their canonical field classes such that

```
[∇f_n] → T̄F,     [-∇(ℒ f_n)] → T̄(AF)     in L²(ν; V).
```

This is a sufficient remaining obligation for this route, not a claim of logical equivalence
to the target. The proven operator core yields `[f_n] → F` and `A[f_n] → AF`; it does not give
the second displayed convergence. The distinction is genuine even for positive diagonal
operators: on `ℓ²`, take `A e_n = n² e_n`, `T e_n = n e_n` and `f_n = n⁻³ e_n` (`n ≥ 1`).
Then `f_n → 0` and `Af_n → 0`, but `‖T Af_n‖ = 1`. This observation rejects an implication
about a supplied graph-approximating sequence; it does not rule out a better sequence.

The current repository's form-core theorem approximates in the graph norm of `T̄`, and its
operator-core theorem in the graph norm of `A`. Neither provides the displayed two-field
approximation. Smooth compact tests are stable under the differential expression for smooth
`U`, but invariance alone has not been turned into the required higher-order core theorem.

Two other possible routes require additional proofs as well:

1. Approximate `ψ` by nonnegative smooth compact tests with sufficient uniform bounds on both
   the tests and their generator images. Plain `L²` graph convergence is inadequate for pairing
   the latter with `Γ(T̄F,T̄F) ∈ L¹`. Such bound/positivity-preserving approximation is not proved.
2. Use the generator-form inequality to avoid `T̄(Af_n)`. For a general `ψ`, this also requires
   the product rule on the relevant nonsmooth domain and control of
   `∫ (Af_n) Γ(T̄f_n,T̄ψ)`. Existing `L²` control of `T̄ψ` alone does not justify that product
   limit. No bound on `T̄(P_s φ)` or gradient estimate is assumed silently.

No existing local or pinned-Mathlib interface located in this review closes these obligations.
The missing higher-order approximation/alternative test extension remains unproved. Time
interpolation, its endpoint limits, gradient estimates, general-law passage, π-Buser and KLS
remain open. Certificates stay 26; the deliberate target hole is unchanged.

## 5. Validation scope

Strictly compile `TestClass.lean` and the independent
`research/audits/BakryEmeryHeatTestClassAudit.lean`, build the aggregate, and run the full
`research/verify.py` after all source/documentation edits. The final snapshot pointer lives in
`build/audit/heat-test-class-takeover/final-snapshot.json`, outside the source snapshot.
No commit, push, toolchain upgrade or modification of the real Git index is part of this work.
A passing receipt verifies the delivered **partial** statements, not the unresolved full target.

Evidence refresh: the incoming run had corrected the obsolete `GammaTwo.lean` module prose
and translated the interior-regularity record's table header. Their stored infrastructure
hashes had not followed those documentation changes. After inspecting the current statements
and these corrections, the two hashes were refreshed; no proof status was changed by that
refresh. The new `TestClass.lean` source is also recorded as evidence of partial progress.

The new module and five audit clients pass strict compilation; all 17 printed axiom reports
use only `propext`, `Classical.choice`, and `Quot.sound`. Automatic implicit parameters are
disabled in both new files. The default build passes (3580 jobs), with the pre-existing single
intentional `KLS/Target.lean` hole. Atlas reports 75 nodes, 26 certificates and no cycles.
Progress views are generated through a temporary index and temporary object database; the
real index is byte-for-byte preserved. Final full verification is recorded only by the
snapshot pointer above, which also reports failure if the final gate does not pass.
