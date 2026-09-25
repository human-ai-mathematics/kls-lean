# Arbitrary heat data: resolvent range and higher-order core review

## Delivery and placement

**The full heat-test extension is still unproved. This round adds no Lean theorem.**
This is a mathematical route review, not a proof or a type-checked candidate. The previous
round's four approximation/smoothing theorems are preserved, not counted as new progress.

Placement recorded before editing: the object is the missing two-field approximation for
the unit-weight tilted-law heat semigroup. This dated decision owns the route analysis;
update the handoff, task note/gap, root summary and progress source description. No production
module, import, public API, hypothesis or certificate changes. Do not add a conditional
density/transfer interface in place of the missing analytic proof. Revalidate the inherited
modified sources and clients, then run the complete build/verifier. These checks cannot
certify the informal arguments in this record.

Incoming dirty files and both Git diffs are saved in `build/audit/heat-test-extension/baseline/`.
The manifest records HEAD, the real-index hash and dirty-file hashes; `source-snapshot.json`
records the complete source snapshot. The old approximation receipt's report hash and snapshot
were checked. The incoming source snapshot equals its recorded
`612bba5863f5be0a256b27d22e462c99708885bd3fad64c1b462377c58358e36`.
That receipt has `full_target_completed: false`; it cannot verify this round's added documents.

## Exact endpoint and existing Lean boundary

Keep the finite-dimensional real inner product space with its Borel structure and Haar
measure `m`, full-dimensional log-concave probability law `ν = m.tilted (-U)`, unit weight,
and smooth convex `U` on the whole space. Set `T = closedWeightedOperator`,
`A = adjointComp T = -ℒ`. For every `g ∈ L²(ν)`, `r > 0`, `s ≥ 0` and nonnegative
`φ ∈ C_c^∞`, put `F = P_r g`, `ψ = P_s[φ]`, `u = TF`, `w = T(AF)`.
The target is integrability of `(Aψ) Γ(u,u)` and `ψ Γ(u,w)`, and

```
0 ≤ -(∫ (Aψ) Γ(u,u) dν)/2 + ∫ ψ Γ(u,w) dν.
```

**There is no new theorem name or Lean signature for this endpoint.**
`integrable_operator_toLp_weakGamma` already proves both integrabilities;
`BakryEmeryHeatApproximationAudit.arbitrary_heat_pairings` supplies the actual heat fields.
`integral_weakGamma_operator_test_nonneg` still requires smooth compactly supported data;
`integral_weakGamma_nonneg_of_mem_domain_of_tendsto` still requires both field limits.
The existing `test_time_zero` client uses `integral_mul_weakGamma_apply_nonneg` and the a.e.
generator identification to obtain the displayed sign at `s = 0`; `zero_test` proves
vanishing at every test time. None is a client of the missing full frontend.

The field witnesses are `mem_closedWeightedOperator_domain_of_pos`,
`mem_adjointComp_domain_of_pos`, and `mem_closedWeightedOperator_domain_adjointComp_of_pos`.
The test witness uses `toLp_mem_adjointComp_domain` and `preserves_domain`. No arbitrary
representative of an `Lp` class is differentiated. No core/regularity premise belongs in
the desired frontend.

## Resolvent route: reduction and precise obstruction

The calculations in this section are **informal**, not new Lean results. Write
`E = D(T)` with `‖h‖_E² = ‖h‖² + ‖Th‖²`, `X = {F ∈ D(A) : AF ∈ D(T)}`,
`J F = F + AF` and `R = (I+A)⁻¹`.

For `h ∈ E`, the resolvent gives `Rh ∈ D(A)` and `A(Rh) = h - Rh ∈ E`, hence `Rh ∈ X`.
Existing inputs are `mem_adjointComp_domain_resolventDomain` and
`resolvent_add_smul_adjointComp` in `Analysis/Semigroup/VonNeumann.lean`, and
`norm_map_resolventDomain_le` in `Resolvent/Limit.lean`. Weak-equation uniqueness gives
`R(JF) = F`. Applying the two contractions to differences gives

```
‖Rδ‖ ≤ ‖δ‖,       ‖TRδ‖ ≤ ‖Tδ‖,
‖ARδ‖ ≤ 2‖δ‖,     ‖TARδ‖ ≤ 2‖Tδ‖.
```

Therefore, **if** `h_n = J[q_n] → JF` in `E` with `q_n ∈ C_c^∞`, then `[q_n] = Rh_n`
converges to `F` with both required fields. The equality `[q_n] = Rh_n` uses the actual
`adjointComp_toLp_eq` and resolvent uniqueness; it does not say that `R` preserves compact
support. Smoothness of `U` gives `-ℒq_n ∈ C_c^∞`, so its closed gradient is `[-∇ℒq_n]`.

The density assertion remains the substantive step. In fact the form identities give

```
‖JF‖_E² = ‖F‖² + 3‖TF‖² + 3‖AF‖² + ‖TAF‖²,
```

using `⟨F,AF⟩ = ‖TF‖²` and `⟨TF,T(AF)⟩ = ‖AF‖²`. Since
`‖TF‖² ≤ ‖F‖‖AF‖`, `J : X → E` is a linear bijection with continuous inverse for
the requested three-term graph norm on `X`. Density of `J(C_c^∞)` in `E` is equivalent
to this **stronger** core property of `X`. It is not claimed necessary for the weaker
two-field-only approximation or for the heat-test inequality.

The attempted orthogonal-complement proof stops at a specific mismatch. For `z ∈ E`
form-orthogonal to `J(C_c^∞)`, smoothness of `U` gives `J[q] ∈ D(A)`, hence

```
0 = ⟨z,J[q]⟩ + ⟨Tz,T(J[q])⟩ = ⟨z,(I+A)²[q]⟩.
```

This is a fourth-order distributional equation. The existing
`toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal` instead requires
`⟨z,(I+A)[q]⟩ = 0`. Substituting `(I+A)z` for its `L²` argument is invalid:
`z ∈ D(T)` does not imply `z ∈ D(A)`. Extending the displayed identity using the known
`A` graph core is also unjustified, since it contains `A²[q]`. New regularity and global
uniqueness at this order are needed. This does not disprove the density assertion.

## A separate external route, not implemented

Consider the first-order symmetric scalar/vector block on compact smooth pairs,

```
D(f,v) = (-div v + ⟨∇U,v⟩, ∇f).
```

Weighted integration by parts gives symmetry. Conjugation by `sqrt(ρ)`, where
`ρ = exp(-U)/Z`, gives the Haar-space off-diagonal operators
`∇ + (∇U)/2` and `-div + ⟨∇U,·⟩/2`. The potential enters at order zero. For a scalar cutoff,

```
[D,χ](f,v) = (-⟨∇χ,v⟩, f ∇χ),
‖[D,χ](f,v)‖² ≤ ‖∇χ‖² (|f|² + ‖v‖²).
```

Thus the propagation-speed bound does not require global bounds on higher derivatives
of `U`. Chernoff's theorem on powers of symmetric first-order systems is a relevant
external input: [original publication](https://doi.org/10.1016/0022-1236(73)90003-7).
Its velocity condition and general-system scope are discussed in
[Bandara and Saratchandran, §3.4](https://arxiv.org/pdf/1606.06190).
This scalar/vector block is generally **not elliptic** in dimension greater than one;
an elliptic-only theorem cannot replace the general-system result.

Here is the reduction that the external core theorem would support. Identify the block
closure with the self-adjoint block built from the repository's closed `T` and `T†`.
Then `(F,0) ∈ D(D³)` exactly for `F ∈ X`, and
`D(F,0) = (0,TF)`, `D²(F,0) = (AF,0)`, `D³(F,0) = (0,TAF)`.
A compact smooth pair core for `D³` gives pairs `(q_n,v_n)` converging to `(F,0)` in that
graph norm. Convergence for `D` and `D²` follows from symmetry:
`‖De‖² ≤ ‖e‖‖D²e‖` and `‖D²e‖² ≤ ‖De‖‖D³e‖` for errors `e ∈ D(D³)`.
The scalar components then supply precisely the two required fields.

This is an **external-theorem reduction**, not a local formalized route. Searches in the
repository and pinned Mathlib found no Chernoff theorem, appropriate finite-propagation
evolution theorem, or block-power core API. The weighted block closure identification
also has not been formalized here. These steps were not completed; no external result
is installed as an axiom or a frontend assumption.

## Alternative limits and remaining work

Test approximation still needs nonnegativity, uniform bounds on the tests and generator
images, and convergence suitable for pairing with the fixed `L¹` fields. The `L²` graph
core supplies none of these bounds or positivity. As an informal diagnostic on `(0,1)`,
`a_n = n^(1/4) 1_(0,1/n)` tends to zero in `L²`, but
`∫ a_n(x) x^(-3/4) dx = 4`. An `L²` limit alone cannot justify an arbitrary fixed `L¹`
pairing. This example is not a new Lean result.

For the generator-form route the specific missing limit is
`∫ (Af_n) Γ(Tf_n,Tψ) dν`. Three `L²` factors need not have an integrable product.
The compact-multiplier theorem bounds both the multiplier and its gradient;
boundedness of `ψ` and `Aψ` supplies no such bound on `Tψ`. Neither the necessary
nonsmooth product rule nor its limit was obtained. No circular gradient estimate is used.

The minimum sufficient remaining statement for the original transfer is still a sequence
`q_n ∈ C_c^∞` with `[∇q_n] → T P_r g` and `[-∇ℒq_n] → TA P_r g` for every `g ∈ L²`,
`r > 0`. Resolvent-range density is a stronger sufficient target, still unproved.

## Verification boundary

The new receipt is `build/audit/heat-test-extension/final-snapshot.json`; inspect its
outcomes and snapshot rather than inferring success from this pointer. It distinguishes
revalidation of inherited proofs from this documentation-only delivery. No final-frontend
client can be instantiated. Local source compilation, independent-client elaboration and
local-module kernel replay trust pinned third-party compiled imports. No fresh replay of
those imports, external checker or remote CI is claimed. Certificates remain 26; Buser,
KLS and the intentional target hole are unchanged. No commit, push or dependency upgrade.
