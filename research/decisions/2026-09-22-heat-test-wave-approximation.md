# Heat-test extension: wave averages and finite splitting

## Status, placement and provenance

**This is a mathematical exploration record. None of the new constructions or estimates below
has been proved in Lean. The arbitrary-data heat-test frontend remains open.**

This records the discussion following the
[earlier route review](2026-09-22-heat-test-extension-route.md), including the subsequent
comparison with the literature and the refinement from exact waves to finite splitting.
The earlier record is preserved as history; its fourth-order orthogonality obstruction does
not invalidate the new approach. Statements labelled as constructions or calculations below
are informal mathematics, not public Lean declarations or audited clients.

Placement recorded before editing: the mathematical object is form-range density for the
unit-weight tilted-law generator, used to obtain genuine smooth compact two-field approximation.
Create this dated decision and add a current entry to `HANDOFF.md`; preserve earlier decisions.
Dependencies are the existing form core, generator identification and two-field transfer, with
external wave theory distinguished from the proposed elementary construction. No module, import,
public API, task completion marker, certificate or progress status changes. Validation is limited
to links, the scoped documentation diff, whitespace and preservation of the incoming dirty tree.
The saved baseline and placement manifest are in `build/audit/heat-test-wave-route/baseline/`.

## Exact objective and notation

Retain the finite-dimensional real inner product space, Haar measure `m`, full-dimensional
log-concave probability law `ν = m.tilted (-U)`, unit weight and globally smooth convex `U`.
Write

```text
H = L²(ν),  T = closed gradient,  A = T†T = -ℒ,
ℒf = Δf - ⟨∇U, ∇f⟩,
E = D(T),  ‖f‖_E² = ‖f‖_H² + ‖Tf‖²,
X = {F ∈ D(A) : AF ∈ D(T)},  JF = F + AF.
```

For smooth compact functions, the classical expression is
`J_cl f = f - Δf + ⟨∇U, ∇f⟩`. Every use of `J` on such a function below must be connected
to the class-level `I+A` by the existing generator identification. No arbitrary `L²`
representative is differentiated.

The final target still quantifies over arbitrary `g ∈ H`, `r > 0`, nonnegative
`φ ∈ C_c^∞` and `s ≥ 0`. For `F = P_r g` and `ψ = P_s[φ]`, it asserts both integrabilities and

```text
0 ≤ -(1/2) ∫ (Aψ) Γ(TF,TF) dν + ∫ ψ Γ(TF,T(AF)) dν.
```

The remaining sufficient approximation is a sequence `q_n ∈ C_c^∞` with
`[∇q_n] → TF` and `[-∇ℒq_n] → T(AF)` in vector-valued `L²(ν)`.
The already formalized sequence `P_(r/2)[f_n]` is not such a sequence of compact functions.

## Literature and the choice of route

The sources inspected during exploration were:

1. M. A. Shubin, *Spectral theory of elliptic operators on non-compact manifolds*,
   Astérisque 207 (1992), Chapter 1, §3, printed pp. 47–48
   ([PDF](https://smf.emath.fr/system/files/filepdf/AST_1992__207__35_0.pdf)).
   The proof of Theorem 3.1 uses smooth wave evolution with common compact spatial support
   on bounded time intervals. The surrounding discussion relates this to powers and
   first-order symmetric systems. This is the main reference for the exact-wave input.
2. P. R. Chernoff, *Essential self-adjointness of powers of generators of hyperbolic
   equations*, JFA 12 (1973), 401–414
   ([DOI](https://doi.org/10.1016/0022-1236(73)90003-7)). The publication and abstract were
   located, but the full original paper was not obtained in this exploration. Do not attribute
   an unchecked exact theorem statement to it.
3. L. Bandara and H. Saratchandran, *Essential self-adjointness of powers of first-order
   differential operators on non-compact manifolds with low-regularity metrics*, §3.4
   ([PDF](https://arxiv.org/pdf/1606.06190)). This was used to check the discussion of
   Chernoff's propagation-speed condition. The scalar/vector block from the earlier record
   is generally nonelliptic; an elliptic-only theorem cannot simply be applied to it.

The recommendation evolved from “literature wave existence plus direct form-range density”
to “finite explicit splitting plus a residual-controlled time average.” Both use the wave
energy mechanism. The latter would avoid implementing a global wave group, a higher-power
self-adjointness theorem, spectral fractional powers, or an exact PDE solution limit.
This is a judgment about the mathematical interfaces, not a verified estimate of Lean effort.
The special constructions below are our deductions for this task; no novelty claim is made,
and they are not presented as quotations or theorem statements from these sources.

## First route: exact waves give form-range density

For `h ∈ C_c^∞` and every finite horizon `L > 0`, suppose we construct a classical smooth wave

```text
u_tt + J_cl u = 0,  u(0) = 0,  u_t(0) = h,
```

with a common compact spatial support throughout `[0,L]`. To use this route in Lean, existence
and that support statement must be proved for the actual coefficients, not supplied as new
assumptions in the heat-test frontend. Smoothness on a neighborhood of the closed time interval
suffices for all endpoint derivatives below.

With `ρ = exp(-U)/Z`, direct weighted integration by parts gives

```text
∂t {ρ (u_t² + |∇u|² + u²)/2} = div(ρ u_t ∇u),
‖u_t(t)‖_H² + ‖u(t)‖_E² = ‖h‖_H².
```

Compact support justifies integration. This uses no Γ₂ inequality, heat-gradient bound or
convexity estimate. The positive zeroth-order term in `J=I+A` controls `‖u(t)‖_E` uniformly
in the horizon; a bound growing exponentially in `L` would not serve the argument below.

### Orthogonality argument found first

If `z ∈ E` is orthogonal in `E` to `J(C_c^∞)`, let `a(t)=⟨z,u(t)⟩_E`.
Joint smoothness and common compact support imply differentiability into the form norm, so
`a''(t)=-⟨z,J u(t)⟩_E=0`, `a(0)=0`, and `a'(0)=⟨z,h⟩_E`.
Consequently

```text
t |⟨z,h⟩_E| = |a(t)| ≤ ‖z‖_E ‖h‖_H.
```

Arbitrarily large finite horizons force `⟨z,h⟩_E=0`. The existing form core gives `z=0`,
and the Hilbert orthogonal-complement criterion gives density. This avoids writing `Jz`,
which would be unjustified when only `z ∈ D(T)` is known.

### Direct time average, which supersedes that argument

Define a classical function

```text
q_L(x) = ∫₀ᴸ (1-t/L) u(t,x) dt.
```

Differentiating under this finite integral, with common compact support, shows `q_L ∈ C_c^∞`.
Two integrations by parts in time give

```text
J_cl q_L = -∫₀ᴸ (1-t/L) u_tt(t) dt = h - u(L)/L,
‖J[q_L] - [h]‖_E ≤ ‖h‖_H/L.
```

Thus one can construct the approximants directly, without orthogonal complements or a resolvent.
The exact-wave route is mathematically supported by classical hyperbolic theory, but no suitable
ready-to-use wave existence API was found in the local library or pinned Mathlib.

## Preferred refinement: finite splitting, without constructing an exact wave

The rest of this record is an informal construction and estimate derivation. Its analytic
identities and bounds remain implementation obligations, rather than assumed inputs.

### Explicit elementary flows and their support

Choose orthonormal coordinates on `V ≃ ℝ^d` and put `b=∇U`. For triples `Y=(u,v,p)`, consider

```text
ℬY = (v, div p - b·p - u, ∇v).
```

This is a different object from the self-adjoint scalar/vector block `D` in the older record.
Its coordinate flow `Q_j(t)` solves `v_t=∂j p_j`, `(p_j)_t=∂j v`, leaving `u` and the other
components of `p` fixed. Explicitly it translates `v+p_j` by `+t e_j` and `v-p_j` by `-t e_j`.
Its zero-order flow `R(t)` is

```text
u_new = cos(t) u + sin(t) v + (cos(t)-1) b·p,
v_new = -sin(t) u + cos(t) v - sin(t) b·p,
p_new = p.
```

Both formulas act on actual smooth functions. Let
`S(t)=R(t) Q_d(t) ... Q_1(t)`. Fix `N ≥ 1`, `δ=L/N ≤ 1`, and `Y₀=(0,h,0)`.
On `t=kδ+θ`, `0 ≤ θ ≤ δ`, use the continuous, piecewise smooth interpolation

```text
Y_δ(t) = S(θ) S(δ)^k Y₀.
```

At shared endpoints the definitions agree. If the initial support is `K₀`, all intermediate
flows on `[0,L]` have support inside `K=K₀+[-L,L]^d`. Each coordinate flow uses time `θ`
in its own coordinate; the support estimate must not be stated as a sharp Euclidean speed-one
estimate for the split scheme. A radius bound `√d L` suffices. The zero-order flow never
enlarges support. Every fixed-time function is smooth and compactly supported.

For estimates, one may first replace `b` by a smooth compactly supported coefficient equal to
`b` on a neighborhood of `K`. All derivatives of this auxiliary coefficient are globally
bounded. The constructed functions and their derivatives are supported where it agrees with
the original `b`, so the residual and weighted identities below use the original operator.
This auxiliary cutoff does not change the probability law or require a convex truncated
potential. It introduces no global derivative bounds on the original `U`.

For `d=0` the coordinate product is empty: only `R` remains, `A=0` and `J=I`.
No argument should divide by `d` or assume a nonempty coordinate set.

### Stability and consistency estimates to implement

For smooth compact triples, write
`|Y|_k² = ∑_{|α|≤k} ‖∂^α Y‖²_{L²(m)}`.
This notation is only a finite derivative norm on classical functions, not a new completed
Sobolev space. Use the Hilbert product norm on the triple.

Translation invariance of Haar measure and the orthogonal characteristic decomposition imply
`|Q_j(t)Y|_k=|Y|_k`. The explicit formula for `R`, Leibniz's rule and bounded derivatives of
the auxiliary coefficient give `|R(t)Y|_k ≤ (1+C_k t)|Y|_k` for `0 ≤ t ≤ 1`.
Iteration therefore gives

```text
sup_{0≤t≤L} |Y_δ(t)|_5 ≤ exp(C₅ L) |Y₀|_5,
```

uniformly in `N`. A first-order expansion of each elementary flow, with the integral Taylor
remainder, gives on one step

```text
|S'(θ)Y - ℬ S(θ)Y|_3 ≤ C θ |Y|_5,  0≤θ≤δ≤1.
```

One way to verify the derivative count is to write the coordinate generators as `M_j ∂j`.
Their mutual commutators have order at most two; commutators with the zero-order coefficient
have order at most one. Equivalently, bound both `S'(θ)Y-ℬY` and `ℬ(S(θ)Y-Y)` by the
first-order Taylor estimates. The constants use only finitely many bounded coefficient
derivatives. Combining with stability yields the residual bound

```text
e = Y_δ' - ℬY_δ = (e_u,e_v,e_p),
sup_{t away from grid nodes} |e(t)|_3 ≤ C_{h,L} δ =: η.
```

All time identities are proved on each cell and summed. The interpolation is continuous;
there are no jumps of `Y_δ` in these first-order integral identities. No convergence to an
exact wave, compactness theorem, Sobolev embedding, or completion of the derivative spaces
is needed. The local remainder and iteration estimates are substantive proof obligations;
merely declaring their types or packaging them as fields would not complete this route.

### Weighted energy and the gradient compatibility defect

The split scheme need not satisfy `p=∇u`. Track this explicitly instead of silently imposing it.
Set `d=p-∇u`. The residual equations and initial data give

```text
u' = v + e_u,
v' = div p - b·p - u + e_v,
p' = ∇v + e_p,
d(t) = ∫₀ᵗ (e_p - ∇e_u) da.
```

In particular, `|d(t)|_2 ≤ C L η`. Local equivalence between Haar and weighted norms on `K`
and the smooth coefficient bounds imply
`‖div d-b·d‖_E ≤ C_K |d|_2`. This explains the need for three derivatives of the residual:
two derivatives of `d` consume three derivatives of `e_u`.

For the actual triple, weighted integration by parts gives the forced energy identity

```text
(1/2) d/dt ‖Y_δ(t)‖²_{L²(ν;ℝ×ℝ×V)} = ⟨Y_δ(t),e(t)⟩_{L²(ν)}.
```

It holds even when `p ≠ ∇u`: the terms `uv` and `-vu` cancel, while the remaining principal
terms integrate as `div(ρ v p)`. Hence

```text
‖Y_δ(t)‖_{L²(ν)} ≤ ‖h‖_H + ∫₀ᵗ ‖e(a)‖_{L²(ν)} da,
‖u(L)‖_E ≤ ‖Y_δ(L)‖_{L²(ν)} + ‖d(L)‖_{L²(ν)}
         ≤ ‖h‖_H + C_K L η.
```

At a zero norm the first inequality can be obtained by differentiating the regularized norm
`sqrt(‖Y‖²+ε)` and sending `ε` to zero. Keeping the leading `‖h‖_H` term independent of `L`
is essential; the coarse unweighted stability bound alone would not give the desired result.

### Time average and the exact residual identity

For the finite construction define
`q_(L,δ)(x)=∫₀ᴸ (1-t/L)u_δ(t,x) dt`, interpreted as the sum of its `N` cell integrals.
Each cell integrand is smooth in space and time up to its endpoints. Differentiation under
the integral at every spatial order, on the common compact support, gives `q_(L,δ) ∈ C_c^∞`.
No time smoothness across grid nodes is required for this assertion.

Since `v'=-J_cl u+div d-b·d+e_v`, cellwise integration by parts gives the exact identity

```text
J_cl q_(L,δ) - h
  = -u_δ(L)/L + (1/L) ∫₀ᴸ e_u(t) dt
    + ∫₀ᴸ (1-t/L) (div d(t)-b·d(t)+e_v(t)) dt.
```

The internal endpoint terms cancel by continuity. Taking the form norm and using the previous
estimates yields, for a finite constant depending on `h`, `L` and local coefficient bounds,

```text
‖J[q_(L,δ)] - [h]‖_E ≤ ‖h‖_H/L + C_{h,L} δ.
```

Constants may grow arbitrarily fast with `L`. For prescribed accuracy, first choose a finite
large `L`, then choose a finite integer `N` large enough that `δ=L/N` makes the second term
small. There is no interchange of these two choices and no uniform-in-`L` coefficient hypothesis.
This supplies an informal constructive proof of

```text
∀ h ∈ C_c^∞, ∀ ε>0, ∃ q ∈ C_c^∞, ‖J[q]-[h]‖_E < ε.
```

It is not yet a Lean theorem. The estimates above must be implemented for the actual explicit
construction before this assertion can be used without additional premises.

## From this construction to the requested two fields

For any `F ∈ X`, `JF ∈ E`. Use the existing form core to choose `h_n ∈ C_c^∞` with
`[h_n] → JF` in `E`. Apply the construction with error less than `1/(n+1)` to obtain
`q_n ∈ C_c^∞` and `J[q_n] → JF` in `E`.

Smoothness of `U` implies `-ℒq_n ∈ C_c^∞`. The existing smooth generator and gradient
identifications put `[q_n] ∈ X` and give
`T[q_n]=[∇q_n]`, `T(A[q_n])=[-∇ℒq_n]`.
For `e=[q_n]-F ∈ X`, the form identities imply

```text
⟨e,Ae⟩ = ‖Te‖²,  ⟨Te,T(Ae)⟩ = ‖Ae‖²,
‖Je‖_E² = ‖e‖² + 3‖Te‖² + 3‖Ae‖² + ‖TAe‖².
```

Thus both required fields converge. This actually gives the stronger graph core on `X`.
The proof uses the domain and adjoint identities for `e`; it does not differentiate `e`
as a classical function, and it does not infer higher-order convergence from an arbitrary
given `A` graph approximation.

For `F=P_r g`, the required membership in `X` is already proved. For `ψ=P_s[φ]`, the existing
generator-domain membership, Markov nonnegativity and bounds on `ψ,Aψ` allow application of
`integral_weakGamma_nonneg_of_mem_domain_of_tendsto` after the new approximation is proved.
The existing integrability results apply to the two limiting fields. No bound on `Tψ` enters.
The final signature must keep all arbitrary-data quantifiers and acquire no wave, core,
residual, sequence, regularity or additional potential-bound premise.

## Local interfaces and implementation order

The relevant existing owners are:

- [WeightedGradient/Multiplier.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Multiplier.lean):
  `exists_seq_smooth_tendsto_graph` supplies the existing form core.
- [HeatSemigroup/Generator.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Generator.lean):
  identify the generator on constructed compact smooth functions.
- [HeatSemigroup/Domain.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Domain.lean):
  arbitrary positive-time data and the required domain witnesses.
- [HeatSemigroup/TestClass.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/TestClass.lean):
  bounds, integrability and the existing conditional two-field transfer.
- [Semigroup/VonNeumann.lean](../../formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean):
  the adjoint/form identities used in the final norm expansion.
- [Semigroup/Resolvent/Basic.lean](../../formalization/FunctionalInequalities/Analysis/Semigroup/Resolvent/Basic.lean):
  `graphL2` models the form Hilbert space. The inherited subtype topology on `T.domain`
  is the ambient `H` topology, not automatically the form topology; do not conflate them.
- [BakryEmery/IntegrationByParts.lean](../../formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts.lean):
  the classical weighted integration identities underlying the energy calculation.

The proposed order is: explicit elementary flows and common support; finite derivative
stability and residual estimate; forced weighted energy and compatibility defect; smoothness
of the finite time average and its error identity; actual form-range approximation; two-field
convergence and the unconditional heat-test frontend. Choose production module ownership under
`workflow.md` and `naming.md` before implementation; this record does not create future modules.

The minimum substantive analytic implementation target is the residual-controlled construction
of `q_(L,δ)`, with the stated error bound. Proving another conditional transfer theorem, or
declaring the stability/consistency estimates as hypotheses, would leave that target open.
After a real frontend exists, its client must instantiate arbitrary `g`, `r>0`, `s≥0`, check
`s=0` and the zero test, and audit the actual pairings and declaration axioms.

## Verification boundary for this record

This edit adds prose and a handoff entry only. No Lean source, client, public theorem, axiom,
certificate count, Buser status or KLS status changes. No source compilation, local kernel
replay, full build, verifier run or remote CI is performed for this documentation-only edit.
No commit, push or dependency upgrade is authorized or performed.

The preceding receipt `build/audit/heat-test-extension/final-snapshot.json` binds the incoming
snapshot `c5e98461a9e022df52603a86afc182d430aaeb7c97af2cba9860f3618016a18a`.
Adding this record changes the source snapshot; that receipt does not cover these new documents
or validate the mathematical route. Documentation-only checks and the delivered snapshot are
recorded separately in `build/audit/heat-test-wave-route/documentation-snapshot.json`.
They do not constitute a formal proof audit.
