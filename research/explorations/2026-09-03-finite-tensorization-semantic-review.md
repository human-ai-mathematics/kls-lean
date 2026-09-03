# Finite tensorization: strict semantic review

Date: 2026-09-03 (Asia/Shanghai).
Node: `lem:poincare-finite-tensorization`, Issue #7.
Reviewed candidate: the 53 public declarations in
`decisions/2026-09-03-finite-tensorization-candidate.md` and their source definitions.
Current HEAD: `4801ca958778ae02cc0d81fc7ec805a4e96a894c`, branch `main`, with the existing local draft.

## Verdict and review scope

**No mathematical error or missing necessary hypothesis was found in the current candidate
signatures. No signature change is required by this review.** The concrete encoding maps,
main theorem directions, probability normalization, test-domain transport, finite induction,
extended constants, Euclidean boundaries, and ledger correspondence are semantically consistent.

This conclusion is based on direct mathematical review, inspection of the pinned Mathlib
implementations, and three independent review assignments: transport/binary reverse bounds;
finite geometry/tensorization; and ledger/Euclidean/source correspondence. The primary reviewer
also checked the definitions, the infimum logic and degenerate/singular-measure examples.
These were review agents, not proof agents. No new Lean proof was implemented.

The node remains **drafted / checked_by: null**. The 52 mathematical placeholders remain.
This review is neither a human statement freeze nor Lean proof certification. This entry is
append-only; the candidate, saved signatures, ledger, and earlier review records were not rewritten.

## 1. Exact semantic foundation

The unchanged `Basic.lean` defines:

- `Admissible μ f`: globally `C∞`, `MemLp f 2 μ`, and integrable squared canonical gradient.
- `energy μ f`: the real integral of that squared gradient.
- `Holds μ C`: probability of μ, `0 ≤ C`, and the inequality for every admissible test.
- `constant μ`: the `ENNReal` infimum of the finite `NNReal` constants satisfying `Holds`.

The new declarations use these definitions directly. They do not substitute a Sobolev domain,
a.e. equivalence classes of gradients, local Lipschitz tests, density assumptions, or a spectral
definition of the constant. The `MemLp` and energy-integrability fields protect both sides of
real-valued identities from relying on unintended totalized values.

## 2. Transport and binary reverse bounds

All 15 declarations in `PoincareTransport.lean` and all 9 declarations in
`ProductReverse.lean` were reviewed.

For a continuous real linear map `q : H →L[ℝ] K`, at a point where f is differentiable,

\[
D(f\circ q)(x)h
= \langle\nabla f(qx),qh\rangle
= \langle q^*\nabla f(qx),h\rangle.
\]

The gradient formula therefore has the correct direction and uses the Hilbert adjoint.
The pointwise differentiability hypothesis is explicit: no chain rule is asserted for the
canonical gradient's default value at a nondifferentiability point. If `q.adjoint` is an
isometry, its linearity implies preservation of the norm, so the squared-gradient identity
is exact, with no contraction factor and no dimension restriction.

`MeasurePreserving q ρ μ` supplies measurability and `ρ.map q = μ`. The target L² test
pulls back to an L² test. For an admissible target test, the squared-gradient identity and
target energy integrability give integrability of the lifted squared gradient. Global
smoothness follows from continuous-linear composition. The resulting variance and energy
identities are sufficient to apply the source Poincaré inequality to every target test.
No step presupposes admissibility of any section of a product test.

For a linear isometry equivalence e, apply the same calculus in both directions using
`e.symm`. This recovers global smoothness, L² membership and energy integrability in both
directions, even for singular Borel laws. The admissibility iff, fixed-constant iff and
optimal-constant equality under pushforward are consequently valid. This is a correspondence
under a geometric equivalence, not a claim that energy descends to arbitrary L² equivalence
classes.

The `WithLp 2` projections have adjoints `(v,0)` and `(0,w)`, whose Hilbert norms are the
original factor norms. Their laws are exactly μ and ν because **both factors are individually
probabilities**. The complete elaborated signatures retain both probability instances in the
projection laws, reverse `Holds` statements, optimal lower bounds, and binary equality.

That distinction is necessary. For example, `μ = 2 δ₀` and `ν = (1/2) δ₀` have a probability
product. Both factor `Holds` predicates fail their probability field; their constants as defined
here are infinite, whereas the product is a point mass with constant zero. Omitting separate
factor normalization would make the reverse assertions false. The candidate does not omit it.

Every finite valid product constant is then a finite valid constant for each factor. Existing
`constant_le` and `le_constant` give the optimal lower bounds; the accepted binary upper bound
gives equality. This argument remains valid when a valid-constant set is empty.

## 3. Finite Hilbert geometry and product laws

All 11 declarations in `FiniteProductGeometry.lean` were reviewed, including the concrete
linear maps inside the two isometry definitions, rather than treating their deferred norm
proofs as evidence.

- Mathlib's `PiLp 2 E` inner product is `∑ i, ⟪x i, y i⟫`, and its norm square is
  `∑ i, ‖x i‖²`. Its measurable structure is transported by `WithLp.ofLp`.
  `(Measure.pi μ).map (WithLp.toLp 2)` is therefore the intended dependent finite product law
  on the Hilbert carrier. The ordinary function space's maximum norm is not used for gradients.
- `PiLp.proj` is coordinate evaluation. Its adjoint is `PiLp.single`, which is norm preserving
  including zero-dimensional factors. `Measure.pi_map_eval` has the product of the other
  factors' masses as a coefficient; the declared factor probability instances make it one.
- The concrete `piCongrLeft E e` sends source coordinate j to target coordinate e j.
  Its application and pushforward statements use that same direction. Reindexing preserves
  the finite sum defining the squared norm.
- The concrete `piOptionEquivProd E` sends x to `(x none, fun i ↦ x (some i))` with both
  product levels equipped with the correct `WithLp 2` norm. Its squared norm is
  `‖x none‖² + ∑ i, ‖x (some i)‖²`. Its measure identity uses **none, tail** in that order.
  Mathlib's similarly named measurable equivalence uses **tail, none**. The candidate correctly
  identifies the need for a swap when using that API; its own map and conclusion are consistent.

The completeness, Borel and second-countability instances for the dependent Hilbert product
were also confirmed by rerunning the existing API probe. The empty product law is a Dirac law
on the unique empty function, as stated by Mathlib's `Measure.pi_of_empty`.

## 4. Finite upper bounds and optimal equality

All 10 declarations in `FiniteTensorization.lean` were reviewed.

The fixed-constant induction is closed under the supplied helper interfaces. The empty
product is a subsingleton Hilbert space, so `Holds 0` is valid. In the Option step, the
isometry/law bridge identifies the family with the binary product of the head and the tail;
existing `Holds.prod` gives the larger of the head constant and tail finite supremum.
`Finset.univ.sup C` in `NNReal` has precisely this recurrence and empty value zero. The
reindexing step preserves that supremum and transports `Holds`. The cast to real occurs
only after taking the finite `NNReal` supremum.

The coordinate lifting already reviewed gives fixed-constant recovery from the product.
Taking infima of finite valid constants gives each extended coordinate lower bound.

For the upper bound, write `S = ⨆ i, constant (μ i)` and `D = constant (piMeasure μ)`.
If `S < D`, then each factor infimum is strictly below D. The definition of infimum supplies
finite valid constants `C i` whose `ENNReal` values are below D. For a nonempty finite family,
their maximum is still below D; fixed-constant tensorization contradicts `constant_le`.
The empty family uses its valid constant zero separately. If `D = ∞`, each chosen constant
and their finite supremum are still finite. If `S = ∞`, the upper bound is immediate.
Thus no infinite value is converted to a real fixed constant. Combining both directions gives
the stated equality without using an attainment theorem.

## 5. Boundary and singular-measure checks

All 8 declarations and the typed applications in
`Project/PoincareFiniteTensorization.lean` were reviewed.

| Case | Semantic check |
| --- | --- |
| Empty family | The unique empty vector carries a probability Dirac law; all tests are constant, variance and gradient energy vanish; fixed and optimal constants are zero. No index nonempty premise occurs in either main theorem. |
| Singleton family | The indexed supremum equals the sole factor constant. The generic `Unique` and concrete `Fin 1` statements agree, including zero dimension. |
| Zero-dimensional factor | A subsingleton Hilbert space has only constant tests and constant zero. Such a factor contributes zero to the maximum; the remaining factors may have any dimensions. |
| All-zero-dimensional family | The product is itself a subsingleton, so both the Euclidean `Holds 0` and constant-zero conclusions are correct. |
| Infinite factor constant | A coordinate lower bound forces the product constant to be infinite. No finite-constant premise is introduced. |
| Singular laws | Coordinate lifts and invertible isometry transports remain valid because they use exact pushforward and pointwise smooth gradient identities. No density or moment bridge is used. |

An explicit infinite-constant example confirms the intended zero-energy behavior. For
`μ = (δ₋₁ + δ₁)/2` on the line, the smooth polynomial `f(t) = (3t − t³)/2` has values ±1
on the two atoms and derivative zero at both. It is an admissible test with variance one and
energy zero, so no finite constant works. Its lift to a normalized product has the same
variance and energy. The candidate's infinite-factor conclusion agrees with this example.

The actual Euclidean type checks cover arbitrary families, `(0,n)` and `(n,0)` binary
products, empty `Fin 0` fixed/optimal constants, zero-dimensional `Fin 1`, and two
zero-dimensional factors. The separate theorem `euclidean_zero_factor` concerns the value
of one factor's constant inside an arbitrary mixed family; the full product formula is the
already-declared generic Euclidean equality. No stronger mixed-family conclusion is silently
claimed for that one helper.

## 6. Clarification: attainment of a constant versus an extremizing test

This is a non-blocking clarification of phrases such as “nonattainment handling” in the
previous validation record. The mathematical signatures and core ledger need no change.

For the present definition and a probability μ, let

\[
S_\mu=\{C\in[0,\infty): \mathrm{Holds}\;\mu\;C\}.
\]

For each fixed admissible f, `Var(f) ≤ C energy(f)` is a closed condition on the finite real
parameter C, since variance and energy are finite real numbers. Their intersection is closed,
and energy nonnegativity makes it an upper set. If `constant μ` is finite, there is at least
one finite valid constant, so `S_μ` is nonempty and its finite infimum belongs to it.
Consequently **a finite optimal constant is itself valid under these definitions**.

Three different statements must remain separate:

1. The tensorization proof does not assume or invoke attainment of the infimum.
2. There may be no admissible extremizing function realizing the best Rayleigh quotient;
   no such function is asserted or required here.
3. A finite infimum of the present valid-constant set cannot fail to be a valid constant.
   If there is no finite valid constant, its `ENNReal` infimum is infinity.

The current ledger says only that no infimum-attainment assumption is imposed, and the design
says that no attaining witness is supplied; these are accurate. They should not be read as
claiming the existence of finite nonattained valid-constant infima. This observation is semantic
review only: no new attainment declaration or Lean proof was added, and the proposed proof
route continues to use finite approximants.

## 7. Proof API caution; no stronger hypothesis is needed

In pinned Mathlib, `MeasurePreserving.integral_comp` requires a `MeasurableEmbedding`.
Ordinary coordinate projections need not be injective, so that API must not be used by adding
an embedding hypothesis to the frozen interface.

The existing candidate assumptions are sufficient: use `integral_map` with the projection's
a.e. measurability, `hmap.map_eq`, and the energy integrand's `AEStronglyMeasurable` evidence
from `hf.energy_integrable`. Integrability pulls back with
`MeasurePreserving.integrable_comp_of_integrable`; L² membership uses
`MemLp.comp_measurePreserving`. Variance also has `MeasurePreserving.variance_fun_comp`.
This is an implementation caution, not a defect in the stated theorems.

Some purely geometric helper signatures carry stronger Borel/second-countability hypotheses
than mathematically necessary, and `Holds.pi` repeats probability data already implied by
its factor `Holds` assumptions. They agree with the requested ambient scope and do not make
any claim false; minimizing them is optional API design rather than a semantic correction.

## 8. Source and snapshot correspondence

BGL Proposition 4.3.1 was independently rechecked at printed pp. 185–187: it states the binary
upper bound with the larger constant in its Markov-triple/Dirichlet framework. The finite
iteration and independent coordinate reverse deductions are correctly distinguished in the
candidate. No arbitrary-Borel test-domain equivalence is attributed to BGL.
[Chapter](https://link.springer.com/chapter/10.1007/978-3-319-00227-9_4),
[full text](https://www.hse.ru/data/2016/11/24/1113029204/bok%253A978-3-319-00227-9.pdf#page=201).

The upstream correspondence remains the specific finite-product analytic ingredient described
in the preceding source audit; no full `prop:products` or KLS conclusion is claimed. The
independent contract reviewer could not refetch the private upstream/GitHub issue in this
turn because of network restrictions. The pinned upstream text and earlier successful fetch
are already available in the statement-stage record and conversation; no new remote-state
verification is asserted here.

The declaration entry point was rerun with `lake env lean`. Its 53-type output is identical
to the saved snapshot, and that snapshot is identical to the block embedded in the candidate
review package. SHA-256 including the final newline remains:
`26f387cbaaf2ce631c02dd79bfebf36f5514e922dd60bf8287fc7a690ac6aed4`.
The candidate ledger object is identical to the current ledger node. The statement-string
SHA-256 remains:
`61ff1d1a7e1258d7cc3e68dae5ebc8111fefb9ac4d4baab1e10b797c948366ab`.

No new Lean source, ledger status, signature, or definition was changed during this review.
No extra proof-completion claim follows from the elaboration check. Human statement review
and freezing, followed by an independent proof phase, are still required.
