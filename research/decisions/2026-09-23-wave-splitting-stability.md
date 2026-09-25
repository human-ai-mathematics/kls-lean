# Finite wave splitting: finite-order stability

## Placement and implementation

This continues the [energy construction](2026-09-22-wave-splitting-energy.md).
The placement plan was recorded in `HANDOFF.md` before editing; the incoming hashes and Git
diffs are in `build/audit/heat-test-splitting-stability/baseline/`.

- [Product.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/Product.lean)
  imports the existing energy definitions and proves the finite directional Leibniz expansion,
  its scalar square bound, and the integrated multiplication bound.
- [Stability.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/Stability.lean)
  uses that product bound to control the actual reaction, complete split step, grid iteration
  and smooth cell at every finite derivative order. The root imports this extension.

The existing explicit-flow and energy modules are unchanged. There is no migration or alias.
The two extensions have different responsibilities: scalar product calculus and integration,
then consequences for the concrete splitting state. No completed Sobolev space is introduced.

## Formalized in Lean

A finite word recursively differentiates along the given coordinate directions. Its equality
with the existing scalar evaluation of `iteratedFDeriv` is proved at every order. Each word
has exactly `2^n` Leibniz choices, retaining multiplicities, and each split distributes exactly
`n` derivatives between the factors. Cauchy--Schwarz gives a finite scalar square estimate.

Write `J_k(f,x)` for the sum of squared scalar derivatives over all ordered coordinate tuples
of lengths zero through `k`. Its integral is `scalarEnergy`; the equality with the finite sum
of the individual squared integrals is proved, including the integrability obligations.
If `B >= 0` and every coefficient derivative through order `k` has square at most `B`, then

```text
J_k(b f,x) <= q_k 4^k B J_k(f,x),
q_k = sum_{n=0}^k card(iota)^n.
```

The same estimate holds after integration for smooth compactly supported `f`. The coefficient
need not itself have compact support. Applying finite-sum Cauchy--Schwarz to `b dot p` gives
`J_k(b dot p,x) <= C_k sum_j J_k(p_j,x)`, where `C_k = card(iota) q_k 4^k B`.

For the existing ordered-coordinate state energy, the actual trigonometric reaction formula,
the product estimate, and Haar preservation of each coordinate sweep now imply

```text
E_k(R(t)Y), E_k(S(t)Y) <= (1 + (1+4C_k)t) E_k(Y),     0 <= t <= 1,
E_k(Y_j) <= exp((1+4C_k) j delta) E_k(Y_0),            0 <= delta <= 1,
E_k(cell_j(theta)) <= exp((1+4C_k)(j delta+theta)) E_k(Y_0), 0 <= theta <= 1.
```

These are proved estimates of the defined flows, not stability assumptions. They cover every
finite order, in particular five, arbitrary finite dimension including zero, and arbitrary
smooth compactly supported initial states. No nonempty, basis or orthonormality assumption is
needed. They remain energies; no equivalence with an unordered multi-index norm or a multilinear
operator norm is asserted. Constants are deliberately non-sharp and may depend on dimension.

Reaction and product estimates use only a measure finite on compact sets; split and iteration
estimates additionally require right-translation invariance. No probability normalization is used.

## Remaining obligations

The raw coefficient derivative bounds are explicit hypotheses of the generic stability theorem.
A localized smooth coefficient agreeing with the original potential gradient on the common
support has not yet been constructed. No such bounds have been added to the heat-test frontend.

Next construct the actual differentiated split residual and prove its third-order `C delta`
bound using the fifth-order stability established here, with the two derivative losses justified.
Coefficient localization is also required before applying the generic estimate to the original
potential. The weighted forced-energy estimate, gradient compatibility defect, residual-controlled
finite time average, form-range density and arbitrary-data heat-test frontend remain open.
The unweighted exponential-in-horizon estimate does not supply the horizon-independent leading
term needed in the later weighted energy argument. Buser and dimension-free KLS remain open;
route completion and ledger certificate count do not change.

## Validation and evidence

[WaveSplittingStabilityAudit.lean](../audits/WaveSplittingStabilityAudit.lean) checks the fifth-order
fixed-horizon estimate with `delta=L/N` for arbitrary compact smooth initial data, the interior
of each mesh cell, empty coordinates at arbitrary order, and the exact product formula at all
orders. Ten transitive axiom reports cover clients and key endpoints. No `sorry`, new axiom or
conclusion-bearing hypothesis package is used.

Strict source checks, a client against a separate current-module artifact view, and the full
library build are logged under `build/audit/heat-test-splitting-stability/`. The final project
verification outcome and exact source snapshot are recorded in `final-snapshot.json` there;
consult that receipt for the actual result. Pinned dependency artifacts remain trusted.
No remote CI, commit, push, or change to the real Git index is performed.
