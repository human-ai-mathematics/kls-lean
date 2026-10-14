# Letwin task closeout and failure analysis

Date: 2026-10-13. Scope: the eight existing weak-route tasks supporting Letwin
arXiv:2607.24164v1 Theorem 2.5 and the compact version of Theorem 1.2, with its
constant 8. The owner requested that these tasks finish and then pause, and asked
for a distinction between mathematical obligations, Lean interfaces and task
decomposition. This record authorizes no new proof requests or retries.

All eight processes ended naturally. N11e (weak third-derivative symmetry) and
W3b2a (mollification preserves a closed convex range) returned candidates and
passed independent isolated compilation, frozen-statement clients and standard
axiom checks. The other six tasks did not pass acceptance. T10f, the previously
integrated conditional reduction from the regular class to compact laws, also
passed independent checking. These supporting results do not prove the regular
class bound, Letwin Theorems 2.5/1.2, unconditional BKL or KLS.

## Evidence and limits

The evidence root is
`build/reviews/2026-10-12-bkl-claude-goal/tasks/`. The independent closeout root is
`build/reviews/2026-10-13-codex-takeover/`; its `STATE.json` records terminal
process states and its `failure-analysis/DIAGNOSTIC-INVENTORY.json` records
frozen source hashes, histories and preserved diagnostics. Final-round candidate
files were compared with the Lean blocks in their recorded responses. Each of
the six current `Statement.lean` files is identical to the initialized frozen
source. The frozen declarations had elaborated successfully; a candidate's claim
that a frozen statement is malformed is not evidence of such a defect.

This is source and diagnostic review, not a proof of the six frozen statements.
No counterexample to those statements was established. The conclusions below
separate invalid candidate arguments from analytic bridges still needing a real
local Lean proof. The absence of that local proof does not establish a new gap
in the published mathematics. Error counts alone do not rank candidate quality:
an empty file or a changed statement can have fewer compiler errors than a
substantive attempt. In particular, LRF0 rounds 13 and 19 compiled comment-only
files; the declaration probe correctly rejected both as `MISSING`.

## Task assessments

| Task | Main obstruction | Assessment |
| --- | --- | --- |
| N10b, generator symmetry; 18 rounds | Construct the actual compactly supported Lipschitz product test, identify its a.e. derivative, establish integrability, then perform the finite matrix cancellations. | Missing analytic adapters and an oversized assembly task; the final candidate's zero-Lipschitz shortcut is invalid. |
| N13c, bounded compactly supported H1 tests; 18 rounds | Localize locally L2 coefficients, control the weak derivative outside a fixed compact neighbourhood, and pass L2 pairings to the limit. | A substantive density/localization bridge plus interface and decomposition problems. The last candidate replaced it with the false claim that bounded f is zero. |
| N14a, weak Brascamp-Lieb; 18 rounds | Connect weighted weak integration by parts, inverse-matrix energy estimates, the C1,1 Bochner identity and centered L2 duality. | The principal upstream Bochner and density results already exist. Their integration and energy bookkeeping remain incomplete; later candidates abandoned the valid route. |
| W3b2b, chain rule in the limit; 18 rounds | Localize the classical chain rule to the open target domain, remove a finite prefix of approximants, and prove both sides' local integral convergence. | Generic analytic interfaces and task decomposition, with genuine dominated-convergence/product-limit obligations still unproved locally. The final candidate does not contain those arguments. |
| R0, regular moment-potential package; 18 rounds | Identify the coordinate Hessian with the derivative of the gradient at Rademacher points and feed that local expansion into the a.e. Monge-Ampere result. | A weak-regularity identification bridge, not evidence that moment-map existence failed. The candidate incorrectly tried to promote C1 to C2. |
| LRF0, conditional final assembly; 20 rounds | Provide the positive-definite delta factorization, contraction of the middle factor, variance identification and Hilbert-Schmidt/trace limit. | Finite-dimensional algebra and interface assembly bundled too broadly. Claims about an unbound W in the original statement were unsupported; the last candidate changed hLR2 and used incorrect scaling. |

### N10b: Piola is available, but the product test was not constructed

The canonical prerequisite is
`Analysis/Matrix/Piola.lean`'s
`sum_integral_inv_hessianMatrix_mul_fderiv_eq`. It already accepts a Lipschitz
compactly supported test, so lack of a C1 test extension is not the obstruction.
The intended test is `eta * exp(-u) * partial_i w`, with the exchanged test for
the primed identity. It needs a real Lipschitz bound and the a.e. product/chain
rule, followed by integrable finite sums and `H^-1 H = 1`.

Round 7 applied Piola without supplying the test or its Lipschitz constant,
then cleared the resulting fact instead of assembling the identity. Round 18
set `Lpsi := 0` for arbitrary eta or w and used an index construction involving
`Fin.elim0` in arbitrary dimension. Compact support does not make a function
constant or zero-Lipschitz. Fixing elaboration around that argument would not
repair its mathematics.

Recommended future separation: product-test Lipschitz/support bounds; a.e.
coordinate derivative and inverse-Hessian integrability; finite matrix/trace
identification; then each integrated identity. Keep the frozen hypotheses.

### N13c: local L2 coefficients require support control

The actual premises give A and b in L2 on each compact set, not globally.
Mollifier derivative commutation and global L2 convergence are already available
in `Analysis/WeakDerivative.lean` and `Analysis/Mollification.lean`.

Round 17 attempted the correct mollification/L2-pairing route, but mixed local
and global measure interfaces, used `0 : Fin n` without handling n = 0, and
treated the product-rule derivative of `chi * f` as `S0.indicator g` without
proving their equality. The latter is a missing locality argument: `chi = 1`
on S0 and `f = 0` outside S0 do not by themselves justify replacing `chi * g`
outside S0. Round 18 instead asserted f = 0 a.e. from its bound and compact
support, which a nonzero smooth bump disproves as an intermediate claim.

Recommended future separation: bounded compact support implies f in L2;
derivative support/locality (or derive vanishing outside the fixed neighbourhood
from L2 convergence of the compactly supported mollified derivatives); uniform
compact support and derivative convergence of the mollifications; convergence
of pairings against locally L2 coefficients; final divergence identity.

### N14a: preserve the weak duality route

Canonical available ingredients include
`Analysis/BakryEmery/Bochner/Lipschitz.lean`'s
`integral_weightedLaplacian_sq_eq_of_lipschitz_gradient`,
`KLS/LogConcave/HeatSemigroup/Range.lean`'s
`centered_mem_closure_compactSmoothDiffusionImage` for a C1 potential, and
`Analysis/Matrix/Positivity.lean`'s `inverse_quadratic_young`.

Round 6 was a substantial attempt at weak weighted pairing and L2 duality.
Its errors include normalization expressed as `(-u) x` versus `-u x`, incorrect
coercion of a probability measure into a filter, and an unprovided coercivity
integrability fact. These require explicit adapters and proved energy bounds.
Applying the existing smooth scalar Brascamp-Lieb theorem would additionally
require unjustified C2 regularity, pointwise positive definiteness, and an
identification of the given weak derivatives with a classical gradient.

Round 18 called a nonexistent `not_integrable_exp_neg_of_lipschitz` to derive a
contradiction. The purported implication is false: on the line,
`u(x) = sqrt(1+x^2)` is smooth, convex and Lipschitz, and `exp(-u(x))` is bounded
by the integrable `exp(-|x|)`. An additive normalization constant preserves
these regularity properties. This is an invalid candidate route, not a missing
lemma name to supply.

Recommended future separation: normalized tilted-law/probability adapters;
weighted weak pairing for compact smooth tests; the a.e. Hessian/gradient
matrix bridge and integrated Young/Bochner estimate; centered L2 closure
duality. Retain weak derivatives and a.e. Hessian positivity in the contract.

### W3b2b: eventual compact range is not an all-index range

The fixed compact Q in the statement already supplies the bounds needed for
Phi and its derivative. The remaining proof must use them: the right-side
product difference splits into a bounded coefficient times `gm-g`, and a
coefficient difference times locally integrable g. The second term needs a
dominated-convergence argument. Classical integration by parts must be localized
to a neighbourhood of the test support because Phi is only C1 on open U.

The final candidate used `Eventually.self_of_nhds` on an `atTop` eventual
statement to claim every approximant takes values in Q. It also used constant
convergence in place of the supplied a.e. convergence, indexed g by
`Finset.univ`, and tried to close the weak integration identity by reflexivity.
Warnings and restricted-measure type errors are real secondary issues, but
correcting them would still leave the essential limit argument absent.

Recommended future separation: local composition measurability/integrability;
tail-index and open-domain localization; the two local L1 product limits;
localized classical pairing; final weak-derivative assembly.

### R0: use pointwise second derivatives at differentiability points

The final candidate obtains the bounded-source CEK potential, its C1 regularity,
the 16/kappa gradient Lipschitz bound, the open-set Alexandrov identity and a
second-order expansion. Those prerequisites are canonical in
`KLS/CEK/MomentMap.lean` and the Convex family.

It then tries `huC1.of_le` to obtain `ContDiff 2 u`. Smoothness monotonicity goes
in the opposite direction. C1 with Lipschitz gradient gives differentiability
of the gradient a.e., not global C2 as a consequence of those regularity facts
alone. A separate stronger regularity theorem cannot be assumed here.

The appropriate missing adapter is at a point where the gradient is
differentiable: identify `hessianMatrix u x` with `D(gradient u)(x)` in coordinates,
prove symmetry using C1 regularity and that pointwise differentiability, and
transfer the operator-norm bound to matrix positivity. The independently checked
N11e candidate contains private helpers for precisely this weak identification;
it does not yet expose a reusable public API or construct the moment potential.
`posDef_and_det_eq_of_quadratic_expansion` in `Viscosity.lean` can then consume the actual
quadratic expansion. This is a focused weak-regularity bridge to formalize on a
future authorized resume, followed by package assembly without a C2 premise.

### LRF0: the declaration is well formed; the algebra is still missing

The original frozen hLR2 has no unbound W, and the frozen source elaborated.
Rounds 13 and 19 returned only comments alleging otherwise; the name probe
correctly rejected them. Round 20 inserted new W/kappa/regular-class binders
into hLR2, which changes the frozen contract, and tried to derive a contradiction
by scaling B. In `tr(B H B H)`, replacing B by tB scales the expression by t^2,
not t^4. The right side `2 tr(B^2)` also scales by t^2, so this supplies no such
contradiction.

Recommended future separation: `M = A_delta S_delta A_delta` with A_delta
positive definite and `I-S_delta^2` positive semidefinite; regular-class
log-concavity and finite fourth moments; matrix/continuous-linear-map and
Hilbert-Schmidt trace identification; scalar delta-to-zero passage; only then
apply the four original hypotheses. This conditional assembly does not require
R0/LR1/LR2 to have been proved first, but it does require the intervening algebra.

## Workflow conclusion

The evidence supports a combination of missing local analytic interfaces,
oversized proof assemblies and deterioration into invalid candidate shortcuts.
It does not support attributing these six failures to a discovered defect in
Letwin's mathematical route. It also does not support describing the remaining
work as spelling or syntax alone: locality, integrability, limit exchange,
matrix identifications and duality must receive actual proofs.

For a future owner-authorized resume, retain useful substantive attempts (notably
N13c round 17, N14a round 6 and the R0 package), discard their invalid shortcuts,
freeze and independently check each small bridge before dispatching a larger
assembly. Stop repeated retries when the same logical step remains unjustified.
No recommendations in this record have been dispatched or implemented as new
proof work. The current closeout integrates only previously independently
accepted candidates and then pauses.
