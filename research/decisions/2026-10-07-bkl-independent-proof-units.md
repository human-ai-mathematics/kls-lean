# Independent proof units in the BKL formalization

Reviewed 2026-10-07 against Bizeul–Klartag–Lehec arXiv:2610.05474v1,
PDF SHA-256 `86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
The objective remains Theorem 1.1 with its whole verified dependency closure.
This is a source-based decomposition plan, not proof or coverage evidence.

Theorem 3.1 is already certified by the operator-domain route. The unproved
smooth representatives of Lemma 2.1 and exact first eigenfunction (19) are
not prerequisites of that accepted route, so they should not displace the
remaining main-theorem work. Proposition 7.1 is partial: its linear-function
step, continuity of the Taylor operator and convex potential (109)–(110)
are proved; the joint law, isotropy, (111)–(112), limit and density remain.

## Ready deterministic units

| Source | Exact unit | Existing support and missing interface | Main-proof consumer |
| --- | --- | --- | --- |
| (94), (105), p. 27 | For `b_m = K^(m-1)((m-1)!)^2`, `K >= 1`, `m >= 3`, `2 <= a <= m-2`: `choose(m-1,a-1) sqrt(b_a b_(m-a+1)) = sqrt(b_m)`; the sum over these `a` equals `(m-3) sqrt(b_m)`, including the empty sum at `m=3` | Mathlib choose/factorial identities, powers, square roots and finite sums; the source envelope and identity are missing | (104) to (106) |
| Final induction estimate, p. 27 | For `C >= 1` and `K >= max{5,9C,64}`: `2 C m^2 b_(m-1) + 4(m-3) sqrt(b_(m-1)b_m) <= b_m`, `m >= 3` | Factorial recurrence plus real inequalities; `b_m = K(m-1)^2 b_(m-1)` | Closure of (95), after the genuine Lemma 5.2 input |
| (99)–(102), p. 26 | Finite arrays: from `forall v, sum_j (sum_k v_k T(j,k))^2 <= b sum_k v_k^2`, derive `sum_i sum_j (sum_k S(i,k)T(j,k))^2 <= b sum_i sum_k S(i,k)^2` | Finite sum inequalities and the existing tensor coefficient arrays; a generic row-contraction estimate is missing | Core of (101)–(102); covariance whitening is a separate adapter |
| (112) and its norm consequence, p. 29 | For `d > 0`, the copy-block index embedding `(i,j) -> (k -> some(i,j(k)))` is injective; its selected squared coefficients have energy at most the whole Hilbert–Schmidt energy | Existing `Analysis/Tensor/{Coordinate,Coefficients,BasisChange}` and injective finite-sum reindexing | If (112) supplies each block as `d!/(sigma sqrt N) T`, derive `(d!)^2/sigma^2 * ||T||^2 <= ||kappa(e_0)||^2` |
| Limit after (112), (113), p. 29 | From the source scalar bound for every `beta > 0`, pass `1 + 2/beta^2` to 1 and retain the factor `b/(d!)^2` | Real limits at infinity; no convergence of the suspension laws is required for this scalar step | Taylor estimate on normalized affine-orthogonal functions |

The `K >= 5` threshold has a mathematical role: the base case follows from
(78) and the third-cumulant bound as `E_2(0) + (1/2) integral E E_3 <= 1+4`.
The bounds `K >= 9C` and `K >= 64` each absorb half of the induction estimate.
These arithmetic units do not prove Theorem 4.1 by themselves.

## Further independent interfaces

| Source | Unit and prerequisites | Boundary |
| --- | --- | --- |
| (72), (98), (104) | Group subsets containing the distinguished first slot by size `a`; their number is `choose(m-1,a-1)`. Reindexing the remaining slots preserves the weighted norm; use the actual L2 triangle inequality on time times probability | Retain the distinguished-slot convention; an extra factor 2 would change the source estimate. Needs the actual subset sum and an L2 adapter |
| (75), (77), (79), p. 21 | Affine transformation of cumulants under centering/whitening; identify the weighted tensor norm and deduce `sum_i H_i A^-1 H_i <= 8 A` from the third-cumulant bound | First use compact laws, which satisfy the current global-moment interfaces. General laws need local exponential moments. Positive-definiteness and whitening are explicit prerequisites |
| Deterministic drift differentiation in Lemma 4.3 | High-order Leibniz expansion of `1/2 D^m <v,A^-1 v>(0)` into `m kappa_m + L_m`, with `v = grad Lambda - grad Lambda(0)` and `A = Hess Lambda(0) > 0` | An independent deterministic identity; full Lemma 4.3 still requires the stochastic evolution (71) and justified spatial differentiation |
| (83)–(91) | Slot actions, congruence invariance and first/second derivatives of `F(A,T)=<T,(A^-1)^(tensor(m-1))T>`; the source bound `sum_i |Sigma_(H_i)T|^2 <= 8(m-1)^2 |T|^2` | Finite-dimensional matrix/tensor analysis can be extracted. Full Lemma 5.1 still needs the actual Ito formula and process hypotheses |
| Lemma 5.2, (93) to (92) | Vanishing boundary subsequence and the integrated limit for a nonnegative integrable energy | Integrability gives an appropriate sequence `T_j -> infinity` with energy tending to zero; it does not imply an ordinary limit at every time. The finite-horizon expectation-zero martingale step is separately stochastic |
| Proposition 7.1, (108) and p. 30 | Finite-copy mean/covariance, Laplace-noise normalization and variance; affine L2 projection and density of smooth bounded-Hessian tests orthogonal to affine functions | These are deterministic probability/Hilbert-space targets. Preserve the noise variance `2/beta^2`, `sigma^2=1+2/beta^2`, and final factor 2 |
| Proposition 7.1, (111)–(112) | Local exponential-moment differentiation near 0 and the mixed cumulant identity, including zero entries from distinct copy blocks | Laplace noise does not have all exponential moments. The current `contDiff_logLaplace` global hypothesis cannot be imposed on it |

## Genuine dependency direction

- Letwin Theorem 1.2 supplies BKL Lemma 4.2 and the matrix bound (79).
- Eldan's process (67) supplies (68)–(71), then Lemma 4.3.
- Lemma 4.3, (69), (79) and deterministic metric derivatives supply Lemma 5.1.
- Lemma 5.1 and its stochastic expectation justification supply Lemma 5.2.
- Lemma 5.2, contraction, subset grouping and factorial induction supply
  Theorem 4.1 for compact laws; approximation extends it to the full source statement.
- Theorem 4.1 supplies the actual cumulant premise of Proposition 7.1;
  Proposition 7.1 supplies Theorem 3.1's Taylor premise; regular approximation
  transfers the bound to the general law in Theorem 1.1.

## Dispatch and placement

Claude owns full Lean signatures, frozen contexts and integration. Send ready
nonoverlapping units to the existing Luna API; Codex reviews the source contract,
actual proof and axiom closure. Prefer the factorial/absorption batch, finite
contraction and the suspension coefficient-block batch while the local-moment
and joint-law interfaces are developed. An independent lemma must close an
actual source obligation, not assume its own conclusion.

BKL-specific envelope and induction results belong in `KLS/BKL/`; reusable
finite contraction and coefficient-selection tools belong in the existing
`Analysis/Tensor/` family. Keep local log-Laplace analysis in the owning generic
family. Record a placement plan before additions, use strict real clients and
retain all pending source statements in the paper register.

Letwin's proof is deterministic, but its moment-measure, Monge–Ampere, Stein
kernel and H^-1 prerequisites are substantial. Small isolated identities there
can support the BKL dependency; they do not discharge Letwin Theorem 1.2.
