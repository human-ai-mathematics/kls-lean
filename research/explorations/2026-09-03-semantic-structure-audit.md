# Semantic and mathematical structure audit

Date: 2026-09-03 (Asia/Shanghai).
Baseline: `main`, HEAD `4801ca958778ae02cc0d81fc7ec805a4e96a894c`, with the existing local changes.
Scope: the current ten reusable Poincare modules, aggregate import, three solution entry points,
ledger contracts, source comments, and mathematical dependency structure.

## Result

No incorrect Lean statement, missing necessary hypothesis, circular mathematical argument, or
ledger/statement mismatch was found. Three independent read reviews covered the definitions and
linear tests, binary upper bound, and transport/finite products. The primary review also checked
source correspondence and the distinction between implemented proofs and node acceptance.

One mathematical explanation in current documentation was incorrect and has been corrected.
Current handoff documents also incorrectly described the completed library proofs as placeholders;
those descriptions have been synchronized. No Lean file, public signature, proof, ledger field,
Lake configuration, or pre-existing decision/exploration record was changed by this audit.

The finite node remains `drafted` / `checked_by: null`. This audit is not a human freeze or acceptance.

## Corrected mathematical explanation

`LEAN_DESIGN.md` previously said that the covariance Rayleigh maximum might not be attained in
infinite dimension. That observation about general bounded self-adjoint operators does not apply
to the finite-second-moment covariance used here. The correct statement distinguishes the current
finite-dimensional Lean theorem from an infinite-dimensional result not yet formalized.

For a Hilbert probability with finite second moment, apply
[Blanchard--Bousquet--Zwald, *Statistical Properties of Kernel Principal Component Analysis*,
Theorem 2.1, p. 8](https://doc.ml.tu-berlin.de/publications/publications/BlaBouZwa06.pdf#page=8)
to the centered random vector. Its covariance is positive and trace-class. Compact self-adjoint
spectral theory therefore gives a maximizing eigenvector on a nontrivial Hilbert space; the zero
operator is immediate. The zero-dimensional convention remains separate. This mathematical
correction does not require a stronger Lean theorem or any change to Issue #2.

The existing `LinearTest.lean` comment correctly says that no infinite-dimensional attainment
theorem is claimed by the implementation; it was not changed.

## Checked mathematical chain

| Layer | Required meaning and checked argument |
| --- | --- |
| Definitions | `Admissible` is global smoothness, L² and integrable squared canonical gradient. `Holds` includes probability and a nonnegative finite real constant. `constant` is the `ENNReal` infimum over finite valid `NNReal` constants. |
| Linear lower bound | Linear tests have constant gradient; `MemLp id 2` supplies their admissibility and identifies the centered covariance quadratic form with variance. The certificate retains that moment hypothesis and allows dimension zero. |
| Binary geometry | `WithLp 2 (E × F)` has the sum-of-squares norm. Ordinary products occur only in measure/Fubini and continuous-linear representations. The pushforward law has the intended normalization. |
| Binary analysis | Global smoothness restricts to every section; L² and finite energy restrict a.e. All real-integral comparisons and exchanges retain integrability. Total variance and Jensen yield the sum of coordinate variances, then the larger factor constant times full energy. |
| Coordinate reverse bounds | `∇(f ∘ q) = q* (∇f ∘ q)` uses pointwise differentiability. The isometric adjoint preserves energy; measure preservation gives the factor law, L² and variance. Both factor probability assumptions are explicit. |
| Finite geometry | `PiLp 2 E` uses the Hilbert norm. Reindexing sends source `j` to target `e j`. The local Option split has `(none, tail)` order and explicitly swaps Mathlib's `(tail, none)` measure decomposition. |
| Finite upper bound | Empty/Option induction uses zero on a subsingleton and the accepted binary maximum bound. Dependent isometries transport laws and inequalities. `Finset.univ.sup C : NNReal` has the correct recurrence and is cast to real only afterward. |
| Optimal equality | Coordinate tests give each lower bound. If the finite supremum of factor infima were below the product constant, each factor would supply a finite valid constant strictly below it; their finite maximum contradicts the fixed upper bound. No infinite constant is converted to real. |

The empty index has a single empty vector, not an empty carrier. Its law is a probability and its
constant is zero. Singleton families, arbitrary mixed zero-dimensional families, all-zero-dimensional
families and infinite factor constants are covered by the current typed application checks and
general statements. No positivity of dimension, moment, density or finite optimum is added to
tensorization.

The following distinctions remain essential:

- A probability product does not imply normalized factors: `2 δ₀` and `(1/2) δ₀` give a probability
  product but cannot satisfy either factor's `Holds` probability field.
- Smooth energy on arbitrary Borel laws need not descend to L² equivalence classes. For `δ₀`, the
  zero function and `x ↦ x` agree a.e. but have energies zero and one. The current theorem does not
  identify its test domain with a closed Dirichlet or Sobolev domain.
- For a probability and the present finite-energy domain, the set of finite valid constants is
  closed and upward closed. A finite optimal constant is valid. The proof needs no assumption of
  this fact, and it does not assert an extremizing test function. These two kinds of attainment
  must not be conflated.
- The raw covariance API is totalized: Mathlib's `covarianceBilin_of_not_memLp` makes it zero
  without `MemLp id 2`. The raw `lambdaMax` is then zero, not an extended infinite covariance.
  Existing moment hypotheses and documentation protect the covariance lower-bound claim.

## Sources and structural follow-up

[BGL Proposition 4.3.1, pp. 185–187](https://www.hse.ru/data/2016/11/24/1113029204/bok%253A978-3-319-00227-9.pdf#page=201)
supplies the binary fixed-constant upper bound in its Markov-triple framework. The local proof
uses a.e. admissible sections rather than identifying its test domain with BGL's. The original
manuscript's [Theorem 3.4](https://github.com/numina-functional-inequalities/kls-exploration/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L59-L68)
states the product optimal-constant identity. Finite iteration, coordinate recovery, extended-real
and empty-family details are explicitly local realizations. LSI, conditional decompositions,
spectral-gap equivalence and the complete KLS product case remain outside the certified claims.

One nonblocking import improvement remains: `FiniteProduct/Geometry.lean` imports
`Product.Reverse`, which brings in the entire binary tensorization proof. Its direct mathematics
needs `prodMeasure` and Mathlib geometry/measure APIs. A later import-only cleanup can move the
theorem dependency to `FiniteProduct/Tensorization.lean`, preserving names and signatures. No
additional wrapper or module is needed. This audit leaves imports unchanged.

Some hypotheses can be weakened locally: the two pure L² section helpers need only `SFinite`
factor measures, and the optimal binary upper bound is automatically true for a
nonprobability factor under the current `constant` definition. These are optional generalizations,
not defects, and do not justify changing frozen interfaces. Factor probability remains necessary
for the reverse/equality claims.

The current `README.md`, `formalization/README.md`, `solutions/README.md`, `LEAN_DESIGN.md`, and
`NEXT_STEPS_CONTEXT_FOR_CODEX.md` now distinguish implemented library proofs from pending human
freeze/acceptance and a named finite-node certificate. Historical stages remain unchanged.

## Verification

- `python3 research/check_ledger.py`: 1 ledger, 3 nodes, 0 errors.
- `python3 -m unittest discover -s research/tests -p 'test_*.py'`: 24 tests passed.
- `cd formalization && lake build`: 2956 jobs, successful, no warnings.
- All 45 current candidate signatures reproduce `2026-09-03-finite-tensorization-signatures-v2.txt`
  byte-for-byte: SHA-256 `1dbb986f5764f752adb516ea108ff771cd6058021ade292da727b451f541ce66`.
- Transitive proof-dependency inspection covers all 45 candidate public declarations, both
  certificates, and seven additional foundational results. The only reported dependencies are
  `propext`, `Classical.choice`, and `Quot.sound` (some definitions use fewer or none).
- Hash comparison confirms all 14 Lean files, the ledger, Lake configuration, and all 22
  pre-existing decision/exploration files are unchanged during this audit.

No statement was frozen, no node was promoted, and no commit or push was made.

## Follow-up: geometry import boundary resolved (2026-09-03)

On the user's subsequent instruction to fix the structural issue, the three relevant import
blocks were adjusted without changing declarations, proofs or source comments:

- `FiniteProduct/Geometry` now imports `Product/Geometry` and explicitly imports Mathlib's
  `Analysis.InnerProductSpace.Adjoint`, retaining its existing PiL2 and product-measure imports.
- `FiniteProduct/Tensorization` imports finite geometry, `Product/Tensorization` and `Transport`,
  matching the binary upper bound and transport interfaces actually used in its proofs.
- `solutions/LemPoincareFiniteTensorization.lean` separately imports `Product/Reverse`, which
  supplies the binary reverse/equality part of this node's statement surface.

The geometry module's local import closure shrinks from eight modules to three (including
itself): `Basic`, `Product/Geometry`, and `FiniteProduct/Geometry`. The finite theorem module
no longer imports binary reverse bounds. All three solution entry points retain exactly their
previous local import closures. No new Lean module or forwarding declaration was introduced.
The current placement rules in `formalization/README.md` record this boundary.

Validation: geometry builds independently; the default `lake build` succeeds with 2956 jobs
and no warnings; the ledger checker reports zero errors; all 24 Python tests pass. All 45
candidate signatures remain byte-identical to the saved v2 snapshot and its SHA-256 above.
Direct text comparison confirms that only the three Lean import blocks changed. The ledger,
toolchain, Lake configuration, other Lean files, and earlier history remain unchanged; this
follow-up is appended to the existing audit record. No freeze, promotion, commit or push occurred.
