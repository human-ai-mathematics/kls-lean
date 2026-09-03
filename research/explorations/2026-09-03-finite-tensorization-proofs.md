# Finite tensorization: proof completion for the 45 candidate declarations

Date: 2026-09-03 (Asia/Shanghai). Proof agent: Claude.
Node: `lem:poincare-finite-tensorization`, Issue #7 (sub-issue of #1).
Baseline: local working tree after the module re-layout and certificate deduplication
(HEAD `4801ca958778ae02cc0d81fc7ec805a4e96a894c`, uncommitted local state).

This is an append-only proof-stage record. It does not assert a human statement freeze and
does not change any ledger field. On direct user instruction in this session — check semantic
alignment with the sources and, if aligned, remove the placeholders — the semantic alignment
was re-confirmed against the existing
[semantic review](2026-09-03-finite-tensorization-semantic-review.md) and BGL Proposition 4.3.1,
and all 45 remaining `sorry` placeholders were replaced by complete proofs. No public signature,
definition, ledger statement, or checker rule was changed.

## Alignment re-check before proving

- `Poincare.Admissible`, `energy`, `Holds`, `constant` in `Poincare/Basic.lean` are unchanged
  and match `KLS.pdf` Definition 2.1 with the normalization `Var_μ(f) ≤ C ∫‖∇f‖² dμ`.
- The binary upper bound with the larger constant matches BGL (2014) Proposition 4.3.1; the
  reverse bounds and both optimal-constant equalities are the independent coordinate-lift
  deductions already identified in the design record, not attributed to BGL.
- Both factor probability instances remain explicit in every reverse/equality statement;
  `piMeasure`, `piCongrLeft` (source `j` to target `e j`) and `piOptionEquivProd`
  (**none, tail** order) are the frozen concrete encodings.
- No signature change was needed; no new public declaration was added. The only additions are
  `private` helpers, `set_option linter.unusedSectionVars false` (the deliberately unused
  ambient instances are part of the candidate signatures), and one local
  `linter.style.haveILetI` suppression for a definitionally transparent `letI` instance.

## Proofs by module

- `Poincare/Transport.lean` (15): chain rule `∇(f∘q) = q† (∇f ∘ q)` via `toDual_gradient`,
  `ContinuousLinearMap.adjoint_inner_left` and `hasGradientAt_iff_hasFDerivAt`; exact norm
  preservation from the isometric adjoint; L²/integrability/variance transport via
  `MemLp.comp_measurePreserving`, `MeasurePreserving.integrable_comp_of_integrable`,
  `MeasurePreserving.variance_fun_comp`, and `integral_map` (no `MeasurableEmbedding` is used);
  the isometry-equivalence transport derives both directions from the projection case with
  `LinearIsometryEquiv.adjoint_eq_symm`; subsingleton spaces via `variance_eq_integral` of a
  constant test.
- `Poincare/Product/Reverse.lean` (9): the adjoints of `WithLp.fstL`/`sndL` are computed by
  `ContinuousLinearMap.eq_adjoint_iff` as the zero-padded insertions, isometric by
  `WithLp.norm_toLp_fst`/`snd`; projection laws from `measurePreserving_fst`/`snd` (each using
  the other factor's probability) through `Measure.map_map`; `Holds.of_prod_left/right` by
  test lifting; `constant_prod_eq` combines the new lower bounds with the accepted
  `constant_prod_le`, which is unchanged.
- `Poincare/FiniteProduct/Geometry.lean` (10): `piMeasure` probability by pushforward; the
  adjoint of `PiLp.proj` is `PiLp.single` by `ext_inner_right` and `PiLp.inner_apply`,
  isometric by `PiLp.norm_single`; coordinate laws from `measurePreserving_eval`;
  the two concrete equivalences' `norm_map'` fields via squared-norm identities
  (`PiLp.norm_sq_eq_of_L2`, `WithLp.prod_norm_sq_eq_of_L2`, `Equiv.sum_comp`,
  `Fintype.sum_option`, `Equiv.piCongrLeft_apply_apply`); the pushforward identities reduce to
  `Measure.pi_map_piCongrLeft` and `Measure.pi_map_piOptionEquivProd`, with the (tail, none)
  order of Mathlib's measurable Option equivalence reconciled by `Measure.prod_swap` and
  `Measure.map_prod_map`, exactly as the design record required.
- `Poincare/FiniteProduct/Tensorization.lean` (11): `Holds.pi` by
  `Fintype.induction_empty_option` with a private motive quantifying over the dependent family,
  measures and constants; the equivalence step uses `piCongrLeft` transport and
  `Finset.sup_map`/`Finset.map_univ_equiv`; the empty step uses the subsingleton Hilbert
  product with valid constant zero; the Option step uses `map_piMeasure_piOptionEquivProd`,
  the accepted binary `Holds.prod`, and the `NNReal` sup recurrence over `Option`.
  `Holds.of_pi` lifts factor tests along `PiLp.proj`. `constant_pi_le` chooses finite valid
  approximants from each defining infimum via `iInf_lt_iff` and `Finset.sup_lt_iff`
  (no attainment, no `toReal` on `⊤`); `constant_pi_eq` combines both directions; the
  empty/unique/subsingleton/infinite-factor statements follow from the transport layer.

## Validation

From the repository root:

- `python3 research/check_ledger.py`: 1 ledger, 3 nodes, 0 errors.
- `python3 -m unittest discover -s research/tests -p 'test_*.py'`: 24 tests, OK.
- `cd formalization && lake build`: Build completed successfully (2956 jobs), with **zero**
  warnings — in particular no `sorry` warnings remain anywhere in the default targets.
- `grep` over `formalization/FunctionalInequalities*` finds no `sorry`, `admit`,
  `native_decide`, `axiom`, or `unsafe` token.
- Axiom audit (`#print axioms`) for `Holds.pi`, `Holds.of_pi`, `constant_pi_eq`,
  `constant_prod_eq`, `constant_map_linearIsometryEquiv`, `constant_pi_empty`,
  `constant_pi_unique`, `constant_pi_of_subsingleton`, `constant_pi_eq_top_of_factor`,
  `map_piMeasure_piOptionEquivProd`, and `Admissible.comp_projection`: each depends only on
  `propext`, `Classical.choice`, `Quot.sound`.
- Signature stability: rerunning the 45 named `#check @...` declarations under
  `pp.universes`/`format.width 100` reproduces
  `research/explorations/2026-09-03-finite-tensorization-signatures-v2.txt` byte-for-byte,
  SHA-256 `1dbb986f5764f752adb516ea108ff771cd6058021ade292da727b451f541ce66`. The full entry
  point additionally prints the unchanged 14 typed application checks, as before.
- The two proved nodes' certificates and their import closures are untouched; the binary
  `Holds.prod` and `constant_prod_le` proofs were not edited.

## Remaining workflow

The ledger node remains `drafted` / `checked_by: null`. Per `research/ledger-schema.md`, the
transition to `proved` requires the human acceptance step: a freeze/acceptance record, a named
node certificate in `solutions/LemPoincareFiniteTensorization.lean` referencing the reusable
library (replacing the draft `#check` entry point), and the ledger update. The mathematics for
that certificate is now fully proved in the library.
