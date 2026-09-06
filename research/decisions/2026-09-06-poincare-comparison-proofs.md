# Poincaré comparison proofs and Fable review follow-up

**Date:** 2026-09-06 (Asia/Shanghai). **Scope:** the twelve reviewed comparison declarations,
their certificates, and the necessary Blueprint/documentation follow-up. Work is local on `main`,
based on `70ca1c19c4d207a31716c2e589c0b096521a5490`; no commit or publication is included.

## Authorization and retained statements

After reading the independent assessment of the Fable review, the repository owner instructed:
“可以，那就证明一下然后有需要的补上”. This authorizes proving the reviewed comparison batch and
implementing the supported corrections. The approved statement surface is the twelve declarations
recorded in `2026-09-06-poincare-comparison-statements.md`, with the same hypotheses and conclusions.
No new literature-facing interface is declared frozen by this proof acceptance.

The two comparison nodes now have complete proofs and named certificates and are recorded as
`proved / checked_by: lean`. The earlier drafted record remains unchanged. Only status prose was
removed from their ledger statements; the mathematical specifications were preserved.

## What is now proved

| Module | Conclusions |
| --- | --- |
| `Poincare/Relaxation.lean` | Arbitrary pre-energy fixed-constant equivalence and equality of extended optima |
| `Energy/Euclidean/AffineComparison.lean` | Smooth restriction, energy-preserving smooth extension, equality of ambient/intrinsic relaxations |
| `Poincare/Euclidean/AffineComparison.lean` | The corresponding finite-constant equivalence and optimal-constant equality |
| `Poincare/Euclidean/LegacyComparison.lean` | Raw test-domain identification and the four legacy/ambient/intrinsic comparisons |

The generic result applies to arbitrary measurable probability spaces and arbitrary finite
pre-energies on real `L²`. Empty test types and zero finite constants are included. The geometric
results apply to every finite-dimensional real Borel Hilbert probability, including singular laws,
proper affine support and dimension zero, without density or second moments. Optimal constants
remain in `ENNReal`, including infinity.

The named certificates package all five and seven conclusions, respectively:

- `Solutions.LemAmbientIntrinsicPoincareComparison.certificate`;
- `Solutions.LemLegacyRelaxedPoincareComparison.certificate`.

Both keep the existing typed application checks. In particular, the Gaussian inequality and exact
constant now transfer to the selected intrinsic-affine frontend, including zero variance. The
comparison modules are exported by `Poincare.Foundation` and hence the library root.

## Proof architecture

1. `L2.continuous_mean`, `continuous_center` and `continuous_variance` supply the actual continuity
   facts used at the limit. They do not depend on smoothness, density or a chosen energy.
2. A finite relaxed-energy point has a recovery sequence. Its finite raw energies converge in
   `NNReal`, since the limit is not infinity. Passing the concrete inequality to the limit proves
   the abstract forward implication, including `C=0`. Constant sequences prove the converse.
3. `ENNReal.eq_of_forall_le_nnreal_iff` identifies the two optima from their finite upper bounds.
   No duplicate order-theoretic API was introduced.
4. The geometric proof uses the chain rule and operator-norm contraction to control gradients
   under smooth, measure-preserving pullback. Its projection map is
   `x ↦ proj_V (x - supportPoint μ)`, and it agrees almost everywhere with the existing measurable
   intrinsic map. It is globally smooth. Reconstruction after restriction recovers an intrinsic
   test; the two energy inequalities then force equality for the constructed extension.
5. The new generic `PreEnergy.sequentialRelaxation_comp_le` transfers a continuous map with
   energy-nonincreasing concrete test lifts to the relaxed energies. It works on arbitrary
   topological spaces, including empty approximation classes; its proof maps each sequence and
   compares its energy liminf. Applying it to both coordinate directions gives exact equality.
6. The legacy bridge identifies the same concrete smooth finite-energy tests using the
   representative variance identity. For the optimal constant, valid finite constants are the
   finite upper bounds of the relaxed optimizer. When finite, its own `toNNReal` is such a bound;
   when infinite, the valid set is empty. No separate attainment or `C+ε` argument is needed.

The proof never asserts raw/relaxed equality for every concrete test of a singular measure.

## Fable review dispositions

- **Relative perimeter:** the unfrozen density Cheeger frontend now uses `∂U ∩ Ω` and the distinct
  notation `h^{sm,rel}`. It permits boundaries crossing the carrier boundary. The identification
  with outer Minkowski content and the cited density frontend remains explicitly `notready`.
  Restricting the whole boundary to `Ω` was rejected: on the uniform unit disk it excludes the
  half-space cut and changes the infimum. No Lean proof of the perimeter identification was added.
- **Factor 4:** the citation now explicitly names the 2018 preprint's equation (2.25), the
  Alonso-Gutiérrez–Bastero book p. 11, and the KLS attribution. A bibliography entry was added.
  The cautious wording is located in the subsequent spherical application. The book-page
  derivation and exact primary normalization have not been verified; the node remains `notready`.
  The fiber proof explanation records the general conditional `κ`-to-`κ C` transmission, while
  the existing `4` specialization continues to depend on its one-dimensional input.
- **CMH:** `thm:affine-covariance-relaxation-closed` is now `notready`. The source core is identified
  explicitly as restrictions of `ℝ + C_c^∞(V)`, completed in the `L² + Σ-energy` norm, in
  `kls-exploration@8185e46ffb040e04fea076953e5bcaeb4157d71a`,
  `modules/kls/41-cmh-normalization.tex`, lines 165–210. The required core comparison with globally
  Lipschitz relaxation is named; translation alone is not presented as its proof.
- **Blueprint navigation:** two mathematical helper nodes and two certificate nodes were added.
  All twelve comparison theorems and `TestFamily.ofPreEnergy` are now linked. The four original
  comparison nodes were updated with their proved status and complete corresponding conclusions.
  Certificate-to-ledger checks now cover all six certificates.
- **Proof route:** current documentation consistently describes the finite-point recovery route.
  The previous direct-liminf suggestion remains historical; it needs nonempty-index or nonzero
  multiplier conditions before distributing multiplication over an infimum at `C=0`.
- **Positive density:** the explicit positivity hypothesis was retained, with a note that real
  inversion in Lean maps zero to zero. Bounded reciprocal alone would not encode positivity.
- **Legacy closure/order helpers:** the purported mandatory separate closure argument was not
  introduced, and the existing Mathlib finite-upper-bound equality lemma was reused.
- **Old copies:** all four ` 2` files were preserved byte-for-byte. Their four exact paths were
  added only to local `.git/info/exclude`; no repository-wide ignore rule or deletion was made.
- **Current documentation:** HANDOFF, design notes, library guides and certificate guides now
  distinguish the six proved nodes from the still-open literature, Dirichlet and KLS interfaces.
  A documentation occurrence of “zero axiom” was changed to “zero field” in `ClosedQuadratic`
  after the existing conservative source-token guard flagged it. The underlying structure and
  guard were unchanged; kernel axiom checks independently confirm the proof dependencies.

## Validation evidence

The pre-edit working-tree snapshot and logs are in the temporary audit directory
`/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-comparison-proofs-4ihd39k7`.
The directory contains the original files, `RawSnapshot.lean`, `raw-after.txt`,
`declaration-comparison.json`, Lean/Blueprint build logs and rendered QA pages.

- Compared the elaborated types and universe parameter lists against the saved draft-batch audit:
  all 706 prior declarations retain their exact types and universe lists; none disappeared.
- The audited imported environment contains 735 local declarations. None has a nonstandard axiom
  dependency. All twelve former comparison placeholders now depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- The two new certificates have explicit `#guard_msgs` axiom checks. `FoundationAxiomAudit`
  now guards 22 declarations, including all twelve comparisons and the key continuity/transport
  helpers. These guards run in the default build.
- `lake build` completed successfully (3241 jobs), including all six certificates, both audit
  modules and the foundation examples. The comparison modules have no placeholder warnings.
- `check_ledger.py`: six nodes, zero errors. `check_blueprint.py`: seven chapter files, 77 labels,
  four active routes, zero errors.
- All 63 Python tests pass. Existing certificate tests now exercise each of the six mappings,
  missing-label cases, missing `leanok`, and uncertified ledger status.
- Blueprint PDF, web and `checkdecls` pass. The PDF has 27 pages, no overfull boxes, no unresolved
  references or bibliography warnings, and eight underfull warnings in existing provenance text.
  The changed proof, certificate and analytic-interface pages were inspected visually.
- `git diff --check` passes. The four previous certificate files and four old local copies are
  unchanged. No reset, commit or push was performed.

These results certify the comparison batch and its stated dependencies. They do not establish
the locally Lipschitz literature comparison, the Cheeger/perimeter bridge, Markov or Dirichlet
structure, covariance-core identification, the universal factor-4 input, or KLS itself.
