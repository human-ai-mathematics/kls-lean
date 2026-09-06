# KLS Blueprint freeze-review follow-up

**Decision date:** 2026-09-05 (Asia/Shanghai).

**Type:** Blueprint statement repair, reference alignment, and route-metadata correction.

## Authority and audited baseline

Work began from clean `main` at
`70ca1c19c4d207a31716c2e589c0b096521a5490`, with `origin` as the canonical remote and the
`legacy-fork` and `legacy-upstream` remotes treated as read-only.  The Lake package remains under
`formalization/`.

The phase-two task named
`research/reviews/2026-09-04-blueprint-mathematical-freeze-review.md` as its human-review source,
but that file is absent from the baseline, every reachable and unreachable local Git object, the
available attachments, and the local task history.  It was therefore not recreated or represented
as a completed human review.  After this absence was reported, the repository user explicitly
authorized direct Blueprint repair using the maintainer's judgment.  The detailed task list,
`HANDOFF.md`, the phase-one reference-alignment decision, the current Blueprint definitions, and
the cited primary literature form the evidence actually used below.

## Statement and dependency changes

### Orientation and status

- `def:log-concave-law` now gives the measure-theoretic Borell definition, including laws on a
  proper affine support.
- `thm:borell-logconcave-density` imports absolute continuity and a log-concave density on the
  affine support, together with finiteness of all moments; it has no `\leanok`.
- `def:literature-poincare-constant` refers to the relative interior of the convex support within
  the affine support.
- `conj:kls` explicitly uses `def:log-concave-law`.

### Open canonical bridges

- `thm:smooth-gradient-relaxation-two-cheeger` is unchanged and remains `\notready`; its prose now
  records the missing singular-measure slope/asymptotic-Lipschitz source.
- The placeholder `thm:smooth-gradient-raw-core-agreement` was replaced by
  `obs:normal-direction-raw-energy`, `q:smooth-gradient-raw-core-agreement`, and the explicit
  density proposal `thm:smooth-gradient-raw-core-agreement-density`.
- `thm:ambient-intrinsic-relaxation-equality` now states equality only after both energies are on
  the common ambient `L^2` carrier and explicitly covers proper affine supports and dimension zero.
- `cor:ambient-intrinsic-constant-equality` separates the induced equality of extended optimal
  constants from the energy theorem.
- A following paragraph records independence from the affine origin through translation isometry.

The density theorem uses the conservative hypotheses that the intrinsic density is positive on
the relative interior of its convex support and that both the density and its reciprocal are
locally essentially bounded.  Mere absolute continuity was not used as a substitute for a
closability/core hypothesis.

### Shared analytic bridges

- `thm:legacy-canonical-constant-comparison` now consumes the constant-level corollary.
- `thm:smooth-lipschitz-constant-equivalence` states the three equal constants for the ambient
  legacy law, the intrinsic law, and the locally Lipschitz frontend, under absolute continuity of
  the intrinsic law.
- `thm:selected-literature-constant-equivalence` explicitly consumes the log-concave definition
  and Borell's density theorem.
- `def:isoperimetric-cheeger-scale` now defines affine-support Minkowski boundary measure and the
  inverse scale with explicit extended and zero-dimensional conventions.
- `thm:logconcave-cheeger-poincare-comparison` is titled Cheeger--Buser and records the constants
  `4` and `pi` with the Milman, Bobkov, Klartag, and De Ponti--Mondino sources.
- `def:isotropic-law` makes centering, identity covariance, finite second moment, and dimension
  zero explicit.
- `thm:affine-isotropic-reduction` whitens only on the affine-support tangent space and is followed
  by the covariance-weighted, affine-invariant `C_P^aff` formulation.
- `thm:one-dimensional-logconcave-poincare` keeps its statement.  Its proof note records that the
  factor `4` appears in Cattiaux--Guillin's 2018 preprint equation (2.25), attributed there to KLS,
  whereas Bobkov's Corollary 4.3 supplies only `12` in this normalization.

The four 45-chapter nodes whose statements quantify over log-concave laws now use
`def:log-concave-law`: `thm:selected-literature-constant-equivalence`,
`thm:logconcave-cheeger-poincare-comparison`, `thm:affine-isotropic-reduction`, and
`thm:one-dimensional-logconcave-poincare`.

### References and route metadata

- The fixed keys `Klartag2023Logarithmic`, `DePontiMondino2021`, `Borell1974Convex`, and
  `CattiauxGuillin2018Poincare` were added with verified publication metadata.  The last key is
  retained as requested, while the entry records the published 2020 Lecture Notes in Mathematics
  version and its 2018 arXiv identifier.
- `targets[conj:kls].prerequisites` was renamed to `adapters`.  The checker, tests, and Blueprint
  README now treat this expression as repository-facing integration metadata, not logical
  premises of KLS.
- The pre-change checker did not require a `thm:selected-literature-constant-equivalence` TeX edge
  on `prop:spectral-sufficiency`, `cor:cmh-recovery-sequence-suffices`, or
  `lem:conditional-fiber-form`, so those three edges were removed.  Existing
  `thm:affine-isotropic-reduction` edges were retained.
- No field of the refuted `eldan-weighted-package-v1` branch was changed.

## Freeze state

No existing retained `\notready` marker was removed.  The marker on the replaced raw/core node was
transferred to `thm:smooth-gradient-raw-core-agreement-density`; the new constant corollary also
receives a marker.  The final count is twelve:

1. `thm:smooth-gradient-relaxation-two-cheeger`;
2. `thm:smooth-gradient-raw-core-agreement-density`;
3. `thm:ambient-intrinsic-relaxation-equality`;
4. `cor:ambient-intrinsic-constant-equality`;
5. `thm:legacy-relaxed-holds-equivalence`;
6. `thm:legacy-canonical-constant-comparison`;
7. `thm:smooth-lipschitz-constant-equivalence`;
8. `thm:selected-literature-constant-equivalence`;
9. `def:isoperimetric-cheeger-scale`;
10. `thm:logconcave-cheeger-poincare-comparison`;
11. `thm:affine-isotropic-reduction`;
12. `thm:one-dimensional-logconcave-poincare`.

These markers await a node-by-node human freeze decision.  The precise supporting definitions
`def:log-concave-law` and `def:isotropic-law`, and the published imported fact
`thm:borell-logconcave-density`, are not new proof claims and do not receive `\leanok`.

## Deliberately unfinished work

- The primary KLS 1995 location supporting the one-dimensional factor `4` was not verified.
- No `def:affine-cheeger-energy` node was introduced.
- No Lean source, production ledger entry, source pin, or `\leanok` marker was changed.
- `lake build` was not rerun because the change contains no Lean source or declaration edit.

## Local validation

The completed working tree passed the following local checks from the repository root:

- `python3 research/check_ledger.py`:
  `1 ledger(s), 4 nodes. 0 error(s).`
- `python3 research/check_blueprint.py`:
  `1 Blueprint schema v2, 7 chapter file(s), 66 labels, 4 active routes. 0 error(s).`
- `python3 -m unittest discover -s research/tests -p 'test_*.py'`:
  `Ran 62 tests`; `OK`.
- `git diff --check`: exit status zero with no output.
- `/tmp/kls-blueprint-venv/bin/python formalization/blueprint/build.py all`: exit status zero;
  PDF, web output, and `checkdecls` completed successfully.

The final PDF has 24 A4 pages.  Its final LaTeX and BibTeX logs contain no unresolved reference,
undefined citation, multiply-defined label, or overfull-box warning, and all 24 rendered pages were
visually inspected without clipping or overlap.

These are local uncommitted working-tree facts.  This decision asserts no commit, push, remote CI,
or human freeze result.
