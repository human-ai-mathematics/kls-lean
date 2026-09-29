# Metric BV overnight handoff (Claude, directed by Codex)

**Status:** phases1–22 independently accepted by Codex. Phase23 integrated upper
content bound is prepared in the Codex review; NOT DELIVERED. Control paused: Mac locked, manual unlock required. Active session
KLS BV phase 22 upper Minkowski thickenings, local_6d6d02c3-742c-45fa-a063-333eea0a2862.
Renewed window ends11:13:30 Asia/Shanghai on2026-09-29; wrap-up10:43:30.
Acceptance prose postdates phase22 frozen receipt. Old sessions remain retired.

## Resumption notes for a new conversation

Context of the previous Claude conversation was near its limit (2026-09-28). To continue:
work only in `/Users/lyuyuwei/Documents/ChatGPT/KLS` (HEAD `2f9f7e2`, dirty tree preserved, real
index unstaged); Codex directs segments and reviews them in `research/handoffs/codex-bv-overnight-review.md`
(never edit it); the senior collaborator's `research/handoffs/moment-map-spectral.md` is not
touched; no commit/push/reset/clean; do not touch `/private/tmp/kls-affine-w2-liminf`. Per segment:
placement plan here first, extend the owning module (`KLS/Geometry/Perimeter/MetricBV.lean`,
`KLS/Geometry/Cheeger/BVConstant.lean`), add a strict client in `research/audits/`, update
HANDOFF/README/`diagram:BV` in `research/progress/nodes.json`/progress-hub prose, regenerate views
with `GIT_INDEX_FILE` and `GIT_OBJECT_DIRECTORY` pointing at an isolated copy (then
`update.py --check`), refresh `research/tasks.json` hashes only for edited pinned files, freeze,
run `python3 research/verify.py`, and put the READY signal in an ignored `build/audit/…/receipt.md`.

## Phase 22 (2026-09-29, renewed eight-hour window; fresh implementation session)

### Baseline

Fresh Fable 5.1 session, started 03:14 Asia/Shanghai after the renewed window
(`research/handoffs/bv-renewed-eight-hours.md`: start 03:13:30, wrap-up 10:43:30, deadline
11:13:30 Asia/Shanghai; these override all earlier window times). Same checkout, HEAD `2f9f7e2`,
real index with no staged changes (SHA-256 of `.git/index` at start `cc0d1c6c…92e54a`), 43
modified/untracked entries preserved. SHA-256 at start: `Cheeger/MinkowskiContent.lean`
`82413123…f70a69` (pinned owner of the lower content; not edited), chapter 45
`b8b8bfdf…9ec5b77`, `research/tasks.json` `906e1cf2…9449b5`, `literature.json`
`fb5afe2f…685c8b8`, `README.md` `1f2f9b45…f006006`, `HANDOFF.md` `19806aa4…c489c6ca`,
`nodes.json` `f611c9a6…dc7e0258`, `research/progress/README.md` `4fa6e2f2…4757a9024`; not
edited: `codex-bv-overnight-review.md` (`26876255…902ff69071` at start),
`moment-map-spectral.md` `7106fbc3…29b8bee5`, `/private/tmp/kls-affine-w2-liminf`. The phase-21
receipt does not cover this snapshot.

### Placement plan (recorded before editing)

Object and role: the upper Minkowski content `upperMinkowskiContent ν B`, the `limsup` along
`𝓝[>] 0` of the same radius quotient `(ν (thickening r B) - ν B) / ENNReal.ofReal r` whose
`liminf` defines the existing lower `minkowskiContent` (object definition, elementary
properties: lower `≤` upper, empty set, zero mass increments), together with the radius mass
`thickeningMass ν B s = (ν (thickening s B)).toReal` and its differentiation (substantive
property): monotonicity, values for nonpositive radii, the `ENNReal`/real conversion of the
increment quotient with a positive denominator, the pointwise bound
`upperMinkowskiContent ν (thickening s B) ≤ ENNReal.ofReal d` at every radius `s` where
`HasDerivAt (thickeningMass ν B) d s` (from `thickening_thickening_subset` and the right
difference quotient; no content comparison is assumed), the `deriv` form, nonnegativity of the
derivative, and Lebesgue-a.e. differentiability of the radius mass by the actual monotone
differentiation theorem `Monotone.ae_differentiableAt`, combined into an a.e. bound at
positive radii.
Exact scope / non-claims: probability laws on a normed additive group with a measurable
structure (the scope of the existing lower content; no Borel, properness, finite-dimension or
density hypothesis enters). The derivative bound holds for every set `B`, including `∅` and
sets whose thickenings carry no extra mass. Not claimed: absolute continuity of the radius mass
(jumps and singular variation remain possible; a.e. differentiability is only that), any
integrated upper-content bound, lower-to-upper recovery or relaxed-upper identity, Lemma 2.1 of
Ambrosio--Di Marino--Gigli in general metric measure spaces, RCD/Buser/KLS conclusions.
Existing owner and consumers: `KLS/Geometry/Cheeger/MinkowskiContent.lean` owns
`minkowskiContent` (namespace `FunctionalInequalities.KLS.Isoperimetry`); it is imported by
`Cheeger/Equality`, `Cheeger/LocalSlopeCoarea`, `Cheeger/MinkowskiConstant`,
`Perimeter/MetricBVMinkowski` and transitively by the Cheeger/Buser/BV chain, and is pinned in
`research/tasks.json`.
Destination module and namespace: new `KLS/Geometry/Cheeger/UpperMinkowskiContent.lean`,
namespace `FunctionalInequalities.KLS.Isoperimetry` (the object family of the lower content).
Required imports / dependency direction: `Cheeger.MinkowskiContent` (the lower object and the
shared quotient) and `Mathlib.Analysis.Calculus.Monotone` (Lebesgue differentiation of monotone
real functions), which the owner does not import; no local module imports the new one.
Extend, split or create, and why: create a focused companion in the owning family (workflow
§3.2–3.3): the monotone-differentiation import would be an avoidable dependency for every
consumer of the owner, and "upper content of thickenings at differentiability radii" is one
responsibility. The lower definition, every existing signature and the pinned owner stay
untouched; no alias and no duplicate lower object.
Public API changes and affected clients: additions only; the root aggregator
`FunctionalInequalities.lean` gains the import.
Validation scope: strict compilation of the new module and the new client
`research/audits/MinkowskiUpperThickeningAudit.lean` (a.e. theorem plus the pointwise derivative
bound as one statement, lower `≤` upper, the empty set, zero increments, the uniform law on
`[0, 1]` with `B = {0}`, where the radius mass is the identity on `(0, 1)`, the derivative is `1`
and the bound is attained, and the Dirac law, where the radius mass jumps at `0`); `#print axioms`
standard three; full default `lake build`; progress views from an isolated index/object store
with only chapter 45 and `research/tasks.json` added; `update.py --check`, `test_views.py`,
`check_blueprint.py`, `git diff --check`; frozen `python3 research/verify.py`; receipt under the
ignored `build/audit/minkowski-upper-thickening/receipt.md`.

### Phase 22 stage status

- [x] module, client, aggregator import, docs, pins, views
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/minkowski-upper-thickening/receipt.md`)

### Phase 22 exact declarations

New `KLS/Geometry/Cheeger/UpperMinkowskiContent.lean` (imports `Cheeger.MinkowskiContent` and
`Mathlib.Analysis.Calculus.Monotone`; namespace `FunctionalInequalities.KLS.Isoperimetry`;
`{V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]`, `ν : ProbabilityMeasure V`):

```lean
def upperMinkowskiContent (ν : ProbabilityMeasure V) (B : Set V) : ℝ≥0∞ :=
  limsup (fun r : ℝ ↦ ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r) (𝓝[>] 0)
theorem minkowskiContent_le_upperMinkowskiContent (ν) (B) : minkowskiContent ν B ≤ upperMinkowskiContent ν B
theorem upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le (ν) {B}
    (h : ∀ r : ℝ, 0 < r → (ν : Measure V) (Metric.thickening r B) ≤ (ν : Measure V) B) : upperMinkowskiContent ν B = 0
theorem upperMinkowskiContent_empty (ν) : upperMinkowskiContent ν (∅ : Set V) = 0
theorem minkowskiContent_empty (ν) : minkowskiContent ν (∅ : Set V) = 0
def thickeningMass (ν : ProbabilityMeasure V) (B : Set V) (s : ℝ) : ℝ := ((ν : Measure V) (Metric.thickening s B)).toReal
theorem thickeningMass_nonneg (ν) (B) (s) : 0 ≤ thickeningMass ν B s
theorem thickeningMass_le_one (ν) (B) (s) : thickeningMass ν B s ≤ 1
theorem ofReal_thickeningMass (ν) (B) (s) : ENNReal.ofReal (thickeningMass ν B s) = (ν : Measure V) (Metric.thickening s B)
theorem monotone_thickeningMass (ν) (B) : Monotone (thickeningMass ν B)
theorem thickeningMass_of_nonpos (ν) (B) {s} (hs : s ≤ 0) : thickeningMass ν B s = 0
theorem thickeningMass_empty (ν) (s) : thickeningMass ν (∅ : Set V) s = 0
theorem measure_thickening_sub_div_eq_ofReal (ν) (B) {s t : ℝ} (ht : 0 < t) :
    ((ν : Measure V) (Metric.thickening (s + t) B) - (ν : Measure V) (Metric.thickening s B)) / ENNReal.ofReal t =
      ENNReal.ofReal ((thickeningMass ν B (s + t) - thickeningMass ν B s) / t)
private theorem tendsto_right_slope_of_hasDerivAt {F : ℝ → ℝ} {d s : ℝ} (hF : HasDerivAt F d s) :
    Tendsto (fun t : ℝ => (F (s + t) - F s) / t) (𝓝[>] 0) (𝓝 d)
theorem upperMinkowskiContent_thickening_le_of_hasDerivAt (ν) (B) {s d : ℝ} (hd : HasDerivAt (thickeningMass ν B) d s) :
    upperMinkowskiContent ν (Metric.thickening s B) ≤ ENNReal.ofReal d
theorem upperMinkowskiContent_thickening_le_deriv_of_differentiableAt (ν) (B) {s : ℝ} (hs : DifferentiableAt ℝ (thickeningMass ν B) s) :
    upperMinkowskiContent ν (Metric.thickening s B) ≤ ENNReal.ofReal (deriv (thickeningMass ν B) s)
theorem deriv_thickeningMass_nonneg (ν) (B) (s) : 0 ≤ deriv (thickeningMass ν B) s
theorem nonneg_of_hasDerivAt_thickeningMass (ν) (B) {s d} (hd : HasDerivAt (thickeningMass ν B) d s) : 0 ≤ d
theorem ae_differentiableAt_thickeningMass (ν) (B) : ∀ᵐ s ∂(volume : Measure ℝ), DifferentiableAt ℝ (thickeningMass ν B) s
theorem ae_upperMinkowskiContent_thickening_le_deriv (ν) (B) :
    ∀ᵐ s ∂(volume : Measure ℝ), upperMinkowskiContent ν (Metric.thickening s B) ≤ ENNReal.ofReal (deriv (thickeningMass ν B) s)
theorem ae_restrict_Ioi_upperMinkowskiContent_thickening_le_deriv (ν) (B) :
    ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi 0)), 0 < s ∧ DifferentiableAt ℝ (thickeningMass ν B) s ∧
      upperMinkowskiContent ν (Metric.thickening s B) ≤ ENNReal.ofReal (deriv (thickeningMass ν B) s)
```

Proof shape: lower `≤` upper is `liminf_le_limsup` (the filter `𝓝[>] 0` is nontrivial); zero
increments make every quotient `0 / ofReal r = 0` (`limsup_le_of_le`); the empty set through
`thickening_empty`, and the lower empty-set value through lower `≤` upper. The radius mass is
monotone by `thickening_mono` and `ENNReal.toReal_mono` (finite masses); the increment
conversion is `ENNReal.ofReal_div_of_pos`, `ENNReal.ofReal_sub` and `ENNReal.ofReal_toReal`
(denominator `ofReal t` with `0 < t`). The pointwise bound: `hasDerivAt_iff_tendsto_slope_zero`
restricted from `𝓝[≠] 0` to `𝓝[>] 0` gives the right difference quotient `→ d`,
`ENNReal.tendsto_ofReal` and `Tendsto.limsup_eq` turn it into `limsup = ofReal d`, and
`limsup_le_limsup` with `thickening_thickening_subset t s B ⊆ thickening (s + t) B`,
`measure_mono`, `tsub_le_tsub_right` and `ENNReal.div_le_div_right` compare the quotients. The
derivative bound is stated for every radius `s` (for `s ≤ 0` the thickening is empty, so the
positive-radius statement of the assignment is included). Nonnegativity of the derivative is
`Monotone.deriv_nonneg`; a.e. differentiability is `Monotone.ae_differentiableAt` (Lebesgue
measure on `ℝ`), combined by `filter_upwards`; the positive-radius version uses
`ae_restrict_mem` and `ae_restrict_of_ae`. No existing definition or signature changed; the pinned
owner `MinkowskiContent.lean` is untouched; the root aggregator gains one import.

### Phase 22 independent client (`research/audits/MinkowskiUpperThickeningAudit.lean`)

`aeDerivativeBound` (a.e. differentiability and the derivative bound as one statement),
`aePositiveRadii`, `pointwiseBound` (bound and `0 ≤ d` from a `HasDerivAt` hypothesis),
`lowerLeUpper`, `emptySet` (upper, lower and radius mass), `massBookkeeping` (monotone, `[0, 1]`,
nonpositive radii, lossless conversion, increment-quotient conversion), `zeroIncrements` (upper and
lower content zero), the uniform law on `[0, 1]` with `B = {0}`: `thickening_ball_real`
(`thickening t (ball 0 s) = ball 0 (s + t)` on `ℝ`, the reverse inclusion by scaling towards the
centre), `uniform_ball`, `uniform_thickeningMass` (radius mass equal to the radius on `(0, 1]`),
`uniform_hasDerivAt` (derivative `1` on `(0, 1)`), `uniformBound` (upper content of the thickening
`≤ 1`) and `uniformAttained` (the upper content is exactly `1`, equal to `ofReal` of the
derivative, so the bound is attained); the Dirac law at `0` with `B = {0}`: radius mass `1` for
positive and `0` for nonpositive radii, `dirac_jump` (not continuous at `0`, so a.e.
differentiability is not absolute continuity) and `diracPositiveRadius` (derivative `0` and zero
upper content at every positive radius). All eleven `#print axioms` reports are
`[propext, Classical.choice, Quot.sound]`; the module compiles strictly with no warnings; the
full default `lake build` (3674 jobs) passed.

Metadata: chapter 45 (upper content, radius mass, derivative bound, non-claims; the remainder of
Lemma 2.1 stays literature), the `ADMG2017` literature row, `diagram:BV` description and
`last_updated` `2026-09-29` in `nodes.json` (evidence source unchanged), HANDOFF (head paragraph
and a phase-22 paragraph, both marked awaiting independent review), root README, progress hub
prose; the four chapter-45 pins in `research/tasks.json` refreshed (no other pinned file edited);
views regenerated from an isolated index/object store (`GIT_INDEX_FILE` copy plus
`GIT_OBJECT_DIRECTORY` with the real store as alternate, adding only `research/tasks.json` and
chapter 45); `update.py --check`, `test_views.py` (4 tests), `check_blueprint.py` (0 errors) and
`git diff --check` passed; the real index hash is unchanged and nothing is staged.

Not claimed: absolute continuity of the radius mass, any integrated upper-content bound, the
lower-to-upper recovery or relaxed-upper identity, Lemma 2.1 in general metric measure spaces,
RCD/Buser/KLS conclusions, remote CI or a ledger certificate.

## Phase 21 (2026-09-29, eight-hour window; last segment of this chat)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `TestClassRelaxation.lean` `5b5ac252…a7d4ffab`, `BVIdentification.lean` `50cd5958…3d58f6a7`, chapter 45 `2158a497…69281485`,
`research/tasks.json` `e6472af7…5fd4ec7e`, `literature.json` `4ae18027…f9a75b92`, `README.md` `4f315095…edd3296b`, `HANDOFF.md`
`1ff4bbf5…c941ca68`, `nodes.json` `2fda073f…67518ccf`; not edited: `codex-bv-overnight-review.md` (`87c384e1…5a47bc49` at start),
`moment-map-spectral.md` `7106fbc3…29b8bee5`. The phase-20 receipt does not cover this snapshot.

### Placement plan

Object: `CompactLocallyLipschitzApproximatingSequence ν B` — locally Lipschitz `f n` with
`∫⁻ x in K, ‖f n x - 1_B x‖ₑ dν → 0` for every compact `K` (bare compact-error convergence; no
local integrability of `f n` is imposed or implied by the class), and its infimum
`compactLocallyLipschitzRelaxation ν B` of liminf slope integrals (`⊤` for an empty class), for
every measure on a metric Borel space. Results: global `L¹` sequences are compact-convergent
(`LocallyLipschitzApproximatingSequence.toCompact`, `setLIntegral_le_lintegral` squeeze), so
`compactLocallyLipschitzRelaxation ≤ locallyLipschitzRelaxation ≤ perimeter` for every measure;
on a proper space with a finite measure phase-20
`perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact` gives the reverse, hence
`compactLocallyLipschitzRelaxation_eq_perimeter`; the premise equivalence
`forall_isCompact_iff_forall_closedBall` on proper spaces (balls are compact; the phase-20
implication for the converse) with both quantifiers intact; closed-support specialization via
`properSpace_support`; intrinsic instance `compactLocallyLipschitzRelaxation_intrinsicClosedSupportLaw`
in `BVIdentification.lean` (no convexity or log-concavity; separate from Cheeger identification).
Owner: extend `Perimeter/TestClassRelaxation.lean` (no new import) and the `IntrinsicTestClass`
section of `Cheeger/BVIdentification.lean`. API additions only. Client:
`research/audits/MetricBVLocalL1RelaxationAudit.lean` (both directions, empty class `⊤`, `⊤`
transfer, zero measure, empty carrier, the equivalence, the intrinsic instance). Validation as in
the previous phases; receipt under ignored `build/audit/metric-bv-local-l1-relaxation/`.

### Phase 21 stage status

- [x] class and infimum, inclusions, equality, equivalence, support and intrinsic instances, client, docs
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-local-l1-relaxation/receipt.md`)

### Phase 21 exact declarations

`Perimeter/TestClassRelaxation.lean`, new section `CompactLocal` (`{X : Type*} [MetricSpace X]
[MeasurableSpace X]`, then `[BorelSpace X]`):

```lean
def CompactLocallyLipschitzApproximatingSequence (ν : Measure X) (B : Set X) : Type _ :=
  {f : ℕ → X → ℝ // (∀ n, LocallyLipschitz (f n)) ∧ ∀ K : Set X, IsCompact K →
    Tendsto (fun n => ∫⁻ x in K, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)}
def compactLocallyLipschitzRelaxation (ν : Measure X) (B : Set X) : ENNReal :=
  ⨅ f : CompactLocallyLipschitzApproximatingSequence ν B, liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop
theorem compactLocallyLipschitzRelaxation_le_liminf (ν) (B) (f) : compactLocallyLipschitzRelaxation ν B ≤ liminf (…) atTop
def LocallyLipschitzApproximatingSequence.toCompact (f : LocallyLipschitzApproximatingSequence ν B) : CompactLocallyLipschitzApproximatingSequence ν B
theorem compactLocallyLipschitzRelaxation_le_locallyLipschitzRelaxation (ν) (B) : compactLocallyLipschitzRelaxation ν B ≤ locallyLipschitzRelaxation ν B
theorem forall_isCompact_iff_forall_closedBall [ProperSpace X] (ν : Measure X) (g : ℕ → X → ℝ≥0∞) :
    (∀ K : Set X, IsCompact K → Tendsto (fun n => ∫⁻ x in K, g n x ∂ν) atTop (𝓝 0)) ↔
      ∀ (x₀ : X) (r : ℝ), 0 < r → Tendsto (fun n => ∫⁻ x in Metric.closedBall x₀ r, g n x ∂ν) atTop (𝓝 0)
theorem compactLocallyLipschitzRelaxation_le_perimeter (ν) (B) : compactLocallyLipschitzRelaxation ν B ≤ perimeter ν B
theorem perimeter_le_compactLocallyLipschitzRelaxation [ProperSpace X] (ν) [IsFiniteMeasure ν] (B) : perimeter ν B ≤ compactLocallyLipschitzRelaxation ν B
theorem compactLocallyLipschitzRelaxation_eq_perimeter [ProperSpace X] (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    compactLocallyLipschitzRelaxation ν B = perimeter ν B
theorem compactLocallyLipschitzRelaxation_closedSupportLaw [SecondCountableTopology X] [ProperSpace X] (ν : ProbabilityMeasure X) (B) :
    compactLocallyLipschitzRelaxation (closedSupportLaw ν : Measure _) B = perimeter (closedSupportLaw ν : Measure _) B
```

`Cheeger/BVIdentification.lean`, section `IntrinsicTestClass`:

```lean
theorem compactLocallyLipschitzRelaxation_intrinsicClosedSupportLaw (μ : ProbabilityMeasure E) (B) :
    compactLocallyLipschitzRelaxation (intrinsicClosedSupportLaw μ : Measure _) B = perimeter (intrinsicClosedSupportLaw μ : Measure _) B
```

Proof shape: `toCompact` squeezes `∫⁻ in K ≤ ∫⁻` (`setLIntegral_le_lintegral`); inclusions by
`le_iInf`; reverse by phase-20 `perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact`;
equivalence by `isCompact_closedBall` and `tendsto_setLIntegral_of_isCompact`; support instances
by `properSpace_support`. No existing definition or signature changed; no new import.

### Phase 21 independent client (`research/audits/MetricBVLocalL1RelaxationAudit.lean`)

`inclusions`, `globalSequenceBound` (direction one, actual global sequence), `identity`,
`compactSequenceBound` (direction two through the identity), `premiseEquivalence`, `topCases`
(empty class `⊤` forces `⊤` perimeter; `⊤` transfer), `zeroMeasure`, `emptyCarrier`,
`uniformSupportIdentity` (closed-support law of the uniform law on `[0, 1]`), `intrinsicIdentity`.
All ten reports and the direct reports of the eleven new owner declarations are
`[propext, Classical.choice, Quot.sound]`; the 21 earlier MetricBV clients and
`CheegerEqualityAudit.lean` recompile strictly; full default `lake build` (3673 jobs) passed;
`#print` of the class shows only the local-Lipschitz and compact-convergence fields.

Metadata: chapter 45, literature row, HANDOFF (phase 20 accepted; phase-21 paragraph; head
statement), root README, progress hub and `diagram:BV` description record that the compact-local
infimum equals the perimeter on proper spaces with finite measures (bare compact-error
convergence; no integrability imposed; not an infinite-measure or non-proper result); four
`research/tasks.json` pins refreshed; views regenerated from an isolated index/object store,
`update.py --check`, `test_views.py` (isolated index), `check_blueprint.py` passed; real index
unstaged; `git diff --check` passed.

### Rollover checkpoint (end of this implementation chat)

The implementation chat (Fable 5.1, context about 83%) stops after phase 21; no next segment is
started here. A fresh same-project session resumes from: this file (read the resumption notes,
the phase-21 record and the window assignment `research/handoffs/bv-eight-hour-2026-09-29.md`),
`codex-bv-overnight-review.md` (never edited), HEAD `2f9f7e2`, dirty tree preserved, real index
with nothing staged, `/private/tmp/kls-affine-w2-liminf` untouched. The phase-21 receipt
`build/audit/metric-bv-local-l1-relaxation/receipt.md` carries the frozen snapshot identity and
report path. Per-segment protocol unchanged: placement plan here first, extend the owning
module, strict client in `research/audits/`, standard-axiom audit, English progress via canonical
records and an isolated `GIT_INDEX_FILE`/`GIT_OBJECT_DIRECTORY` copy (adding only the dirty
`research/tasks.json` and chapter 45), `update.py --check`/`test_views.py`/`check_blueprint.py`,
freeze, `python3 research/verify.py`, receipt under ignored `build/audit/…/receipt.md`, then
READY_FOR_CODEX_REVIEW. Window: wrap-up from 08:24, deadline 08:54 Asia/Shanghai 2026-09-29;
Codex chooses each next assignment; never two implementation sessions.

## Phase 20 (2026-09-29, eight-hour window)

### Baseline

Same conversation (context about 75%), same checkout, HEAD `2f9f7e2`, real index with no staged
changes. SHA-256 at start: `LocalLipschitzTests.lean` `21addf53…1ce76cfd` (extended; not pinned in
`research/tasks.json`), chapter 45 `1a961a54…4794d28b`, `research/tasks.json` `b0d8279d…2cb42413`, `literature.json`
`cd79c6ed…2ea28e74`, `README.md` `3773e86e…7fa1c60d`, `HANDOFF.md` `8372ec79…685b0e5d`, `nodes.json` `1783784b…aeb172b8`; not edited:
`codex-bv-overnight-review.md` (`3b7b10ad…8c43a2a1` at start; Codex may append), `moment-map-spectral.md`
`7106fbc3…29b8bee5`. The phase-19 receipt does not cover this snapshot.

### Placement plan

Object and role: a local-convergence test-class bridge. Premise: locally Lipschitz `f n`
converging to `1_B` in `L¹(ν)` on every closed ball (explicit hypothesis
`∀ x₀ r, 0 < r → Tendsto (fun n => ∫⁻ x in closedBall x₀ r, ‖f n x - 1_B x‖ₑ ∂ν) atTop (𝓝 0)`;
no global `L¹` convergence, no global Lipschitz constant, no integrability of `f n`, no energy
comparison). Conclusion on a proper space with a finite Borel measure: an actual
`ApproximatingSequence ν B` with no larger liminf slope integral, hence the perimeter bound.

Mathematics, in two separated steps. (1) Finite-measure clamp lemma, no properness: for one
centre `x₀` and convergence on the closed balls around it, the clamped sequence
`clampUnit ∘ f n` converges globally: pointwise `‖clampUnit (f n x) - 1_B x‖ₑ ≤ ‖f n x - 1_B x‖ₑ`
(`abs_clampUnit_sub_le`, `clampUnit_of_mem`) and `≤ 1`; for `ε > 0` a fixed radius with
`ν (closedBall x₀ R)ᶜ ≤ ε/2` (`tendsto_measure_compl_ball`), then eventually the ball integral
is `≤ ε/2` (fixed radius, not expanding balls), and `lintegral_add_compl` gives `≤ ε`
(`ENNReal.tendsto_nhds_zero`). The un-clamped sequence is not claimed to converge globally.
(2) Slope contraction `apply (clampUnit ∘ f) x ≤ apply f x` (`apply_le_of_dist_le`), local
Lipschitz continuity of the clamp (`LocallyLipschitz.comp` with the `1`-Lipschitz `clampUnit`),
then phase-17 `exists_approximatingSequence_of_locallyLipschitz` on the clamped sequence and
`liminf_le_liminf`; empty carrier by the zero test. Bounded-ball versus compact: on a proper
space closed balls are compact and every compact set lies in a closed ball, so convergence on
every closed ball is equivalent to convergence on every compact set; the implication used for a
compact-set premise is proved (`tendsto_setLIntegral_of_isCompact`), and the results are stated
for the bounded-ball premise, with the compact-set premise as a corollary.

Owner and destination: extend `KLS/Geometry/Perimeter/LocalLipschitzTests.lean` (same
responsibility: locally Lipschitz approximants on proper spaces; same imports, no new import), in
new sections `Clamp` (pointwise contractions, `lipschitzWith_clampUnit`, the finite-measure
clamp lemma without properness) and `BoundedBall` (proper-space bridge, perimeter bound,
compact-set corollary). API: additions only; no existing definition or signature changes; no new
predicate (explicit hypothesis). Client: `research/audits/MetricBVLocalL1Audit.lean`: full
signatures exercising the local premise and the actual sequence output; a sequence that
converges on every ball but is not globally integrable (on `ℝ` with a finite measure: `f n x =
1_B x + (1/(n+1)) · x²`-type is globally integrable for the two-atom law… use instead the exact
premise with `x ↦ x²`, which is not globally Lipschitz, and the clamp lemma's non-claim);
empty carrier; zero measure; the empty set; the compact-set corollary. Validation: strict
compilation, full `lake build`, all MetricBV clients, standard transitive axioms, chapter-45 and
literature prose (bounded-ball `L¹` on proper spaces; the general non-proper/infinite-measure
literature theorem remains outside scope) with pins refreshed, isolated-index progress
generation with `update.py --check`, `test_views.py`, `check_blueprint.py`, frozen full
`research/verify.py`, receipt under ignored `build/audit/metric-bv-local-l1-tests/`.

### Phase 20 stage status

- [x] clamp contractions and finite-measure clamp lemma, proper-space bridge, client, docs
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-local-l1-tests/receipt.md`)

### Phase 20 exact declarations

`KLS/Geometry/Perimeter/LocalLipschitzTests.lean`, new section `Clamp` (`{X : Type*}
[MetricSpace X]`, then `[MeasurableSpace X]`, then `[BorelSpace X]`; `MetricSpace` omitted for
the two pointwise indicator lemmas):

```lean
theorem lipschitzWith_clampUnit : LipschitzWith 1 clampUnit
theorem apply_clampUnit_comp_le (f : X → ℝ) (x : X) :
    Energy.LocalSlope.apply (fun y => clampUnit (f y)) x ≤ Energy.LocalSlope.apply f x
theorem locallyLipschitz_clampUnit_comp {f : X → ℝ} (hf : LocallyLipschitz f) :
    LocallyLipschitz (fun y => clampUnit (f y))
theorem enorm_clampUnit_sub_indicator_le (f : X → ℝ) (B : Set X) (x : X) :
    ‖clampUnit (f x) - B.indicator (1 : X → ℝ) x‖ₑ ≤ ‖f x - B.indicator (1 : X → ℝ) x‖ₑ
theorem enorm_clampUnit_sub_indicator_le_one (f) (B) (x) : ‖clampUnit (f x) - B.indicator (1 : X → ℝ) x‖ₑ ≤ 1
theorem tendsto_setLIntegral_of_isCompact (ν : Measure X) {g : ℕ → X → ℝ≥0∞}
    (hloc : ∀ (x₀ : X) (r : ℝ), 0 < r → Tendsto (fun n => ∫⁻ x in Metric.closedBall x₀ r, g n x ∂ν) atTop (𝓝 0))
    {K : Set X} (hK : IsCompact K) : Tendsto (fun n => ∫⁻ x in K, g n x ∂ν) atTop (𝓝 0)
theorem tendsto_lintegral_clampUnit_of_forall_closedBall (ν : Measure X) [IsFiniteMeasure ν]
    (x₀ : X) {B : Set X} {f : ℕ → X → ℝ}
    (hloc : ∀ r : ℝ, 0 < r → Tendsto (fun n =>
      ∫⁻ x in Metric.closedBall x₀ r, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖clampUnit (f n x) - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)
```

Section `BoundedBall` (`[MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]`):

```lean
theorem exists_approximatingSequence_of_locallyLipschitz_of_forall_closedBall (ν : Measure X)
    [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n))
    (hloc : ∀ (x₀ : X) (r : ℝ), 0 < r → Tendsto (fun n =>
      ∫⁻ x in Metric.closedBall x₀ r, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    ∃ g : ApproximatingSequence ν B, liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop
theorem perimeter_le_liminf_of_locallyLipschitz_of_forall_closedBall (ν) [IsFiniteMeasure ν] {B} {f} (hf) (hloc) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop
theorem perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact (ν) [IsFiniteMeasure ν] {B} {f} (hf)
    (hloc : ∀ K : Set X, IsCompact K → Tendsto (fun n => ∫⁻ x in K, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (…) atTop
```

Proof shape. Clamp lemma: `ENNReal.tendsto_nhds_zero`; for `ε` take `N` with
`ν (ball x₀ N)ᶜ ≤ ε/2` from `tendsto_measure_compl_ball`, fix `r = N + 1`, eventually the ball
integral is `≤ ε/2` (`hloc r`), then `lintegral_add_compl` on the measurable closed ball, the
pointwise contraction inside and the bound by one outside (`setLIntegral_one`),
`ENNReal.add_halves`. Compact: a compact set is bounded, hence inside `closedBall x₀ (max R 1)`;
`lintegral_mono_set` and a squeeze; empty carrier separately. Bridge: empty carrier by the zero
test; otherwise phase-17 `exists_approximatingSequence_of_locallyLipschitz` on the clamped
sequence (`locallyLipschitz_clampUnit_comp`, clamp lemma at a chosen centre) and
`liminf_le_liminf` with `apply_clampUnit_comp_le` (via `apply_le_of_dist_le`). Corollary from
`isCompact_closedBall`. No existing definition or signature changed; no new import.

### Phase 20 independent client (`research/audits/MetricBVLocalL1Audit.lean`)

| Client | Content |
| --- | --- |
| `clampLemma` | the finite-measure clamp lemma without properness |
| `compactFromBalls` | convergence on every closed ball gives convergence on every compact set |
| `existenceForm`, `perimeterBound`, `compactCorollary` | full signatures with the local premise and the actual sequence output |
| `locallyLipschitz_add_const_mul`, `perturbedSequence` | the local premise genuinely used: `u n + (n + 1)⁻¹ h` with `h` locally Lipschitz of no assumed integrability (bounded on each compact ball) still converges on every ball; perimeter bound for the perturbed sequence |
| `emptyCarrier`, `zeroMeasure`, `emptySet` | degenerate cases |

All ten reports and the direct reports of the ten new owner declarations are
`[propext, Classical.choice, Quot.sound]`; the twenty earlier MetricBV clients recompile
strictly; the full default `lake build` (3673 jobs) passed.

Metadata. Chapter 45, the literature row, HANDOFF head statement (phase 19 marked accepted;
phase-20 paragraph), root README, progress hub and the `diagram:BV` description record the
bounded-ball (equivalently compact-set) scope on proper spaces with finite measures and keep the
non-proper/infinite-measure `L¹_loc` theorem and Theorem 3.6 as literature; four
`research/tasks.json` pins refreshed; views regenerated from an isolated index/object store,
`update.py --check`, `test_views.py` (isolated index) and `check_blueprint.py` passed; real index
unstaged; `git diff --check` passed. Obstacles: `omit … in` placements; Mathlib has no
`LocallyLipschitz.add` (client helper from the definition); `push_cast` already rewrites `‖c‖₊`.
Context of the implementation session is about 78%; a rollover is not yet needed.

## Phase 19 (2026-09-29, eight-hour window)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `MetricBVMinkowski.lean` `4dec26c1…9f224eda` (not edited), `FunctionalInequalities.lean` `63de6f1d…138ae904`,
chapter 45 `8771e13f…333d0345`, `research/tasks.json` `eb8e44a6…45dda8e6`, `literature.json` `26b75fb6…52d5fc80`, `README.md`
`62c6347d…412e6f4e`, `HANDOFF.md` `56d67ef7…169fc974`, `nodes.json` `67a2901b…99ee39ee` (Codex refreshed its BV evidence hash and
prose after phase 18; only targeted sentences are edited here); not edited:
`codex-bv-overnight-review.md` (`99cfb007…5dec3af3` at start; Codex may append), `moment-map-spectral.md`
`7106fbc3…29b8bee5`. The phase-18 receipt does not cover this snapshot.

### Placement plan

Object: the relaxed lower Minkowski content as a set infimum, for a probability law `ν` on a
normed additive group with Borel structure: `MinkowskiApproximatingSequence ν B`, measurable
sets `A n` with `∫⁻ ‖1_{A n} - 1_B‖ₑ dν → 0` (only measurability and convergence as fields), and
`relaxedMinkowskiContent ν B = ⨅ A, liminf (minkowskiContent ν (A n))`, `⊤` for an empty class.
The content is the existing `Isoperimetry.minkowskiContent` (a liminf over radii; not the
limsup-radius upper content). No finite dimension, inner product, properness or log-concavity.

Results. `perimeter_le_relaxedMinkowskiContent` for every `B` (phase-10
`perimeter_le_liminf_minkowskiContent`, `le_iInf`); `relaxedMinkowskiContent_le_perimeter`: if
`perimeter ν B = ⊤` by order, otherwise the phase-10 recovery sequence
`exists_minkowskiRecovery` is a member of the class whose contents converge to the perimeter
(`Tendsto.liminf_eq`); hence `relaxedMinkowskiContent_eq_perimeter` — for every `B`, so in
particular for measurable `B` (the requested form; the stronger form follows directly and is
kept). Consequences: `relaxedMinkowskiContent_le_minkowskiContent` for measurable `B` through
the constant sequence (`liminf_const`), the sequential lower semicontinuity
`relaxedMinkowskiContent_le_liminf_of_tendsto` for measurable `A n → B` through the equality and
phase-6 `perimeter_le_liminf_of_tendsto`, `relaxedMinkowskiContent_eq_top_of_isEmpty` (empty
class) and the `⊤`/zero transfers as clients. No pointwise `perimeter = content` (the client
exhibits `relaxedMinkowskiContent < minkowskiContent` for the rationals under the Gaussian law).

Owner and destination: new focused module `KLS/Geometry/Perimeter/RelaxedMinkowski.lean` at the
perimeter/Minkowski integration boundary (imports `Perimeter/MetricBVMinkowski` only; the
existing owner keeps its bridge, coarea, selection, recovery and ratio sections, and this module
adds the set-infimum object and its identity, a separate responsibility). Root
`FunctionalInequalities.lean` gains the import. API: additions only; no alias; no existing
definition or signature changes. Client: `research/audits/MetricBVRelaxedMinkowskiAudit.lean`:
full signatures (including the measurable-`B` form), both directions with actual sequences (the
constant sequence and the phase-10 recovery sets), zero perimeter (`Iic (1/2)` under the
two-atom law), dimension zero, `⊤` transfer and empty-class `⊤` (conditional), and the strict
inequality example (rationals under `gaussianReal 0 1`: relaxed content `0`, content `⊤`).
Validation: strict compilation, full `lake build`, all MetricBV clients, standard transitive
axioms, chapter-45 and literature prose (this is the normed-space set-infimum identity, not
Lemma 2.1 or Theorem 3.6 in general metric measure spaces) with pins refreshed, isolated-index
progress generation with `update.py --check`, `test_views.py`, `check_blueprint.py`, frozen full
`research/verify.py`, receipt under ignored `build/audit/metric-bv-relaxed-minkowski/`.

### Phase 19 stage status

- [x] class and infimum, both inequalities, equality, consequences, strict client, docs
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-relaxed-minkowski/receipt.md`)

### Phase 19 exact declarations

New module `KLS/Geometry/Perimeter/RelaxedMinkowski.lean` (imports `Perimeter/MetricBVMinkowski`
only), namespace `MetricBV`, `{V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]
[BorelSpace V]` (`BorelSpace` omitted where unused):

```lean
def MinkowskiApproximatingSequence (ν : ProbabilityMeasure V) (B : Set V) : Type _ :=
  {A : ℕ → Set V // (∀ n, MeasurableSet (A n)) ∧
    Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0)}
def relaxedMinkowskiContent (ν : ProbabilityMeasure V) (B : Set V) : ENNReal :=
  ⨅ A : MinkowskiApproximatingSequence ν B, liminf (fun n => Isoperimetry.minkowskiContent ν (A.1 n)) atTop
theorem relaxedMinkowskiContent_le_liminf (ν) (B) (A : MinkowskiApproximatingSequence ν B) :
    relaxedMinkowskiContent ν B ≤ liminf (fun n => Isoperimetry.minkowskiContent ν (A.1 n)) atTop
theorem relaxedMinkowskiContent_eq_top_of_isEmpty (ν) (B) [IsEmpty (MinkowskiApproximatingSequence ν B)] :
    relaxedMinkowskiContent ν B = ⊤
theorem perimeter_le_relaxedMinkowskiContent (ν : ProbabilityMeasure V) (B : Set V) :
    perimeter (ν : Measure V) B ≤ relaxedMinkowskiContent ν B
theorem relaxedMinkowskiContent_le_perimeter (ν : ProbabilityMeasure V) (B : Set V) :
    relaxedMinkowskiContent ν B ≤ perimeter (ν : Measure V) B
theorem relaxedMinkowskiContent_eq_perimeter (ν : ProbabilityMeasure V) (B : Set V) :
    relaxedMinkowskiContent ν B = perimeter (ν : Measure V) B
def MinkowskiApproximatingSequence.const (ν) {B} (hB : MeasurableSet B) : MinkowskiApproximatingSequence ν B
theorem relaxedMinkowskiContent_le_minkowskiContent (ν) {B} (hB : MeasurableSet B) :
    relaxedMinkowskiContent ν B ≤ Isoperimetry.minkowskiContent ν B
theorem relaxedMinkowskiContent_le_liminf_of_tendsto (ν) {B} {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0)) :
    relaxedMinkowskiContent ν B ≤ liminf (fun n => relaxedMinkowskiContent ν (A n)) atTop
```

Proof shape. `perimeter ≤`: `le_iInf` with phase-10 `perimeter_le_liminf_minkowskiContent` (any
`B`). `≤ perimeter`: `eq_or_ne (perimeter ν B) ⊤`; the `⊤` case by `le_top` after rewriting; else
phase-10 `exists_minkowskiRecovery` yields `A` with measurability, convergence and
`Tendsto (content) (𝓝 (perimeter))`, so `⟨A, hA, hconv⟩` is a member and `Tendsto.liminf_eq`
closes. Constant sequence: convergence by `simp` (the integrand vanishes), `liminf_const` after a
`change` exposing the constant. Lower semicontinuity: rewrite both sides with the identity, then
phase-6 `perimeter_le_liminf_of_tendsto`. The equality holds for every `B` (stronger than the
requested measurable form, which follows directly). No finite dimension, inner product,
properness or log-concavity; the content is the existing liminf-radius outer content. No existing
definition or signature changed; root import added.

### Phase 19 independent client (`research/audits/MetricBVRelaxedMinkowskiAudit.lean`)

| Client | Content |
| --- | --- |
| `identity`, `identityMeasurable`, `bothInequalities` | full signatures (all sets; the requested measurable form; both directions) |
| `constantSequence` | direction one with the actual constant sequence: relaxed ≤ content, hence `perimeter ≤ content` |
| `recoverySequence` | direction two with the actual phase-10 recovery sets: relaxed ≤ their liminf `= perimeter` |
| `lowerSemicontinuity` | sequential lower semicontinuity |
| `topCases` | infinite perimeter transfers; an empty class forces infinite perimeter (conditional) |
| `zeroDimensional` | `Fin 0 → ℝ`: relaxed content `0` |
| `zeroPerimeter` | `Iic (1/2)` under `(δ₀ + δ₁)/2`: outer content `0`, relaxed content `0`, perimeter `0` |
| `strictGap` | rationals under `gaussianReal 0 1`: relaxed content `0`, outer content `⊤` (no pointwise equality) |

All ten reports and the direct reports of the ten new owner declarations are
`[propext, Classical.choice, Quot.sound]`; the twenty earlier MetricBV clients and
`CheegerEqualityAudit.lean` recompile strictly; the full default `lake build` (3673 jobs) passed;
`#print MinkowskiApproximatingSequence` shows only the measurability and convergence fields.

Metadata. Chapter 45 records the normed-space set-infimum identity as an equality of infima
with a possibly strict pointwise inequality, keeping Theorem 3.6 (with Lemma 2.1) in general
metric measure spaces as literature; four `research/tasks.json` pins refreshed;
`literature.json` row updated likewise; HANDOFF head statement, phase 18 marked accepted,
phase-19 paragraph; root README, progress hub, `diagram:BV` description (Codex's refreshed
evidence hash untouched) updated; views regenerated from an isolated index/object store,
`update.py --check`, `test_views.py` (isolated index) and `check_blueprint.py` passed; real index
unstaged; `git diff --check` passed. Obstacles: `liminf_const` needed a `change` exposing the
constant sequence; three `omit [BorelSpace V]` annotations. Next (Codex chooses): bounded-ball
`L¹` convergence as a separate exact notion, or extending the metric scope of the Minkowski
results after inspecting which normed-space dependencies are essential.

## Phase 18 (2026-09-29, eight-hour window)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `LocalLipschitzTests.lean` `21addf53…1ce76cfd` (not edited), `MetricBV.lean` `6f4533f6…0cb6e95b` (not edited),
`BVIdentification.lean` `ff353137…dfd146e9`, `FunctionalInequalities.lean` `84c9afa3…764013b8`, chapter 45 `d0f9c518…1edc7cd5`,
`research/tasks.json` `751e9dd3…1859534a`, `literature.json` `ea9870e1…77822037`, `README.md` `b0b0e61f…c6c7a95c`, `HANDOFF.md`
`2d5fb6ca…90376858`, `nodes.json` `6e683bce…204ee5e1`; not edited: `codex-bv-overnight-review.md` (`91b0eb93…b32fb2a7` at start;
Codex may append), `moment-map-spectral.md` `7106fbc3…29b8bee5`. The phase-17 receipt does not
cover this snapshot.

### Placement plan

Objects: two relaxation infima of the liminf of integrated local slopes, as actual sequence
classes with no perimeter value or energy comparison as a field:
(1) `LipschitzApproximatingSequence ν B` — `f : ℕ → X → ℝ` with each `f n` globally Lipschitz
(values and supports unrestricted) and `∫⁻ ‖f n - 1_B‖ₑ dν → 0` — and `lipschitzRelaxation ν B`
(its infimum, `⊤` for an empty class); the class of Ambrosio--Di Marino--Gigli Definition 3.3
(with the one-point local Lipschitz constant, which is `Energy.LocalSlope.apply`);
(2) `LocallyLipschitzApproximatingSequence ν B` / `locallyLipschitzRelaxation ν B` with
Mathlib's `LocallyLipschitz` and the same global `L¹` convergence (the Remark 3.5 variant with
global `L¹`). Both are defined for every measure on a metric Borel space; no `ProperSpace` on
definitions or on the global result.

Results. Inclusions of classes: tests are globally Lipschitz
(`ApproximatingSequence.toLipschitz`, using `Test.lipschitz`; the `L¹` convergence is
`indicatorDistance` by definition) and globally Lipschitz functions are locally Lipschitz
(`LipschitzApproximatingSequence.toLocallyLipschitz`), giving for every measure
`locallyLipschitzRelaxation ≤ lipschitzRelaxation ≤ perimeter` (`le_iInf`/`iInf_le_of_le`).
Reverse: for a finite measure, phase-3 `perimeter_le_liminf_of_lipschitz` gives
`perimeter ≤ lipschitzRelaxation` (any metric space), hence
`lipschitzRelaxation_eq_perimeter`; on a proper space phase-17
`perimeter_le_liminf_of_locallyLipschitz` gives `perimeter ≤ locallyLipschitzRelaxation`, hence
`locallyLipschitzRelaxation_eq_perimeter` and `locallyLipschitzRelaxation_eq_lipschitzRelaxation`.
Empty classes (`⊤`), infinite perimeter, the zero measure and the empty carrier pass through the
infima without case analysis. Closed-support specialization: the closed support of a measure on
a proper space is proper (`ProperSpace.of_isClosed Measure.isClosed_support`), so for a
probability law on a proper second-countable metric space both relaxations of
`closedSupportLaw ν` equal its perimeter (`lipschitzRelaxation_closedSupportLaw`,
`locallyLipschitzRelaxation_closedSupportLaw`); the intrinsic instance
`intrinsicClosedSupportLaw μ = closedSupportLaw (intrinsicMeasure μ)` on the finite-dimensional
direction space (proper by `FiniteDimensional.proper_real`) gives
`lipschitzRelaxation_intrinsicClosedSupportLaw` and
`locallyLipschitzRelaxation_intrinsicClosedSupportLaw` for every finite-dimensional probability
law — no convexity or log-concavity — kept distinct from the identification of the constant with
`Isoperimetry.constant` (phase 16, log-concave hypothesis).

Owner and destination: new focused module `KLS/Geometry/Perimeter/TestClassRelaxation.lean`
(perimeter family; imports `Perimeter/LocalLipschitzTests`, hence `MetricBV`; no other import),
holding the definitions, inclusions, both equalities and the generic `closedSupportLaw`
specialization; the intrinsic instance goes to the Cheeger integration owner
`Cheeger/BVIdentification.lean` (new import of `TestClassRelaxation`; it already imports
`BVConstant`, which owns `intrinsicClosedSupportLaw`), so no perimeter module imports the Cheeger
family. Root `FunctionalInequalities.lean` gains the import. API: additions only; no existing
definition or signature changes; no alias. Client:
`research/audits/MetricBVTestClassAudit.lean`: full signatures; both directions used (a test
sequence bounds the Lipschitz relaxation; a locally Lipschitz sequence bounds the perimeter, with
`x ↦ x²` on the two-atom law giving `locallyLipschitzRelaxation twoAtom {1} ≤ 1`); empty class
`⊤`; `⊤` consistency; the zero measure; the empty carrier; the generic closed-support instance for
a proper law on `ℝ`; the intrinsic instance. Validation: strict compilation of both modules and
the client, full `lake build`, all MetricBV clients, standard transitive axioms, chapter-45 and
literature prose (Definition 3.3 / Remark 3.5 distinction; only the proved scope) with pins
refreshed, isolated-index progress generation with `update.py --check`, `test_views.py`,
`check_blueprint.py`, frozen full `research/verify.py`, receipt under ignored
`build/audit/metric-bv-test-class-identification/`.

### Phase 18 stage status

- [x] classes and infima, inclusions, both equalities, support specializations, client, docs
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-test-class-identification/receipt.md`)

### Phase 18 exact declarations

New module `KLS/Geometry/Perimeter/TestClassRelaxation.lean` (imports
`Perimeter/LocalLipschitzTests` only), namespace `MetricBV`,
`{X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]` (`BorelSpace` omitted where
unused):

```lean
def LipschitzApproximatingSequence (ν : Measure X) (B : Set X) : Type _ :=
  {f : ℕ → X → ℝ // (∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n)) ∧
    Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)}
def lipschitzRelaxation (ν : Measure X) (B : Set X) : ENNReal :=
  ⨅ f : LipschitzApproximatingSequence ν B,
    liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop
def LocallyLipschitzApproximatingSequence (ν : Measure X) (B : Set X) : Type _ :=
  {f : ℕ → X → ℝ // (∀ n, LocallyLipschitz (f n)) ∧ Tendsto (…same…) atTop (𝓝 0)}
def locallyLipschitzRelaxation (ν : Measure X) (B : Set X) : ENNReal := ⨅ f : LocallyLipschitzApproximatingSequence ν B, liminf (…) atTop
theorem lipschitzRelaxation_le_liminf / locallyLipschitzRelaxation_le_liminf (ν) (B) (f) : … ≤ liminf (fun n => ∫⁻ x, apply (f.1 n) x ∂ν) atTop
def ApproximatingSequence.toLipschitz (g : ApproximatingSequence ν B) : LipschitzApproximatingSequence ν B
def LipschitzApproximatingSequence.toLocallyLipschitz (f) : LocallyLipschitzApproximatingSequence ν B
theorem lipschitzRelaxation_le_perimeter (ν : Measure X) (B : Set X) : lipschitzRelaxation ν B ≤ perimeter ν B
theorem locallyLipschitzRelaxation_le_lipschitzRelaxation (ν) (B) : locallyLipschitzRelaxation ν B ≤ lipschitzRelaxation ν B
theorem locallyLipschitzRelaxation_le_perimeter (ν) (B) : locallyLipschitzRelaxation ν B ≤ perimeter ν B
theorem perimeter_le_lipschitzRelaxation (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) : perimeter ν B ≤ lipschitzRelaxation ν B
theorem lipschitzRelaxation_eq_perimeter (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    lipschitzRelaxation ν B = perimeter ν B
theorem perimeter_le_locallyLipschitzRelaxation [ProperSpace X] (ν) [IsFiniteMeasure ν] (B) : perimeter ν B ≤ locallyLipschitzRelaxation ν B
theorem locallyLipschitzRelaxation_eq_perimeter [ProperSpace X] (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    locallyLipschitzRelaxation ν B = perimeter ν B
theorem locallyLipschitzRelaxation_eq_lipschitzRelaxation [ProperSpace X] (ν) [IsFiniteMeasure ν] (B) : locallyLipschitzRelaxation ν B = lipschitzRelaxation ν B
-- section ClosedSupport, [SecondCountableTopology X]
theorem properSpace_support [ProperSpace X] (ν : Measure X) : ProperSpace ν.support
theorem lipschitzRelaxation_closedSupportLaw (ν : ProbabilityMeasure X) (B : Set (ν : Measure X).support) :
    lipschitzRelaxation (closedSupportLaw ν : Measure _) B = perimeter (closedSupportLaw ν : Measure _) B
theorem locallyLipschitzRelaxation_closedSupportLaw [ProperSpace X] (ν : ProbabilityMeasure X) (B) :
    locallyLipschitzRelaxation (closedSupportLaw ν : Measure _) B = perimeter (closedSupportLaw ν : Measure _) B
```

`Cheeger/BVIdentification.lean` (new import `Perimeter/TestClassRelaxation`), new section
`IntrinsicTestClass`, `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
[MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]`:

```lean
theorem lipschitzRelaxation_intrinsicClosedSupportLaw (μ : ProbabilityMeasure E)
    (B : Set (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction).support) :
    lipschitzRelaxation (intrinsicClosedSupportLaw μ : Measure _) B = perimeter (intrinsicClosedSupportLaw μ : Measure _) B
theorem locallyLipschitzRelaxation_intrinsicClosedSupportLaw (μ) (B) :
    locallyLipschitzRelaxation (intrinsicClosedSupportLaw μ : Measure _) B = perimeter (intrinsicClosedSupportLaw μ : Measure _) B
```

Proof shape. `toLipschitz` uses `Test.lipschitz` and the test sequence's convergence (the `L¹`
distance is `indicatorDistance` by definition); `toLocallyLipschitz` uses
`LipschitzWith.locallyLipschitz` on the chosen constant. Inclusions: `le_iInf` and the
`_le_liminf` instances at the transported sequence (`cost` is the slope integral by definition).
Reverse inequalities: `le_iInf` with phase-3 `perimeter_le_liminf_of_lipschitz` (finite measure,
any metric space) and phase-17 `perimeter_le_liminf_of_locallyLipschitz` (finite measure, proper
space). Support: `ProperSpace.of_isClosed Measure.isClosed_support`; the closed-support law is a
probability measure; the intrinsic instance is the generic one on the finite-dimensional direction
space (`FiniteDimensional.proper_real`). No existing definition or signature changed; no
`ProperSpace` on definitions or on the global result.

### Phase 18 independent client (`research/audits/MetricBVTestClassAudit.lean`)

| Client | Content |
| --- | --- |
| `globalIdentity`, `localIdentity`, `bothClassesAgree`, `inclusions` | full signatures; inclusions for every measure |
| `testSequenceBound` | direction one used: any test sequence bounds the Lipschitz relaxation |
| `lipschitzSequenceBound` | direction two used: any Lipschitz sequence bounds the perimeter through the identity |
| `emptyClassTop` | an empty locally Lipschitz class forces all three values `⊤` through the infima |
| `topTransfer` | infinite perimeter transfers to both relaxations |
| `zeroMeasure`, `emptyCarrier` | the zero measure on `ℝ` (both relaxations `0`); `X = Empty` |
| `squareSequence`, `squareRelaxationBound` | `x ↦ x²` as an actual locally Lipschitz sequence for `(δ₀ + δ₁)/2`, `B = {1}`: relaxation and perimeter `≤ 1` |
| `uniformSupportIdentity` | the closed-support law of the uniform law on `[0, 1]` (a proper law on `ℝ`) |
| `intrinsicIdentity`, `intrinsicUniform` | the actual closed intrinsic support, generic and for the uniform law |

All fifteen reports and the direct reports of the twenty-two new owner declarations are
`[propext, Classical.choice, Quot.sound]`; the nineteen earlier MetricBV clients and
`CheegerEqualityAudit.lean` recompile strictly; the full default `lake build` (3672 jobs) passed;
`#print LipschitzApproximatingSequence` shows only the Lipschitz and convergence fields.

Metadata. Chapter 45: the relaxation-infimum sentences now record the proved scope (Definition
3.3 class for every finite Borel measure; locally Lipschitz with global `L¹` on proper spaces, in
particular the closed intrinsic support; `L¹_loc` not a local theorem; Theorem 3.6 in general
metric measure spaces remains literature), four `research/tasks.json` pins refreshed;
`literature.json` row updated likewise; HANDOFF head statement, phase 17 marked accepted,
phase-18 paragraph; root README, progress hub, `diagram:BV` description (node state unchanged)
updated; views regenerated from an isolated index/object store, `update.py --check`,
`test_views.py` (isolated index) and `check_blueprint.py` passed; real index unstaged;
`git diff --check` passed. Obstacles: `omit … in` must precede a docstring; iCloud I/O lag on a
freshly written file (relative-path compile retried with an absolute path). Next (Codex
chooses): the relaxed Minkowski set-infimum equality from the existing recovery and lower
semicontinuity; bounded-ball `L¹` convergence as an exact separate notion.

## Phase 17 (2026-09-29, eight-hour window)

### Baseline

Same conversation (model switched to Fable 5.1), same checkout, HEAD `2f9f7e2`, real index with
no staged changes. SHA-256 at start: `MetricBV.lean` `6f4533f6…0cb6e95b` (not edited),
`FunctionalInequalities.lean` `52992c18…ae5c9854`, chapter 45 `81c7368d…af8fefbd`,
`research/tasks.json` `21bd5b5c…f5245d6b`, `literature.json` `9725a24d…8cb5b2e3`, `README.md`
`029fdd7b…fad21744`, `HANDOFF.md` `7cd5344c…8ae3cb2c`, `nodes.json` `8bd97927…76cd8349`; not
edited: `codex-bv-overnight-review.md` (`8a804f59…86284271` at start; Codex may append),
`moment-map-spectral.md` `7106fbc3…29b8bee5`. The phase-16 receipt does not cover this snapshot.

### Placement plan

Object and role: a test-class bridge for the existing relaxation, extending the accepted
finite-measure globally Lipschitz bridge (phase 3) to genuinely locally Lipschitz approximants
(Mathlib's `LocallyLipschitz`) on a proper metric space: for a finite Borel measure `ν`, a set
`B` and `f n : X → ℝ` locally Lipschitz with `∫⁻ ‖f n - 1_B‖ₑ dν → 0`, an actual
`ApproximatingSequence ν B` with no larger liminf of slope integrals, hence
`perimeter ν B ≤ liminf ∫⁻ apply (f n) dν`. Source scope check: Ambrosio--Di Marino--Gigli
Definition 3.3 uses globally Lipschitz approximants with global `L¹` convergence (already
covered one-sidedly by phase 3); the locally Lipschitz variant of their Remark 3.5 is what this
segment covers, with global `L¹` convergence and on proper spaces only; `L¹_loc` convergence and
the named infimum equality are not part of this segment.

Mathematics. Same truncation as phase 3, `truncateFun x₀ R f = cutoff x₀ R · clampUnit ∘ f`,
whose pointwise slope and error bounds (`apply_truncateFun_le`, `enorm_truncateFun_sub_le`)
never used a Lipschitz hypothesis; they are restated for arbitrary real functions (proofs copied
from the accepted `Test.truncate` lemmas, whose statements and bodies stay unchanged). The only
new analytic input is global Lipschitz continuity of the truncation of a locally Lipschitz `f`
on a proper space: `f` is Lipschitz on the compact closed ball `closedBall x₀ (R + 1)` by
Mathlib's `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact` (constant `L`, no uniform
constant for the sequence is assumed); inside the ball the product secant bound gives `L + 1`;
for a pair crossing the ball the outside value is `0` and `cutoff x₀ R x ≤ dist x y` (the cutoff
is at most `R + 1 - dist x x₀ ≤ dist y x₀ - dist x x₀`); two outside points give `0`
(`cutoff_le_dist_of_le`, `lipschitzWith_truncateFun_of_locallyLipschitz`). Then
`Test.truncateOfLocallyLipschitz`, the copied cost/distance/tendsto/liminf lemmas
(`tendsto_measure_compl_ball` for the tails), `exists_approximatingSequence_of_locallyLipschitz`
(empty carrier by the zero test) and `perimeter_le_liminf_of_locallyLipschitz`. Infinite slope
integrals and empty classes are handled by `ENNReal` and by constructing the sequence.

Owner and destination: new focused module `KLS/Geometry/Perimeter/LocalLipschitzTests.lean`
(perimeter family), importing `Perimeter/MetricBV` and
`Mathlib.Topology.Algebra.MetricSpace.Lipschitz` (compactness lemma); the basic owner
`MetricBV.lean` is not edited (properness and local-Lipschitz imports stay out of it); no
analytic helper module is created because Mathlib owns the compactness step (the repository's
`Analysis/Lipschitz/Local.lean` X2 is its finite-dimensional instance and is untouched). Root
`FunctionalInequalities.lean` gains the import. API: additions only; no alias. Client:
`research/audits/MetricBVLocalLipschitzAudit.lean`: full signatures; `x ↦ x²` is locally
Lipschitz but not globally Lipschitz, and for the two-atom law `(δ₀ + δ₁)/2` it equals
`1_{{1}}` a.e., so the bound applies with a non-globally-Lipschitz input; empty carrier, zero
measure, constant sequences/empty set. Validation: strict compilation, full `lake build`, all
MetricBV clients, standard transitive axioms, chapter-45/literature prose (source-faithful
Definition 3.3/Remark 3.5 distinction) with pins refreshed, isolated-index progress generation
with `update.py --check`, `test_views.py`, `check_blueprint.py`, frozen full
`research/verify.py`, receipt under ignored `build/audit/metric-bv-local-lipschitz/`.

### Phase 17 stage status

- [x] raw truncation bounds, proper-space Lipschitz bound, test, bridge, strict client, docs
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-local-lipschitz/receipt.md`)

### Phase 17 exact declarations

New module `KLS/Geometry/Perimeter/LocalLipschitzTests.lean` (imports `Perimeter/MetricBV`,
`Mathlib.Topology.Algebra.MetricSpace.Lipschitz`), namespace `MetricBV`. Section `Pointwise`,
`{X : Type*} [MetricSpace X]` (`[ProperSpace X]` where stated):

```lean
def truncateFun (x₀ : X) (R : ℝ) (f : X → ℝ) (x : X) : ℝ := cutoff x₀ R x * clampUnit (f x)
theorem Test.truncate_toFun (x₀) (R) (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    (Test.truncate x₀ R f hf : X → ℝ) = truncateFun x₀ R f   -- rfl
theorem truncateFun_eq_zero (x₀) (R) (f) (hx : R + 1 ≤ dist x x₀) : truncateFun x₀ R f x = 0
theorem truncateFun_nonneg / truncateFun_le_one (x₀) (R) (f) (x)
theorem cutoff_le_dist_of_le {x₀ x y : X} {R : ℝ} (hy : R + 1 ≤ dist y x₀) : cutoff x₀ R x ≤ dist x y
theorem apply_truncateFun_le (x₀) (R) (f : X → ℝ) (x) :
    Energy.LocalSlope.apply (truncateFun x₀ R f) x ≤
      Energy.LocalSlope.apply f x + (Metric.ball x₀ R)ᶜ.indicator 1 x
theorem enorm_truncateFun_sub_le (x₀) (R) (f) (B) (x) :
    ‖truncateFun x₀ R f x - B.indicator (1 : X → ℝ) x‖ₑ ≤
      ‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (Metric.ball x₀ R)ᶜ.indicator 1 x
theorem lipschitzWith_truncateFun_of_locallyLipschitz [ProperSpace X] (x₀ : X) (R : ℝ)
    {f : X → ℝ} (hf : LocallyLipschitz f) : ∃ K : ℝ≥0, LipschitzWith K (truncateFun x₀ R f)
def Test.truncateOfLocallyLipschitz [ProperSpace X] (x₀ : X) (R : ℝ) (f : X → ℝ)
    (hf : LocallyLipschitz f) : Test X   -- toFun := truncateFun x₀ R f
theorem coe_truncateOfLocallyLipschitz … : (Test.truncateOfLocallyLipschitz x₀ R f hf : X → ℝ) = truncateFun x₀ R f
```

Section `Bridge`, `[MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]`:

```lean
theorem cost_truncateOfLocallyLipschitz_le (ν : Measure X) (x₀) (R) (hf : LocallyLipschitz f) :
    cost ν (Test.truncateOfLocallyLipschitz x₀ R f hf) ≤
      ∫⁻ x, Energy.LocalSlope.apply f x ∂ν + ν (Metric.ball x₀ R)ᶜ
theorem indicatorDistance_truncateOfLocallyLipschitz_le (ν) (x₀) (R) (hf) (B) :
    indicatorDistance ν (Test.truncateOfLocallyLipschitz x₀ R f hf) B ≤
      ∫⁻ x, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν + ν (Metric.ball x₀ R)ᶜ
theorem tendsto_indicatorDistance_truncateOfLocallyLipschitz (ν) [IsFiniteMeasure ν] (x₀) {B}
    {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n)) (hconv) :
    Tendsto (fun n : ℕ => indicatorDistance ν (Test.truncateOfLocallyLipschitz x₀ n (f n) (hf n)) B) atTop (𝓝 0)
theorem liminf_cost_truncateOfLocallyLipschitz_le (ν) [IsFiniteMeasure ν] (x₀) (hf) :
    liminf (fun n : ℕ => cost ν (Test.truncateOfLocallyLipschitz x₀ n (f n) (hf n))) atTop ≤
      liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop
theorem exists_approximatingSequence_of_locallyLipschitz (ν : Measure X) [IsFiniteMeasure ν]
    {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    ∃ g : ApproximatingSequence ν B,
      liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop
theorem perimeter_le_liminf_of_locallyLipschitz (ν : Measure X) [IsFiniteMeasure ν]
    {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n)) (hconv : …) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop
```

Proof shape. The two pointwise bounds are the accepted phase-3 proofs restated for an arbitrary
real function (`Test.truncate`'s statements and bodies are untouched; `Test.truncate_toFun` links
them). Global Lipschitz bound: `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
(isCompact_closedBall x₀ (R + 1)) hf.locallyLipschitzOn` gives `L`; constant `L + 1`; four cases
on `dist x x₀ ≤ R + 1`, `dist y x₀ ≤ R + 1`: both inside, the product secant bound
`abs_mul_sub_mul_le` with `LipschitzOnWith.dist_le_mul`; one outside, the outside value is `0`
and `truncateFun ≤ cutoff ≤ dist` (`cutoff_le_dist_of_le`: `cutoff ≤ R + 1 - dist x x₀ ≤
dist y x₀ - dist x x₀ ≤ dist x y`); both outside, `0`. The bridge lemmas are the phase-3 proofs
with the new test. No uniform constant, boundedness or bounded support of `f n`; `B` arbitrary;
empty carrier by the zero test; `ENNReal` throughout. `MetricBV.lean` unchanged; root import added.

### Phase 17 independent client (`research/audits/MetricBVLocalLipschitzAudit.lean`)

| Client | Content |
| --- | --- |
| `truncationLipschitz`, `explicitSequence`, `existenceForm`, `perimeterBound` | full signatures (explicit sequence: convergence and liminf bound) |
| `globalCase` | the globally Lipschitz bridge as a special case (`LipschitzWith.locallyLipschitz`) |
| `emptyCarrier` | `X = Empty`, any measure, set and sequence |
| `zeroMeasure` | the zero measure on `ℝ`: every set has perimeter `0` |
| `emptySetZero` | the empty set with the zero sequence |
| `squareLocallyLipschitz`, `squareNotLipschitz` | `x ↦ x²` is locally Lipschitz (`ContDiff.locallyLipschitz`) and has no global constant |
| `square_indicator_dist`, `square_slope_integral` | for `(δ₀ + δ₁)/2`: `x² = 1_{{1}}` on both atoms; slope integral `= 1` (`apply_eq_norm_gradient`, gradient `2x`) |
| `squareBound` | hence `perimeter twoAtom {1} ≤ 1` from a non-globally-Lipschitz constant sequence |

All thirteen reports and the direct reports of the fourteen new owner declarations are
`[propext, Classical.choice, Quot.sound]`; the seventeen earlier MetricBV clients recompile
strictly; the full default `lake build` (3671 jobs) passed.

Metadata. Source check recorded (Ambrosio--Di Marino--Gigli Definition 3.3 = globally Lipschitz,
global `L¹`, the phase-3 class; Remark 3.5 = locally Lipschitz/`L¹_loc` variants; this segment:
locally Lipschitz with global `L¹` on proper spaces). Chapter 45's former "test class not
matched" sentence replaced by the source-faithful statement (both bounds stated; `L¹_loc` and
the relaxation-infimum equality not local theorems), four `research/tasks.json` pins refreshed;
`literature.json` row for Ambrosio--Di Marino--Gigli updated likewise; HANDOFF head statement and
phase-17 paragraph (phase 16 marked accepted), root README, progress hub, `diagram:BV`
description (node state unchanged: formalized for the log-concave identification) updated; views
regenerated from an isolated index/object store, `update.py --check`, `test_views.py` (isolated
index) and `check_blueprint.py` passed; real index unstaged; `git diff --check` passed.
Obstacles: `Energy.LocalSlope` must be qualified under `FunctionalInequalities` in clients; the
non-Lipschitz proof needed explicit absolute-value rewrites. Next (Codex chooses): the named
relaxation infimum over locally Lipschitz global-`L¹` sequences and its equality with `perimeter`
on proper spaces; bounded-ball `L¹` convergence as a separate exact notion.

## Phase 16 (2026-09-28, scoped endpoint)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `BVIdentification.lean` `38130b0f…bb60b69f`, `literature.json` `f7fd0a08…41c2ef0d`, `README.md` `02d35d63…71b50838`,
`HANDOFF.md` `0640f4c4…eca2d370`, `nodes.json` `12bd0ccf…3038c80f`, `research/tasks.json` `aeef597c…91121c4a`, chapter 45
`4fef67e1…d3c10722`; not edited: `codex-bv-overnight-review.md` (`0dc9ffac…fcb3799f` at start; Codex may append),
`moment-map-spectral.md` `7106fbc3…29b8bee5`. The phase-15 receipt does not cover this snapshot.

### Placement plan

Object and role: identification of the existing BV Cheeger constants of a law and of its
closed-support law, and the frontend `intrinsicHalfConstant μ = Isoperimetry.constant μ` for
finite-dimensional log-concave probability laws. Owner: the Cheeger integration module
`KLS/Geometry/Cheeger/BVIdentification.lean` (extend; it already imports `BVConstant`,
`Equality` and `MetricBVMinkowski`), adding the imports `Perimeter/ConvexSupport` and
`LogConcave/Transport` at this integration layer only; `MetricBV.lean`, the slope layer and
`ConvexSupport.lean` gain no application import. Setting for the constants:
`[NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
[BorelSpace E] [SecondCountableTopology E]`, `hconv : Convex ℝ (ν : Measure E).support`.

Correspondence (proved, not assumed). With `S = (ν : Measure E).support` and `ι = Subtype.val`:
trace `B ↦ ι ⁻¹' B` (measurable by `measurable_subtype_coe`; mass
`closedSupportLaw ν (ι ⁻¹' B) = ν (S ∩ B) = ν B` by `closedSupportLaw_apply`,
`Subtype.image_preimage_coe`, `measure_inter_conull` with `measure_compl_support`); image
`A ↦ ι '' A` (measurable by `MeasurableSet.subtype_image`; mass `ν (ι '' A) = closedSupportLaw ν A`;
trace `ι ⁻¹' (ι '' A) = A` by injectivity); perimeters agree by phase 15. Declarations:
`measure_closedSupportLaw_preimage` (trace mass), `symmetricConstant_closedSupportLaw_eq`,
`halfConstant_closedSupportLaw_eq` (both by two `le_iInf`/`iInf_le` inequalities over the actual
admissible families; empty families, `⊤` perimeters, zero ratios and mass `1/2` need no special
case), then `intrinsicHalfConstant_eq_constant_of_convex` (explicit structural hypothesis: the
intrinsic law has convex closed support) and `intrinsicHalfConstant_eq_constant`
(`hμ : LogConcave μ`, convexity from `hμ.intrinsicMeasure.convex_support`), via
`halfConstant_intrinsicMeasure_eq_constant` (phase 12). No claim for nonconvex supports.

Client: `research/audits/MetricBVIntrinsicIdentificationAudit.lean`: full signatures, the
correspondence masses, the uniform law on `[0, 1]` (proper convex support) with both constants
transferred, `dirac 0` (singleton support; empty admissible family, all constants `⊤`), and the
log-concave frontend including the intrinsic symmetric form. Documentation: HANDOFF, root README,
progress hub, `diagram:BV` (assessment decided from the exact statement; its label and scope are
the closed-support identification), chapter-45 prose sentence on `h_BV(K, ν)` and the two
literature rows, all with the log-concave/convex-support hypotheses visible; pins refreshed if
chapter 45 changes. Validation: strict compilation, full `lake build`, all MetricBV clients,
standard axioms, isolated-index progress generation with `update.py --check`, `test_views.py`,
`check_blueprint.py`, frozen full `research/verify.py`, receipt under ignored
`build/audit/metric-bv-intrinsic-identification/`.

### Phase 16 stage status

- [x] correspondence, constant equalities, log-concave frontend, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-intrinsic-identification/receipt.md`)

### Phase 16 exact declarations

Placement refinement: the trace-mass lemma is generic in the closed-support law and went to its
owner, `Perimeter/MetricBV.lean` section `ClosedSupport` (no new import), as
`closedSupportLaw_preimage` (the plan's `measure_closedSupportLaw_preimage`):

```lean
theorem closedSupportLaw_preimage (ν : ProbabilityMeasure X) (B : Set X) :
    (closedSupportLaw ν : Measure (ν : Measure X).support) (Subtype.val ⁻¹' B) = (ν : Measure X) B
```

`Cheeger/BVIdentification.lean` (new imports `Perimeter/ConvexSupport`, `LogConcave/Transport`),
sections `ClosedSupport` and `IntrinsicClosedSupport`:

```lean
theorem symmetricConstant_le_div {X} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (ν : ProbabilityMeasure X) {A : Set X} (hA : MeasurableSet A) (h0 : 0 < ν A) (h1 : ν A < 1) :
    symmetricConstant ν ≤ perimeter ν A / min (ν A) (1 - ν A)
theorem halfConstant_le_div {X} … (h1 : ν A ≤ 1 / 2) : halfConstant ν ≤ perimeter ν A / ν A
-- [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
-- [BorelSpace E] [SecondCountableTopology E]
theorem image_closedSupportLaw (ν : ProbabilityMeasure E) (hconv : Convex ℝ (ν : Measure E).support)
    {A : Set (ν : Measure E).support} (hA : MeasurableSet A) :
    MeasurableSet (Subtype.val '' A) ∧ ν (Subtype.val '' A) = closedSupportLaw ν A ∧
      perimeter ν (Subtype.val '' A) = perimeter (closedSupportLaw ν) A
theorem symmetricConstant_closedSupportLaw_eq (ν) (hconv) :
    symmetricConstant (closedSupportLaw ν) = symmetricConstant ν
theorem halfConstant_closedSupportLaw_eq (ν) (hconv) :
    halfConstant (closedSupportLaw ν) = halfConstant ν
-- additionally [FiniteDimensional ℝ E]
theorem intrinsicHalfConstant_eq_constant_of_convex (μ : ProbabilityMeasure E)
    (hconv : Convex ℝ (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support) :
    intrinsicHalfConstant μ = Isoperimetry.constant μ
theorem intrinsicHalfConstant_eq_constant (μ : ProbabilityMeasure E) (hμ : LogConcave μ) :
    intrinsicHalfConstant μ = Isoperimetry.constant μ
theorem symmetricConstant_intrinsicClosedSupportLaw_eq_constant (μ) (hμ : LogConcave μ) :
    symmetricConstant (intrinsicClosedSupportLaw μ) = Isoperimetry.constant μ
```

Proof shape. Constants: `le_antisymm`; closed-support ≤ ambient by `le_iInf` over the ambient
admissible `B`, bounding by the trace (`measurable_subtype_coe`, trace mass, phase-15 perimeter
equality); ambient ≤ closed-support by `le_iInf` over the admissible `A`, bounding by the image
(`MeasurableSet.subtype_image`, `closedSupportLaw_apply`, `Subtype.val_injective.preimage_image`).
Frontend: unfold `intrinsicHalfConstant`/`intrinsicClosedSupportLaw`, rewrite with
`halfConstant_closedSupportLaw_eq`, conclude with phase-12 `halfConstant_intrinsicMeasure_eq_constant`;
log-concave convexity via `LogConcave.intrinsicMeasure` and `LogConcave.convex_support`
(finite-dimensional ⇒ proper). No definition or earlier signature changed.

### Phase 16 independent client (`research/audits/MetricBVIntrinsicIdentificationAudit.lean`)

| Client | Content |
| --- | --- |
| `traceMass`, `imageCorrespondence` | the actual correspondence (mass, measurability, perimeter) |
| `symmetricTransfer`, `halfTransfer`, `allConstants` | constant equalities; with phase 12 all equal the Minkowski constant |
| `frontendOfConvex`, `frontendLogConcave`, `frontendSymmetric` | the structural and log-concave frontends |
| `uniformInterval_support`, `uniformIntervalConstants` | proper convex support `Icc 0 1` of the uniform law |
| `diracZero_support`, `diracConstantsTop` | singleton support: empty admissible family, all constants `⊤` on both laws |
| `diracFrontend` | the log-concave frontend for an actual log-concave law (`logConcave_dirac`) |

All thirteen reports and the direct reports of the nine new owner declarations are
`[propext, Classical.choice, Quot.sound]`; the sixteen earlier MetricBV clients and
`CheegerEqualityAudit.lean` recompile strictly; the full default `lake build` (3670 jobs) passed.

Documentation. `diagram:BV` is marked formalized (`local_strict_client` evidence: the frozen
`BVIdentification.lean` with its SHA-256), label `Closed-support BV identification (log-concave)`,
with a description stating exactly what the ✓ covers and what it does not. Chapter 45's sentence on
`h_BV(K, ν)` now records the local log-concave (convex-support) proof, keeping the
Ambrosio--Di Marino--Gigli unrestricted test class, nonconvex supports and general metric-measure
comparisons as literature; its four `research/tasks.json` pins refreshed. `literature.json` rows
for Ambrosio--Di Marino--Gigli and De Ponti--Mondino updated (both remain `partial` by the
coverage rule). HANDOFF (phase 15 accepted, phase 16 paragraph, head statement), root README and
progress hub (including its current-handoff sentence) updated with the log-concave hypothesis
visible; KLS open. Views regenerated from an isolated index/object store; `update.py --check`,
`test_views.py` (isolated index) and `check_blueprint.py` passed; real index unstaged;
`git diff --check` passed. Obstacles: an unused-section-variable omission in the client.

This phase is the scoped endpoint; no further workstream was started.

## Phase 15 (2026-09-28, resumed after a connection outage)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `FunctionalInequalities.lean` `83de62e9…0fbd8940`, `MetricBV.lean` `975f776e…4b4e0041` (not edited),
`research/tasks.json` `aeef597c…91121c4a` (not edited), `README.md` `69564797…199ae719`, `HANDOFF.md` `5500bf64…0aba946b`,
`nodes.json` `ae2a0328…2e1a3691`; not edited: `codex-bv-overnight-review.md` (`ba43b44b…6cb962f1` at start; Codex may
append), `moment-map-spectral.md` `7106fbc3…29b8bee5`. The phase-14 receipt does not cover this
snapshot.

### Placement plan

Object and role: discharge the phase-14 retraction hypothesis for a probability law with convex
closed support in a real Hilbert space, using the actual nearest-point projection, and conclude
`perimeter (ν : Measure E) B = perimeter (closedSupportLaw ν) (Subtype.val ⁻¹' B)` for every
`B`, assuming only `Convex ℝ (ν : Measure E).support` (no retraction, extension, slope bound or
perimeter comparison). Scope: `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
[MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]` (no finite dimension needed); the
support may be unbounded, a singleton, or proper; no density or full ambient support.

New narrow module `KLS/Geometry/Perimeter/ConvexSupport.lean` (the projection needs
`Mathlib.Analysis.InnerProductSpace.Projection.Minimal`, which the generic metric owner
`MetricBV.lean` must not import; no existing owner of convex projections exists in the
repository, and its only consumer is this perimeter bridge, so it is not extracted to an
`Analysis` family). Imports: `Perimeter/MetricBV`, that Mathlib file. Namespace
`FunctionalInequalities.KLS.MetricBV`. Declarations, for a nonempty complete convex `K`:
`nearestPoint hne hc hconv : E → K` (`Classical.choose` of
`exists_norm_eq_iInf_of_complete_convex`), `norm_sub_nearestPoint` (attains the infimum),
`inner_sub_nearestPoint_le` (variational inequality via `norm_eq_iInf_iff_real_inner_le_zero`),
`nearestPoint_coe` (fixes `K`: the variational inequality at `w = u` gives `‖u - p u‖² ≤ 0`),
`lipschitzWith_nearestPoint` (`LipschitzWith 1`: adding the two variational inequalities gives
`‖p u₁ - p u₂‖² ≤ ⟪u₁ - u₂, p u₁ - p u₂⟫ ≤ ‖u₁ - u₂‖ ‖p u₁ - p u₂‖`); then
`perimeter_eq_closedSupportLaw_of_convex` (support nonempty by `Measure.nonempty_support` for the
nonzero probability law, complete as a closed subset of a complete space, full mass by
`Measure.measure_compl_support`, then phase 14 with `closedSupportLaw ν` definitionally the comap
law). Root `FunctionalInequalities.lean` gains the import. No existing file other than the root,
docs and generated views is edited; no `tasks.json` pin is affected. The optional
`LogConcave.convex_support` frontend and the `intrinsicHalfConstant` identification are not part
of this segment.

Client: `research/audits/MetricBVConvexSupportAudit.lean` (new): full signatures, the
projection's properties, the measurable-`B` form, a proper bounded convex support (the
uniform law on `[0, 1]` in `ℝ`, with support computed to be `Icc 0 1`), a singleton support
(`dirac 0` on `ℝ`), and a consequence. Validation: strict compilation, full `lake build`, all
MetricBV clients, standard transitive axioms, isolated-index progress generation with
`update.py --check`, `test_views.py`, `check_blueprint.py`, frozen full `research/verify.py`,
receipt under ignored `build/audit/metric-bv-convex-support/`.

### Phase 15 stage status

- [x] nearest-point projection, convex-support equality, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-convex-support/receipt.md`)

### Phase 15 exact declarations

New module `KLS/Geometry/Perimeter/ConvexSupport.lean` (imports `Perimeter/MetricBV`,
`Mathlib.Analysis.InnerProductSpace.Projection.Minimal`), namespace `MetricBV`. Section
`NearestPoint`, `{E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E}`:

```lean
def nearestPoint (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) (u : E) : K
theorem norm_sub_nearestPoint (hne) (hc) (hconv) (u : E) :
    ‖u - nearestPoint hne hc hconv u‖ = ⨅ w : K, ‖u - w‖
theorem inner_sub_nearestPoint_le (hne) (hc) (hconv) (u : E) {w : E} (hw : w ∈ K) :
    ⟪u - nearestPoint hne hc hconv u, w - nearestPoint hne hc hconv u⟫ ≤ 0
theorem nearestPoint_coe (hne) (hc) (hconv) (z : K) : nearestPoint hne hc hconv z = z
theorem lipschitzWith_nearestPoint (hne) (hc) (hconv) : LipschitzWith 1 (nearestPoint hne hc hconv)
```

and, with `[CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]`:

```lean
theorem perimeter_eq_closedSupportLaw_of_convex (ν : ProbabilityMeasure E)
    (hconv : Convex ℝ (ν : Measure E).support) (B : Set E) :
    perimeter (ν : Measure E) B =
      perimeter (closedSupportLaw ν : Measure (ν : Measure E).support) (Subtype.val ⁻¹' B)
```

Proof shape. `nearestPoint` is `Classical.choose` of `exists_norm_eq_iInf_of_complete_convex`;
the variational inequality is `norm_eq_iInf_iff_real_inner_le_zero`; fixed points by
`real_inner_self_nonpos`; nonexpansiveness: with `a = p u₁`, `b = p u₂`, the variational
inequalities at `b` and `a` add to `‖a - b‖² ≤ ⟪u₁ - u₂, a - b⟫ ≤ ‖u₁ - u₂‖ ‖a - b‖`
(`inner_sub_left`, `inner_neg_right`, `real_inner_le_norm`, `nlinarith`). The main theorem:
nonempty support by `Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)`, completeness by
`isClosed_support.isComplete`, full mass by `Measure.measure_compl_support`
(second countable ⇒ hereditarily Lindelöf), then `perimeter_eq_comap_subtype_of_retraction`.
No other source file changed except the root import; no pin affected.

### Phase 15 independent client (`research/audits/MetricBVConvexSupportAudit.lean`)

| Client | Content |
| --- | --- |
| `projectionProperties` | infimum, variational inequality, fixed points, `LipschitzWith 1` |
| `convexSupport`, `convexSupportMeasurable` | full signature and the measurable-`B` form |
| `traceDetermines` | on a convex support, sets with the same trace have equal perimeters |
| `uniformInterval_support` | the uniform law on `[0, 1]` has support exactly `Icc 0 1` (closed full-mass set; interior in the Lebesgue support; closure) |
| `uniformIntervalConvex` | the equality for that proper convex support, which misses `2` |
| `diracZero_support`, `diracSingleton` | `dirac 0` has support `{0}`; every set has perimeter `0` via the one-point support |

All eight reports and the direct reports of the six new owner declarations are
`[propext, Classical.choice, Quot.sound]`; the fifteen earlier MetricBV clients recompile
strictly; the full default `lake build` (3670 jobs) passed.

Metadata: phase 14 marked accepted and phase-15 sentence (pending Codex review) in `HANDOFF.md`;
root `README.md`, progress-hub prose and the `diagram:BV` description updated (still `partial`,
label unchanged, KLS open); Blueprint, `literature.json` and `research/tasks.json` unchanged;
views regenerated from an isolated index/object store, `update.py --check`, `test_views.py`
(isolated index) and `check_blueprint.py` passed; real index unstaged; `git diff --check` passed.
Obstacles: an explicit coercion `(nearestPoint … : E)` in the nonexpansiveness proof. Suggested
next (for Codex to decide): the `intrinsicHalfConstant` identification, transporting measurable
sets and masses between the closed-support law and the intrinsic coordinate law (whose support
is convex for log-concave laws, `LogConcave.convex_support`).

## Phase 14 (2026-09-28)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `Energy/LocalSlope/Basic.lean` `089bd36e…67f74d66` (four consistent pins in `research/tasks.json`),
`MetricBV.lean` `7d8c1fc0…b0163b5c`, `research/tasks.json` `88cfd043…f174d027`, `README.md` `c280b8bb…ef8cca7c`, `HANDOFF.md`
`9d4cf169…3e6ef120`, `nodes.json` `92a39b0b…c675e1e0`; not edited: `codex-bv-overnight-review.md` (`e3973fe3…458f0799` at start;
Codex may append), `moment-map-spectral.md` `7106fbc3…29b8bee5`. The phase-13 receipt does not
cover this snapshot.

### Placement plan

Object and role: a structural retraction theorem for the existing perimeter, partial progress
toward the closed-support identification (not yet `closedSupportLaw` equality for arbitrary
supports, not the closed convex projection, not `intrinsicHalfConstant`). Statement: for a finite
Borel measure `ν` on a metric space `X`, a measurable `s` with `ν sᶜ = 0`, and an actual map
`r : X → s` with `LipschitzWith 1 r` and `r z = z` for `z : s`,
`perimeter ν B = perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B)`.

(1) Generic tool, owner `Energy/LocalSlope/Basic.lean` (section `Metric`, no import):
`apply_comp_le_of_lipschitzWith_one` — for `r : X → Y` with `LipschitzWith 1 r`,
`apply (g ∘ r) x ≤ apply g (r x)`, proved secant by secant: if `r x' = r x` the secant of
`g ∘ r` is `0`; otherwise `0 < dist (r x') (r x) ≤ dist x' x < ρ`, so the secant of `g ∘ r` is
at most the secant of `g` at `r x'` (larger or equal numerator ratio with smaller denominator);
`x' = x` gives `0/0 = 0`. Not inferred from global Lipschitz constants. The four pins of this
file are refreshed afterwards.
(2) Bridge, owner `Perimeter/MetricBV.lean`, section `SubsetRestriction` (placed after
`LipschitzBridge`, whose `perimeter_le_liminf_of_lipschitz` it uses; same imports, no split):
`perimeter_le_comap_subtype_of_retraction` — for every actual approximating sequence `g` of the
trace, the composed functions `g n ∘ r` are globally Lipschitz but in general NOT of bounded
support, so they are not claimed to be tests; full mass gives `ν.restrict s = ν`
(`Measure.restrict_eq_self_of_ae_mem`), `lintegral_subtype_comap` moves both the `L¹` error and
the slope integral to the subtype, where `g n (r z) = g n z` and the slope bound applies at
`z` (`r z = z`), so the `L¹` errors equal the trace errors (`→ 0`) and the slope integrals are at
most the trace costs; the finite-measure bridge then bounds `perimeter ν B` by the liminf of the
trace costs, and `le_iInf` over the trace class concludes (empty class: `⊤`, vacuous).
`perimeter_eq_comap_subtype_of_retraction` combines with phase-13 `perimeter_comap_subtype_le`.
Measurability of `B` is not needed (the measurable-`B` form is a client). No finiteness of the
perimeter, no nonempty class, no slope-integral or perimeter comparison is assumed.

Client: `research/audits/MetricBVSupportRetractionAudit.lean` (new): full signatures, the
collapsed-point slope case, the genuine proper retract `Set.projIcc 0 1` onto `Icc 0 1 ⊂ ℝ` for
`volume.restrict (Icc 0 1)` and for the two-atom law `(δ₀ + δ₁)/2`, the zero measure, and a
consequence beyond an alias (finite perimeter transfers in both directions; the trace of
`Iic (1/2)` under the two-atom law has the ambient perimeter `0`). Validation: strict
compilation of both modules, full `lake build`, all MetricBV clients, standard transitive
axioms, pin refresh, isolated-index progress generation with `update.py --check`,
`test_views.py`, `check_blueprint.py`, frozen full `research/verify.py`, receipt under ignored
`build/audit/metric-bv-support-retraction/`.

### Phase 14 stage status

- [x] slope composition bound, retraction inequality/equality, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-support-retraction/receipt.md`)

### Phase 14 exact declarations

`Energy/LocalSlope/Basic.lean`, section `Metric` (`{X : Type*} [MetricSpace X]`):

```lean
theorem apply_comp_le_of_lipschitzWith_one {Y : Type*} [MetricSpace Y] {r : X → Y}
    (hr : LipschitzWith 1 r) (g : Y → ℝ) (x : X) : apply (g ∘ r) x ≤ apply g (r x)
```

`Perimeter/MetricBV.lean`, end of section `SubsetRestriction`
(`[MetricSpace X] [MeasurableSpace X] [BorelSpace X]`):

```lean
theorem perimeter_le_comap_subtype_of_retraction (ν : Measure X) [IsFiniteMeasure ν]
    {s : Set X} (hs : MeasurableSet s) (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r)
    (hrs : ∀ z : s, r z = z) (B : Set X) :
    perimeter ν B ≤ perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B)
theorem perimeter_eq_comap_subtype_of_retraction (ν : Measure X) [IsFiniteMeasure ν]
    {s : Set X} (hs : MeasurableSet s) (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r)
    (hrs : ∀ z : s, r z = z) (B : Set X) :
    perimeter ν B = perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B)
```

Proof shape. Slope: `iInf₂_mono`/`iSup₂_le`; for each `x'` in the `ρ`-ball, if
`dist (r x') (r x) = 0` then `r x' = r x` and the secant is `ofReal 0`; otherwise
`div_le_div_of_nonneg_left` with `0 < dist (r x') (r x) ≤ dist x' x` and `le_iSup₂` at `r x'`
(inside the `ρ`-ball). Bridge: `ν.restrict s = ν` (`restrict_eq_self_of_ae_mem`, `ae_iff`);
`lintegral_subtype_comap` rewrites `∫ h dν = ∫ h ∘ val d(ν.comap val)`; on `s`,
`g n (r z) = g n z`, so the `L¹` errors of `g n ∘ r` are exactly the trace errors
(`tendsto_congr` with the trace sequence's convergence) and their slope integrals are at most the
trace costs (slope lemma at `z`, `r z = z`); `perimeter_le_liminf_of_lipschitz` (finite measure;
Lipschitz constants `K * 1`) and `le_iInf` over the actual trace class conclude. No bounded support
is claimed for `g n ∘ r`; no finiteness of perimeters, nonempty class, or comparison is assumed;
`B` need not be measurable. Equality with phase-13 `perimeter_comap_subtype_le`.

### Phase 14 independent client (`research/audits/MetricBVSupportRetractionAudit.lean`)

| Client | Content |
| --- | --- |
| `slopeComposition`, `retractionLe`, `retractionEq` | full signatures |
| `collapsedSlope` | a fully collapsing constant map: the bound holds and the composed slope is `0` |
| `retractionEqMeasurable` | the requested form with measurable `B` |
| `finiteTransfer`, `zeroTransfer` | finiteness transfers both ways; zero trace perimeter forces zero ambient perimeter |
| `projIccRetraction` | `projIcc 0 1` is `1`-Lipschitz, fixes `Icc 0 1`, which is proper (`2 ∉ Icc 0 1`) |
| `uniformInterval` | equality for `volume.restrict (Icc 0 1)` on `ℝ` |
| `twoAtomInterval` | equality for `(δ₀ + δ₁)/2` (atoms in `Icc 0 1`) |
| `zeroMeasure` | equality for the zero measure |

All eleven reports and the direct reports of the three new owner declarations are
`[propext, Classical.choice, Quot.sound]`; the fourteen earlier MetricBV clients recompile
strictly; the full default `lake build` (3669 jobs) passed.

Metadata: the four `research/tasks.json` pins of `Energy/LocalSlope/Basic.lean` refreshed; phase 13
marked accepted and phase-14 sentence (pending Codex review) in `HANDOFF.md`; root `README.md`,
progress-hub prose and the `diagram:BV` description updated (still `partial`, label unchanged, KLS
open); Blueprint and `literature.json` unchanged; views regenerated from an isolated index/object
store, `update.py --check`, `test_views.py` (isolated index) and `check_blueprint.py` passed; real
index unstaged; `git diff --check` passed. Obstacles: a constant map is `LipschitzWith 0`
(weakened to `1`); the two-atom measure needed an explicit `IsFiniteMeasure` instance. Suggested
next (for Codex to decide): the closed convex support projection as an actual nonexpansive
retraction in a Hilbert space, giving `closedSupportLaw` equality for convex supports.

## Phase 13 (2026-09-28, resumed workflow)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `Energy/LocalSlope/Basic.lean` `ffba9ad3…806896ae` (pinned four times in `research/tasks.json`, pins
consistent), `MetricBV.lean` `479a926a…45b02412`, `research/tasks.json` `0ddff984…3e7f87f5`, `README.md` `785bd2c0…dd63803c`,
`HANDOFF.md` `23ed3fd7…70dc1efe`, `nodes.json` `34cc1372…d0ba8bcc`; not edited: `codex-bv-overnight-review.md`
(`8c732381…50a6a2e5` at start; Codex may append), `moment-map-spectral.md` `7106fbc3…29b8bee5`. The phase-12
receipt does not cover this snapshot.

### Placement plan

Object and role: a one-sided comparison, partial progress toward the closed-intrinsic-support
identification: restriction to a measurable subset, in particular the closed measure support,
does not increase the metric BV perimeter. Target (actual definitions):
`perimeter (closedSupportLaw ν : Measure _) (Subtype.val ⁻¹' B) ≤ perimeter (ν : Measure X) B`
for `[MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]`, a
probability law `ν` and `B : Set X`. No reverse inequality, no constant equality, no
Minkowski/BV pointwise statement, no literature test-class identification.

(1) Generic tool, owner `Energy/LocalSlope/Basic.lean` (section `Metric`, no new import):
`apply_comp_le_of_isometry` — for an isometry `e : Y → X`, `apply (f ∘ e) y ≤ apply f (e y)`
(each punctured `Y`-ball secant is an `X`-ball secant at the same distance; `iInf`/`iSup`
monotonicity). The four pins of this file in `research/tasks.json` are refreshed after the edit.
(2) Object restriction, owner `Perimeter/MetricBV.lean` (same dependencies and responsibility;
no split, no new import), new section `SubsetRestriction` before `ClosedSupport`:
`Test.restrict f s : Test s` (`f ∘ Subtype.val`; Lipschitz by composition with the
`1`-Lipschitz inclusion, bounded range by inclusion of ranges, bounded support as the preimage of
a bounded set under the isometric inclusion); for measurable `s` and any measure `ν`, with
`ν.comap Subtype.val`: `cost_restrict_le` (pointwise slope bound, `lintegral_subtype_comap`,
`setLIntegral_le_lintegral`), `indicatorDistance_restrict_le` (the pulled-back indicator is the
indicator of the preimage), `ApproximatingSequence.restrict` (squeeze of the distances),
`perimeter_comap_subtype_le` (`le_iInf` over the actual class, `perimeter_le_sequence` for the
restricted sequence and `liminf_le_liminf` of the costs; an empty ambient class gives `⊤` on the
right and the bound is vacuous). (3) Specialization in section `ClosedSupport`:
`perimeter_closedSupportLaw_le` (the support is closed, hence measurable; `closedSupportLaw ν`
is by definition the comap law). Measurability of `B` is not used; the requested measurable-`B`
form is a client.

Client: `research/audits/MetricBVSupportRestrictionAudit.lean` (new): full signatures, the
isometry slope lemma, the measurable-`B` form, a proper closed support (the two-atom law
`(δ₀ + δ₁)/2` on `ℝ`: `0 ∈ support`, `1/2 ∉ support`) with the comparison instantiated, the empty
set, top ambient perimeter (vacuous), the whole space. Validation: strict compilation of both
modules, dependent modules and all MetricBV clients; standard transitive axioms;
`research/tasks.json` pin refresh; isolated-index progress generation, `update.py --check`,
`check_blueprint.py`, `test_views.py` (isolated index); frozen full `research/verify.py`; receipt
under ignored `build/audit/metric-bv-support-restriction/`.

### Phase 13 stage status

- [x] slope lemma, test/sequence restriction, perimeter comparisons, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-support-restriction/receipt.md`)

### Phase 13 exact declarations

`Energy/LocalSlope/Basic.lean`, section `Metric` (`{X : Type*} [MetricSpace X]`):

```lean
theorem apply_comp_le_of_isometry {Y : Type*} [MetricSpace Y] {e : Y → X} (he : Isometry e)
    (f : X → ℝ) (y : Y) : apply (f ∘ e) y ≤ apply f (e y)
```

`Perimeter/MetricBV.lean`, new section `SubsetRestriction` (before `ClosedSupport`;
`[MetricSpace X] [MeasurableSpace X] [BorelSpace X]`):

```lean
def Test.restrict (f : Test X) (s : Set X) : Test s   -- toFun := fun z => f z
theorem cost_restrict_le (ν : Measure X) {s : Set X} (hs : MeasurableSet s) (f : Test X) :
    cost (ν.comap Subtype.val) (f.restrict s) ≤ cost ν f
theorem indicatorDistance_restrict_le (ν : Measure X) {s : Set X} (hs : MeasurableSet s)
    (f : Test X) (B : Set X) :
    indicatorDistance (ν.comap Subtype.val) (f.restrict s) (Subtype.val ⁻¹' B) ≤
      indicatorDistance ν f B
def ApproximatingSequence.restrict {ν : Measure X} {B : Set X} {s : Set X}
    (hs : MeasurableSet s) (g : ApproximatingSequence ν B) :
    ApproximatingSequence (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B)
theorem perimeter_comap_subtype_le (ν : Measure X) {s : Set X} (hs : MeasurableSet s)
    (B : Set X) :
    perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) ≤ perimeter ν B
```

and in section `ClosedSupport` (`[SecondCountableTopology X]`):

```lean
theorem perimeter_closedSupportLaw_le (ν : ProbabilityMeasure X) (B : Set X) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) (Subtype.val ⁻¹' B) ≤
      perimeter (ν : Measure X) B
```

Proof shape. Slope: `iInf₂_mono` over radii, `iSup₂_le` over `Y`-points, `le_iSup₂` at `e z` using
`he.dist_eq`. Test: Lipschitz via `hK.comp (LipschitzWith.subtype_val s)`, range inclusion,
support bounded through `Metric.isBounded_iff` (subtype distance = ambient distance). Cost:
pointwise slope bound, `lintegral_subtype_comap`, `setLIntegral_le_lintegral`. Distance: the
pulled-back indicator equals the ambient indicator at `z.1` (case split), then the same two
lemmas. Perimeter: `le_iInf` over the actual ambient class, `perimeter_le_sequence` for the
restricted sequence, `liminf_le_liminf` with `cost_restrict_le`. Support: closed hence measurable;
`closedSupportLaw ν` is definitionally the comap law. Measurability of `B` is not used. No
existing definition or signature changed.

### Phase 13 independent client (`research/audits/MetricBVSupportRestrictionAudit.lean`)

| Client | Content |
| --- | --- |
| `isometrySlope`, `restrictCost`, `restrictDistance`, `subsetPerimeter`, `supportPerimeter` | full signatures |
| `restrictSequence` | the restricted sequence consists of the restricted tests (definitional) |
| `supportPerimeterMeasurable` | the requested form with measurable `B` |
| `emptySet`, `wholeSpace` | traces of `∅` and `univ` have perimeter `0` on the support |
| `topAmbient` | top ambient perimeter: vacuous bound |
| `twoAtomSupport` | `(δ₀ + δ₁)/2` on `ℝ`: `0 ∈ support`, `1/2 ∉ support` (a proper closed support) |
| `twoAtomRestriction` | the trace of `Iic (1/2)` on that support has perimeter `0` (ambient content `0`) |

All twelve reports and the direct reports of the seven new owner declarations are
`[propext, Classical.choice, Quot.sound]`; the thirteen earlier MetricBV clients recompile
strictly; the full default `lake build` (3669 jobs) passed after the `LocalSlope/Basic.lean`
edit.

Metadata: the four `research/tasks.json` pins of `Energy/LocalSlope/Basic.lean` refreshed to the
edited file; phase-13 sentence (pending Codex review) in the BV paragraph of `HANDOFF.md`; root
`README.md`, progress-hub prose and the `diagram:BV` description updated (still `partial`, label
`NEXT: Closed-support BV identification` unchanged, KLS open); Blueprint chapter 45 and
`literature.json` unchanged (their closed-support wording remains accurate); views regenerated
from an isolated index/object store (adding the dirty `research/tasks.json` and chapter 45),
`update.py --check`, `test_views.py` (isolated index) and `check_blueprint.py` passed, real index
unstaged, `git diff --check` passed. Obstacles: explicit `Subtype.val : s → X` annotations and an
explicit integrand for `lintegral_subtype_comap`; `simp` normalizes `1/2` to `2⁻¹` before using
membership hypotheses (rewrote indicators explicitly). Suggested next (for Codex to decide): the
reverse direction, extending tests from the closed support (a McShane-type Lipschitz extension
with clamping and cutoff) to compare `intrinsicHalfConstant` with the intrinsic coordinate law.

## Phase 12 (2026-09-28, scoped endpoint)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `BVConstant.lean` `8261524d…90eba3f1`, `MinkowskiConstant.lean` `d0bb14fc…b1907bf2`,
`Equality.lean` `3135a91f…9b4bde5f`, `MetricBVMinkowski.lean` `4dec26c1…9f224eda`, `MetricBV.lean`
`479a926a…45b02412` (none of these is edited), `FunctionalInequalities.lean` `eae93c7d…a2f1f2d8`,
chapter 45 `e4142e78…c9a204d7`, `research/tasks.json` `8d63c8d6…73c09605`, `README.md` `4681019e…7de6083e`,
`HANDOFF.md` `a0fac114…236b8cfa`, `nodes.json` `bd6ba0a4…780dd81b`; not edited:
`codex-bv-overnight-review.md` (`6a7294f1…3cb962c9` at start; Codex may append),
`moment-map-spectral.md` `7106fbc3…29b8bee5`. The phase-11 receipt does not cover this snapshot.

### Placement plan

Object and role: identification of two existing Cheeger constants, the metric BV
`MetricBV.symmetricConstant` / `halfConstant` and `Isoperimetry.minkowskiConstant`, for a
probability law on a normed group with Borel structure (the scope where both are defined; it
contains the finite-dimensional inner-product frontend). New narrowly named integration module in
the Cheeger family, `KLS/Geometry/Cheeger/BVIdentification.lean`, importing `BVConstant`,
`Equality` (which provides `minkowskiConstant` via `MinkowskiConstant` and the frontend identity
`constant_eq_minkowskiConstant_intrinsic`) and `Perimeter/MetricBVMinkowski`; the basic perimeter
owner and the recovery bridge import no Cheeger constant. Root `FunctionalInequalities.lean` gains
the import. Declarations (namespace `MetricBV`): `minkowskiConstant_le_div` (helper: an admissible
set bounds the Minkowski infimum), `symmetricConstant_le_minkowskiConstant` (termwise
`perimeter ≤ content`, `ENNReal.div_le_div_right`), `minkowskiConstant_le_symmetricConstant`
(for each admissible `B`: infinite perimeter gives quotient `⊤` since the denominator is positive
and finite; finite perimeter uses the phase-11 eventual admissibility of the recovery sets and the
limit of their Minkowski quotients, via `ge_of_tendsto`), `symmetricConstant_eq_minkowskiConstant`,
`halfConstant_eq_minkowskiConstant` (via `halfConstant_eq_symmetricConstant`), and the frontend
corollaries `symmetricConstant_intrinsicMeasure_eq_constant`,
`halfConstant_intrinsicMeasure_eq_constant` (`= Isoperimetry.constant μ` for the intrinsic
coordinate law). Empty admissible families, top constants, zero ratios, dimension zero and mass
`1/2` need no special case (both sides are infima over the same admissible family); no admissible
set is assumed to exist; no pointwise perimeter/content equality is claimed.

Distinctions retained: this is the local Lean identification for the `Lip_b` sequential
relaxation defined here, on normed-group laws and the intrinsic coordinate law. Not covered:
`intrinsicHalfConstant` on the closed intrinsic support `K` (a metric subspace, where
`minkowskiConstant` is not defined), the literature test-class equivalence with
Ambrosio--Di Marino--Gigli's unrestricted relaxation (Lemma 2.1, Theorem 3.6), general
metric-measure or RCD comparisons, the Buser route beyond existing proofs, and dimension-free KLS.
Documentation: HANDOFF, root README, progress hub prose, `diagram:BV` description (the node stays
`partial`, since its scope includes the closed-support identification); chapter 45 prose sentence
that calls the BV--Minkowski Cheeger-infimum equality a literature comparison is corrected to
state the local theorem and the remaining closed-support and test-class distinctions (no
`\lean` tag added; `research/tasks.json` chapter-45 hash refreshed accordingly).
Client: `research/audits/MetricBVCheegerIdentificationAudit.lean`: full signatures, the
empty-family/top case (dimension zero), a realized intermediate-mass case (the two-atom law with
`B = Iic (1/2)`, both constants `0`), half-mass form. Validation: strict compilation of the new
module and all MetricBV clients, standard transitive axioms, isolated-index progress generation
and `update.py --check`, frozen full `research/verify.py`, receipt under ignored
`build/audit/metric-bv-cheeger-identification/`.

### Phase 12 stage status

- [x] identification module, frontend corollary, strict client, docs/Blueprint prose/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-cheeger-identification/receipt.md`)

### Phase 12 exact declarations

New module `KLS/Geometry/Cheeger/BVIdentification.lean` (imports `Cheeger/BVConstant`,
`Cheeger/Equality`, `Perimeter/MetricBVMinkowski`), namespace `FunctionalInequalities.KLS.MetricBV`,
`{V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]` (the helper omits
`BorelSpace`):

```lean
theorem minkowskiConstant_le_div (ν : ProbabilityMeasure V) {A : Set V} (hA : MeasurableSet A)
    (h0 : 0 < (ν : Measure V) A) (h1 : (ν : Measure V) A < 1) :
    Isoperimetry.minkowskiConstant ν ≤
      Isoperimetry.minkowskiContent ν A / min ((ν : Measure V) A) (1 - (ν : Measure V) A)
theorem symmetricConstant_le_minkowskiConstant (ν : ProbabilityMeasure V) :
    symmetricConstant ν ≤ Isoperimetry.minkowskiConstant ν
theorem minkowskiConstant_le_symmetricConstant (ν : ProbabilityMeasure V) :
    Isoperimetry.minkowskiConstant ν ≤ symmetricConstant ν
theorem symmetricConstant_eq_minkowskiConstant (ν : ProbabilityMeasure V) :
    symmetricConstant ν = Isoperimetry.minkowskiConstant ν
theorem halfConstant_eq_minkowskiConstant (ν : ProbabilityMeasure V) :
    halfConstant ν = Isoperimetry.minkowskiConstant ν
-- {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
-- [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
theorem symmetricConstant_intrinsicMeasure_eq_constant (μ : ProbabilityMeasure E) :
    symmetricConstant (Probability.intrinsicMeasure μ) = Isoperimetry.constant μ
theorem halfConstant_intrinsicMeasure_eq_constant (μ : ProbabilityMeasure E) :
    halfConstant (Probability.intrinsicMeasure μ) = Isoperimetry.constant μ
```

Proof shape. `≤`: `iInf_mono` over the four binders with
`ENNReal.div_le_div_right (perimeter_le_minkowskiContent ν hB)`. `≥`: `le_iInf` over admissible
`B`; if `perimeter B = ⊤`, the quotient is `⊤` by `ENNReal.top_div_of_ne_top` (denominator `≤ 1`);
otherwise `ge_of_tendsto` with the phase-11 quotient limit and, eventually, the phase-11 window plus
`minkowskiConstant_le_div` for the recovery sets. No admissible set is assumed; empty families,
`⊤` and zero values and mass `1/2` are covered by the same infima. Half-mass via the accepted
`halfConstant_eq_symmetricConstant`; frontend via the existing
`Isoperimetry.constant_eq_minkowskiConstant_intrinsic`. `BVConstant.lean`, `MinkowskiConstant.lean`,
`Equality.lean`, `MetricBV.lean` and `MetricBVMinkowski.lean` are byte-identical to the baseline;
root `FunctionalInequalities.lean` gains the import.

### Phase 12 independent client (`research/audits/MetricBVCheegerIdentificationAudit.lean`)

| Client | Content |
| --- | --- |
| `lowerInequality`, `upperInequality` | the two inequalities separately, full signatures |
| `identification`, `halfIdentification`, `threeConstants` | the equalities |
| `frontendSymmetric`, `frontendHalf` | intrinsic coordinate law: both BV constants `= Isoperimetry.constant μ` |
| `emptyFamilyTop` | `Fin 0 → ℝ`: empty admissible family, all three constants `⊤` |
| `twoAtomConstants` | `(δ₀ + δ₁)/2`, `B = Iic (1/2)` admissible (mass `1/2`, content `0`): all three constants `0` |

All nine reports and the direct reports of the seven owner declarations are
`[propext, Classical.choice, Quot.sound]`; the twelve earlier MetricBV clients and
`CheegerEqualityAudit.lean` (31 reports, consumer of `Equality.lean`) recompile strictly with
standard reports only.

Documentation. Resolved pending claims: HANDOFF's "final identification with
`Isoperimetry.constant` remains unproved" (now: proved for the intrinsic coordinate law, not for
`intrinsicHalfConstant` on the closed support); chapter 45's "the final BV--Minkowski
Cheeger-infimum equality remain literature comparisons" (now: local Lean proof for the
bounded-support relaxation on normed-space laws; closed support `K`, the Ambrosio--Di
Marino--Gigli unrestricted relaxation and general metric-measure comparisons remain literature;
no `\lean` tag added); `literature.json` rows for Ambrosio--Di Marino--Gigli and De
Ponti--Mondino (their stale "complement symmetry unformalized" wording also corrected). Phase 11
marked accepted in HANDOFF; root README, progress hub, `diagram:BV` description updated; the
`BV` node stays `partial` and its label unchanged (its scope includes the closed-support
identification), KLS open. `research/tasks.json`: the four chapter-45 evidence hashes refreshed
to the edited chapter. Views regenerated from an isolated index/object store (adding the dirty
`research/tasks.json` and chapter 45); `update.py --check`, `check_blueprint.py` (0 errors) and
`test_views.py` against that isolated index passed. `test_views.py` against the real index fails
only because the real index intentionally keeps the older chapter 45 (line anchors differ), as it
did since phase 2. Real index unstaged; `git diff --check` passed. Obstacles: `Probability`
namespace qualification in the client; an unused `BorelSpace` omitted for the helper.

This phase is the scoped endpoint of the coordinated workflow; no further workstream was started.

## Phase 11 (2026-09-28)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `MetricBV.lean` `624f1f73…85b66e24`, `MetricBVMinkowski.lean` `f2b8c3a5…b21ddb90`,
`README.md` `ff2e5903…9a090741`, `HANDOFF.md` `349e0a81…46b380db`, `nodes.json`
`3e800832…e34c6119`; not edited: `codex-bv-overnight-review.md` (`06f0b1f7…` at start; Codex may
append), `moment-map-spectral.md` `7106fbc3…29b8bee5`, the pinned `MinkowskiContent.lean`,
`MinkowskiConstant.lean`, `BVConstant.lean`, `LocalSlopeCoarea.lean`. The phase-10 receipt does
not cover this snapshot.

### Placement plan

Object and role: the last recovery prerequisite before the Cheeger-infimum comparison, split by
responsibility. (a) Generic mass continuity under set-indicator `L¹` convergence (the convergence
mode of the lower-semicontinuity theorem) goes to the basic owner `Perimeter/MetricBV.lean`, with
no new import: `measure_le_add_lintegral_indicator_sub` (`ν A ≤ ν B + ∫ ‖1_A - 1_B‖ₑ`, measurable
`A`, `B`, any measure, via `ν (A \ B) ≤ ∫ ‖1_A - 1_B‖ₑ`) and
`tendsto_measure_of_tendsto_indicator` (finite measure, measurable `A n`, `B`: `ν (A n) → ν B`,
proved from the two-sided bound with `ENNReal.tendsto_nhds`, not assumed). (b) Recovery-specific
results at the integration boundary `Perimeter/MetricBVMinkowski.lean` (no Cheeger-constant
import): a reusable ratio lemma `tendsto_div_min_one_sub` (numerators `→ a ≠ ⊤`, masses `→ m`
with `0 < m < 1`: `a_n / min m_n (1 - m_n) → a / min m (1 - m)`; continuity of `min` and of
`1 - ·`, limiting denominator nonzero because `0 < m` and `0 < 1 - m`, finite because `m ≤ 1`,
so `ENNReal.Tendsto.div` applies; `m = 1/2` needs no branch), and for measurable `B` with finite
perimeter: `tendsto_measure_minkowskiRecoverySet`,
`eventually_measure_minkowskiRecoverySet_mem_Ioo` (for `0 < ν B < 1`; `Ioo 0 1` is open),
`tendsto_minkowskiContent_div_min_minkowskiRecoverySet` and
`tendsto_perimeter_div_min_minkowskiRecoverySet`, the latter two being exactly the symmetric
quotients `minkowskiContent ν A / min (ν A) (1 - ν A)` of `minkowskiConstant` and
`perimeter ν A / min (ν A) (1 - ν A)` of `symmetricConstant`. Masses `0` and `1` are excluded
from the ratio theorems; no half-mass constraint, no Cheeger equality.

Client: `research/audits/MetricBVRatioRecoveryAudit.lean` (new): full signatures, mass
convergence at mass `0` (the ratio theorem not applied), the half-mass case, a concrete two-atom
law `(δ₀ + δ₁)/2` on `ℝ` with `B = Iic (1/2)` (mass `1/2`, content and perimeter `0`, so the
hypotheses are satisfiable), and dimension zero (no mass window exists). Validation: strict
compilation of both modules, `BVConstant.lean` and all MetricBV clients; standard transitive
axioms; isolated-index progress generation and `update.py --check`; frozen full
`research/verify.py`; receipt under ignored `build/audit/metric-bv-ratio-recovery/`.

### Phase 11 stage status

- [x] mass continuity, ratio lemma, recovery masses/window/ratios, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-ratio-recovery/receipt.md`)

### Phase 11 exact declarations

`MetricBV.lean` (after `perimeter_le_liminf_of_tendsto`; generic `{α : Type*} [MeasurableSpace α]`):

```lean
theorem measure_le_add_lintegral_indicator_sub (ν : Measure α) {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ν A ≤ ν B + ∫⁻ x, ‖A.indicator (1 : α → ℝ) x - B.indicator 1 x‖ₑ ∂ν
theorem tendsto_measure_of_tendsto_indicator (ν : Measure α) [IsFiniteMeasure ν]
    {A : ℕ → Set α} {B : Set α} (hA : ∀ n, MeasurableSet (A n)) (hB : MeasurableSet B)
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : α → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    Tendsto (fun n => ν (A n)) atTop (𝓝 (ν B))
```

`MetricBVMinkowski.lean`, new section `RatioRecovery`:

```lean
theorem tendsto_div_min_one_sub {ι : Type*} {l : Filter ι} {a m : ι → ℝ≥0∞} {a₀ m₀ : ℝ≥0∞}
    (ha : Tendsto a l (𝓝 a₀)) (hm : Tendsto m l (𝓝 m₀)) (h0 : 0 < m₀) (h1 : m₀ < 1) :
    Tendsto (fun i => a i / min (m i) (1 - m i)) l (𝓝 (a₀ / min m₀ (1 - m₀)))
-- [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V], ν : ProbabilityMeasure V,
-- hBm : MeasurableSet B, hB : perimeter (ν : Measure V) B < ⊤
theorem tendsto_measure_minkowskiRecoverySet (ν) (hBm) (hB) :
    Tendsto (fun n => (ν : Measure V) (minkowskiRecoverySet ν hB n)) atTop (𝓝 ((ν : Measure V) B))
theorem eventually_measure_minkowskiRecoverySet_mem_Ioo (ν) (hBm) (hB)
    (h0 : 0 < (ν : Measure V) B) (h1 : (ν : Measure V) B < 1) :
    ∀ᶠ n in atTop, (ν : Measure V) (minkowskiRecoverySet ν hB n) ∈ Set.Ioo 0 1
theorem tendsto_minkowskiContent_div_min_minkowskiRecoverySet (ν) (hBm) (hB) (h0) (h1) :
    Tendsto (fun n => Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n) /
        min ((ν : Measure V) (minkowskiRecoverySet ν hB n))
          (1 - (ν : Measure V) (minkowskiRecoverySet ν hB n))) atTop
      (𝓝 (perimeter (ν : Measure V) B / min ((ν : Measure V) B) (1 - (ν : Measure V) B)))
theorem tendsto_perimeter_div_min_minkowskiRecoverySet (ν) (hBm) (hB) (h0) (h1) :
    -- the same with `perimeter (ν : Measure V) (minkowskiRecoverySet ν hB n)` as numerator
```

Proof shape. Mass bound: `ν A ≤ ν (B ∪ A \ B) ≤ ν B + ν (A \ B)` and
`ν (A \ B) = ∫ 1_{A \ B} ≤ ∫ ‖1_A - 1_B‖ₑ` (measurable `A \ B`). Mass continuity:
`ENNReal.tendsto_nhds` (finite `ν B`), eventually `d_n ≤ ε` from `ENNReal.tendsto_nhds_zero`,
upper bound directly, lower bound from the swapped bound and `enorm_sub_rev`, `tsub_le_iff_right`.
Ratio lemma: `Tendsto.min` of `m` and `1 - m` (`ENNReal.Tendsto.sub`, `1 ≠ ⊤`); the limiting
denominator is nonzero (`lt_min h0 (tsub_pos_of_lt h1)`) and finite (`≤ 1 - m₀ ≤ 1`), so
`ENNReal.Tendsto.div` applies with no finiteness of the numerator limit. Window: `Ioo_mem_nhds`.
Measurability of `B` is used only for mass continuity. The Cheeger constants
(`BVConstant.lean`, `MinkowskiConstant.lean`) are not imported by the bridge or the owner;
their quotients appear verbatim in the statements.

### Phase 11 independent client (`research/audits/MetricBVRatioRecoveryAudit.lean`)

| Client | Content |
| --- | --- |
| `massBound`, `massContinuity`, `ratioLemma` | full signatures of the generic lemmas |
| `recoveryMass`, `massWindow`, `contentRatio`, `perimeterRatio` | full signatures of the recovery results |
| `halfMass` | `ν B = 2⁻¹`: limit `perimeter B / 2⁻¹`, no branch |
| `massZero` | mass `0`: masses tend to `0`; the ratio theorem is not applied |
| `zeroDimensionalNoWindow` | `Fin 0 → ℝ`: no set has mass in `(0, 1)` |
| `twoAtomHalfLine` | `(δ₀ + δ₁)/2`, `B = Iic (1/2)`: mass `1/2`, content `0` (thickenings below `1/2` miss the atom at `1`), perimeter `0`, content quotients `→ 0` |

All eleven reports and the direct reports of the seven new owner declarations are
`[propext, Classical.choice, Quot.sound]`; `BVConstant.lean` and the eleven earlier MetricBV
clients recompile strictly with standard reports only.

Metadata: phase 10 marked accepted and phase-11 sentence added (pending Codex review) in the BV
paragraph of `HANDOFF.md`; root `README.md`, progress-hub prose and the `diagram:BV` description
updated (still `partial`, label unchanged, KLS open); Blueprint and `research/tasks.json`
unchanged; views regenerated from an isolated index/object store (adding only the dirty
`research/tasks.json` and chapter 45), `update.py --check` passed, real index unstaged,
`git diff --check` passed. Obstacles: `add_le_add_left` argument convention (used `gcongr`);
`one_lt_two` needs an instance ENNReal lacks here (used `ENNReal.one_lt_two`). Suggested next:
the Cheeger-infimum comparison `symmetricConstant = minkowskiConstant` on the admissible family
(one direction from phase 7 termwise, the other from these ratio limits), without asserting it
beyond what is proved.

## Phase 10 (2026-09-28)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `MetricBV.lean` `624f1f73…85b66e24`, `MetricBVMinkowski.lean`
`59ea36f6…c5e2aec3`, `README.md` `fdbd2fef…533e703f`, `HANDOFF.md`
`3d12e347…97b09444`, `nodes.json` `ec0c2040…40ac7759`; not edited:
`codex-bv-overnight-review.md` (`f93a9bd2…a95175c0` at start; Codex may append),
`moment-map-spectral.md` `7106fbc3…29b8bee5`, the pinned `MinkowskiContent.lean`,
`LocalSlopeCoarea.lean`. The phase-9 receipt does not cover this snapshot.

### Placement plan

Object and role: recovery of the metric BV perimeter by actual Minkowski contents, at the
existing integration boundary `KLS/Geometry/Perimeter/MetricBVMinkowski.lean` (extend: the
construction only combines that module's selection with `MetricBV` recovery and lower
semicontinuity; no new responsibility or import). For a probability law `ν` on a normed group
with Borel structure and `B` with `perimeter ν B < ⊤`, an explicitly defined sequence of
measurable sets `minkowskiRecoverySet ν hB n` with `∫ ‖1_{A_n} - 1_B‖ₑ dν → 0` and
`minkowskiContent ν A_n → perimeter ν B` (and, as a direct consequence, `perimeter ν A_n → perimeter ν B`).
No mass constraint, no pointwise `content B = perimeter B`, no Cheeger infimum statement; nothing
for infinite perimeter beyond the general lower bound below.

Construction (all choices explicit): `recoveryWidth n = 1/(n + 3) ∈ (0, 1/2)`, `→ 0`;
`minkowskiRecoveryTest ν hB n = recoveryTest hB` with test error below
`ofReal (recoveryWidth n / (n + 1))` and cost below `perimeter + ofReal (1/(n + 1))`;
`minkowskiRecoveryLevel` is `Classical.choose` of `exists_superlevel_selection` for that test with
width `recoveryWidth n` and slack `1/(n + 1)`; `minkowskiRecoverySet = {level ≤ test}`.
Bounds: indicator error `≤ ofReal (recoveryWidth n / (n + 1)) / ofReal (recoveryWidth n) =
ofReal (1/(n + 1)) → 0`; content `≤ (perimeter + ofReal (1/(n + 1))) / ofReal (1 - 2 recoveryWidth n)
+ ofReal (1/(n + 1)) → perimeter / 1 + 0` (finite perimeter; `ENNReal.Tendsto.div` with limit
denominator `1`). Lower bound, not a pointwise `perimeter B ≤ cost f_n`: the new general lemma
`perimeter_le_liminf_minkowskiContent` (any measurable sets converging in `L¹`, from phase 6
lower semicontinuity and phase 7 `perimeter ≤ content`), so liminf content `≥ perimeter`.
Measurability of `B` is not used by the proof (the requested measurable-`B` form is a client).

Declarations (namespace `MetricBV`, section `MinkowskiRecovery`): `recoveryWidth` and its three
facts, `perimeter_le_liminf_minkowskiContent`, `minkowskiRecoveryTest`, `minkowskiRecoveryLevel`,
`minkowskiRecoverySet`, `measurableSet_minkowskiRecoverySet`, the two per-term bounds,
`tendsto_indicator_minkowskiRecoverySet`, `tendsto_minkowskiContent_minkowskiRecoverySet`,
`tendsto_perimeter_minkowskiRecoverySet`, `exists_minkowskiRecovery`. Client:
`research/audits/MetricBVMinkowskiRecoveryAudit.lean` (new): full signatures, measurable-`B`
form, zero perimeter (empty set, null sets, the whole space of a probability law), dimension
zero, the general lower bound at infinite perimeter (contents of converging measurable sets have
infinite liminf). API: additions only. Validation: strict compilation of the module and all
MetricBV clients, standard transitive axioms, isolated-index progress generation and
`update.py --check`, frozen full `research/verify.py`, receipt under ignored
`build/audit/metric-bv-minkowski-recovery/`.

### Phase 10 stage status

- [x] recovery sets and convergence, lower bound, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-minkowski-recovery/receipt.md`)

### Phase 10 exact declarations

`MetricBVMinkowski.lean`, new section `MinkowskiRecovery` (namespace `MetricBV`;
`[NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]`, `ν : ProbabilityMeasure V`,
`hB : perimeter (ν : Measure V) B < ⊤`):

```lean
theorem perimeter_le_liminf_minkowskiContent (ν) {B} {A : ℕ → Set V}
    (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) :
    perimeter (ν : Measure V) B ≤ liminf (fun n => Isoperimetry.minkowskiContent ν (A n)) atTop
def recoveryWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 3)
theorem recoveryWidth_pos / recoveryWidth_lt_half (n) ; theorem tendsto_recoveryWidth
def minkowskiRecoveryTest (ν) (hB) (n) : Test V
  -- recoveryTest hB, error ofReal (recoveryWidth n / (n + 1)), excess ofReal (1 / (n + 1))
theorem exists_minkowskiRecoveryLevel (ν) (hB) (n) : ∃ t ∈ Ioo …, … -- phase-9 selection instance
def minkowskiRecoveryLevel (ν) (hB) (n) : ℝ := Classical.choose (exists_minkowskiRecoveryLevel ν hB n)
def minkowskiRecoverySet (ν) (hB) (n) : Set V :=
  {x | minkowskiRecoveryLevel ν hB n ≤ minkowskiRecoveryTest ν hB n x}
theorem measurableSet_minkowskiRecoverySet (ν) (hB) (n) : MeasurableSet (minkowskiRecoverySet ν hB n)
theorem lintegral_enorm_minkowskiRecoverySet_sub_le (ν) (hB) (n) :
    ∫⁻ x, ‖(minkowskiRecoverySet ν hB n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1))
theorem minkowskiContent_minkowskiRecoverySet_le (ν) (hB) (n) :
    Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n) ≤
      (perimeter (ν : Measure V) B + ENNReal.ofReal (1 / ((n : ℝ) + 1))) /
        ENNReal.ofReal (1 - 2 * recoveryWidth n) + ENNReal.ofReal (1 / ((n : ℝ) + 1))
theorem tendsto_indicator_minkowskiRecoverySet (ν) (hB) : Tendsto (… L¹ error …) atTop (𝓝 0)
theorem tendsto_minkowskiContent_minkowskiRecoverySet (ν) (hB) :
    Tendsto (fun n => Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n)) atTop
      (𝓝 (perimeter (ν : Measure V) B))
theorem tendsto_perimeter_minkowskiRecoverySet (ν) (hB) : Tendsto (perimeter of A_n) … (𝓝 (perimeter B))
theorem exists_minkowskiRecovery (ν) (hB) : ∃ A : ℕ → Set V, (∀ n, MeasurableSet (A n)) ∧
    Tendsto (L¹ error) atTop (𝓝 0) ∧ Tendsto (contents) atTop (𝓝 (perimeter (ν : Measure V) B))
```

Proof shape. Error: selection bound `indicatorDistance / ofReal δ_n`, test error
`< ofReal (δ_n/(n+1))`, `ENNReal.ofReal_div_of_pos`, `field_simp`. Content: selection bound with
`cost < perimeter + ofReal (1/(n+1))` (`gcongr`). Upper limit: `ENNReal.Tendsto.div` (numerator
`→ perimeter`, denominator `ofReal (1 - 2 δ_n) → 1`, conditions `1 ≠ 0`, `1 ≠ ⊤`) plus
`ofReal (1/(n+1)) → 0`, so limsup content `≤ perimeter` via `limsup_le_limsup`. Lower limit:
`perimeter_le_liminf_minkowskiContent` (phase 6 `perimeter_le_liminf_of_tendsto` on the
measurable recovery sets, then phase 7 termwise). `tendsto_of_le_liminf_of_limsup_le` concludes;
the perimeter convergence squeezes between the same bounds. Finiteness of the perimeter is used
for the strict test threshold and for the limit of the numerator; `B` need not be measurable.
Mass convergence was not added (not needed; kept out of scope).

### Phase 10 independent client (`research/audits/MetricBVMinkowskiRecoveryAudit.lean`)

| Client | Content |
| --- | --- |
| `lowerBound` | full signature of `perimeter_le_liminf_minkowskiContent` |
| `explicitSequence` | measurability, both per-term bounds and all three convergences for `minkowskiRecoverySet` |
| `widths` | `0 < recoveryWidth n < 1/2`, `recoveryWidth → 0` |
| `measurableRecovery` | the requested form with measurable `B` |
| `zeroPerimeter`, `emptySet` | zero perimeter: contents tend to `0` |
| `nullSet` | measurable null sets have zero perimeter, hence vanishing recovery contents |
| `fullSet` | the whole space of a probability law (constant one), vanishing contents |
| `zeroDimensional` | `Fin 0 → ℝ`: every set, vanishing contents |
| `infinitePerimeter` | at `perimeter = ⊤` every measurable `L¹` approximation has liminf content `⊤` |

All ten reports and the direct reports of the thirteen new owner declarations are
`[propext, Classical.choice, Quot.sound]`; the ten earlier MetricBV clients recompile strictly
with standard reports only.

Metadata: phase 9 marked accepted and phase-10 sentence added (pending Codex review) in the BV
paragraph of `HANDOFF.md`; root `README.md`, progress-hub prose and the `diagram:BV` description
updated (still `partial`, label unchanged, KLS open), and the stale "reverse direction/inequality
is open" wording corrected to "the pointwise reverse fails in general" (phase 8 client
`pointwiseReverseFails`); Blueprint and `research/tasks.json` unchanged; views regenerated from
an isolated index/object store (adding only the dirty `research/tasks.json` and chapter 45),
`update.py --check` passed, real index unstaged, `git diff --check` passed. Obstacles: none.
Suggested next: the Cheeger infimum comparison, i.e. keeping the recovery sets inside the
admissible mass window (`0 < ν A_n < 1`, via `ν A_n → ν B`) to compare the half-mass BV and
Minkowski Cheeger constants.

## Phase 9 (2026-09-28)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `MetricBV.lean` `ccd47c2c…3d541a93`, `MetricBVMinkowski.lean` `81cf1bb9…1f98ef2f`,
`README.md` `fd509bb4…23d2e22d`, `HANDOFF.md` `487e5e38…cf08faf1`, `nodes.json`
`9592877e…c32308d8`; not edited: `codex-bv-overnight-review.md` (`b51d4dbf…b719a73b` at start;
Codex may append), `moment-map-spectral.md` `7106fbc3…29b8bee5`, the pinned
`MinkowskiContent.lean`, `LocalSlopeCoarea.lean` and the `C¹` theorem. The phase-8 receipt does
not cover this snapshot.

### Placement plan

Object and role: a recovery/identification prerequisite at the existing integration boundary
`KLS/Geometry/Perimeter/MetricBVMinkowski.lean` (extend; the responsibilities, test superlevel
sets measured by Minkowski content, match that module). Statement: for a probability law `ν` on
a normed group with Borel structure, a test `f`, a set `B`, real `0 < δ < 1/2` and real `ε > 0`,
there is `t ∈ (δ, 1 - δ)` with `A = {x | t ≤ f x}` measurable,
`minkowskiContent ν A ≤ cost ν f / ofReal (1 - 2δ) + ofReal ε`, and
`∫⁻ ‖1_A - 1_B‖ₑ dν ≤ indicatorDistance ν f B / ofReal δ`.

Mathematics. (1) Pointwise error, for any real function `g` and `δ ≤ t ≤ 1 - δ`, `δ > 0`:
`‖1_{t ≤ g}(x) - 1_B(x)‖ₑ ≤ ‖g x - 1_B(x)‖ₑ / ofReal δ` (the left side is `0` or `1`; when `1`,
either `x ∈ A \ B` with `g x ≥ t ≥ δ`, or `x ∈ B \ A` with `1 - g x > 1 - t ≥ δ`); integrated
by `lintegral_mono` and `lintegral_mul_const'` (no measurability of `B`, `A` or `g` needed).
(2) Selection with positive slack, without measurability of the content: for any
`φ : ℝ → ℝ≥0∞`, `a < b`, finite `C` with `∫⁻ t in Ioo a b, φ t ≤ C` and `ε > 0`, some
`t ∈ Ioo a b` has `φ t ≤ C / ofReal (b - a) + ofReal ε`; otherwise `setLIntegral_mono'` (no
measurability of `φ`) and `setLIntegral_const` give `C + ofReal ε · ofReal (b - a) ≤ C`,
impossible for finite `C`. (3) The cost of a test is finite for a finite measure (slope bounded
by the Lipschitz constant): new `cost_ne_top` in the owner `MetricBV.lean`. (4) The proved
test coarea `lintegral_minkowskiContent_superlevel_le_cost` restricted to `Ioo δ (1 - δ)` via
`Measure.restrict_le_self`; `(1 - δ) - δ = 1 - 2δ`. Measurability of `A`: closed superlevel set
of a continuous function.

Scope: `B` need not be measurable (the requested form with measurable `B` is a client).
Declarations: `cost_ne_top` (`MetricBV.lean`, no new import);
`enorm_indicator_superlevel_sub_le`, `lintegral_enorm_indicator_superlevel_sub_le`,
`exists_mem_Ioo_le_div_add_of_setLIntegral_le`, `exists_superlevel_selection`
(`MetricBVMinkowski.lean`). The generic selection lemma stays in this module (its only consumer;
no new abstraction). Client: `research/audits/MetricBVSuperlevelSelectionAudit.lean` (new): full
signatures, the measurable-`B` form, zero cost, zero error, the zero test, dimension zero, the
perimeter bound via phase 7, and the pointwise error at the endpoints `t = δ`, `t = 1 - δ`. API:
additions only. Validation: strict compilation of both modules and all MetricBV clients, standard
transitive axioms, isolated-index progress generation and `update.py --check`, frozen full
`research/verify.py`, receipt under ignored `build/audit/metric-bv-superlevel-selection/`.

### Phase 9 stage status

- [x] error lemmas, selection lemma, finite cost, main selection, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-superlevel-selection/receipt.md`)

### Phase 9 exact declarations

`MetricBV.lean` (after `cost_zero`; `[MetricSpace X] [MeasurableSpace X] [BorelSpace X]`):

```lean
theorem cost_ne_top (ν : Measure X) [IsFiniteMeasure ν] (f : Test X) : cost ν f ≠ ⊤
```

`MetricBVMinkowski.lean`, new section `SuperlevelSelection` (namespace `MetricBV`):

```lean
theorem enorm_indicator_superlevel_sub_le {X : Type*} (g : X → ℝ) (B : Set X) {δ t : ℝ}
    (hδ : 0 < δ) (hδt : δ ≤ t) (ht : t ≤ 1 - δ) (x : X) :
    ‖{y | t ≤ g y}.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ≤
      ‖g x - B.indicator (1 : X → ℝ) x‖ₑ / ENNReal.ofReal δ
theorem lintegral_enorm_indicator_superlevel_sub_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (g : X → ℝ) (B : Set X) {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (ht : t ≤ 1 - δ) :
    ∫⁻ x, ‖{y | t ≤ g y}.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν ≤
      (∫⁻ x, ‖g x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) / ENNReal.ofReal δ
theorem exists_mem_Ioo_le_div_add_of_setLIntegral_le {φ : ℝ → ℝ≥0∞} {a b : ℝ} (hab : a < b)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hφ : ∫⁻ t in Set.Ioo a b, φ t ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo a b, φ t ≤ C / ENNReal.ofReal (b - a) + ENNReal.ofReal ε
-- [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
theorem exists_superlevel_selection (ν : ProbabilityMeasure V) (f : Test V) (B : Set V)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo δ (1 - δ), MeasurableSet {x | t ≤ f x} ∧
      Isoperimetry.minkowskiContent ν {x | t ≤ f x} ≤
        cost (ν : Measure V) f / ENNReal.ofReal (1 - 2 * δ) + ENNReal.ofReal ε ∧
      ∫⁻ x, ‖{x | t ≤ f x}.indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        indicatorDistance (ν : Measure V) f B / ENNReal.ofReal δ
```

Proof shape. Pointwise error: four cases on `t ≤ g x` and `x ∈ B`; the two mismatch cases use
`δ ≤ g x` resp. `δ ≤ 1 - g x` and `ENNReal.le_div_iff_mul_le`. Integrated: `lintegral_mono` and
`lintegral_mul_const'` (finite `(ofReal δ)⁻¹`), no measurability. Selection: by contradiction,
`setLIntegral_mono'` (pointwise on the measurable interval, no measurability of `φ`) and
`setLIntegral_const`, `Real.volume_Ioo`, `ENNReal.div_mul_cancel` give
`C + ofReal ε · ofReal (b - a) ≤ C`, contradicting `ENNReal.lt_add_right` for finite `C`. Main:
coarea for tests restricted by `lintegral_mono' Measure.restrict_le_self`, finite cost by
`cost_ne_top`, `(1 - δ) - δ = 1 - 2δ`, measurability from Lipschitz continuity. `B` is never
required to be measurable. No other declaration changed; `MinkowskiContent.lean`,
`LocalSlopeCoarea.lean` and the `C¹` theorem are untouched.

### Phase 9 independent client (`research/audits/MetricBVSuperlevelSelectionAudit.lean`)

| Client | Content |
| --- | --- |
| `pointwiseError`, `integratedError`, `sliceSelection`, `costFinite`, `selection` | full signatures |
| `endpointErrors` | the error bound at `t = δ` and `t = 1 - δ` |
| `selectionMeasurable` | the requested form with measurable `B` |
| `zeroCost` | cost `0`: selected content at most `ε` |
| `zeroError` | error `0`: selected set at zero indicator distance |
| `zeroTest` | `Test.zero`: every admissible level is positive, the selected set is `∅` |
| `zeroDimensional` | `Fin 0 → ℝ`: every test has cost `0` |
| `perimeterForm` | with phase 7: the selected set's BV perimeter obeys the same bound |

All twelve reports and the direct reports of the five new owner declarations are
`[propext, Classical.choice, Quot.sound]`; `BVConstant.lean` and the nine earlier MetricBV
clients recompile strictly with standard reports only.

Metadata: phase 8 marked accepted and phase-9 sentence added (pending Codex review) in the BV
paragraph of `HANDOFF.md`, with the remaining sequence-level recovery and Cheeger identification
gaps; root `README.md`, progress-hub prose and the `diagram:BV` description updated (still
`partial`, label unchanged, KLS open); Blueprint and `research/tasks.json` unchanged; views
regenerated from an isolated index/object store (adding only the dirty `research/tasks.json` and
chapter 45), `update.py --check` passed, real index unstaged, `git diff --check` passed.
Obstacles: none (`push_neg` is deprecated in this Mathlib; `push Not` used). Suggested next: the
sequence-level recovery, applying the selection along an approximating sequence with `δ, ε → 0`
while tracking the factor `1/(1 - 2δ)` and the mass constraints of the Cheeger quotients.

## Phase 8 (2026-09-28)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `MinkowskiContent.lean` `82413123…14f70a69` (pinned in `research/tasks.json`; not edited),
`Energy/LocalSlope/Basic.lean` `ffba9ad3…806896ae` (not edited), `MetricBVMinkowski.lean`
`5b0006e2…b64c64c8`, `FunctionalInequalities.lean` `0b3b49ae…5b044df1`, `README.md`
`e679432e…6bd19a3c`, `HANDOFF.md` `44c99dba…f10ad639`, `nodes.json` `1b14dabc…02ab3cad`; not
edited: `codex-bv-overnight-review.md` (`8f602f8a…f1047805` at start; Codex may append),
`moment-map-spectral.md` `7106fbc3…29b8bee5`. The phase-7 receipt does not cover this snapshot.

### Placement plan

Object and role: a substantive property of the existing outer Minkowski content, the Minkowski
coarea inequality with the actual pointwise local slope: for a probability law `ν` and a
globally Lipschitz `u` (no `ContDiff`),
`∫⁻ t, minkowskiContent ν {x | t ≤ u x} ≤ ∫⁻ x, Energy.LocalSlope.apply u x ∂ν`. A recovery
prerequisite; not the pointwise inequality content ≤ BV perimeter (false in general: a null set
with heavy closure) and not a Cheeger identification. The existing `minkowskiContent`,
`ballSup` API, `limsup_ofReal_ballSup_le` and the `C¹` theorem
`lintegral_minkowskiContent_superlevel_le` keep their statements and proofs.

Mathematics. (1) Growth-quotient bound, proved not assumed: for every `ρ > 0` and `0 < r < ρ`,
`ofReal ((ballSup u r x - u x) / r) ≤ ⨆_{dist y x < ρ} ofReal (|u y - u x| / dist y x)`, since
each `y` in the closed `r`-ball with `u y > u x` has `0 < dist y x ≤ r < ρ` and
`(u y - u x)/r ≤ (u y - u x)/dist y x` (when the supremum is `⊤` the bound is trivial); hence
along any positive radii `r n → 0` the limsup of the quotients is at most every such supremum,
i.e. at most the local slope (its infimum over `ρ`). (2) Layer cake: the existing proof's steps
(near-neighbour witness, measurable strip `T n` in `ℝ × V`, Tonelli via `Measure.prod_apply` and
`prod_apply_symm`, Fatou, reverse Fatou under the uniform bound `K`) are repeated verbatim as a
generic lemma bounding the superlevel-content integral by `∫ limsup` of the growth quotients at
`r n = 1/(n+1)`; the `C¹` proof is not refactored, to keep the pinned module untouched.

Scope: only `[NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]` (what `ballSup`,
`minkowskiContent` and the product-measure steps need), which contains the finite-dimensional
inner-product setting; constants, dimension zero, unbounded values and supports and all `ENNReal`
conventions are included without extra hypotheses.

Owner and destination: new module `KLS/Geometry/Cheeger/LocalSlopeCoarea.lean` in the
Minkowski-content family (`Isoperimetry` namespace), importing `Cheeger/MinkowskiContent.lean`
and `Energy/LocalSlope/Basic.lean`: `limsup_ofReal_ballSup_le_localSlope`,
`lintegral_minkowskiContent_superlevel_le_limsup`,
`lintegral_minkowskiContent_superlevel_le_localSlope`. The basic local-slope module gains no
application import; the pinned `MinkowskiContent.lean` is not edited. The `MetricBV.Test`
specialization goes to the existing bridge `Perimeter/MetricBVMinkowski.lean` (new import of
`LocalSlopeCoarea`): `lintegral_minkowskiContent_superlevel_le_cost`, and with phase 7 the
BV-perimeter coarea upper bound `lintegral_perimeter_superlevel_le_cost`. Root
`FunctionalInequalities.lean` gains the new module import. Client:
`research/audits/MetricBVMinkowskiCoareaAudit.lean` (new): full signatures, constant, dimension
zero, the unbounded identity on `ℝ` for an arbitrary law, the `C¹` consistency with the gradient
version, and the Test specializations. API: additions only. Validation: strict compilation of
both touched modules and all MetricBV clients, standard transitive axioms, isolated-index
progress generation and `update.py --check`, frozen full `research/verify.py`, receipt under
ignored `build/audit/metric-bv-minkowski-coarea/`.

### Phase 8 stage status

- [x] growth bound, layer cake, slope coarea, Test specialization, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-minkowski-coarea/receipt.md`)

### Phase 8 exact declarations

New module `KLS/Geometry/Cheeger/LocalSlopeCoarea.lean`, namespace
`FunctionalInequalities.KLS.Isoperimetry`, `{V : Type*} [NormedAddCommGroup V]` (the last two
also `[MeasurableSpace V] [BorelSpace V]`):

```lean
theorem limsup_ofReal_ballSup_le_localSlope (u : V → ℝ) (x : V) {r : ℕ → ℝ}
    (hrpos : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) :
    limsup (fun n => ENNReal.ofReal ((ballSup u (r n) x - u x) / r n)) atTop
      ≤ Energy.LocalSlope.apply u x
theorem lintegral_minkowskiContent_superlevel_le_limsup (ν : ProbabilityMeasure V) {u : V → ℝ}
    {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, limsup (fun n : ℕ => ENNReal.ofReal
        ((ballSup u (1 / ((n : ℝ) + 1)) x - u x) / (1 / ((n : ℝ) + 1)))) atTop ∂(ν : Measure V)
theorem lintegral_minkowskiContent_superlevel_le_localSlope (ν : ProbabilityMeasure V)
    {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂(ν : Measure V)
```

Extended bridge `KLS/Geometry/Perimeter/MetricBVMinkowski.lean` (new import of
`LocalSlopeCoarea`), namespace `MetricBV`, section `Bridge`:

```lean
theorem lintegral_perimeter_superlevel_le_localSlope (ν : ProbabilityMeasure V) {u : V → ℝ}
    {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, perimeter (ν : Measure V) {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂(ν : Measure V)
theorem lintegral_minkowskiContent_superlevel_le_cost (ν : ProbabilityMeasure V) (f : Test V) :
    ∫⁻ t, Isoperimetry.minkowskiContent ν {x | t ≤ f x} ∂(volume : Measure ℝ) ≤
      cost (ν : Measure V) f
theorem lintegral_perimeter_superlevel_le_cost (ν : ProbabilityMeasure V) (f : Test V) :
    ∫⁻ t, perimeter (ν : Measure V) {x | t ≤ f x} ∂(volume : Measure ℝ) ≤
      cost (ν : Measure V) f
```

Proof shape. Growth bound: `le_iInf₂` over the slope radii `ρ`; eventually `r n < ρ`; if the
secant supremum `S` is finite, `csSup_le` shows `ballSup u (r n) x ≤ u x + S.toReal · r n`
(points with `u y ≤ u x` trivially; points with `u y > u x` have `0 < dist y x ≤ r n < ρ`, so
`u y - u x ≤ S.toReal · dist y x`); no Lipschitz or boundedness hypothesis is needed. Layer cake:
verbatim reuse of the `C¹` proof's steps 1–3 and Fatou/reverse Fatou, with `Measurable u` from
`hK.continuous` instead of `ContDiff`. The pinned `MinkowskiContent.lean` and
`Energy/LocalSlope/Basic.lean` are byte-identical to the baseline; the `C¹` signature is
unchanged (rechecked). Root `FunctionalInequalities.lean` gains the `LocalSlopeCoarea` import.

### Phase 8 independent client (`research/audits/MetricBVMinkowskiCoareaAudit.lean`)

| Client | Content |
| --- | --- |
| `growthBound`, `layerCake`, `slopeCoarea` | full signatures of the three coarea declarations |
| `lipschitzPerimeter`, `testContent`, `testPerimeter` | full signatures of the BV specializations |
| `constantFunction` | constants: the superlevel-content integral is `0` |
| `zeroDimensional` | `Fin 0 → ℝ`: the integral is `0` for every Lipschitz function |
| `identityLine` | the unbounded identity on `ℝ`, arbitrary law: integral at most `1` |
| `c1Consistency` | `C¹`: slope integral = gradient integral, recovering the old theorem |
| `pointwiseReverseFails` | rationals under `gaussianReal 0 1`: BV perimeter `0`, content `⊤` |

All eleven reports and the direct reports of the six new owner declarations (and
`perimeter_le_minkowskiContent`) are `[propext, Classical.choice, Quot.sound]`; the eight earlier
MetricBV clients, `MinkowskiContent.lean` and `research/audits/CheegerInequalityRouteStatements.lean`
(the existing consumer of the `C¹` theorem) recompile strictly.

Metadata: phase-8 sentence in the BV paragraph of `HANDOFF.md` (pending Codex review), root
`README.md`, progress-hub prose and the `diagram:BV` description (still `partial`, label
unchanged, KLS open); Blueprint and `research/tasks.json` unchanged (the pinned
`MinkowskiContent.lean` is untouched); views regenerated from an isolated index/object store
(adding only the dirty `research/tasks.json` and chapter 45), `update.py --check` passed, real
index unstaged, `git diff --check` passed. Obstacles: none. Refactor candidate (not done, to keep
the pinned module untouched): derive the `C¹` theorem from
`lintegral_minkowskiContent_superlevel_le_limsup` to remove the duplicated layer cake. Suggested
next: a coarea-type lower bound for the relaxed perimeter of superlevel sets along recovery
sequences (toward BV Cheeger ≥ Minkowski Cheeger), not a pointwise reverse inequality.

## Phase 7 (2026-09-28)

### Baseline

Same conversation, same checkout, HEAD `2f9f7e2`, real index with no staged changes. SHA-256 at
start: `MetricBV.lean` `ccd47c2c…3d541a93`, `FunctionalInequalities.lean` `a7f4aa75…9a4037ba`
(tracked, clean), `README.md` `54f3ffa1…16dc4cc2`, `HANDOFF.md` `f1763b2a…64367c2b`,
`nodes.json` `9cb9f182…8164037d`; not edited: `codex-bv-overnight-review.md`
`149070d5…7317bb10` (Codex may append while this phase runs), `moment-map-spectral.md`
`7106fbc3…29b8bee5`, and the pinned `KLS/Geometry/Cheeger/MinkowskiContent.lean`. The phase-6
receipt does not cover this snapshot.

### Placement plan

Object and role: a one-sided identification bridge between two existing objects,
`MetricBV.perimeter` (metric relaxation) and `Isoperimetry.minkowskiContent` (outer Minkowski
content with open thickenings, liminf over `r ↓ 0`): for a probability law `ν` on `V` and a
measurable `B`, `perimeter (ν : Measure V) B ≤ minkowskiContent ν B`. One inequality, not
identification; no statement about the Cheeger infima. Definitions unchanged.

Scope: `minkowskiContent` needs only `[NormedAddCommGroup V] [MeasurableSpace V]`, so the bridge
is stated for `[NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]` (no inner product,
completeness, second countability or finite dimension; the zero-dimensional space needs no
special case). The ramp lemmas hold on every metric space with a Borel measure.

Boundary-slope caution. The naive ramp `(1 - d(·, B)/r)₊` equals `1` on `closure B` but can have
slope `1/r` at boundary points of `B` (e.g. `ν = δ₀` on `ℝ`, `B = [0, ∞)`: content `0`, naive
cost `1/r`), so it does not give the bound when `B`'s boundary carries mass. Two-radius plateau
ramp instead: for `0 < s < t`, `plateauRamp B s t x = clampUnit ((t - d(x, B)) / (t - s))`. It is
`(t - s)⁻¹`-Lipschitz, equals `1` on the open set `{d < s}` ⊇ `closure B` and `0` on the open
set `{d > t}`, where the local slope is therefore zero; so the slope is at most
`(t - s)⁻¹ · 1_{s ≤ d ≤ t}` and `{s ≤ d ≤ t} ⊆ B^r \ B` for `t < r`, `B` nonempty. Also
`|ramp - 1_B| ≤ 1_{B^t \ B}`. With `ν(B^r \ B) = ν(B^r) - ν(B)` (measurable `B`, finite
measure): cost `≤ (t - s)⁻¹ (ν(B^r) - ν(B))` and `L¹` distance `≤ ν(B^r) - ν(B)`.

Proof of the bridge: top content is trivial; `B = ∅` is `perimeter_empty`. Otherwise, for every
`a` above the content (`a = ⊤` trivial), the quotient `Q(r) = (ν(B^r) - ν(B))/r` is frequently
below `a` in `𝓝[>] 0`; choose `r_k ∈ (0, 1/(k+1))` with `Q(r_k) < a`, `s_k = r_k/(2(k+2))`,
`t_k = r_k - s_k`, so `r_k/(t_k - s_k) = 1 + 1/(k+1)`. Then the `L¹` distance is at most
`a · r_k → 0` and the cost at most `a · (1 + 1/(k+1)) → a`; the accepted finite-measure bridge
`perimeter_le_liminf_of_lipschitz` gives `perimeter ≤ a`. Closure mass enters only implicitly:
finite content forces `ν(B^r) - ν(B) = Q(r) r → 0` along the chosen radii (consistent with
`measure_closure_eq_of_minkowskiContent_ne_top`, which the client checks alongside). The sought
energy/content bound is not assumed.

Owner and destination: new module `KLS/Geometry/Perimeter/MetricBVMinkowski.lean` at the
integration boundary (perimeter family; imports `Perimeter/MetricBV.lean` and
`Cheeger/MinkowskiContent.lean`), namespace `FunctionalInequalities.KLS.MetricBV`:
`plateauRamp`, `lipschitzWith_plateauRamp`, `apply_plateauRamp_le`, `enorm_plateauRamp_sub_le`,
`lintegral_apply_plateauRamp_le`, `lintegral_enorm_plateauRamp_sub_le`,
`perimeter_le_minkowskiContent`. This avoids importing the Minkowski-content stack (Lebesgue,
product measures) into `MetricBV.lean`; nothing imports the new module except the root
`FunctionalInequalities.lean` (one added import, needed for the library build and audit view).
Client: `research/audits/MetricBVMinkowskiAudit.lean` (new): full signatures, the `δ₀` boundary
example with zero content, empty set, top content, dimension zero, and the closure-mass
consequence. API: additions only. Validation: strict compilation of the new module, `MetricBV.lean`,
the new and earlier MetricBV clients; standard transitive axioms; isolated-index progress generation
and `update.py --check`; frozen full `research/verify.py`; receipt under ignored
`build/audit/metric-bv-minkowski-upper/`.

### Phase 7 stage status

- [x] ramp lemmas and bridge, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-minkowski-upper/receipt.md`)

### Phase 7 exact declarations

New module `KLS/Geometry/Perimeter/MetricBVMinkowski.lean`, namespace
`FunctionalInequalities.KLS.MetricBV`. Section `PlateauRamp`, `{X : Type*} [MetricSpace X]`
(the last two also `[MeasurableSpace X] [BorelSpace X]`):

```lean
def plateauRamp (B : Set X) (s t : ℝ) (x : X) : ℝ :=
  clampUnit ((t - Metric.infDist x B) / (t - s))
theorem plateauRamp_nonneg / plateauRamp_le_one (B) (s t) (x)
theorem plateauRamp_eq_one (hst : s < t) (hx : Metric.infDist x B ≤ s) : plateauRamp B s t x = 1
theorem plateauRamp_eq_zero (hst : s < t) (hx : t ≤ Metric.infDist x B) : plateauRamp B s t x = 0
theorem lipschitzWith_plateauRamp (B : Set X) (hst : s < t) :
    LipschitzWith (Real.toNNReal (t - s)⁻¹) (plateauRamp B s t)
theorem apply_plateauRamp_le (B : Set X) (hst : s < t) (x : X) :
    Energy.LocalSlope.apply (plateauRamp B s t) x ≤
      ((fun y => Metric.infDist y B) ⁻¹' Set.Icc s t).indicator (fun _ => ENNReal.ofReal (t - s)⁻¹) x
theorem enorm_plateauRamp_sub_le (hB : B.Nonempty) (hs : 0 ≤ s) (hst : s < t) (x : X) :
    ‖plateauRamp B s t x - B.indicator (1 : X → ℝ) x‖ₑ ≤
      (Metric.thickening t B \ B).indicator (1 : X → ENNReal) x
theorem lintegral_apply_plateauRamp_le (ν : Measure X) (hB : B.Nonempty)
    (hs : 0 < s) (hst : s < t) (htr : t < r) :
    ∫⁻ x, Energy.LocalSlope.apply (plateauRamp B s t) x ∂ν ≤
      ENNReal.ofReal (t - s)⁻¹ * ν (Metric.thickening r B \ B)
theorem lintegral_enorm_plateauRamp_sub_le (ν : Measure X) (hB : B.Nonempty)
    (hBm : MeasurableSet B) (hs : 0 ≤ s) (hst : s < t) (htr : t ≤ r) :
    ∫⁻ x, ‖plateauRamp B s t x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν ≤ ν (Metric.thickening r B \ B)
```

Section `Bridge`, `{V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]`:

```lean
theorem perimeter_le_minkowskiContent (ν : ProbabilityMeasure V) {B : Set V}
    (hBm : MeasurableSet B) :
    perimeter (ν : Measure V) B ≤ Isoperimetry.minkowskiContent ν B
```

Proof shape. `B = ∅`: `perimeter_empty`. Otherwise `le_of_forall_gt_imp_ge_of_dense`; `a = ⊤`
trivial; `frequently_lt_of_liminf_lt` on the content liminf in `𝓝[>] 0` intersected with
`Ioo 0 (1/(k+1))` chooses `r k`; `s k = r k / (2 (k + 2))`, `t k = r k - s k`, so
`r k (t k - s k)⁻¹ = 1 + 1/(k+1)`. `measure_sdiff` and `ENNReal.div_mul_cancel` give
`ν(B^{r k} \ B) ≤ a · r k`; hence `L¹` error `≤ a/(k+1) → 0` and slope integral
`≤ a (1 + 1/(k+1)) → a`; `perimeter_le_liminf_of_lipschitz` (probability law, hence finite)
concludes. No energy/content bound is assumed; `measure_closure_eq_of_minkowskiContent_ne_top` is
not needed in the proof (finite quotients force the annulus mass to vanish along the radii) and
is checked alongside in the client. Root `FunctionalInequalities.lean` gains one import (after
`BVConstant`); `MetricBV.lean`, `MinkowskiContent.lean` (pinned) and all definitions are
unchanged. `BVConstant.lean`'s docstring still says the BV and Minkowski infima are distinct
objects, which remains accurate (only one inequality is proved); it was not edited.

### Phase 7 independent client (`research/audits/MetricBVMinkowskiAudit.lean`)

| Client | Content |
| --- | --- |
| `bridge` | full signature of `perimeter_le_minkowskiContent` |
| `rampLipschitz`, `rampSlope` | Lipschitz and boundary-safe slope bounds, full signatures |
| `rampSlopeZeroOnClosure` | zero slope at every point of `closure B` (the boundary caution) |
| `emptySet`, `topContent` | empty set; top content consistency |
| `zeroDimensional` | `Fin 0 → ℝ`: the bound, and perimeter `0` |
| `diracHalfLine` | `δ₀` on `ℝ`, `B = [0, ∞)`: content `0`, hence perimeter `0` (the naive ramp costs `1/r`) |
| `finiteContent` | finite content ⇒ finite perimeter, `ν(closure B) = ν(B)`, and a recovery sequence |

All nine reports and the direct reports of all eight owner declarations are
`[propext, Classical.choice, Quot.sound]`; the seven earlier MetricBV clients recompile strictly
with standard reports only.

Metadata: phase-7 sentence in the BV paragraph of `HANDOFF.md` (pending Codex review), root
`README.md`, progress-hub prose and the `diagram:BV` description (still `partial`, label
unchanged, KLS open); Blueprint and `research/tasks.json` unchanged; views regenerated from an
isolated index/object store (adding only the dirty `research/tasks.json` and chapter 45),
`update.py --check` passed, real index unstaged, `git diff --check` passed. Obstacles: none.
Suggested next: the reverse inequality (Minkowski content ≤ perimeter needs coarea/regularity
and fails in general without it), or the Cheeger-infimum inequality this one-sided bound gives
directly (BV Cheeger constant ≤ Minkowski constant on the same admissible family).

## Phase 6 (2026-09-28)

### Baseline

Same conversation as phase 5, same checkout, HEAD `2f9f7e2`, real index with no staged changes.
Since the accepted phase-5 snapshot `ae727604…` only `HANDOFF.md` (Codex's acceptance marking)
and Codex's review record changed. SHA-256 at start: `MetricBV.lean` `1599c179…5c107656`,
`README.md` `6b4473b4…06e974f8`, `HANDOFF.md` `9e4a2f5f…ef033866`, `nodes.json`
`fd9bfcf1…3cc0eca0`; not edited: `codex-bv-overnight-review.md` `a03ecb33…bec8545a`,
`moment-map-spectral.md` `7106fbc3…29b8bee5`. The phase-5 receipt does not cover this snapshot.

### Placement plan

Object and role: sequential lower semicontinuity of the existing relaxation `perimeter ν` under
global `L¹(ν)` convergence of set indicators, for every Borel measure: if
`∫⁻ ‖1_{B n} - 1_B‖ₑ dν → 0` with measurable `B n`, then
`perimeter ν B ≤ liminf (perimeter ν ∘ B) atTop`. A relaxation property, not the BV–Minkowski
comparison. Proof: for every `a` strictly above the liminf (possibly `a = ⊤`; if the liminf is
`⊤` there is no such `a` and the bound is trivial) the indices with `perimeter ν (B n) < a` are
frequent; for `ε k = (k + 1)⁻¹` choose such an index `m k` with set distance below `ε k`
(frequently ∧ eventually), then by the phase-4 epsilon test a `g k` with distance to `B (m k)`
below `ε k` and cost below `a`. The triangle bound `indicatorDistance ν g B ≤
indicatorDistance ν g C + ∫⁻ ‖1_C - 1_B‖ₑ` (for measurable `C`, since `g` is continuous) gives
distance to `B` at most `2 ε k → 0`, so `g` is an approximating sequence for `B` with every cost
below `a`; `perimeter_le_sequence` gives `perimeter ν B ≤ a`, and density of `ENNReal` gives the
claim. No perimeter is assumed finite, no recovery sequence or cost bound is assumed, and an
empty approximation class for `B` or for some `B n` is allowed (it only makes perimeters `⊤`).
Measurability of `B` itself is not used by the proof; the owner theorem therefore assumes only
measurable `B n`, and the client checks the requested form with measurable `B` as well.
Owner and destination: `KLS/Geometry/Perimeter/MetricBV.lean` (extend after the recovery
sequence: `indicatorDistance_le_add`, `perimeter_le_liminf_of_tendsto`). No new imports
expected. Client: `research/audits/MetricBVLowerSemicontinuityAudit.lean` (new): full signature,
the requested form, constant sequences, empty carrier, zero perimeter of null sets,
infinite target and infinite liminf (whole line for Lebesgue measure on `ℝ`), and the consequence
that no measurable sets of finite liminf perimeter converge to the whole line there. API:
additions only. Validation: strict compilation of the module, `BVConstant.lean`, the new and the
six earlier MetricBV clients, standard transitive axioms, isolated-index progress generation and
`update.py --check`, frozen full `research/verify.py`, receipt under ignored
`build/audit/metric-bv-lower-semicontinuity/`.

### Phase 6 stage status

- [x] triangle bound and lower semicontinuity, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-lower-semicontinuity/receipt.md`)

### Phase 6 exact declarations

In `FunctionalInequalities.KLS.MetricBV` (`MetricBV.lean`, after `exists_recoverySequence`;
`{X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]`, no finiteness):

```lean
theorem indicatorDistance_le_add (ν : Measure X) (g : Test X) (B : Set X) {C : Set X}
    (hC : MeasurableSet C) :
    indicatorDistance ν g B ≤
      indicatorDistance ν g C + ∫⁻ x, ‖C.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν
theorem perimeter_le_liminf_of_tendsto (ν : Measure X) {B : Set X} {Bn : ℕ → Set X}
    (hBn : ∀ n, MeasurableSet (Bn n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(Bn n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => perimeter ν (Bn n)) atTop
```

Proof shape. `le_of_forall_gt_imp_ge_of_dense` reduces to levels `a` above the liminf (none if
the liminf is `⊤`; `a = ⊤` allowed). `frequently_lt_of_liminf_lt` gives frequent indices with
`perimeter ν (Bn n) < a`; intersected with the eventually small set distances they give `m k`
with distance below `(k + 1)⁻¹` (`choose`); `exists_test_lt_of_perimeter_lt` gives `g k` with
distance to `Bn (m k)` below `(k + 1)⁻¹` and cost below `a`. The triangle bound (the only use
of measurability: `1_{Bn (m k)}`, with `g k` continuous, makes the first summand measurable for
`lintegral_add_left'`) bounds the distance to `B` by `2 (k + 1)⁻¹ → 0`, so `g` is an
`ApproximatingSequence ν B`; `perimeter_le_sequence` and `liminf_le_of_frequently_le'` give
`perimeter ν B ≤ a`. No cost bound, recovery sequence or finiteness is assumed; the limit set
need not be measurable. Definitions and earlier signatures unchanged; no new imports; module
docstring extended.

### Phase 6 independent client (`research/audits/MetricBVLowerSemicontinuityAudit.lean`)

| Client | Content |
| --- | --- |
| `lowerSemicontinuity` | full signature of the owner theorem |
| `requestedForm` | the requested statement with measurable `B` and `Bn` |
| `triangleBound` | full signature of `indicatorDistance_le_add` |
| `constantSequence` | consistency for the constant sequence |
| `nullSet` | a measurable `ν`-null set has zero perimeter (limit of `∅`) |
| `emptyCarrier` | `X = Empty`, arbitrary sequence |
| `lebesgueWholeLineTop` | `perimeter volume univ = ⊤` on `ℝ` |
| `infiniteBoundary` | infinite target and infinite liminf (constant whole line) |
| `noFiniteApproximationOfWholeLine` | measurable sets converging to `univ` in `L¹(volume)` have liminf perimeter `⊤` |

All nine reports and the direct reports of both owner declarations are
`[propext, Classical.choice, Quot.sound]`. The six earlier MetricBV clients (4 + 8 + 11 + 8 + 5 +
8 reports) and `BVConstant.lean` recompile strictly with standard reports only.

Metadata: phase-6 sentence in the BV paragraph of `HANDOFF.md` (pending Codex review), root
`README.md`, progress-hub prose and the `diagram:BV` description (still `partial`, label
unchanged, KLS open); Blueprint and `research/tasks.json` unchanged; views regenerated from an
isolated index/object store (adding only the dirty `research/tasks.json` and chapter 45),
`update.py --check` passed, real index unstaged, `git diff --check` passed. Obstacles: none.
Suggested next: the relaxed BV–Minkowski Cheeger-infimum bridge (e.g. comparing
`perimeter` with the outer Minkowski content on the test class used there).

## Phase 5 (2026-09-28, new conversation)

### Baseline

New Claude conversation (the phase-1–4 conversation is stopped), same checkout, HEAD `2f9f7e2`,
real index with no staged changes; the dirty tree is extended in place. SHA-256 at start:
`MetricBV.lean` `b0d51bd5…4984d6cb`, `README.md` `700d3722…62f75bd0`, `HANDOFF.md`
`3278836a…4cc44a2c`, `research/progress/nodes.json` `aa28ac46…7d0e5674`; not edited:
`codex-bv-overnight-review.md` `bb6b242b…72fc751f`, `moment-map-spectral.md` `7106fbc3…29b8bee5`.
`MetricBV.lean` is not pinned in `research/tasks.json`. The phase-4 receipt does not cover this
snapshot.

### Placement plan

Object and role: a recovery sequence for the existing relaxation, i.e. an actual
`ApproximatingSequence ν B` whose costs converge to `perimeter ν B` in the `ENNReal` topology,
for every Borel measure `ν` and every `B` with `perimeter ν B < ⊤`. Not Minkowski recovery and
not lower semicontinuity of the relaxation. Construction: for positive error and threshold
sequences `ε n`, `η n`, choose (by `Classical.choose`) the phase-4 test with
`indicatorDistance < ε n` and `cost < perimeter + η n` (the threshold is strictly above the
finite perimeter by `ENNReal.lt_add_right`). If `ε → 0` the tests form an approximating sequence
(squeeze); if `η → 0` the limsup of the costs is at most the perimeter, and
`perimeter_le_sequence` gives the liminf lower bound, so the costs converge (no pointwise lower
bound is claimed: single tests may cost less than the perimeter). The concrete choice
`ε n = η n = (n + 1)⁻¹` gives the existence form. Finiteness is necessary for the threshold
construction; for infinite perimeter the class may be empty and nothing is claimed.
Owner and destination: `KLS/Geometry/Perimeter/MetricBV.lean` (extend next to
`exists_test_lt_of_perimeter_lt`; a general `tendsto_cost_of_limsup_le` for any approximating
sequence, `recoveryTest`, `recoverySequence` and their bounds, `exists_recoverySequence`). No new
imports expected. Client: `research/audits/MetricBVRecoverySequenceAudit.lean` (new): full
signatures, empty carrier, zero perimeter (empty set for Lebesgue measure on `ℝ`, the whole line
for the Gaussian law), and the infinite-perimeter boundary (`univ` for Lebesgue measure on `ℝ`
fails the hypothesis). API: additions only; `Test`, `cost`, `indicatorDistance`,
`ApproximatingSequence`, `perimeter` unchanged. Validation: strict compilation of the module and
the new client, the earlier five MetricBV clients recompiled, standard transitive axioms,
isolated-index progress generation with `update.py --check`, frozen full `research/verify.py`,
receipt under ignored `build/audit/metric-bv-recovery-sequence/`.

### Phase 5 stage status

- [x] lemma family, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt
  `build/audit/metric-bv-recovery-sequence/receipt.md`)

### Phase 5 exact declarations

In `FunctionalInequalities.KLS.MetricBV` (`MetricBV.lean`, after
`exists_test_lt_of_perimeter_lt`; `{X : Type*} [MetricSpace X] [MeasurableSpace X]
[BorelSpace X]`, no finiteness of the measure):

```lean
theorem tendsto_cost_of_limsup_le {ν : Measure X} {B : Set X} (s : ApproximatingSequence ν B)
    (h : limsup (fun n => cost ν (s.1 n)) atTop ≤ perimeter ν B) :
    Tendsto (fun n => cost ν (s.1 n)) atTop (𝓝 (perimeter ν B))
def recoveryTest {ν : Measure X} {B : Set X} (hB : perimeter ν B < ⊤) {ε η : ENNReal}
    (hε : 0 < ε) (hη : 0 < η) : Test X   -- Classical.choose of the phase-4 test, threshold perimeter + η
theorem indicatorDistance_recoveryTest_lt (hB) (hε) (hη) :
    indicatorDistance ν (recoveryTest hB hε hη) B < ε
theorem cost_recoveryTest_lt (hB) (hε) (hη) :
    cost ν (recoveryTest hB hε hη) < perimeter ν B + η
def recoverySequence {ν : Measure X} {B : Set X} (hB : perimeter ν B < ⊤) {ε η : ℕ → ENNReal}
    (hε0 : ∀ n, 0 < ε n) (hη0 : ∀ n, 0 < η n) (hε : Tendsto ε atTop (𝓝 0)) :
    ApproximatingSequence ν B   -- n ↦ recoveryTest hB (hε0 n) (hη0 n), distances squeezed to 0
theorem indicatorDistance_recoverySequence_lt (hB) (hε0) (hη0) (hε) (n : ℕ) :
    indicatorDistance ν ((recoverySequence hB hε0 hη0 hε).1 n) B < ε n
theorem cost_recoverySequence_lt (hB) (hε0) (hη0) (hε) (n : ℕ) :
    cost ν ((recoverySequence hB hε0 hη0 hε).1 n) < perimeter ν B + η n
theorem tendsto_cost_recoverySequence (hB) (hε0) (hη0) (hε) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => cost ν ((recoverySequence hB hε0 hη0 hε).1 n)) atTop (𝓝 (perimeter ν B))
theorem exists_recoverySequence (ν : Measure X) (B : Set X) (hB : perimeter ν B < ⊤) :
    ∃ g : ApproximatingSequence ν B,
      Tendsto (fun n => cost ν (g.1 n)) atTop (𝓝 (perimeter ν B))
```

Proof shape. The upper bound is `limsup cost ≤ limsup (perimeter + η n) = perimeter` from the
per-term strict bounds; the lower bound is `perimeter_le_sequence` (liminf), combined by
`tendsto_of_le_liminf_of_limsup_le`. No pointwise lower bound on single costs is used or true in
general. `exists_recoverySequence` uses `ε n = η n = ((n + 1 : ℕ) : ENNReal)⁻¹`. The module
docstring was extended; definitions `Test`, `cost`, `indicatorDistance`, `ApproximatingSequence`,
`perimeter` and all earlier signatures are unchanged; no new imports.

### Phase 5 independent client (`research/audits/MetricBVRecoverySequenceAudit.lean`)

| Client | Content |
| --- | --- |
| `recoverySequenceExists` | full signature of `exists_recoverySequence` |
| `explicitSequence` | both per-term bounds, vanishing distances and cost convergence for arbitrary positive vanishing `ε`, `η` |
| `limsupCriterion` | `tendsto_cost_of_limsup_le` for an arbitrary approximating sequence |
| `liminfEq` | consequence: some approximating sequence has liminf cost equal to the perimeter |
| `emptyCarrier` | `X = Empty`, any measure and set: costs tend to `0` |
| `lebesgueEmpty` | zero perimeter for an infinite measure (empty set, Lebesgue on `ℝ`) |
| `gaussianWholeLine` | zero perimeter of `univ` for `gaussianReal 0 1` via the phase-3 bridge |
| `lebesgueWholeLineInfinite` | `perimeter volume univ = ⊤` on `ℝ`, so the hypothesis fails; nothing claimed |

All eight reports and the direct reports of the five main declarations are
`[propext, Classical.choice, Quot.sound]`. The five earlier MetricBV clients (4 + 8 + 11 + 8 + 5
reports) and `BVConstant.lean` recompile strictly with standard reports only.

Commands (from `formalization/`): `lake env lean -DwarningAsError=true
FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV.lean`, `lake build
FunctionalInequalities.KLS.Geometry.Perimeter.MetricBV`, `lake env lean -DwarningAsError=true
../research/audits/MetricBVRecoverySequenceAudit.lean`, the same for the earlier clients and
`KLS/Geometry/Cheeger/BVConstant.lean`. Metadata: phase-5 sentence in the BV paragraph of
`HANDOFF.md` (pending Codex review), root `README.md`, progress-hub prose and the `diagram:BV`
description (still `partial`, label unchanged, KLS open); Blueprint and `research/tasks.json`
unchanged (`MetricBV.lean` is not pinned); views regenerated from an isolated index/object store
(adding only the dirty `research/tasks.json` and chapter 45), `update.py --check` passed, real
index unstaged, `git diff --check` passed. Obstacles: none. Suggested next: lower semicontinuity
of the relaxation under `L¹` convergence (a diagonal argument over recovery sequences), then the
relaxed BV–Minkowski Cheeger-infimum bridge.

## Phase 4 (2026-09-28)

### Placement plan

Object and role: an epsilon recovery test for the existing relaxation, the prerequisite for
diagonal recovery and lower semicontinuity (not Minkowski recovery). Statement: for every Borel
measure `ν` on a metric space (no finiteness), set `B`, `a : ENNReal` with `perimeter ν B < a`
and `ε : ENNReal` with `0 < ε`, there is `g : Test X` with `indicatorDistance ν g B < ε` and
`cost ν g < a`. Proof: `iInf_lt_iff` selects an approximating sequence with liminf cost below
`a`; `frequently_lt_of_liminf_lt` gives frequently small costs (the liminf is not an eventual
bound); `L¹` convergence gives eventually small distances; intersect. `a = ⊤` is allowed; an
empty approximation class makes the perimeter `⊤`, so the hypothesis excludes it without an extra
assumption. Owner: `KLS/Geometry/Perimeter/MetricBV.lean` (extend next to `perimeter_le_sequence`).
Client: `research/audits/MetricBVRecoveryAudit.lean` (finite and top thresholds). API: additions
only; definitions unchanged.

### Phase 4 stage status

- [x] lemma, strict client, docs/progress
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt)

### Phase 4 exact declaration

In `FunctionalInequalities.KLS.MetricBV` (`MetricBV.lean`, after `perimeter_le_sequence`;
`{X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]`, no finiteness):

```lean
theorem exists_test_lt_of_perimeter_lt (ν : Measure X) (B : Set X) {a : ENNReal}
    (ha : perimeter ν B < a) {ε : ENNReal} (hε : 0 < ε) :
    ∃ g : Test X, indicatorDistance ν g B < ε ∧ cost ν g < a
```

Client `research/audits/MetricBVRecoveryAudit.lean` (five standard-only reports):
`recoveryTest` (full signature), `topThreshold` (`a = ⊤`, finite perimeter), `finiteThresholdEmpty`
(any measure, `B = ∅`, `a = 1/2`), `lebesgueEmpty` (Lebesgue measure on `ℝ`, an infinite measure),
`gaussianWholeLine` (standard Gaussian, `B = univ`, any `a > 0`, via the phase-3 bridge). The
earlier four MetricBV clients recompile with only standard reports.

Commands: `lake env lean -DwarningAsError=true FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV.lean`
and `lake env lean -DwarningAsError=true ../research/audits/MetricBVRecoveryAudit.lean` (from
`formalization/`). Metadata: BV paragraph of `HANDOFF.md`, root `README.md`, progress-hub prose
and the `diagram:BV` description (still `partial`); Blueprint and `research/tasks.json` unchanged;
views regenerated from an isolated index/object store, `update.py --check` passed, real index
unstaged. Obstacles: none. Suggested next: a diagonal recovery sequence from these tests, then
lower semicontinuity of the relaxation under `L¹` convergence.

## Phase 3 (2026-09-28)

### Baseline

HEAD `2f9f7e2`, real index with no staged changes. Current files are extended, never replaced
from older copies; SHA-256 at start: `README.md` `ec42d0bc…77cb`, `HANDOFF.md`
`1e684a07…edbac`, `research/progress/nodes.json` `06e8ab4b…6640`, `research/progress/README.md`
`c852fc2f…3663`; not edited: `research/handoffs/codex-bv-overnight-review.md` `0a99dffd…02ed`,
`research/handoffs/moment-map-spectral.md` `7106fbc3…bee5`. Earlier receipts do not cover this
snapshot.

### Placement plan

Object and role: a test-class bridge for the existing `MetricBV.perimeter`. Given globally
Lipschitz `f n : X → ℝ` (each with its own constant, values and support unrestricted) whose global
`L¹(ν)` distance `∫⁻ ‖f n x - B.indicator 1 x‖ₑ dν` to `1_B` tends to zero, on a metric space with a
finite Borel measure, construct explicit tests `g n` (`Test.truncate x₀ n (f n)` =
`cutoff x₀ n · clampUnit ∘ f n`) with the same `L¹` convergence and
`liminf cost (g n) ≤ liminf ∫⁻ slope (f n)`; hence `perimeter ν B ≤ liminf ∫⁻ slope (f n)`.
Mathematics: `|χ c(y) - χ c(x)| ≤ |f y - f x| + |χ y - χ x|` for `χ, c ∈ [0, 1]`, so
`slope (g n) ≤ slope (f n) + 1_{(ball x₀ n)ᶜ}`; and `|χ c - 1_B| ≤ |f - 1_B| + 1_{(ball x₀ n)ᶜ}`.
The errors are `ν (ball x₀ n)ᶜ → 0` (finite measure). Infinite costs are kept in `ENNReal`;
the empty carrier is handled by the zero test. Non-claims: no identification of global
Lipschitz/global `L¹` with the literature's locally Lipschitz/`L¹_loc` classes, no unrestricted
relaxation definition (not needed for the deliverable; the converse inequality is immediate since
tests are globally Lipschitz), no BV–Minkowski identification.
Owner and destination: `KLS/Geometry/Perimeter/MetricBV.lean` (extend, perimeter family; reuses
`cutoff`, `clampUnit`, `tendsto_measure_compl_ball` and `Energy.LocalSlope.apply_le_add`). No new
imports. Client: `research/audits/MetricBVLipschitzAudit.lean` (new). Public API: additions only.
Validation: strict compilation, standard transitive axioms, isolated-index progress generation,
full verifier on the frozen final snapshot, receipt under ignored `build/`.

### Phase 3 stage status

- [x] truncated test and pointwise bounds
- [x] explicit sequence theorem, existence form with empty carrier, perimeter upper bound
- [x] strict independent client and axiom reports
- [x] documentation, canonical BV node, progress regeneration (isolated index)
- [ ] full verifier on the frozen snapshot (result recorded only in the receipt)

### Phase 3 exact declarations

In `FunctionalInequalities.KLS.MetricBV` (`KLS/Geometry/Perimeter/MetricBV.lean`, section
`LipschitzBridge`; file variables `{X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]`,
omitted where unused):

```lean
theorem abs_mul_sub_mul_le {u v c c' : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hc0 : 0 ≤ c')
    (hc1 : c' ≤ 1) : |u * c - v * c'| ≤ |c - c'| + |u - v|
def Test.truncate (x₀ : X) (R : ℝ) (f : X → ℝ) (hf : ∃ K : ℝ≥0, LipschitzWith K f) : Test X
  -- toFun x = cutoff x₀ R x * clampUnit (f x)
theorem apply_truncate_le (x₀ : X) (R : ℝ) {f : X → ℝ} (hf : ∃ K : ℝ≥0, LipschitzWith K f) (x : X) :
    Energy.LocalSlope.apply (Test.truncate x₀ R f hf) x ≤
      Energy.LocalSlope.apply f x + (Metric.ball x₀ R)ᶜ.indicator 1 x
theorem enorm_truncate_sub_le (x₀ : X) (R : ℝ) {f : X → ℝ} (hf : ∃ K : ℝ≥0, LipschitzWith K f)
    (B : Set X) (x : X) :
    ‖Test.truncate x₀ R f hf x - B.indicator (1 : X → ℝ) x‖ₑ ≤
      ‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (Metric.ball x₀ R)ᶜ.indicator 1 x
theorem cost_truncate_le (ν : Measure X) (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    cost ν (Test.truncate x₀ R f hf) ≤ ∫⁻ x, Energy.LocalSlope.apply f x ∂ν + ν (Metric.ball x₀ R)ᶜ
theorem indicatorDistance_truncate_le (ν : Measure X) (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) (B : Set X) :
    indicatorDistance ν (Test.truncate x₀ R f hf) B ≤
      ∫⁻ x, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν + ν (Metric.ball x₀ R)ᶜ
theorem tendsto_indicatorDistance_truncate (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X)
    {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => indicatorDistance ν (Test.truncate x₀ n (f n) (hf n)) B) atTop (𝓝 0)
theorem liminf_cost_truncate_le (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X)
    {f : ℕ → X → ℝ} (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n)) :
    liminf (fun n : ℕ => cost ν (Test.truncate x₀ n (f n) (hf n))) atTop ≤
      liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop
theorem exists_approximatingSequence_of_lipschitz (ν : Measure X) [IsFiniteMeasure ν]
    {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    ∃ g : ApproximatingSequence ν B,
      liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop
theorem perimeter_le_liminf_of_lipschitz (ν : Measure X) [IsFiniteMeasure ν]
    {B : Set X} {f : ℕ → X → ℝ} (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop
```

Scope. The Lipschitz constant of `f n` is an arbitrary existential per `n`; neither the values nor
the support of `f n` are bounded; the `L¹` quantity is the same global `∫⁻ ‖· - 1_B‖ₑ dν` used by
`indicatorDistance`; costs are `ENNReal` and may be infinite; the empty carrier is handled by the
zero test. The reverse inequality (tests are globally Lipschitz with finite `L¹` distance) is
immediate from the definition; no unrestricted-relaxation definition was added, since the
deliverable did not need it. `perimeter`, `Test` and all earlier signatures are unchanged. No
identification with locally Lipschitz tests or `L¹_loc` convergence, and no BV–Minkowski
identification, is claimed.

### Phase 3 independent client (`research/audits/MetricBVLipschitzAudit.lean`)

| Client | Content |
| --- | --- |
| `truncatedSlope`, `truncatedDistance` | the two pointwise bounds, full signatures |
| `explicitConvergence`, `explicitCost` | the explicit sequence `Test.truncate x₀ n (f n)` |
| `existenceForm`, `perimeterBound` | the existence form and the perimeter upper bound |
| `emptyCarrier` | an empty carrier (`X = Empty`), where no base point exists |
| `gaussianWholeLine` | an approximant that is not a test: the constant `1` on `ℝ` (unbounded support) gives `perimeter (gaussianReal 0 1) univ = 0`, outside the finite-space theorem `perimeter_univ` |

### Phase 3 commands and results

```sh
cd formalization
lake build FunctionalInequalities.KLS.Geometry.Cheeger.BVConstant
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV.lean
lake env lean -DwarningAsError=true ../research/audits/MetricBVLipschitzAudit.lean
lake env lean -DwarningAsError=true ../research/audits/MetricBVComplementAudit.lean
lake env lean -DwarningAsError=true ../research/audits/MetricBVInterfaceAudit.lean
lake env lean -DwarningAsError=true ../research/audits/MetricBVCheegerAudit.lean
```

Observed: builds succeed; `MetricBV.lean` compiles with no warnings; the new client prints eight
reports and the earlier clients eight, four and eleven, each exactly
`[propext, Classical.choice, Quot.sound]`.

Metadata: the BV paragraph of `HANDOFF.md` (phase 2 now recorded as accepted; phase 3 pending
review), the root `README.md` status sentence, the non-generated progress-hub prose, the
`diagram:BV` description (still `partial`, label unchanged) and chapter-45 prose (explicitly
restricted to global Lipschitz/global `L¹`) were updated. `research/tasks.json` hashes were
refreshed only for chapter 45 (`MetricBV.lean` is not pinned). Progress views were regenerated
from an isolated index/object store; `update.py --check` passed; the real index has no staged
changes. All four routes and the approach-table statuses are unchanged; KLS remains open.

### Phase 3 obstacles

None. Finiteness of the measure is used only for `ν (ball x₀ n)ᶜ → 0`.

## Phase 2 (2026-09-28)

### Baseline

- HEAD `2f9f7e2`, real index with no staged changes (index file SHA-256 at start
  `13d9a239feba15ea9053ae1d6d9863825dcafbbbb21e453ef14157009e01da8f`).
- Starts from the current tree including Codex's documentation repair; these files are read
  and extended, never replaced from an older copy. SHA-256 at start:
  `README.md` `c22fcf748b3a014757be9ef0ccecc3c6fafce1e0d76d16f67c9874de91fc2348`,
  `HANDOFF.md` `d2d1b5a81f422cde8291aae6097fa70ed0bcdb31be77e9bce07b31491f70742f`,
  `research/progress/nodes.json` `704b0676e564a312e1601a7aa5b1400ade7e2d08fb2f8cee9f6c8d75eeeb2354`,
  `research/progress/README.md` `8cc27aec4d9f7ebd315ea32a0962d31cec8d185637fa067e5f349972d29a827e`,
  `research/handoffs/moment-map-spectral.md` `7106fbc3e145eaa02be7d2ddab755a887a0173a61bf1fea2c72b4a9329b8bee5`
  (not edited), `research/handoffs/codex-bv-overnight-review.md`
  `341f179c6c613ba0469e9c6144f7003d88889ec6b944fda6ac56875f9bf38596` (maintained by Codex; not
  edited). The phase-1 full-verifier receipt does not cover this snapshot.

### Placement plan

Object and role: equality of the two existing BV Cheeger infima `halfConstant ν` (measurable
`B`, `0 < ν B ≤ 1/2`, quotient `perimeter B / ν B`) and `symmetricConstant ν` (measurable `B`,
`0 < ν B < 1`, quotient `perimeter B / min (ν B) (1 - ν B)`) for every probability measure on
a metric space with Borel measurable structure. Both definitions stay unchanged.
Mathematics: `symmetricConstant ≤ halfConstant` because a half-mass test set has
`ν B < 1` and `min (ν B) (1 - ν B) = ν B`. Conversely, a symmetric test set with `ν B ≤ 1/2` is a
half-mass test set with the same quotient, and one with `1/2 < ν B < 1` is replaced by `Bᶜ`:
it is measurable, `ν Bᶜ = 1 - ν B ∈ (0, 1/2)`, `perimeter Bᶜ = perimeter B` by the accepted
finite-measure complement symmetry, and the minimum is `1 - ν B`. The boundary `ν B = 1/2`
falls in the first case; empty admissible families give `⊤` on both sides; infinite perimeter
is carried by `ENNReal` division. Consequences: the intrinsic closed-support instance and the
zero-dimensional `symmetricConstant = ⊤`.
Owner and destination: `KLS/Geometry/Cheeger/BVConstant.lean` (extend; both definitions live
there). No new imports. Client: `research/audits/MetricBVCheegerAudit.lean` (new).
Public API: additions only. Validation: strict compilation, standard transitive axioms, a
full-verifier receipt for the frozen final snapshot. No claim of BV–Minkowski identification.

### Phase 2 stage status

- [x] equality theorem and corollaries in `BVConstant.lean`
- [x] strict independent client and axiom reports
- [x] documentation, canonical BV node evidence, progress regeneration (isolated index)
- [x] first full verifier run (snapshot `39b4e0d3…`); superseded by the audit repair below
- [x] audit repair requested by Codex (vacuous infinite-perimeter client replaced)
- [ ] full verifier on the repaired frozen snapshot: run after this file was finalized; receipt in
  the ignored `build/audit/metric-bv-halfsym/receipt-repair.md`, so recording it does not
  change the certified snapshot

### Phase 2 exact declarations

In `FunctionalInequalities.KLS.MetricBV` (`KLS/Geometry/Cheeger/BVConstant.lean`, file variables
`{X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]`; the two helper lemmas omit the
metric and Borel instances they do not use):

```lean
theorem le_one_sub_of_le_half {m : ENNReal} (h : m ≤ 1 / 2) : m ≤ 1 - m
theorem one_sub_lt_half_of_half_lt {m : ENNReal} (h : 1 / 2 < m) (h1 : m ≤ 1) : 1 - m < 1 / 2
theorem halfConstant_eq_symmetricConstant (ν : ProbabilityMeasure X) :
    halfConstant ν = symmetricConstant ν
theorem symmetricConstant_eq_top_of_subsingleton [Subsingleton X] (ν : ProbabilityMeasure X) :
    symmetricConstant ν = ⊤
theorem intrinsicHalfConstant_eq_symmetricConstant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [FiniteDimensional ℝ E] (μ : ProbabilityMeasure E) :
    intrinsicHalfConstant μ = symmetricConstant (intrinsicClosedSupportLaw μ)
```

`halfConstant` and `symmetricConstant` are unchanged, including measurable test sets, strictly
positive mass, `ν B ≤ 1/2` versus `ν B < 1`, and the `min (ν B) (1 - ν B)` denominator. The
proof uses `perimeter_compl_of_isFiniteMeasure` (accepted in phase 1) and Mathlib's
`prob_compl_eq_one_sub`. No new imports; no existing signature changed. Consumers of the two
definitions: only the audit clients.

### Phase 2 boundary cases (independent client `research/audits/MetricBVCheegerAudit.lean`)

| Client | Case |
| --- | --- |
| `halfEqSymmetric` | the general equality, full signature |
| `massOneHalf` | a set with `ν B = 1/2` is admissible in the half-mass family |
| `massAboveHalf` | `1/2 < ν B < 1` bounds `halfConstant` by `perimeter B / (1 - ν B)`, via the complement |
| `infiniteSymmetricQuotient` | conditional: a measurable `B` with `0 < ν B < 1` and `perimeter B = ⊤` has symmetric quotient `⊤`, and that quotient bounds `symmetricConstant` |
| `infiniteHalfQuotient` | conditional: a measurable `B` with `0 < ν B ≤ 1/2` and `perimeter B = ⊤` has half-mass quotient `⊤`, and that quotient bounds `halfConstant` |
| `infiniteAdmissibleFamily` | conditional: if every admissible set (measurable, `0 < ν B < 1`) has infinite perimeter, both constants are `⊤`; the quantifier excludes `∅` and other inadmissible sets |
| `admissibleFamilyPremiseOnePoint` | consistency only: the previous premise holds (vacuously) on a one-point space; not an infinite-perimeter example |
| `onePoint` | one-point space: empty admissible families, both `⊤` |
| `gaussianReal` | an unbounded non-finite carrier (standard Gaussian on `ℝ`) |
| `intrinsicEquality` | the closed intrinsic support instance |
| `intrinsicZeroDimension` | zero affine dimension: `symmetricConstant = ⊤` on the intrinsic support |

### Phase 2 verification commands and results

```sh
cd formalization
lake build FunctionalInequalities.KLS.Geometry.Cheeger.BVConstant
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/Geometry/Cheeger/BVConstant.lean
lake env lean -DwarningAsError=true ../research/audits/MetricBVCheegerAudit.lean
lake env lean -DwarningAsError=true ../research/audits/MetricBVComplementAudit.lean
lake env lean -DwarningAsError=true ../research/audits/MetricBVInterfaceAudit.lean
```

Observed after the audit repair: build succeeds; `BVConstant.lean` compiles with no warnings; the
repaired client prints eleven reports and the phase-1 clients eight and four, every one exactly
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no new axiom).

Audit repair (Codex review, 2026-09-28). The first version's `infinitePerimeter` assumed
`∀ B, perimeter ν B = ⊤`, which contradicts `perimeter_empty`; it compiled but tested nothing.
It is replaced by the three conditional clients and the consistency client above, which quantify
only over admissible sets. These are conditional quotient checks: no set of infinite perimeter
is constructed, and none is claimed. `BVConstant.lean` and all other clients are unchanged by
the repair.

Metadata. `HANDOFF.md` (BV current-result paragraph), root `README.md` (status sentence), the
non-generated prose of `research/progress/README.md` (current handoff and BV bullet), the
canonical `diagram:BV` node in `research/progress/nodes.json` (description; evidence source now
this handoff; state still `partial`, label still `NEXT: Metric BV identification`) and the
chapter-45 proof prose were updated. All four routes, the combined diagram topology and the
approach-table statuses are unchanged; dimension-free KLS remains open and no BV–Minkowski
identification is claimed. `research/tasks.json` evidence hashes were refreshed only for the
edited chapter 45 (`BVConstant.lean` is not pinned). Progress views were generated with
`GIT_INDEX_FILE`/`GIT_OBJECT_DIRECTORY` pointing at an isolated copy (adding only
`research/tasks.json` and chapter 45); `update.py --check` passed; the real index has no staged
changes. Codex's review record and the senior spectral handoff were not edited.

### Phase 2 obstacles

None. The equality needs no hypothesis beyond a probability measure (finiteness for complement
symmetry is automatic). Next candidate: Ambrosio–Di Marino–Gigli Lemma 2.1 (perimeter bounded by
lower Minkowski content after `L¹` relaxation) as the first half of the BV–Minkowski bridge.

## Phase 1 record (accepted)

## Working directory and baseline

- Working directory: `/Users/lyuyuwei/Documents/ChatGPT/KLS` (main checkout). The old
  `/private/tmp/kls-affine-w2-liminf` worktree was not touched or merged.
- Baseline HEAD: `2f9f7e2` ("Formalize metric BV perimeter interface and align progress").
- Preserved dirty baseline (unchanged by this work):
  - `README.md` modified (1 line), SHA-256
    `2577843af55a8316cb0553601d840948ba839ce5ea58ae142ae9a0c6ecc51c56`;
  - `research/handoffs/moment-map-spectral.md` (untracked), SHA-256
    `7106fbc3e145eaa02be7d2ddab755a887a0173a61bf1fea2c72b4a9329b8bee5`.
- No commit, push, reset or clean. The real Git index was not modified; progress views were
  generated from an isolated copy of the index. `KLS.kls` and its isolated hole are untouched.

## Placement plan (phase 1)

Object and role: complement symmetry `perimeter ν Bᶜ = perimeter ν B` of the existing
`MetricBV.perimeter` (tests: bounded-value, bounded-support Lipschitz functions; actual `L¹`
convergence to the indicator; `ENNReal` liminf of the local-slope integral), beyond the
finite-space case.

Mathematical conditions. `1 - f` does not have bounded support, so it is not a test. The
reflected test is `Test.reflect x₀ R f = χ_R · (1 - clamp₀₁ f)`, where `χ_R` is a 1-Lipschitz
radial cutoff (`1` on `closedBall x₀ R`, `0` outside `ball x₀ (R+1)`). Pointwise:
`slope (reflect) ≤ slope f + 1_{(ball x₀ R)ᶜ}` and
`|reflect − 1_{Bᶜ}| ≤ |f − 1_B| + 1_{(ball x₀ R)ᶜ}`. With `R = n` the errors are
`ν (ball x₀ n)ᶜ`, which tend to zero for a **finite** measure. Finiteness is necessary, not a
proof artifact: for Lebesgue measure on `ℝ`, `perimeter ∅ = 0` while `perimeter univ = ⊤`
(no bounded-support test is `L¹`-close to `1`). The theorem needs no separability,
completeness, doubling or probability normalization; the empty space is handled separately.

Destinations and dependency direction:
- `Energy/LocalSlope/Basic.lean` (extended; owner of `LocalSlope.apply`): generic local-slope
  comparison tools. No new imports.
- `KLS/Geometry/Perimeter/MetricBV.lean` (extended; owner of `perimeter`): clamp, cutoff,
  reflected test, pointwise and integrated bounds, the finite-measure theorem, the
  closed-support specialization and the infinite-measure obstruction. No new imports.
- `KLS/Geometry/Cheeger/BVConstant.lean` (extended): the intrinsic closed-support specialization,
  placed next to `intrinsicClosedSupportLaw`, which is defined there.
- `research/audits/MetricBVComplementAudit.lean` (new independent client).

## Stage status

- [x] local-slope comparison lemmas
- [x] reflected cut-off test and its pointwise and integrated bounds
- [x] general complement symmetry for finite measures
- [x] closed-support-law and intrinsic closed-support specializations
- [x] infinite-measure obstruction (finiteness is necessary)
- [x] strict client and axiom reports
- [x] Blueprint prose and progress views aligned (no node status change)
- [ ] full verifier receipt: run on the frozen snapshot after this file was written; the
  receipt location is recorded in the ignored `build/audit/metric-bv-complement/receipt.md`
  so that recording it does not change the certified snapshot

## Exact declarations

`FunctionalInequalities.Energy.LocalSlope` (in `Energy/LocalSlope/Basic.lean`, any metric space):

```lean
theorem apply_le_add {g a b : X → ℝ} {x : X} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ y, dist y x < r₀ → dist (g y) (g x) ≤ dist (a y) (a x) + dist (b y) (b x)) :
    apply g x ≤ apply a x + apply b x
theorem apply_le_of_dist_le {g a : X → ℝ} {x : X} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ y, dist y x < r₀ → dist (g y) (g x) ≤ dist (a y) (a x)) : apply g x ≤ apply a x
theorem apply_le_of_lipschitzWith {f : X → ℝ} {K : NNReal} (hf : LipschitzWith K f) (x : X) :
    apply f x ≤ K
theorem apply_eq_zero_of_eqOn_ball {f : X → ℝ} {x : X} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ y, dist y x < r₀ → f y = f x) : apply f x = 0
```

`FunctionalInequalities.KLS.MetricBV` (in `MetricBV.lean`; `[MetricSpace X] [MeasurableSpace X]
[BorelSpace X]`):

```lean
def Test.zero : Test X
theorem cost_zero (ν : Measure X) : cost ν Test.zero = 0
theorem perimeter_empty (ν : Measure X) : perimeter ν (∅ : Set X) = 0
def clampUnit (t : ℝ) : ℝ := max (min t 1) 0          -- with nonneg/le_one/zero/of_mem/abs_sub_le
def cutoff (x₀ : X) (R : ℝ) (x : X) : ℝ := clampUnit (R + 1 - dist x x₀)
                                        -- with abs_sub_le/eq_one/eq_zero/nonneg/le_one
theorem abs_mul_one_sub_sub_le {u v c c' : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hc0 : 0 ≤ c')
    (hc1 : c' ≤ 1) : |u * (1 - c) - v * (1 - c')| ≤ |c - c'| + |u - v|
def Test.reflect (x₀ : X) (R : ℝ) (f : Test X) : Test X
theorem apply_reflect_le (x₀ : X) (R : ℝ) (f : Test X) (x : X) :
    Energy.LocalSlope.apply (Test.reflect x₀ R f) x ≤
      Energy.LocalSlope.apply f x + (Metric.ball x₀ R)ᶜ.indicator 1 x
theorem enorm_reflect_sub_le (x₀ : X) (R : ℝ) (f : Test X) (B : Set X) (x : X) :
    ‖Test.reflect x₀ R f x - Bᶜ.indicator (1 : X → ℝ) x‖ₑ ≤
      ‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (Metric.ball x₀ R)ᶜ.indicator 1 x
theorem cost_reflect_le (ν : Measure X) (x₀ : X) (R : ℝ) (f : Test X) :
    cost ν (Test.reflect x₀ R f) ≤ cost ν f + ν (Metric.ball x₀ R)ᶜ
theorem indicatorDistance_reflect_le (ν : Measure X) (x₀ : X) (R : ℝ) (f : Test X) (B : Set X) :
    indicatorDistance ν (Test.reflect x₀ R f) Bᶜ ≤ indicatorDistance ν f B + ν (Metric.ball x₀ R)ᶜ
theorem tendsto_measure_compl_ball (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X) :
    Tendsto (fun n : ℕ => ν (Metric.ball x₀ n)ᶜ) atTop (𝓝 0)
theorem perimeter_compl_le_of_isFiniteMeasure (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    perimeter ν Bᶜ ≤ perimeter ν B
theorem perimeter_compl_of_isFiniteMeasure (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    perimeter ν Bᶜ = perimeter ν B
theorem perimeter_univ_eq_top_of_forall_isBounded (ν : Measure X)
    (h : ∀ S : Set X, Bornology.IsBounded S → ν Sᶜ = ⊤) : perimeter ν Set.univ = ⊤
theorem perimeter_compl_ne_real_volume :
    perimeter (volume : Measure ℝ) (∅ : Set ℝ)ᶜ ≠ perimeter (volume : Measure ℝ) ∅
-- section ClosedSupport, additionally [SecondCountableTopology X]:
theorem perimeter_compl_closedSupportLaw (ν : ProbabilityMeasure X)
    (B : Set (ν : Measure X).support) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) Bᶜ =
      perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) B
```

In `BVConstant.lean`:

```lean
theorem perimeter_compl_intrinsicClosedSupportLaw {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [FiniteDimensional ℝ E] (μ : ProbabilityMeasure E)
    (B : Set (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support) :
    perimeter (intrinsicClosedSupportLaw μ : Measure _) Bᶜ =
      perimeter (intrinsicClosedSupportLaw μ : Measure _) B
```

**API change to review.** `MetricBV.perimeter_empty` previously sat in `section FiniteSpace` with
`[Finite X]` and was proved with `Test.const 0`. It is now proved with the new `Test.zero` and
has no `[Finite X]` hypothesis; its name and conclusion are unchanged and all consumers
(`perimeter_eq_zero_of_subsingleton`, `MetricBVInterfaceAudit.lean`) compile unchanged. The
generalization is needed for the Lebesgue counterexample. All other changes are additions; the
finite-space `perimeter_compl` is kept, since it covers arbitrary (possibly infinite) measures.

## Verification commands and receipts

Run from `formalization/`:

```sh
lake build FunctionalInequalities.Energy.LocalSlope.Basic \
  FunctionalInequalities.KLS.Geometry.Perimeter.MetricBV \
  FunctionalInequalities.KLS.Geometry.Cheeger.BVConstant
lake env lean -DwarningAsError=true FunctionalInequalities/Energy/LocalSlope/Basic.lean
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV.lean
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/Geometry/Cheeger/BVConstant.lean
lake env lean -DwarningAsError=true ../research/audits/MetricBVComplementAudit.lean
lake env lean -DwarningAsError=true ../research/audits/MetricBVInterfaceAudit.lean
```

Observed (2026-09-28): all builds succeed; the three modules compile with no warnings; the new
client prints eight reports and the existing interface client four, each exactly
`[propext, Classical.choice, Quot.sound]`:
`slopeComparison`, `emptyPerimeter`, `finiteMeasureComplement`, `closedSupportComplement`,
`intrinsicComplement`, `gaussianRealComplement` (standard Gaussian on `ℝ`, an unbounded
non-finite carrier), `infiniteMassObstruction`, `lebesgueCounterexample`.

Metadata: `research/tasks.json` evidence hashes were refreshed only for the four edited pinned
files (`Energy/LocalSlope/Basic.lean`, chapter `45-shared-analytic-bridges.tex`; MetricBV and
BVConstant are not pinned). The chapter-45 proof prose now states finite-measure complement
symmetry, its closed-support consequence and the necessity of finiteness; the half-mass/
symmetric equality, Lemma 2.1, Theorem 3.6 recovery and the BV–Minkowski identification are
still literature comparisons. No Blueprint node changed status. Progress views were regenerated
with `GIT_INDEX_FILE=<copy of .git/index> python3 research/progress/update.py` after adding only
`research/tasks.json` and the chapter to the copy; only statement line anchors and the input
digest changed in `STATUS.md` and `LITERATURE.md`.

Full verifier: `python3 research/verify.py` on the frozen tree; see
`build/audit/metric-bv-complement/receipt.md` (ignored path) for the report path, exit status and
snapshot hash.

## Real obstacles and next steps

- None for phase 1. Finite measure is a genuine necessary condition, shown by
  `perimeter_compl_ne_real_volume`; the closed-support and intrinsic laws are probability
  measures, so the result applies to them without further hypotheses.
- Next candidates for review: the half-mass/symmetric Cheeger equality
  (`halfConstant = symmetricConstant` for probability laws, which now needs only complement
  symmetry and mass bookkeeping, including the `ν B = 1/2` and infinite-perimeter cases), then
  the Ambrosio–Di Marino–Gigli relaxation of Minkowski content.
- Not claimed: equivalence with the unrestricted Lipschitz-test perimeter, any Minkowski or
  Cheeger identification, or any change to the numerical π-Buser results.
