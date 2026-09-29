# One-dimensional log-concave Poincaré inequality `C_P^lit(ν) ≤ 12·Var_ν`: statement, semantic alignment, and proof

Date: 2026-09-10 (Asia/Shanghai). Baseline: local `main` submission `5e5c704`, working tree containing uncommitted on the same day Dirichlet witness work (`thm:smooth-gradient-relaxation-dirichlet`) and untracked `research/weekly/`; local branch leads `origin/main` by two commits and lags three document commits. User instructions: no commit, no push.
Lean/Mathlib is v4.33.0, Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`.
User approves "proceed to one-dimensional 12·Var" after completion of Dirichlet witness.

## Verification and Node Selection

Default `lake build` passes; receipt for Dirichlet witness `build/verification/20260910T092922.606486Z` passes.
`thm:one-dimensional-logconcave-poincare` is marked in Blueprint as "verified published input, not a local Lean proof", with sidecar claim `imported` (Bobkov 1999 Corollary 4.3 and (1.3)); tasks.json is `mathematics: published`, priority 5, infrastructure `unchecked`. It is the sole numerical input for the conditional fiber branch `cor:conditional-fiber-twelve-bound`. The library already contains Borell density representation (`IsBorellDensity`: measurable, non-negative, upper semicontinuous, log-concave, `withDensity` representation; internally continuous and positive), `LogConcave.absolutelyContinuous_of_interior_support_nonempty`, `LogConcave.convex_support`,
environment second moment `LogConcave.memLp_id_two`/[`integrable_id`], smooth test and literature constants match `LogConcave.smoothTest_constant_eq_localSlope`, and `Poincare.SmoothTest.Admissible.variance_le_integral_sq_sub`.
Mathlib already has partial integration `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, improper integral `integral_Ioi_of_hasDerivAt_of_tendsto`, `Directed.measure_iUnion`, `ofReal_variance`, `variance_dirac`.
No new Mathlib interface is needed, so `unchecked → available` is not proven in this round.

## Statement Design

Blueprint: every "online" log-concave probability measure ν satisfies `C_P^lit(ν) ≤ 12 Var_ν(T)`, including the zero variance case.

New module (all in `formalization/FunctionalInequalities/`):

| module | content |
| --- | --- |
| `Probability/Line/Cdf.lean` | `Probability.Line.cdf μ x := μ.real (Iic x)`; monotone, bounded, limit; increment integral, continuity, derivative when Lebesgue density exists `hasDerivAt_cdf`, median exists `exists_cdf_eq_half`, single point zero measure, uniform shift forward `map_cdf_eq_uniform : μ.map (cdf μ) = volume.restrict (Icc 0 1)`, `∫ cdf = 1/2`, `∫ (cdf − 1/2)² = 1/12`, `∫ (cdf − 1/2)³ = 0`, `integrable_comp_cdf` |
| `Probability/Line/ExpIntegral.lean` | interval integral of `C·exp(κ(s − x₀))` and decay direction half-line integral and integrability |
| `KLS/LogConcave/Line/Density.lean` | `structure KLS.LineDensity μ` (`ρ`, `isBorell`); `LogConcave.exists_lineDensity`, `convex_interior_support`, `measure_compl_interior_support`, `mem_interior_support_of_cdf`; `LineDensity.pos`, `concaveOn_log`, `ae_eq_zero_of_not_mem_interior_support`, `logSlope`; lower bound for chords `mul_exp_le_of_mem_Icc`, upper bound by extrapolation `le_mul_exp_of_not_mem_Ioo`, support exponent `exists_supergradient` |
| `KLS/LogConcave/Line/Hazard.lean` | four-point inequality `mul_le_mul_of_add_eq`; monotone failure rate `mul_measureReal_Ioi_le`, `mul_cdf_le`; median bounds `two_mul_measureReal_Ioi_le` (`2ρ(m)·μ(Ioi x) ≤ ρ x`, `m ≤ x`), `two_mul_cdf_le` (`2ρ(m)·F x ≤ ρ x`, `x ≤ m`); support line bounds `le_add_mul_cdf_sub` (`ρ x ≤ ρ m + k(F x − 1/2)`) |
| `KLS/LogConcave/Line/Hardy.lean` | interval Hardy step `Probability.Line.integral_sq_mul_le_of_le_integral_abs`; `integral_sq_sub_mul_le_right/left`; half-line `setIntegral_Ioi_sq_sub_le`, `setIntegral_Iic_sq_sub_le`; `LineDensity.smoothTest_holds : SmoothTest.Holds μ (1/ρ m)²` |
| `KLS/LogConcave/Line/Variance.lean` | `hasDerivAt_comparison`, `comparison_deriv_nonpos`, `quadratic_bound_le_sub`, `one_div_le_integral_mul` (`1/(12ρ(m)) ≤ ∫(x−m)(F−1/2)`), `one_div_le_variance` (`1/(12ρ(m)²) ≤ Var`) |
| `KLS/LogConcave/Line/Poincare.lean` | `KLS.logConcave_dirac`; `LogConcave.smoothTest_holds_twelve_variance`, `direction_eq_bot_or_interior_support_nonempty`, `localSlope_constant_le_twelve_variance`, `localSlope_constant_le_twelve_evariance` |
| `Poincare/LocalSlope/Basic.lean` (added) | `Intrinsic.constant_eq_zero_of_direction_subsingleton`, `constant_eq_zero_of_direction_eq_bot` |

Certificate `Solutions.ThmOneDimensionalLogConcavePoincare.certificate ν hν`:
`Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal (12 * variance id ν)` and
`≤ 12 * evariance id ν`. Three `example`: finite constant; Dirac measure at origin (log-concave, zero variance, constant `≤ 0`); smooth test inequality `SmoothTest.Holds ν (12·Var)` when the support is non-empty.

**What is claimed.** The table above declares and certifies, for any compact set on ℝ, a log-concave probability law. **What is not claimed.** No smaller universal constant (historical 4), any higher-dimensional conclusion, Cheeger inequality, spectral gap or generator, or conclusions on raw test energy; Hardy constant `1/ρ(m)²` is not claimed to be optimal. **Finiteness scope and dimension zero.** Line taken as ℝ, coordinate T as `id`; zero variance implies affine support is a point, direction space is zero-dimensional, constant is 0, covered by the general theorem.

## Semantic Alignment

| Blueprint clause | Lean | Conclusion |
| --- | --- | --- |
| Log-concave probability measure ν on a line | `ν : ProbabilityMeasure ℝ`, `KLS.LogConcave ν` (compact set definition of `def:log-concave-law`) | Consistent |
| `C_P^lit(ν)` | `Poincare.LocalSlope.Intrinsic.constant ν` (`def:literature-poincare-constant`; intrinsic measure first) | Consistent |
| `Var_ν(T)` | `variance id ν` (Mathlib `ProbabilityTheory.variance`, second moment of log-concave measures finite, guaranteed by `memLp_id_two`) | Consistent |
| Inequality `≤ 12 Var` | `≤ ENNReal.ofReal (12 * variance id ν)`; additionally `≤ 12 * evariance id ν` | Consistent (read in extended reals; extended variance form as supplement) |
| Zero variance case | Direction space `= ⊥` is often constant 0; Dirac examples `logConcave_dirac` and `variance_dirac` | Consistent |
| Proof: "verified published input, not a local Lean proof" | Local Lean proof, different path from Bobkov's Cheeger argument | Lean stronger: nodes change from `imported` to `proved`, recorded |
| Proof note: historical origin of constant 4 | Not addressed | Retained as historical origin |

No weakness of Lean over Blueprint was found. `\uses{def:log-concave-law,def:literature-poincare-constant}` is actually used in Lean; the proof additionally uses `thm:selected-literature-constant-equivalence` (smooth test and literature constant equal), which is explicitly noted in the proof text as `\cref`, though `\uses` remains unchanged (to avoid altering the dependency graph; can be added in subsequent node review if needed).
The theorem block of Blueprint supplements the reading of ℝ, `id`, `ENNReal.ofReal` in Lean and zero-dimensional explanation; the proof block retains the Bobkov source and adds a summary of the local route, removing "not a local Lean proof".

## Proof Route

1. **Zero-dimensional/positive-dimensional bisection.** `(affineSupport ν).direction : Submodule ℝ ℝ` is an ideal of ℝ, `Ideal.eq_bot_or_top`;
   `⊥` when `holds_zero_of_subsingleton` is a constant 0; when `⊤` the affine support is nonempty hence `affineSupport = ⊤`,
   `interior_support_nonempty_of_affineSupport_eq_top` The interior support Ω is nonempty.
2. **Density and support.** Ω is an open convex (interval), `μ Ωᶜ = 0` (support convex ⇒ boundary Haar null + absolutely continuous); Borell density ρ on Ω
   Continuous positive, `log ρ` concave, Ω exterior a.e. equal to zero; F continuous on Ω with `F' = ρ`; the median m exists and `m ∈ Ω`.
3. **Failure rate and median bounds.** The four-point inequality `ρ a ρ e ≤ ρ b ρ c` (`a ≤ b ≤ c ≤ e`, `a + e = b + c`), along translation
   `s ↦ s + (y − x)` by `MeasurePreserving.setIntegral_preimage_emb` integral yields `ρ x·μ(Ioi y) ≤ ρ y·μ(Ioi x)`
   With the mirror; setting x = m yields `2ρ(m)(1 − F) ≤ ρ` (right) and `2ρ(m)F ≤ ρ` (left), holding for all x (zero on both sides outside Ω).
4. **Hardy.** For a smooth admissible test f, set `g = f − f(m)`. Integrate `g²·(1 − F)'` by parts on `[m, x] ⊂ Ω`:
   `∫ g²ρ = −g(x)²(1−F(x)) + ∫ 2gg'(1−F) ≤ ∫ 2|g||g'|(1−F)`, then use `2(1−F) ≤ ρ/c` with
   `2|g||g'|/c ≤ g² + g'²/c²` gets `∫_m^x g²ρ ≤ c⁻²∫_m^x g'²ρ`; left side uses F symmetry. Ray: write `∫_S g² dμ` as
   The measure of `μ.withDensity (ofReal g²)`, `Ioi m ∩ Ω ⊆ ⋃_{q ∈ ℚ ∩ Ω, q > m} Ioc m q` (oriented family, `Directed.measure_iUnion`),
   Ωᶜ has measure zero, yielding `∫_{Ioi m} g² dμ ≤ c⁻²∫_{Ioi m} f'² dμ`; adding both sides and using `variance_le_integral_sq_sub`,
   `gradient_eq_deriv'` Write the energy as `∫ f'²`, obtaining `SmoothTest.Holds μ (1/c)²`. No need for Cauchy–Schwarz, Fubini, or improper integrals.
5. **Variance lower bound.** The support slope k at the median `log ρ` is given to `ρ s ≤ c·e^{k(s−m)}`; and the chord lower/upper bound/
   The exponential integral (`ExpIntegral`) combination, combined with the symbol of `k` and the position of x relative to m in four cases yields `ρ ≤ c + k(F − 1/2)`.
   Let `φ(u) = (u−1/2)/c − k(u−1/2)²/(2c²)`, `Ψ(x) = φ(F x) − (x − m)`, `Ψ' = ρ(c − kδ)/c² − 1 ≤ 0`
   (`r(c − kδ) ≤ c²` when `0 ≤ r ≤ c + kδ`), FTC gives `Ψ ≤ 0` (x ≥ m), `Ψ ≥ 0` (x ≤ m), hence
   `φ(F)(F−1/2) ≤ (x−m)(F−1/2)` on Ω; uniformly pushed forward to `∫φ(F)(F−1/2) dμ = 1/(12c)`; `∫(F−1/2) dμ = 0` the
   `x − E` replace `x − m`; `ab ≤ c a²/2 + b²/(2c)` and `∫(F−1/2)² = 1/12` to `Var ≥ 1/(12c²)`.
6. **Assembly.** `(1/c)² = 12·(1/(12c²)) ≤ 12·Var`, `Holds.mono`; `smoothTest_constant_eq_localSlope` and
   `constant_le` gives `Intrinsic.constant ν ≤ ofReal (12 Var)`; `ofReal_variance` gives the extended variance form.

Pit: The section variable of `theorem` is included only by statement (e.g., `continuous_cdf` requires `include d in`); `HasDerivAt.mul`
Different from the instance path of `^2`, `simpa`/`convert` fails while `exact` succeeds; if the `a b` parameter of `Continuous.intervalIntegrable` is written outside the parentheses, it will be treated as a parameter of the outer function; `if_pos ⟨_, _⟩` requires `And.intro`; the `Directed` family of `set` uses `if … then … else ∅` with ℚ as the indicator to avoid subtype issues involving `max`; assumptions in the form of `Set.mem_Ioi`/`mem_Iic` require prior `have : x < s := hsx` before they can be used by `linarith`; `positivity` does not recognize `variance` as non-negative; `ENNReal.ofReal_eq_coe_nnreal` replaces `ofReal` with `NNReal` via forced conversion to apply `constant_le`.

## Metadata Synchronization

- ledger adds `thm:one-dimensional-logconcave-poincare` (proved / lean, `kind: lemma` according to warehouse inheritance rules), nineteen
  proved node; `check_blueprint.CERTIFICATES` added mapping; lakefile `Solutions` root added certificate module; root aggregation
  `FunctionalInequalities.lean` import `KLS.LogConcave.Line.Poincare` (transitive import `Probability/Line/*` and `Line/*`).
- Blueprint theorem block anchors sixteen statements and certificates, statements and proofs marked `leanok`; the route sidecar's claim is changed from `imported` to `proved`,
  Add Lean proof and retain Bobkov's published citation as source.
- tasks.json: Change node to `available`, register seven new modules, `LocalSlope/Basic.lean`, and the hash of libraries and Mathlib dependencies;
  After adding two lemmas to `LocalSlope/Basic.lean`, refresh the three existing evidence hashes that reference it.
- Current guide: HANDOFF (new section, nineteen counting, certificate table, conditional fiber branching with "one-dimensional input" text, next-stage list), README,
  `verification.md`, `solutions/README.md`, `formalization/README.md`, `blueprint/README.md`, `KLS/README.md`,
  `KLS/LogConcave/README.md` (`Line/` five lines and dependency declarations), `Poincare/README.md`, `naming.md` (`Probability.Line.cdf`,
  `KLS.LineDensity` and 12·Var naming), root module document highlights. statement golden, `STATEMENT_CHECKS` unchanged.

## Evidence Boundary

The default `lake build` passes (3369 jobs), with certificates guarded by standard axioms of thirteen library-level declarations. The final verification receipt is generated by `python3 research/verify.py` after this record and all guide edits, with its source code SHA recorded within the receipt itself, not written back to this file.
Local kernel replay trusts third-party compiled imports; no isolated rebuilds, remote CI, commit, or push performed; fork between local and remote branches is left for user handling.

## Note: Differences from the original coefficients 4 and literature verification (2026-09-10, added on the same day)

The user points out that the original text of the conditional fiber bridge writes the coefficient 4; the current certification for one-dimensional input is 12; thus, what can be assembled next is
`D_{μ,ρ}(f) ≤ 12∫|∇f|² dμ`, `Var_μ(f) ≤ C·D_{μ,ρ}(f) ⟹ C_P(μ) ≤ 12C`: the sufficiency of the route pair with respect to KLS is preserved, the value 4 is not reproduced.
On the same day, the literature verification result for the coefficient 4 is:

- Bobkov 1999 (Ann. Probab. 27, p. 1915) Corollary 4.3 gives `1/(12 Var) ≤ λ₁ ≤ 1/Var`, and explicitly writes
  "We do not know, however, if the constant on the left is optimal"; the two bounds in Proposition 4.1
  `1/√(3 Var) ≤ Is ≤ √2/√Var` are attained in the uniform law and the bilateral exponential law.
- The arXiv 2018 version (2.25) and the GAFA revised version (2.13) of Cattiaux–Guillin are both `Var_ν(f) ≤ 4 Var_ν(x) ν(|∇f|²)`,
  noting "credited to Kannan, Lovász and Simonovits, mentioned in [Alonso-Gutiérrez–Bastero] p.11",
  and the wording regarding the one-dimensional application is identical in both versions: "it seems that we may replace 12 by 4".
  The original location of KLS 1995 remains inaccessible, consistent with the review record 2026-09-05 stating "primary KLS 1995 location … not verified".
- The exponential law `e^{-x}` (`C_P = 4`, `Var = 1`) shows that any κ < 4 fails: 4 is a lower bound.
- A local proof path cannot reach 4: the Hardy step `C_P ≤ 1/ρ(m)²` achieves equality in the exponential law, the variance step `Var ≥ 1/(12ρ(m)²)` achieves equality in the uniform law,
  and the extremal laws of the product of these two steps differ; the Cheeger path is similarly limited by the uniform law (`h·σ = 2/√12 < 1`).
  A possible path is the Muckenhoupt theorem `C_P ≤ 4B` (`B = sup_x μ(Ioi x)∫_m^x ρ⁻¹` and its mirror) combined with the log-concave law `B ≤ Var`;
  the latter holds numerically in examples such as exponential, uniform, Gauss, Laplace, truncated exponential, and exponential plus uniform (truncated at 2π for the exponential law 0.88 with respect to 0.926),
  but no proof is available, and no such proof is found in the literature.
- The CMH exact values (line, product, Dirichlet distribution) belong to the moment mapping Stein kernel constants;
  the CMH(μ) and W₂ definitions are not yet available in the repository (marked as missing in `thm:cmh-recovery-affine-poincare-bound`),
  and are incomparable to the results in this node and existing Gaussian results.

Conclusion: The coefficient 4 is currently an unverified claim in the literature, not a formalizable theorem input; this node remains 12, with the Blueprint's historical origin passage unchanged.

### Addendum II: Verification of the Alonso-Gutiérrez–Bastero Book (2026-09-10, added on the same day)

The user provided the full PDF of Alonso-Gutiérrez–Bastero (LNM 2131, 2015). Verification results:

- p.11 (beginning of Section 1.4) states in the original text: "Kannan, Lovász and Simonovits [37] proved that
  `Var_μ f ≤ 4 inf_{x₀∈ℝⁿ} E_μ|x − x₀|² E_μ|∇f|²` for any locally Lipschitz function f in L²(μ)",
  which is a general statement in dimension n, citing only KLS 1995, and the book contains no proof.
- The actual KLS result proved in the book is Theorem 1.13 (Section 1.6.1, using localization): the Cheeger-type inequality
  `μ⁺(A) ≥ (C / inf_{x₀} E|x − x₀|) min{μ(A), μ(Aᶜ)}`, with constant C being an unspecified absolute constant.
- The one-dimensional case in the book is Theorem 1.5 (Section 1.4.2, along Bobkov): `1/(3 Var) ≤ Is(μ)² ≤ 2/Var`,
  `Is(μ) = 2 e^{−W(a)}` (a being the median), and `1/(12 Var) ≤ λ₁(μ) ≤ 1/Var`—exactly the constant 12 certified in this node.

Conclusion: This book cannot serve as a proof source for the one-dimensional coefficient 4; the only possible original source for 4 remains KLS 1995 in this paper, pending acquisition for verification.
This node remains 12.
