# Finite Poincaré tensorization: semantic review and acceptance

**Date:** 2026-09-03 (Asia/Shanghai).

**Issue:** [#7](https://github.com/human-ai-mathematics/kls-lean/issues/7), a native
sub-issue of #1.

**Node:** `lem:poincare-finite-tensorization`.

**Starting commit:** `4801ca958778ae02cc0d81fc7ec805a4e96a894c` on `main`.

## Human ratification and chronology

The user supplied the completed library proofs through the separately recorded proof stage,
then requested several semantic and structural reviews. Following those reviews, the user said
“I think it is ready; make one final check that the semantics align, then we can move to the next step”. The final two
independent read-only reviews passed. The accompanying
[freeze record](../decisions/2026-09-03-finite-tensorization-freeze.md) records this approval
of the current 45-declaration surface, exact ledger claim, encodings, and specialization checks.
No earlier freeze is asserted or backdated. The previous draft, implementation, migration, and
deduplication records retain their historical states.

Acceptance adds the sole named `Solutions.LemPoincareFiniteTensorization.certificate`, directly
composing the already reviewed library. It does not alter any reusable mathematical definition,
statement, or proof. The approved state is recorded as `frozen` / `null` before the proof gates;
the final ledger becomes `proved` / `lean` only after those gates pass.

## Source correspondence and scope

The actual pinned manuscript source was re-read at
[`modules/02-results-toolkit.tex`, lines 59–68](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L59-L68).
Its Theorem 3.4 states the product Poincaré optimal-constant identity. Its accompanying LSI and
conditional-decomposition claims are outside this certificate.

BGL (2014), §4.3, Proposition 4.3.1, printed pp. 185–187, supplies the binary upper-bound
correspondence ([text](https://www.hse.ru/data/2016/11/24/1113029204/bok%253A978-3-319-00227-9.pdf#page=201)).
The finite upper bound iterates the already accepted `Holds.prod`. Coordinate test lifts give
the reverse bounds independently. BGL's Markov-triple/Dirichlet-domain framework does not by
itself identify the repository's test class with that domain for arbitrary Borel measures.

The local class remains globally smooth real-valued L² functions with integrable squared
canonical Hilbert gradient, using `Var(f) ≤ C ∫ ‖gradient f‖²`. Finite fixed constants use
`NNReal` and its real cast; optimal constants stay in `ENNReal`. Hilbert carriers, dependent
families, empty and zero-dimensional cases, and infinite constants are explicit local
specifications. No second moment or density is needed. This is the finite-product ingredient
of the upstream `prop:products`, not its separate one-dimensional log-concave bound,
Cheeger–Poincaré comparison, or full KLS conclusion.

## Certificate and complete interface coverage

The certificate in `solutions/LemPoincareFiniteTensorization.lean` has three independent
universally quantified blocks. Data for one block do not become extra assumptions of another.

| Ledger conclusion | Machine-checked coverage |
| --- | --- |
| Binary fixed recovery, each optimal lower bound, maximum equality | First certificate block; `Holds.of_prod_left/right`, `constant_left/right_le_prod`, `constant_prod_eq` |
| Finite fixed supremum bound and fixed coordinate recovery | Second block; `Holds.pi`, `Holds.of_pi` |
| Coordinate optimal lower bounds, finite upper bound, indexed-supremum equality | Second block; `constant_le_pi`, `constant_pi_le`, `constant_pi_eq` |
| Empty fixed/optimal zero, singleton recovery, all-subsingleton zero, infinite factor | Second block; `holds_pi_empty`, `constant_pi_empty/unique/of_subsingleton/eq_top_of_factor` |
| General subsingleton Hilbert probability has fixed and optimal zero | Third block; `holds_zero_of_subsingleton`, `constant_eq_zero_of_subsingleton` |
| Projection and linear-isometry admissibility, L², variance, energy, `Holds`, and optimal constants | Proved `Transport` declarations, all named in the same entry point's 45 public-interface checks |
| Dependent Hilbert law, coordinate projection, reindexing and Option split, with norm/measure compatibility | Proved `FiniteProduct/Geometry` declarations and the same complete public-interface checks |
| Arbitrary Euclidean dimensions, empty/singleton/mixed-zero/all-zero cases | Eight fully quantified typed application families and six concrete boundary applications in the same default-build entry point |

There is one named certificate for this node. The supporting public statements are checked and
audited directly, without recreating a `Project/` layer or additional Euclidean wrappers. The
45 public-interface checks and all 14 application checks are retained unchanged from the
approved candidate. The aggregate library now exports the accepted binary reverse and finite
tensorization modules as well as the earlier proved modules.

## Final mathematical review

Two independent reviews covered Transport/finite geometry and Basic/binary reverse/finite
tensorization. No semantic defect requiring a mathematical edit was found.

1. `MeasurePreserving q ρ μ` means `ρ.map q = μ`; tests pull back as `f ∘ q`. The chain rule
   uses the Hilbert adjoint `q.adjoint`. Its isometry property preserves gradient energy exactly.
   General pushforward integration is used, without adding injectivity of `q`.
2. L² and energy identities retain their `MemLp` or `Admissible` hypotheses. The inherited
   binary upper-bound proof still uses a.e. admissible sections and does not differentiate an
   unverified marginal integral or strengthen an a.e. statement to every section.
3. Both binary factors are explicitly probabilities. Probability of their product alone would
   not normalize them individually, so the reverse/equality statements retain this premise.
4. `PiLp 2` and `WithLp 2` carry the square-sum Hilbert norm. Reindexing maps coordinate `j`
   to `e j`; the Option split consistently uses `(none, tail)` and reconciles Mathlib's opposite
   measurable-equivalence order using the swap map.
5. The finite proof includes the empty family, whose product carrier is a singleton. The
   `NNReal` finite supremum and `ENNReal` indexed supremum then both equal zero. Singleton and
   zero-dimensional cases specialize without positive-dimension hypotheses.
6. The optimal upper bound chooses finite valid factor constants below a hypothetical larger
   product constant and contradicts the finite supremum bound. It never converts `⊤` to a real
   constant and never assumes an attained infimum. This does not claim that a finite optimal
   constant is invalid: for the present finite-energy test class, validity at a finite optimal
   constant and existence of an extremizing test function are distinct questions.

## Preservation of accepted work

The six pre-existing reusable mathematical modules were compared against the starting commit
after stripping comments, whitespace and changed import paths. Their Lean definitions,
statements and proofs are unchanged. In particular, the original `Basic` semantic contract,
linear-test/covariance implementation and accepted binary upper-bound proof are preserved.
Both earlier ledger node objects remain byte-for-byte equal as JSON data to the baseline.

The directory moves and removal of redundant `Project/` forwarding declarations were already
requested and reviewed in the
[deduplication record](2026-09-03-certificate-deduplication.md). Both retained old solution
certificate types and the two explicitly frozen binary public types are preserved. Historical
wrapper names are not reintroduced solely to reproduce an old audit count.

## Publication gates

Follow the user's existing direct-`main` workflow. In addition to the local checks below,
publication requires a clean checkout of the delivered commit with fresh project artifacts;
only the pinned third-party dependency cache may be reused. GitHub Actions must then succeed
for that exact published commit. The final commit SHA, clean-checkout result, frozen-contract
comparison, and Actions URL are attached to
[Issue #7](https://github.com/human-ai-mathematics/kls-lean/issues/7) when those gates
finish. The issue checklist is completed only after publication validation, not from an earlier
CI result.

## Local machine-verification results

The complete default build succeeded with **2956 jobs and no warnings**. The ledger checker
passed after promotion with **1 ledger, 3 proved nodes, 0 errors**, traversing the finite
certificate's complete local import closure. All **24 Python regression tests** passed.
No checker, test, toolchain, dependency pin, or CI-workflow exemption was introduced.

The three required commands were:

```bash
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization && lake build
```

`#print axioms` was run on every one of the 45 approved public declarations, all three named
solution certificates, and the two frozen binary upper-bound declarations: **50 declarations**
in total. Their dependencies are subsets of `[propext, Classical.choice, Quot.sound]`; each of
the three certificates depends on exactly those three axioms. There is no `sorryAx` or extra
project axiom. The static certificate/import guard also passes for all three proved nodes.

Fresh type output reproduced the approved files byte for byte. SHA-256 results:

```text
45 public declaration types: 1dbb986f5764f752adb516ea108ff771cd6058021ade292da727b451f541ce66
2 frozen binary types:       75e576722a02a1c49588534389331ed1f493fec233ee21756e348c23f8424d0a
2 retained old certificates: 81c99ab13552a477214158f5fb6cdf45b090e66ed77d425258fd0a6cb6a6dbee
finite ledger statement:    61ff1d1a7e1258d7cc3e68dae5ebc8111fefb9ac4d4baab1e10b797c948366ab
new certificate type:       1812c2be5407a9588fbc42a43c819617d7db8bc753899ecd10e2b066716bba76
```

The ledger statement hash excludes an extra newline; type hashes include the final newline.
For the 45-declaration and certificate outputs, set `pp.universes true` and `format.width 100`
then use `#check @...`. The two frozen binary types retain their original default printing
options. All 14 typed application expressions match the approved historical source after
ignoring comment changes and whitespace. Both previous ledger node objects match the baseline.

The unique new certificate's complete elaborated type is:

```text
Solutions.LemPoincareFiniteTensorization.certificate.{u_1, u_2, u_3, u_4,
  u_5} : (∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} ℝ E]
    [inst_2 : CompleteSpace.{u_1} E] [inst_3 : MeasurableSpace.{u_1} E] [BorelSpace.{u_1} E]
    [SecondCountableTopology.{u_1} E] [inst_6 : NormedAddCommGroup.{u_2} F] [inst_7 : InnerProductSpace.{0, u_2} ℝ F]
    [inst_8 : CompleteSpace.{u_2} F] [inst_9 : MeasurableSpace.{u_2} F] [BorelSpace.{u_2} F]
    [SecondCountableTopology.{u_2} F] (μ : MeasureTheory.Measure.{u_1} E) (ν : MeasureTheory.Measure.{u_2} F)
    [MeasureTheory.IsProbabilityMeasure.{u_1} μ] [MeasureTheory.IsProbabilityMeasure.{u_2} ν],
    (∀ ⦃C : ℝ⦄,
        FunctionalInequalities.Poincare.Holds.{max u_2 u_1} (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν)
            C →
          FunctionalInequalities.Poincare.Holds.{u_1} μ C ∧ FunctionalInequalities.Poincare.Holds.{u_2} ν C) ∧
      LE.le.{0} (FunctionalInequalities.Poincare.constant.{u_1} μ)
          (FunctionalInequalities.Poincare.constant.{max u_2 u_1}
            (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν)) ∧
        LE.le.{0} (FunctionalInequalities.Poincare.constant.{u_2} ν)
            (FunctionalInequalities.Poincare.constant.{max u_2 u_1}
              (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν)) ∧
          Eq.{1}
            (FunctionalInequalities.Poincare.constant.{max u_2 u_1}
              (FunctionalInequalities.Poincare.prodMeasure.{u_1, u_2} μ ν))
            (max.{0} (FunctionalInequalities.Poincare.constant.{u_1} μ)
              (FunctionalInequalities.Poincare.constant.{u_2} ν))) ∧
  (∀ {ι : Type u_3} [inst : Fintype.{u_3} ι] {E : ι → Type u_4} [inst_1 : (i : ι) → NormedAddCommGroup.{u_4} (E i)]
      [inst_2 : (i : ι) → InnerProductSpace.{0, u_4} ℝ (E i)] [inst_3 : ∀ (i : ι), CompleteSpace.{u_4} (E i)]
      [inst_4 : (i : ι) → MeasurableSpace.{u_4} (E i)] [∀ (i : ι), BorelSpace.{u_4} (E i)]
      [∀ (i : ι), SecondCountableTopology.{u_4} (E i)] (μ : (i : ι) → MeasureTheory.Measure.{u_4} (E i))
      [∀ (i : ι), MeasureTheory.IsProbabilityMeasure.{u_4} (μ i)],
      (∀ (C : ι → NNReal),
          (∀ (i : ι), FunctionalInequalities.Poincare.Holds.{u_4} (μ i) ↑(C i)) →
            FunctionalInequalities.Poincare.Holds.{max u_4 u_3} (FunctionalInequalities.Poincare.piMeasure.{u_3, u_4} μ)
              ↑(Finset.sup.{0, u_3} Finset.univ.{u_3} C)) ∧
        (∀ ⦃C : ℝ⦄ (i : ι),
            FunctionalInequalities.Poincare.Holds.{max u_4 u_3} (FunctionalInequalities.Poincare.piMeasure.{u_3, u_4} μ)
                C →
              FunctionalInequalities.Poincare.Holds.{u_4} (μ i) C) ∧
          (∀ (i : ι),
              LE.le.{0} (FunctionalInequalities.Poincare.constant.{u_4} (μ i))
                (FunctionalInequalities.Poincare.constant.{max u_4 u_3}
                  (FunctionalInequalities.Poincare.piMeasure.{u_3, u_4} μ))) ∧
            LE.le.{0}
                (FunctionalInequalities.Poincare.constant.{max u_4 u_3}
                  (FunctionalInequalities.Poincare.piMeasure.{u_3, u_4} μ))
                (⨆ i, FunctionalInequalities.Poincare.constant.{u_4} (μ i)) ∧
              Eq.{1}
                  (FunctionalInequalities.Poincare.constant.{max u_4 u_3}
                    (FunctionalInequalities.Poincare.piMeasure.{u_3, u_4} μ))
                  (⨆ i, FunctionalInequalities.Poincare.constant.{u_4} (μ i)) ∧
                (IsEmpty.{u_3 + 1} ι →
                    FunctionalInequalities.Poincare.Holds.{max u_4 u_3}
                        (FunctionalInequalities.Poincare.piMeasure.{u_3, u_4} μ) 0 ∧
                      Eq.{1}
                        (FunctionalInequalities.Poincare.constant.{max u_4 u_3}
                          (FunctionalInequalities.Poincare.piMeasure.{u_3, u_4} μ))
                        0) ∧
                  (∀ (h : Unique.{u_3 + 1} ι),
                      Eq.{1}
                        (FunctionalInequalities.Poincare.constant.{max u_4 u_3}
                          (FunctionalInequalities.Poincare.piMeasure.{u_3, u_4} μ))
                        (FunctionalInequalities.Poincare.constant.{u_4} (μ default.{u_3 + 1}))) ∧
                    ((∀ (i : ι), Subsingleton.{u_4 + 1} (E i)) →
                        Eq.{1}
                          (FunctionalInequalities.Poincare.constant.{max u_4 u_3}
                            (FunctionalInequalities.Poincare.piMeasure.{u_3, u_4} μ))
                          0) ∧
                      ∀ (i : ι),
                        Eq.{1} (FunctionalInequalities.Poincare.constant.{u_4} (μ i)) Top.top.{0} →
                          Eq.{1}
                            (FunctionalInequalities.Poincare.constant.{max u_4 u_3}
                              (FunctionalInequalities.Poincare.piMeasure.{u_3, u_4} μ))
                            Top.top.{0}) ∧
    ∀ {E : Type u_5} [inst : NormedAddCommGroup.{u_5} E] [inst_1 : InnerProductSpace.{0, u_5} ℝ E]
      [inst_2 : CompleteSpace.{u_5} E] [inst_3 : MeasurableSpace.{u_5} E] [BorelSpace.{u_5} E]
      [SecondCountableTopology.{u_5} E] (μ : MeasureTheory.Measure.{u_5} E) [MeasureTheory.IsProbabilityMeasure.{u_5} μ]
      [Subsingleton.{u_5 + 1} E],
      FunctionalInequalities.Poincare.Holds.{u_5} μ 0 ∧ Eq.{1} (FunctionalInequalities.Poincare.constant.{u_5} μ) 0
```
