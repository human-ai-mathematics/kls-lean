# Independent review of the 2026-10-03 overnight statements

Date: 2026-10-03. Reviewer: gpt-5.6-luna, given for each item the pinned paper statement and
standing assumptions from `literature.json`, the module docstring and the Lean declaration. The
review is advisory; the recorded relations are Claude's and are listed with each item.

## Summary

| Item | Recorded | Review | Disposition |
| --- | --- | --- | --- |
| De Ponti–Mondino Lemma 3.2 | same | faithful | — |
| De Ponti–Mondino Lemma 3.3 | same | stronger | Lean proves strict decrease; the map note already records that this implies the paper's "decreasing". Kept `same`. |
| Bobkov Lemma 3.1 | same | faithful | — |
| E. Milman Lemma 4.1 | same | partial | Only the documented degenerate case `f = 0`, `1 − ε < 0`, where the paper's literal statement is false and Lean's real infimum gives `0`. Kept `same` with the note; owner decision listed. |
| Lee–Vempala Lemma 42 | same | faithful | — |
| Guédon–Milman Lemma A.2 | same | faithful | — |
| Bobkov Proposition 4.1 | partial | partial | — |
| Klartag–Lehec 2025 Lemma 4.7 | stronger | stronger | — |
| Guédon–Milman Lemma 2.2 | same | faithful | — |

## Reviewer output

## DePontiMondino2021 Lemma 3.2

Recorded relation: `same`

VERDICT: faithful

- The hypotheses `0 < T` and `0 < x` match the positive parameter and domain in Lemma 3.2.
- The conclusion exactly states \(f_1(x)\ge 1/\sqrt T\), with the same constant.
- `buserRatioPos` faithfully encodes \(\sqrt{x}/\arctan(\sqrt{e^{Tx}-1})\).
- Real-valued division and square roots are appropriate here because both \(T\) and \(x\) are strictly positive; no degenerate \(T=0\) or \(x=0\) case is being asserted.
- No RCD, measure, infimum, ENNReal, or essential-supremum assumptions are relevant to this auxiliary one-variable lemma.
- The separately stated strict monotonicity theorem is stronger than the paper’s non-strict “increasing” wording, but this lower-bound declaration itself is not stronger or weaker.

## DePontiMondino2021 Lemma 3.3

Recorded relation: `same`

VERDICT: stronger

- The paper’s Lemma 3.3 states that, for fixed \(T>0\),  
  \[
  f_2(x)=\frac{\sqrt{x}}{\log(e^{Tx}+\sqrt{e^{2Tx}-1})}
  \]
  is decreasing on \((0,\infty)\).
- `buserRatioNeg T` is exactly this real-valued function, with the same constants and exponent \(2Tx\).
- `hT : 0 < T` matches the paper’s positivity hypothesis on \(T\); no RCD or measure-theoretic assumptions are relevant to this elementary lemma.
- `StrictAntiOn ... (Ioi 0)` gives strict decrease for all \(0<x<y\), hence implies the paper’s non-strict “decreasing” conclusion.
- The domain is the open positive half-line, so the degenerate endpoint \(x=0\) is neither asserted nor needed.
- No infimum, `ENNReal`, essential supremum, or other convention is involved here; the statement is purely about real functions.

## Bobkov1999 Lemma 3.1 (Borell)

Recorded relation: `same`

VERDICT: faithful

- The quantifiers match: a log-concave probability measure, a symmetric convex measurable set \(B\) with \(\theta=\mu(B)>1/2\), and every real \(t\ge 1\).
- `hsymm : ∀ x ∈ B, -x ∈ B` is equivalent to symmetry about the origin.
- The conclusion has exactly the paper’s bound, with `((μ : Measure E) B).toReal` representing \(\mu(B)\) and `t • B` representing \(tB\).
- The exponent `((t - 1) / 2)` and factor `((1 - θ) / θ)` are correct; no apparent constant or denominator mismatch occurs.
- The added `MeasurableSet B` is appropriate: the paper’s \(\mu(B)\) presupposes measurability (and the module documentation explicitly records this issue).
- Assuming the ambient typeclass hypotheses impose finite-dimensional real normed-space structure, the scope agrees with the stated Borell formulation.
- Using `ENNReal.toReal` is harmless here because \(\mu\) is a probability measure and \(B\) is measurable, so its measure is finite.
- No extra nondegeneracy assumption is needed: \(\theta>1/2\) rules out the degenerate cases relevant to the formula.

## Milman2009 Lemma 4.1

Recorded relation: `same`

VERDICT: partial

- For nondegenerate \(f\), the hypotheses and constants faithfully encode Milman’s statement: \(D>0\), \(0<\theta<1\), finite \(L^1\)-norm, and \(\|f\|_2\le D\|f\|_1\).
- The ENNReal formulation of the norm inequality is equivalent here; together with finite \(L^1\)-norm it supplies the required \(L^2\) integrability.
- The conclusion has the correct \(\varepsilon=(1-\theta)^2/D^2\), threshold \(\theta\|f\|_1\), and quantile direction.
- Measurability and the probability-measure assumption are standard formal encodings of the paper’s measurable probability-space setting, not substantive extra restrictions.
- For nonzero \(L^1\)-norm, the hypotheses force \(D\ge 1\), so \(1-\varepsilon\) lies in the intended quantile range \((0,1)\).
- In the degenerate case \(f=0\), the Lean `lowerQuantile` uses real `sInf` and returns \(0\) for an empty or unbounded-below defining set.
- The paper’s literal quantile is instead \(-\infty\) when \(1-\varepsilon<0\); hence the paper’s displayed inequality is not literally represented in that exceptional case, while the Lean conclusion remains trivially true.
- Thus the formalization is faithful modulo the explicitly documented real-infimum convention, but not fully equivalent to the paper’s quantile statement in that degenerate case.

## LeeVempala2024 Lemma 42 (Eldan)

Recorded relation: `same`

VERDICT: faithful

- The Lean theorem quantifies over a finite-dimensional real matrix `A`, a symmetric real matrix `Δ`, and real exponents `α, β ≥ 0`, matching Lemma 42.
- `A.PosDef` is the standard real positive-definiteness assumption and includes the required symmetry/Hermitian property.
- `Δ.IsSymm` faithfully encodes that `Δ` is symmetric.
- `cfc (fun x => x ^ α) A` is the continuous-functional-calculus interpretation of the spectral power \(A^\alpha\); for positive-definite `A`, this agrees with the paper’s real matrix power.
- The conclusion has exactly the paper’s inequality:
  \[
  \operatorname{Tr}(A^\alpha\Delta A^\beta\Delta)
  \leq
  \operatorname{Tr}(A^{\alpha+\beta}\Delta^2).
  \]
- The exponents are universally quantified through implicit `{α β : ℝ}` together with `hα` and `hβ`; no exponent restriction is missing or added.
- The finite index type permits the harmless degenerate zero-dimensional case, where the statement is vacuous; this does not materially change faithfulness.
- No constants, measure-theoretic conventions, or stochastic-localization hypotheses are relevant to this deterministic lemma.

## GuedonMilman2011 Lemma A.2

Recorded relation: `same`

VERDICT: faithful

- The hypotheses match the paper: `ε > 0`, `ε ≤ ∫_{(0,∞)} ρ`, and `∫_{(0,∞)} ρ ≤ 1 − ε`.
- `Ioi 0` is the standard Lebesgue-measure encoding of the integral over \((0,\infty)\); the endpoint \(0\) is immaterial.
- The surrounding `LineDensity` assumptions encode that `ρ` is a log-concave probability density, so no substantive hypothesis from the paper is missing.
- The conclusion is the same inequality, expressed in `ENNReal`:  
  `ENNReal.ofReal ε * eLpNorm ρ ⊤ volume ≤ ENNReal.ofReal (ρ 0)`.
- `eLpNorm ρ ⊤ volume` correctly represents the essential supremum \(\|\rho\|_\infty\), and `ofReal` embeds the real quantities into `ENNReal`.
- Nonnegativity of a density makes the `ofReal` formulation equivalent to \(\rho(0)\ge ε\|\rho\|_\infty\); there is no problematic degenerate or sign case.
- The intermediate almost-everywhere bound is appropriate because the essential supremum is used, while the theorem retains the pointwise value at \(0\), as in the paper’s representative.

## Bobkov1999 Proposition 4.1

Recorded relation: `partial`

VERDICT: partial

- The theorem formalizes only the lower bound, encoded as  
  `Is(μ)⁻¹ ^ 2 ≤ 3 * Var(μ)`, equivalent to `1/(3 Var μ) ≤ Is(μ)^2` in the nondegenerate finite-valued setting.
- It does not formalize Proposition 4.1 in full: the upper bound `Is(μ)^2 ≤ 2 / Var μ` and the equality cases are absent.
- The constant `3` and the variance normalization agree with the paper.
- `Is(μ)` is represented by the ENNReal Minkowski Cheeger constant, and variance by extended variance; this is a standard encoding, with ENNReal inversion handling zero and infinite values.
- The theorem is stated for log-concave laws with a density in the displayed context, while the documentation says the surrounding `LogConcave` result also covers Dirac laws. Including Dirac laws is an extension rather than a discrepancy, provided the theorem’s actual hypotheses indeed permit them.
- For nondegenerate absolutely continuous log-concave probability measures on `ℝ`, the conclusion matches the paper’s lower bound.
- Thus, relative to the cited proposition, the formalization is weaker/incomplete, not stronger: it records only one of the proposition’s inequalities and none of its equality characterizations.

## KlartagLehecThin2025 Lemma 4.7

Recorded relation: `stronger`

VERDICT: stronger

- The Lean theorem matches the paper’s hypotheses and conclusion under standard encoding: indices use `Finset.range k`, and integrals are interval integrals from `0` to `t`.
- `hμc` and `hℓc` express continuity on `[0,∞)`, while `hℓ0` expresses nonnegativity of the `λᵢ`.
- `hℓ` correctly encodes the pointwise ordering `ℓ₀(t) ≥ ⋯ ≥ ℓₙ₋₁(t)`; its quantifiers are harmlessly broader because `i ≤ j < n` implies `i < n`.
- The majorization hypothesis is quantified over every `t ≥ 0` and every `k ≤ n`, exactly as required, and the conclusion has the same quantifiers.
- The factor `2` and the exponential `exp (2 ∫ λᵢ)` agree with the paper.
- The Lean statement omits the paper’s assumption that the `μᵢ` are nonnegative. The supplied proof does not use that assumption, so this is a genuine strengthening rather than a mismatch.
- No ENNReal, infimum, essential-supremum, degeneracy, or other measure-theoretic convention is relevant to this elementary lemma.

## GuedonMilman2011 Lemma 2.2 (Grunbaum)

Recorded relation: `same`

VERDICT: faithful

- The Lean theorem quantifies over a probability measure on `ℝ`, with `LogConcave μ`, nonempty interior of the support, and mean zero; this is the standard measure-theoretic encoding of a log-concave density with barycenter at the origin.
- `hi : (interior μ.support).Nonempty` rules out lower-dimensional or degenerate log-concave laws and supplies the “support has nonempty interior” condition implicit in the paper’s density hypothesis.
- The conclusion uses `μ.real (Ici 0)`, which is exactly `P(X ≥ 0)`, and the bounds `exp (-1) = 1/e` and `1 - exp (-1)`.
- The proof establishes positivity on both open half-lines and applies the one-sided estimate plus reflection; this correctly handles the possible distinction between `Ioi`, `Iio`, and `Ici`.
- No paper parameters or universal constants are relevant to this lemma, so none are missing.
- The hypotheses are not materially stronger than “has a log-concave density”: for a probability measure on the line, log-concavity together with full-dimensional support is the corresponding standard formulation.
- The use of `ENNReal.toReal` is harmless here because probability measures are finite; it represents ordinary real probabilities rather than changing the assertion.

