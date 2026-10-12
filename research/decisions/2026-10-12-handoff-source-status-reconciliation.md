# Handoff and source-status reconciliation after the given-potential results

Date: 2026-10-12. Controller: Codex thread `01a12de4-2412-7082-ae33-15b1c3502420`. Integrator: the sole reviewed Claude
conversation, final AA–AE writer window (documentation only, before the final full verification).

The earlier current-state paragraphs below still stated that Brascamp–Lieb, the substitution of Lemma 2.4 and (2.10) remain
open without qualification. They were superseded by the AD integration (scalar Brascamp–Lieb, Letwin Lemma A.6, for a GIVEN
potential with positive definite Hessian: finite-energy `C²` and extended-energy `C^∞` forms) and the AE integration ((2.9)–
(2.10) and the nonnegative remainders for a GIVEN potential satisfying the Monge–Ampère relation). The corrected wording
states the actual boundary: the given-potential results are formalized; their application to the moment map of the source
law, the noncompact A.4/A.5 consumption of the trace, the tensor comparison, the source positive-semidefinite trace bound and
Letwin Theorems 2.5 and 1.2 remain open. No Lean source, statement, lemma-map relation, status, coverage or certificate changed.
Older historical records are not edited.

## Superseded text (verbatim)

The passages are quoted in code blocks, so their links are inert here; their claims are unchanged.

`HANDOFF.md` — Letwin Theorem 2.5 matrix support (2026-10-12:

```text
Letwin Theorem 2.5 matrix support (2026-10-12, working tree; verified for its own snapshot by the full local receipt `20261011T185855.461851Z`): the Jordan decomposition of every real symmetric matrix with derived positive semidefinite parts, mixed and energy trace positivity, and the pointwise domination `tr((P − N)H(P − N)H) ≤ tr(PHPH) + tr(NHNH)` without commutation, in `Analysis/Matrix/{Sign,Trace}.lean` (Blueprint `lem:letwin-symmetric-jordan`, audit `BKL/LetwinSymmetricJordanAudit.lean`, record [2026-10-12 symmetric Jordan integration](research/decisions/2026-10-12-letwin-symmetric-jordan-integration.md)). It is generic matrix algebra: the positive semidefinite integral bound, its measure extension, the moment map, Brascamp–Lieb and Letwin Theorem 2.5 itself remain open, and Letwin T25 stays partial.
```

`HANDOFF.md` — Letwin Theorem 2.5 extension step (2026-10-12:

```text
Letwin Theorem 2.5 extension step (2026-10-12, working tree; it needs its own matching full local receipt): `symmetric_trace_integral_extension` in the new `Analysis/Matrix/Integral.lean` derives, for any measure and any measurable positive semidefinite matrix field, the bound `∫ tr(BHBH) dν ≤ 2 tr(B²)` with its integrability for every symmetric `B` from the same bound for every positive semidefinite `A`, a named hypothesis (Blueprint `lem:letwin-symmetric-integral`, audit `BKL/LetwinSymmetricIntegralAudit.lean` with an actual two-point law). The positive semidefinite bound, the moment map, Brascamp–Lieb and Letwin Theorem 2.5 itself remain open; Letwin T25 stays partial.
```

`HANDOFF.md` — Letwin Lemma A.6 support (2026-10-12:

```text
Letwin Lemma A.6 support (2026-10-12, working tree; it needs its own matching full local receipt): in the new `KLS/LogConcave/HeatSemigroup/Range.lean`, the images of compactly supported smooth functions under the ordinary weighted diffusion operator are dense in the mean-zero classes of `L²(ν)` for a log-concave `ν = m.tilted(−U)` with `C¹` `U` (`centered_mem_closure_compactSmoothDiffusionImage`; Blueprint `lem:letwin-centered-range`; audit `BKL/LetwinCenteredRangeAudit.lean` with the actual Gaussian law). It is finite-energy Brascamp–Lieb infrastructure: Brascamp–Lieb itself, Lemma A.6, the moment map and Letwin Theorem 2.5 remain open; Letwin LA6 is partial.
```

`HANDOFF.md` — Further Letwin Lemma A.6 supports (2026-10-12:

```text
Further Letwin Lemma A.6 supports (2026-10-12, working tree; they need their own matching full local receipt): compactly supported coercivity of the ordinary weighted diffusion, `∫ ∇²U(∇u, ∇u) dμ ≤ ∫ (ℒu)² dμ` with both integrability conclusions (`compact_ordinary_diffusion_coercivity` in `Analysis/BakryEmery/Curvature.lean`), and the inverse-quadratic Young inequality for positive definite matrices (`inverse_quadratic_young` in `Analysis/Matrix/Positivity.lean`); Blueprint `lem:letwin-finite-energy-supports`, audit `BKL/LetwinFiniteEnergyAudit.lean`. They concern the ordinary weighted Laplacian, not the inverse-Hessian operator: Brascamp–Lieb itself and Lemma A.6 remain open.
```

`HANDOFF.md` — Letwin (2.8) for Theorem 2.5 (2026-10-12:

```text
Letwin (2.8) for Theorem 2.5 (2026-10-12, working tree; same receipt condition): in the new `Analysis/BakryEmery/HessianTrace.lean`, the pointwise identity `L tr(BHBH) = 2 tr(BHB·LH) + 2 Σ φ^{ab} tr(B∂_aH B∂_bH)` holds for smooth `φ`, any `V` and every constant real `B`, with no PSD, commutation or Monge–Ampère premise (`hessianInverseOperator_trace_stdHessianMatrix_sq`; Blueprint `lem:letwin-hessian-trace`; audit `BKL/LetwinHessianTraceAudit.lean` with the nonconstant quartic `x⁴/12 + x²/2`). The substitution of Lemma 2.4, (2.10), the tensor comparison and the trace bound remain open; Letwin T25 and LA6 stay partial.
```

`research/handoffs/2026-10-12-bkl-letwin-t25-goal.md` — Proof obligations:

```text
- The source Hessian bound, the mean-Hessian identity (Lemma 2.3) for the actual moment relation, the trace evolution
  (2.8)–(2.10) with its nonnegative terms, the noncompact integration (A.4/A.5 applied to the real trace test), the tensor
  comparison (2.12) for nonidentity `H`, and Brascamp–Lieb (A.6) for the actual potential.
```

`research/handoffs/2026-10-12-bkl-letwin-t25-goal.md` — Proof obligations:

```text
  (`Analysis/BakryEmery/HessianTrace.lean`); its Monge–Ampère substitution, (2.10) and the trace bound remain open.
```

`research/progress/literature.json` — E23:

```text
Formalized for an arbitrary real coefficient field A (symmetric at each point, no positivity) and drift b, on C² functions, in the standard orthonormal basis (Luna LET23-H/LET23-N, 2026-10-08; clients research/audits/BKL/NondivergenceAudit.lean: rank 0, and the cross-direction product ⟨e_i,·⟩⟨e_j,·⟩ exposing 2A_ij − b_i⟨e_j,x⟩ − b_j⟨e_i,x⟩). The source specialization A = (∇²φ)⁻¹, the Monge–Ampère/Brascamp–Lieb inputs and Theorem 2.5 are not formalized. The specialization A = (∇²φ)⁻¹, b = ∇V∘∇φ (hessianInverseOperator) and its Leibniz rule are now formalized for a given φ (MA-Inverse, 2026-10-08); Theorem 2.5 remains open.
```

`research/progress/literature.json` — L24:

```text
Proof: differentiate log det Hess phi = -phi + V(grad phi) twice (Jacobi's formula); positivity from convexity of V and a Hilbert-Schmidt Gram-matrix representation. Not formalized. Partial (Codex route bundle MA-Inverse, independently accepted 2026-10-08): the display (2.5) — derivative of the inverse Hessian ∂_k(∇²φ)⁻¹_ij = −Σ (∇²φ)⁻¹_ia ∂_kac φ (∇²φ)⁻¹_cj — in operator and coordinate forms for a given smooth φ with positive definite Hessian, and the derivative of the right-hand side −φ + V∘∇φ of the log-det equation (2.2) taken as a hypothesis, with V smooth only on an open neighbourhood of the gradient image. Jacobi's formula (Codex route bundle MA-Jacobi, independently accepted 2026-10-08) gives the left-hand side, hence the first derivative (2.4) of the equation; the second derivative (2.6) with the inverse-Hessian operator and the positive semidefiniteness of both right-hand matrices (V convex on the open K containing the gradient image; the Gram term weighted by (∇²φ)⁻¹ ⊗ (∇²φ)⁻¹) are formalized (bundle MA-Second-Derivative, independently accepted 2026-10-08). The local Lemma 2.4 identity is therefore proved for a GIVEN smooth φ with positive definite Hessian satisfying the zero-order equation (2.2); the upstream Lemma 2.2 (existence and regularity of the moment map, the zero-order equation itself) remains the open gap, as do Theorem 2.5, Brascamp–Lieb and Proposition 2.8.
```

`research/progress/literature.json` — T25:

```text
Proof: for B >= 0, apply L to Tr(B Hess phi B Hess phi), substitute Lemma 2.4, integrate using Lemma A.5 (c = 2), compare third-derivative terms pointwise ((b_i - b_j)^2 identity), and apply the Brascamp-Lieb inequality (Lemma A.6) to B^{1/2} Hess phi B^{1/2}, whose mean is B by Lemma 2.3; general B via |B|. Matrix inequalities: traces of products of PSD matrices, Hilbert-Schmidt Gram matrices. Equation (2.12) formalized as the finite symmetric-tensor identity for arbitrary real weights (⇑); the coordinate normalization, diagonalization and the identification with the inverse-Hessian contractions, and Theorem 2.5 itself, are not formalized. Support (Codex route bundle MA-Metric-IntegrationByParts, independently accepted 2026-10-08): the integration by parts (2.2) for the inverse-Hessian operator L on smooth tests with one compactly supported, for a GIVEN smooth φ with positive definite Hessian, ∫e^{−φ} = 1 and the zero-order MA equation with V smooth on an open neighbourhood of closure K ⊇ range ∇φ: coordinate divergence of (∇²φ)⁻¹, flux identity, density divergence form of L, ∫Lf dν = 0 and integrated symmetry on compact tests (Analysis/BakryEmery/MongeAmpere.lean section Divergence, IntegrationByParts/InverseHessian.lean). Brascamp–Lieb (A.6), the trace estimate itself and the moment map remain unformalized; the noncompact extension is LA4 and LA5 (for given cutoffs). Matrix support for the extension from PSD to all symmetric B (strong-API candidate, gpt-6-astra, accepted 2026-10-12): the Jordan decomposition B = P − N with derived PSD parts, PN = NP = 0 and tr B² = tr P² + tr N², nonnegative mixed and energy traces, and the pointwise domination tr((P−N)H(P−N)H) ≤ tr(PHPH) + tr(NHNH) for symmetric H without commutation, for every finite index type; the measure extension is formalized conditionally on the PSD bound (symmetric_trace_integral_extension: for any measure and any measurable PSD field H, the PSD bound for every PSD A gives the same bound, with derived integrability, for every symmetric B; strong-API candidate, gpt-6-astra, accepted 2026-10-12); the PSD integral bound itself, the moment map and Theorem 2.5 are not formalized. Pointwise trace identity (2.8) (strong-API candidate, gpt-6-astra, accepted 2026-10-12): for smooth phi, any V and every constant real matrix B, L tr(B H B H) = 2 tr(B H B (L H)) + 2 sum_ab phi^{ab} tr(B d_a H B d_b H) at every point, H the Hessian matrix in the standard orthonormal basis and L H entrywise, with no PSD, commutation or Monge-Ampere premise; the substitution of Lemma 2.4, (2.10), the tensor comparison and the trace bound are not formalized. (2.9) and (2.10) for a GIVEN potential (strong-API candidate, gpt-6-astra, accepted 2026-10-12): for smooth phi with positive definite Hessian satisfying the zero-order Monge-Ampere relation, with V smooth only on an open neighbourhood of closure K containing the gradient range, L H = -H + H Hess V(grad phi) H + G (G the inverse-Hessian third-derivative Gram matrix) and (2.10) for every constant real B; for K open, V convex on K and B positive semidefinite the three remainders are nonnegative, so L tr(BHBH) + 2 tr(BHBH) >= 0 pointwise. The integration of this pointwise condition (Lemmas A.4-A.5 for this trace function), the tensor comparison (2.12) with the mean Hessian, the source trace bound and the moment map of the source law are not formalized.
```

`research/progress/literature.json` — LA6:

```text
Proof: Brascamp-Lieb [14, Theorem 4.1] on the bounded convex sets {phi < R}, then monotone convergence. Partial: only a supporting step of the finite-energy argument is formalized: for a log-concave nu = m.tilted(-U) with C^1 U on a finite-dimensional space, the images -L f of compactly supported smooth f under the ordinary weighted diffusion operator are dense in the mean-zero classes of L^2(nu) (every centered g, arbitrary; strong-API candidate, gpt-6-astra, accepted 2026-10-12). Two further supports (strong-API candidate, gpt-6-astra, accepted 2026-10-12): compactly supported coercivity of the ordinary weighted diffusion (integral of Hess U(grad u, grad u) <= integral of (L u)^2 under m.tilted(-U), with both integrability conclusions, U of class C^2; the ordinary weighted Laplacian, not the inverse-Hessian operator) and the inverse-quadratic Young inequality 2 v.w <= v.H^{-1}v + w.Hw for positive definite H over any finite index type. The inequality itself is formalized for a GIVEN potential (strong-API candidate, gpt-6-astra, accepted 2026-10-12): for a log-concave nu = m.tilted(-U) with Hess U positive definite at every point (no uniform bound) and C^1 f in L^2(nu), Var f <= integral of <grad f, (Hess U)^{-1} grad f>, in a finite-energy form (U of class C^2, integrable energy) and an extended form with the right side possibly infinite (U smooth, no energy premise; bounded C^1 f included), in every dimension, with equality for the standard Gaussian law and f = id. Partial: the source potential phi is the moment map, whose existence, Euler-Lagrange identification, push-forward and regularity (Lemmas 2.1-2.2) are not formalized, so Lemma A.6 for the source law is not.
```
