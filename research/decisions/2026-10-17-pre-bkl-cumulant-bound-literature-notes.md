# BKL literature values before the Theorem 4.1 certificate

Date: 2026-10-17. This record preserves, as historical data, the exact `research/progress/literature.json` values that the integration of `thm:bkl-cumulant-bound` ([integration record](2026-10-17-bkl-cumulant-bound-integration.md)) supersedes: the BKL2026 T41 relation, uses, declarations and note, `remaining`, the priority-1 target and next step, and the T11/T41 proof-path steps. Their claims are unchanged here and describe the state before the stage-3 integration.

```json
{
 "T41": {
  "relation": "partial",
  "uses": [
   "L42",
   "L43",
   "L51",
   "L52",
   "E95"
  ],
  "declarations": [
   {
    "name": "FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_one_one",
    "source": "formalization/FunctionalInequalities/KLS/BKL/SecondCumulant.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.LogConcave.cumulant_two_eq_inner_of_isotropic",
    "source": "formalization/FunctionalInequalities/KLS/BKL/SecondCumulant.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.envelope",
    "source": "formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.absorption_le_envelope",
    "source": "formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.sum_choose_mul_sqrt_envelope",
    "source": "formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean"
   },
   {
    "name": "FunctionalInequalities.Analysis.Tensor.sum_sq_contract_le",
    "source": "formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean"
   },
   {
    "name": "FunctionalInequalities.Analysis.BakryEmery.gradient_logLaplace_zero_of_compact",
    "source": "formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean"
   },
   {
    "name": "FunctionalInequalities.Analysis.BakryEmery.fderiv_centeredGradient_logLaplace_zero_of_compact",
    "source": "formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean"
   },
   {
    "name": "FunctionalInequalities.Analysis.BakryEmery.inner_cumulantVector_single_ringInverse_cumulantVector",
    "source": "formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean"
   },
   {
    "name": "FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_of_compact",
    "source": "formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Leibniz.lean"
   },
   {
    "name": "FunctionalInequalities.Analysis.BakryEmery.directional_centeredGradient_logLaplace_zero_of_compact",
    "source": "formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Leibniz.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.LogConcave.cond",
    "source": "formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound.compact",
    "source": "formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.compactPosterior_cumulant_bound",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/Standardization.lean"
   },
   {
    "name": "FunctionalInequalities.Analysis.BakryEmery.tendsto_cumulant_cond_closedBall",
    "source": "formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_of_compact",
    "source": "formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.sqrt_lowerDrift_energy_le",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/Energy.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_one",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffInduction.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.cumulantBoundCompact_of_cutoffEnergyClaim",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffInduction.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_all",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffInduction.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.theorem41Compact_of_letwinCompact",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffInduction.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integral_lyapunov_le",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/LyapunovMoment.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.measure_norm_gt_le",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/LyapunovMoment.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integral_energy_le_weighted_add",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffInduction.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.exists_weighted_energy_le",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffInduction.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.theorem41Compact",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Theorem41.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.theorem41",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Theorem41.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.lemma51Bound",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Theorem41.lean"
   },
   {
    "name": "FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_succ",
    "source": "formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffInductionStep.lean"
   }
  ],
  "note": "Proof along Eldan stochastic localization for compactly supported μ, then approximation; no local stochastic calculus. The cumulant tensors κ_m are defined locally (Analysis/BakryEmery/Cumulant/Basic.lean, cumulant). Supporting arithmetic of Section 6 formalized (envelope b_m, (105)–(106), absorption, contraction (101)–(102)); the source theorem is not claimed unconditionally (see the cutoff-induction sentences at the end). Base case m = 2 (Codex route bundle Local-Second-Cumulant, independently accepted 2026-10-08): CumulantBound 1 1, i.e. R₂ = Id for every isotropic log-concave law in every dimension, is proved unconditionally from one exponential radius (κ₂ = centered second moment = covariance pairing; Parseval). This covers only the m = 2 base; the all-order bound comes from the cutoff induction below. CGF jets at zero (p. 20 before (74); Luna gpt-5.6-luna units CGF1-M/CGF1-C with recorded closing repairs, independently accepted 2026-10-08): ∇Λ(0) = ∫x dμ and D(∇Λ − ∇Λ(0))(0) = Cov μ for compactly supported laws (Analysis/BakryEmery/Cumulant/Local.lean section GradientJets; cumulantVector records the Riesz vector of the last cumulant slot). The higher jets Dʳ(∇Λ − ∇Λ(0))(0)[h] = cumulantVector μ h (⟪·,w⟫ = κ_{r+1}(h,w), all r ≥ 1; Luna units CGF1-J2a/J2b + the J2c v2 assembly, independently accepted 2026-10-08; generic supports in Analysis/IteratedDerivative/GradientJet.lean) are formalized. The singleton terms of (74), ⟪κ₂(w,·), A⁻¹κ_{k+1}(h,·)⟫ = κ_{k+1}(h,w) for invertible covariance A (Luna unit D74s, independently accepted 2026-10-08; Cumulant/Local.lean section SingletonAllocation), are formalized. The raw (74) expansion at a fixed compactly supported law, D^m⟨v,Mv⟩(0)[h] = Σ_{∅≠J⊊[m]} ⟨κ_{|J|+1}(h_J,·), Mκ_{m−|J|+1}(h_{Jᶜ},·)⟩ for ANY continuous linear M (Luna units D74a1/D74a2r/D74a3r + the D74A assembly, independently accepted 2026-10-09; Analysis/BakryEmery/Cumulant/Leibniz.lean), is formalized; its grouping 2m κ_m + 2 L_m with (72) for M = A⁻¹ is formalized (E7274); the stochastic differential (73) (Lemma 4.3) remains unformalized. Cutoff induction (Claude-controller batches 8–9, 2026-10-13; KLS/BKL/Localization/CutoffInduction.lean): the cutoff form of (95) is the predicate CutoffEnergyClaim K d; its base case m = 2 (cutoffEnergyClaim_one, K ≥ 5) and the passage claim ⇒ CumulantBoundCompact d (b_{d+1}) (cumulantBoundCompact_of_cutoffEnergyClaim) are proved; the Section 6 pointwise bound behind (99)–(104) is sqrt_lowerDrift_energy_le (Localization/Energy.lean). theorem41Compact_of_letwinCompact proves, by strong induction with K = 153, ∃ K ≥ 1, ∀ d ≥ 2, CumulantBoundCompact d ((d!)² K^d), but only under three explicit hypotheses: LetwinCompactBound (Letwin Theorem 1.2 for compactly supported laws, open at that date), the induction step hstep (the order-m cutoff claim from the lower orders, i.e. Lemma 5.2 in cutoff form, Lemma 5.1 and the Lyapunov moment bound, open at that date), and hbound (dischargeable by cumulantBoundCompact_of_cutoffEnergyClaim). Batch 10 (2026-10-13) adds two inputs of the then-open induction step: the Lyapunov moment bound E 𝒱(p_t) ≤ 𝒱(p_0)e^{Kt} with its Markov tail along the cutoff process, from a generator bound taken as a hypothesis (IsEldanCutoff.integral_lyapunov_le, IsEldanCutoff.measure_norm_gt_le; Localization/LyapunovMoment.lean), and the boundary-term split and mean-value choice of the horizon (IsEldanCutoff.integral_energy_le_weighted_add, IsEldanCutoff.exists_weighted_energy_le; CutoffInduction.lean). Batch 13 (2026-10-13): the induction step is proved (cutoffEnergyClaim_succ, Localization/CutoffInductionStep.lean, with Lemma 5.1 as the named hypothesis Lemma51Bound, discharged by lemma51Bound), and theorem41 (KLS/BKL/Theorem41.lean) proves ∃ K ≥ 1, ∀ d ≥ 2, CumulantBound d ((d!)² K^d) for every isotropic log-concave law in every dimension, with K = 153 on the compact stage, assuming only LetwinCompactBound (Letwin Theorem 1.2 for compactly supported isotropic log-concave laws). Standard axioms only. Current (2026-10-17): LetwinCompactBound is proved (letwinCompactBound, certified as thm:letwin-compact-quadratic-bound), and the finite-horizon cutoff form of (95) for every order is certified with it (lem:bkl-cutoff-energy, item E95). The stage-2 source audit accepted the cutoff route: process existence, Dynkin's identity, Q positive semidefinite, the coefficients, generators and energies, the Lyapunov bound and the induction. The composition of theorem41 with letwinCompactBound is not added: the source-form statement of Theorem 4.1, including m = 2, awaits the stage-3 review, so the entry stays partial."
 },
 "remaining": "Theorem 3.1 is formalized in the source form and certified (thm:bkl-taylor-criterion) by the operator route: the iterates are built in the generator domain D(A) and an approximate first eigenfunction at λ = 1/C_P replaces (19); (32)–(36), (47), Lemmas 3.2–3.4, 3.3 for every q, 3.8, 3.9 and Corollaries 3.5, 3.7 hold for these iterates (reviewed stronger forms), with the weak Hessian, the curvature form of (16), (48) and Lemma 3.6 on D(A). Lemma 2.2 is formalized in the source form, Lemma 3.6 also on 𝒜; the regular-law adapter derives the probability normalization, Gaussian tails and all exponential moments from (12). Lemma 2.1 (operator-domain inverse, componentwise lift; temperate functions in the generator domain), (15) and (16) on 𝒜, steps of Proposition 7.1 (the Laplace noise, the joint law with its density (109), log-concavity under (110), exponential moment and local smoothness, isotropy from (108), (111)–(112) for the chosen N, the Hilbert–Schmidt step, the β → ∞ limit, the affine-orthogonal decomposition, continuity of T_d on L², the linear-function step and (113) for the smooth normalized class; (113) on the affine-orthogonal class and the assembly (107) — Proposition 7.1 in the source form, conditional on its hypothesis) and the Section 6 envelope arithmetic and Lemma 4.2 conditionally on the Letwin bound have restricted or conditional counterparts. The deterministic spatial step of the proof of Lemma 4.3 ((74) grouped as 2m κ_m + 2 L_m with (72)) is formalized. Equation (95) is certified in finite-horizon cutoff form (lem:bkl-cutoff-energy), from the actual compact constant-8 theorem; Theorem 4.1 is proved conditionally on LetwinCompactBound, which is now proved, but the composition is not added before the stage-3 source-form review. Theorems 1.1 and 4.1 in the source form, Lemmas 4.3 (the stochastic differential (73)), 5.1 and 5.2 along the uncut process (their generator and cutoff forms are formalized), Lemma 2.1 on 𝒜 (smooth representatives and the pointwise equation), the existence of a first eigenfunction (19), the uncut Eldan process (strong solution, uniqueness, non-explosion) and the noncompact Letwin theorem are not formalized. Theorem 3.1 is a certified supporting theorem; the paper is not covered until Theorem 1.1 is.",
 "priority_target": "BKL Theorem 1.1 through source-form Theorem 3.1 and Proposition 7.1 certificates, and Theorem 4.1. Theorem 4.1 and KLS.Conjecture are proved conditionally on LetwinCompactBound; that compact input is now proved and certified (thm:letwin-compact-quadratic-bound), the cutoff stochastic-localization route is source-reviewed and (95) is certified in cutoff form, but the source-form Theorem 4.1 awaits the stage-3 review, so unconditional BKL and dimension-free KLS are not claimed and remain open. Proposition 7.1 retains its cumulant hypothesis.",
 "priority_next_step": "Roadmap stage 1 (Letwin constant 8) is complete in its compact form (2026-10-16): letwinCompactBound : LetwinCompactBound, n > 0, every compactly supported isotropic log-concave law, every self-adjoint form including singular and indefinite ones, exact constant 8, certified in source form and sealed by an independently accepted full local report (8e21b1f6, snapshot d90cec22). Active (2026-10-17): roadmap stage 2, stochastic localization in BKL arXiv:2610.05474v1 Sections 4-6. The existing cutoff-only route (KLS/BKL/Localization/, Probability/Diffusion/) is source-reviewed, and the finite-horizon cutoff form of (95) for every order is a registered supporting certificate (lem:bkl-cutoff-energy), formalized and registered; milestone acceptance requires the exact full local receipt and its independent acceptance, recorded in the Goal control checkpoint (scope chosen by the owner on 2026-10-17: the BKL-sufficient cutoff route, then stage 3); the uncut Eldan process (strong solution, uniqueness, non-explosion) and the literal stochastic identities (68)-(73) are not proved. Then a source-faithful review of BKL Theorem 4.1; only then the KLS composition through conjecture_of_letwinCompact (not added; KLS.kls stays open). The noncompact Letwin Theorem 1.2 is not on the BKL critical path. One candidate at a time with the existing API loop (idle), coordinated by the current Codex chat and the original Claude session; no commit, push or publication is authorized. BKL remains primary.",
 "proof_path": {
  "T11": {
   "paper": "BKL2026",
   "item": "T11",
   "entries": [
    "FunctionalInequalities.KLS.BKL.Localization.conjecture_of_letwinCompact"
   ],
   "boundary": "The conditional KLS assembly is proved under LetwinCompactBound, which is now proved in its compact form (Letwin T12). The composition is not added: Theorem 4.1 is certified in the source form (thm:bkl-cumulant-bound), and the KLS composition (stage 4) follows the stage-3 acceptance. Unconditional Theorem 1.1 and KLS remain open."
  },
  "T41": {
   "paper": "BKL2026",
   "item": "T41",
   "entries": [
    "Solutions.ThmBklCumulantBound.certificate",
    "FunctionalInequalities.KLS.BKL.Localization.theorem41"
   ],
   "boundary": "Source-form Theorem 4.1 certified: one universal K ≥ 1 (153), every m ≥ 2, every dimension and every isotropic log-concave law, through the cutoff route and the compact-to-general passage; theorem41 stays the conditional interface. The uncut process and the literal (68)–(73) are not formalized.",
   "certificate": "thm:bkl-cumulant-bound"
  }
 }
}
```
