# Migration-comment history

Archived on 2026-10-18 from the frozen baseline source of the migration-comment cleanup. The 43 module
comments below are the complete original blocks, verbatim, with their source paths, original start lines,
old source-file SHA-256 and original comment SHA-256. They are historical records of module-layout
migration notes and preservation boilerplate; they assign no proof, certificate or paper-coverage status.
The live source keeps every byte outside comments, each mathematical title, source locator and
proof explanation. Two comments were corrected rather than trimmed: the `KLS/BKL/Reduction.lean`
locator of the closed producers now names `KLS/BKL/Poincare.lean`, and `KLS/Letwin/CompactBound.lean`
states its compact-only scope without process wording. Verification receipts keep certifying their own
recorded snapshots; this maintenance is not a new Lean run.

## formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/MomentBound.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/MomentBound.lean)

Original comment at line 4; old source SHA-256 `3f2fc44ecf6aad91bc66bb79f775a68d97f8688a9d9eefbc28e585f5b2f69a53`; original comment SHA-256 `5f26332bd472831a3c41caa464911204f1b36e3d16c21a6539a4440f3ba56f0c`.

````lean
/-!
# Cumulant norm bounds from moment bounds

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean)

Original comment at line 4; old source SHA-256 `cea62ee66ae06a950da0403104f08ecdfadb9296e6434ac4bac92dbd7f669078`; original comment SHA-256 `e0e1d2f7a7c33427441c3aab3aa29ffa579dfd74859b900dba1163b035b0bdc0`.

````lean
/-!
# Generic weak Hessian coordinates and pointwise identification

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean)

Original comment at line 3; old source SHA-256 `2d7b5c2573392a3ae475548a2b8e944a5d3377c61b81e80463f9bf8e84d34a36`; original comment SHA-256 `a0dedd9638102cdc07e618b4b6bc043d4d446089e073ed38d44a38e19ab25487`.

````lean
/-!
# Proximal points, Moreau derivatives and resolvent symmetry

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Matrix/Trace/Algebra.lean)

Original comment at line 10; old source SHA-256 `e4f2669e91aeee01bd499855a741844854dc59502a4a81ea1ffc2db7e681b871`; original comment SHA-256 `74d72a94d260f692da900b0de8436b7102e48b30242c39275e4892bf2d3a8145`.

````lean
/-!
# Finite real matrix trace algebra and the elementary trace-energy bound

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean)

Original comment at line 9; old source SHA-256 `e1f137376bda114c5d7d87e96186a74ca45a5128eca06496c0f8e8e445518acf`; original comment SHA-256 `541566d9b7144210b8705f844a98ed89b24ac336d7d2652a610c128d96a50858`.

````lean
/-!
# Spectral trace positivity, Jordan domination and tensor comparison

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/Analysis/Matrix/Trace/Power.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Matrix/Trace/Power.lean)

Original comment at line 8; old source SHA-256 `8774e28c6f9ebb5ea6136409fb8dfe010bd9f1943cd5085a13b97ed7542d907c`; original comment SHA-256 `4475b8df235cf8df03bf69bc5e68203b61048f9c7ef01d53862757f336812243`.

````lean
/-!
# Trace inequalities for real spectral powers

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/CumulantBound.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/CumulantBound.lean)

Original comment at line 4; old source SHA-256 `e60d4ce28e36b01331423f77922b7205efa63b9ab8486462e5838c6fe87c5482`; original comment SHA-256 `c19a226dfe868e6968cfb4a45ba65fb6760ff404e4e4a44c924a611c7e1c2c47`.

````lean
/-!
# BKL Theorem 4.1 and the cutoff (95), closed

The proved compact Letwin bound `LogConcave.Suspension.letwinCompactBound` discharges the explicit hypothesis of the shared
producers `cutoffEnergyClaim_of_letwinCompact` and `cumulantBound_of_letwinCompact` (`Theorem41.lean`), at `K = 153` for every
order `d + 1 ≥ 2`. These closed endpoints are consumed by the certificates of `lem:bkl-cutoff-energy` and
`thm:bkl-cumulant-bound` and by the final Poincaré assembly. The uncut Eldan process and the literal (68)–(73) are not
constructed. Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Bound.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Bound.lean)

Original comment at line 4; old source SHA-256 `7050e12974db27d817b08c3dfc56b68d91ef9e84af6228cb12be67dac63aef08`; original comment SHA-256 `aca07d5dbc19b313fc9d24d32c8d9970e4d5ca1597fac4359a4f14b0a0d79286`.

````lean
/-!
# A-priori cumulant bounds for isotropic log-concave laws

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Base.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Base.lean)

Original comment at line 11; old source SHA-256 `be02f77208ba5e71bdcc7e53eaff1ef8a18eee56157d7552ba7d6784bf592100`; original comment SHA-256 `989420bf40fa883b0970219e85f618d7c91831b47fa52205a71a487254b0cae8`.

````lean
/-!
# The second-order base case of the cutoff energy claim

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Basic.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Basic.lean)

Original comment at line 5; old source SHA-256 `82c0492c168aa09daf863226f8a0d19e54b0c9478f408276453a850a688e039c`; original comment SHA-256 `487a698136fcdf60627e553c170b61fc089b45937e15837c6bd7e53fd7e56af4`.

````lean
/-!
# The cutoff-weighted energy claim

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Boundary.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Boundary.lean)

Original comment at line 11; old source SHA-256 `d26bbf369c966e42bd9f745e8d1f4fa2e9ce3b4e8a408b23e4f7148b43e2b57c`; original comment SHA-256 `bccf0144e4f1efef52931de8f3deef0423b49e6d7d7810b2a269cf2632ba9f80`.

````lean
/-!
# Boundary control and horizon choice for cutoff energy

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Induction.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Induction.lean)

Original comment at line 4; old source SHA-256 `ecff1fdd221f8c65ebcf928d858bcbb7fc79c983a41fc4c1a598c2b6a38193cf`; original comment SHA-256 `eb5850f5d07c75bea0a12093ce52192bc87046332654164e6aae97518fd13ae1`.

````lean
/-!
# Strong induction for the compact cumulant theorem

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/ToCumulant.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/ToCumulant.lean)

Original comment at line 10; old source SHA-256 `64196bba118de2d9384956a0975b95ce5007b8dd4b513726ea915ff83c383228`; original comment SHA-256 `76e3f6a460fa79008f0c1f22c4ab4ffe4935621e388a0a354a7de11d564ab70f`.

````lean
/-!
# From cutoff energy claims to compact cumulant bounds

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Bound.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Bound.lean)

Original comment at line 8; old source SHA-256 `640fc4a36e3f9a40332ee4c2c3fbe44830ddd3a05d6c2a1b7ba289bc9733e21e`; original comment SHA-256 `2c94fb537d08f1a50c6ed2e191119fb813889eadb0ffc619a05bb07f556b3aea`.

````lean
/-!
# A-priori posterior energy bounds

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Integral.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Integral.lean)

Original comment at line 11; old source SHA-256 `697debf21357a320020baef0776b12976da0b392e3b015e0f28bb8fc3f453087`; original comment SHA-256 `dc5e0492a1b63772f9edee9c804191914c5988d738361d596c0def3369003cd6`.

````lean
/-!
# Integrated energy bound along the cutoff Eldan process

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Regularity.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Regularity.lean)

Original comment at line 9; old source SHA-256 `bdaf1c619a79845f0b9a3fce3bb5f102bc59845eb6efe5635a0f8e71d2ebfee1`; original comment SHA-256 `08f814025069d7925e1153308145c52231487d020ee832158234c81174374c4b`.

````lean
/-!
# Regularity of posterior cumulant energies and their generators

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean)

Original comment at line 11; old source SHA-256 `c719062a04faa77f55d4162dd0e2e811647a653099eea504de1c6fa87b487750`; original comment SHA-256 `b88fae677c20a960ca50d06c4eaf57e1a708abb58dc202f5378482a8eb74343e`.

````lean
/-!
# The Lyapunov function and its exact generator calculus

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Bound.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Bound.lean)

Original comment at line 14; old source SHA-256 `d4c6a01daa9ab0998e8fee23174fe7b990e00110a80c90f622f74ef1cdb4f140`; original comment SHA-256 `c587038805e3e39fcc748db6933c61bbc274329b55eff4fddcf2a90a867bfc5d`.

````lean
/-!
# Generator bounds for the localization Lyapunov function

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Integral.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Integral.lean)

Original comment at line 4; old source SHA-256 `66ce3eedc01098b2137e9310eb2a7954b20d7b897b991465963aec5f57b33238`; original comment SHA-256 `38f34b49c98628b04024677c85d687be23324c3a10596215dc7683427c15a60b`.

````lean
/-!
# Integrals of bounded functionals of cutoff Eldan processes

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Poincare.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Poincare.lean)

Original comment at line 4; old source SHA-256 `4d8c4cd812d3cec75e75abb269bb66e66a9ab4bbf38d9a5a8a91741f15388a11`; original comment SHA-256 `0cda689eb53081e461154f2ccac708e57471923ee777ab9783cf7aa5d4e4eb3e`.

````lean
/-!
# BKL Theorem 1.1 and the closed KLS producers

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Posterior/Covariance.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Posterior/Covariance.lean)

Original comment at line 15; old source SHA-256 `15c56104a163ed0ca55ba538c4ce18e1d5c6ca11a250857f2ed6ffa56a844c0e`; original comment SHA-256 `dc5f17c54aaeae5b95aafd54907e18f9e1b575727f7a1513d220078e60f61659`.

````lean
/-!
# Covariance algebra and radius bounds for compact posteriors

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Posterior/Moments.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Posterior/Moments.lean)

Original comment at line 17; old source SHA-256 `fe0d295e59491396577d1e6d2781dedb886d0a7b5cdbdff7b619808521b9efb0`; original comment SHA-256 `9379118e68c1d9049d9bcc24255f20a0e489f408f3ecd4042401fd91c3ad96c7`.

````lean
/-!
# Sixth moments of standardized compact posteriors

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Posterior/Noise.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Posterior/Noise.lean)

Original comment at line 16; old source SHA-256 `5b6e750aadfd696f193700d7aceb87590425136240b6ddfd1e64339f104d5bbf`; original comment SHA-256 `0928daea5dda60d2cfb637a17e90e7e0cb4a354eb5a277b202a022aa0b5c3476`.

````lean
/-!
# Noise estimates and coordinate identities for compact posteriors

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Posterior/Regularity.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Posterior/Regularity.lean)

Original comment at line 16; old source SHA-256 `0b85e81cc7a752377e45ee3ba80bbd44869856add6e7a461a0a705a252e39a5c`; original comment SHA-256 `e968326ef1124825db97d85644fa149a22f7b8372f74216633e031e272d9abaa`.

````lean
/-!
# Joint regularity of compact-posterior localization coefficients

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Posterior/Standardization.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Posterior/Standardization.lean)

Original comment at line 16; old source SHA-256 `b7b05688baf06179036c1e58ed583b87a642b949813f6e78fa228e6fffbd09eb`; original comment SHA-256 `20e6f113210db702998ac06f416eba019a8c44d1710d31ff1b070e5135a3377b`.

````lean
/-!
# Canonical covariance standardization of compact posteriors

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Reduction.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Reduction.lean)

Original comment at line 6; old source SHA-256 `fe521768bca8b914cbd7e80a2e16b112691be47578dceadd5e5df2b06c627de9`; original comment SHA-256 `823589fa12f1fb69354a5fc34e9ffb9dede78969eed5a50bfd61e441ec78c362`.

````lean
/-!
# BKL p. 30: reduction of Theorem 1.1 to Theorems 3.1, 4.1 and Proposition 7.1

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 30 (proof of Theorem 1.1). Given the universal cumulant
bound of Theorem 4.1, `R^ν_{d+1} ≤ (d!)² K^d · Id` for all `d ≥ 2` (`CumulantBound d ((d!)² K^d)`,
`K ≥ 1`), Proposition 7.1 gives `|T_d f|² ≤ 2K^d ‖f‖² ≤ (2K)^d ‖f‖²` for every isotropic regular law,
isotropy gives `|T_1 f| ≤ ‖f‖`, and Theorem 3.1 with `R = √(2K)` yields `C_P(μ) ≤ 2 C_{3.1} K`.
This module contains the reduction only; its hypothesis is not discharged here. The closed producers
are `BKL.Localization.theorem11` and `conjecture` (`KLS/BKL/Theorem41.lean`); Section 2's regular approximation is separate.
-/
````

## formalization/FunctionalInequalities/KLS/BKL/Theorem41.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Theorem41.lean)

Original comment at line 7; old source SHA-256 `0142189f4f75faa69b2137ec82fc2c1d46b023f80029ff85c0245b16d250b1e4`; original comment SHA-256 `140034dadbce59b878fed7684c7508e6f451397052ba448dd0fd78824ffd2e6f`.

````lean
/-!
# BKL Theorem 4.1: the universal cumulant bound

Module layout: research/decisions/2026-10-17-bkl-module-reorganization.md.
Existing declarations and their mathematical scope are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Cutoff.lean

[Current source](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Cutoff.lean)

Original comment at line 8; old source SHA-256 `d61600a73a2beefb25ce9b63c398c5f09f55657a93610b703428c79537b21e09`; original comment SHA-256 `32e99023afba715cdad6e33ab67e17138af2558d39ccd665b011363f5a6fbad2`.

````lean
/-!
# Regular-source height cutoffs and bounded weak cutoff testing

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Potential.lean

[Current source](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Potential.lean)

Original comment at line 11; old source SHA-256 `11d56724f8361597ec175b97b47ebb54cb13e2ea6d5f0d7089360ecdcceeb946`; original comment SHA-256 `15c62ad1072909f573f3d0462024db4cc8e6176badb2bf73ccca71e6602e24eb`.

````lean
/-!
# Actual regular-class C1 moment potentials

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/TraceStein.lean

[Current source](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/TraceStein.lean)

Original comment at line 19; old source SHA-256 `1a6064285161d2fc71f5aec1c53b116cd8397dd438d07050e7520c89ed97e5cd`; original comment SHA-256 `6179b13364598d084373577c2e86278d4ae5496a5d352a44853df1602a1e9593`.

````lean
/-!
# Trace and weak Stein estimates at one regular moment witness

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakDerivative.lean

[Current source](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakDerivative.lean)

Original comment at line 15; old source SHA-256 `f545b8b9c2378d5cad931c41a7aada546491dfc75d37af4f5265a5d764b722e4`; original comment SHA-256 `8752e2c6bba9a70db4c346033000415837552e78a0166af9fedf840021460654`.

````lean
/-!
# Regular-source weak tensors and first Monge–Ampere derivatives

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean

[Current source](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean)

Original comment at line 13; old source SHA-256 `fd9e790f3d85eda908a83a7ae985d0f7f2e8873945cf72727cace9b55873ea3c`; original comment SHA-256 `430376b1a685358b54cb666db337e4d6aaa6ccfdfec7ab7f066176f65ad2ec89`.

````lean
/-!
# Regular-source weak inverse, Hessian mean, evolution and testing

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Approximation.lean

[Current source](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Approximation.lean)

Original comment at line 4; old source SHA-256 `5d19e4e6a588b496fcdb5cda8593cf974718be0cc5fa15bbd7d15cc8b2c690cd`; original comment SHA-256 `d0052d7d033c900081610efd0590e6b32d4ce620b0eb4de791e65a8f938e8c7f`.

````lean
/-!
# Bounded-support reductions for globally Lipschitz approximations

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Basic.lean

[Current source](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Basic.lean)

Original comment at line 11; old source SHA-256 `f82d85f0a8665efd72bebff100359d051a7d1c4b7b8ba94b0c7e9e063486db20`; original comment SHA-256 `726b060cd9d28506cec2a5ef5a4542435ae4e435fba06c1e8b04b2b27340836a`.

````lean
/-!
# Metric BV tests, relaxation, recovery and elementary bounds

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Complement.lean

[Current source](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Complement.lean)

Original comment at line 3; old source SHA-256 `dca5f7aff4a8f82b47d17b7dda0fb3c4d329547a775c046f3ae6b5cfeed534a1`; original comment SHA-256 `017ac14b08cc5f04e4ea5cf132ce73c222f55b324167ef178397d73e32c7f005`.

````lean
/-!
# Metric BV complement symmetry for finite measures

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Counterexample.lean

[Current source](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Counterexample.lean)

Original comment at line 3; old source SHA-256 `46bff5e0004d9634b096debbd6152aff43764a7adaacf9fe49689371cbe17a4c`; original comment SHA-256 `29b92af38d08599d52c2ac2310cc3d6180746956abb90c42bba520982e746c18`.

````lean
/-!
# Infinite-volume counterexample to metric BV complement symmetry

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Finite.lean

[Current source](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Finite.lean)

Original comment at line 3; old source SHA-256 `a1ebc15e6aa42b31d2359c71ab1ad2f3e86f38587546a0828267a7d3132116d2`; original comment SHA-256 `94e4be0fc5470b358d955c2cac4a6fcd7845dcb5e84f02e7855f045cd7a90cf8`.

````lean
/-!
# Metric BV on finite and singleton metric spaces

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Scaling.lean

[Current source](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Scaling.lean)

Original comment at line 3; old source SHA-256 `ca4676fb651feeb2ccff389f5b814403161d1dee225c0064e0cb780f534614ed`; original comment SHA-256 `0ccdd64c81a175dfafbb94ced9e4e9896e35275e9d4450efd01456d0e3c384a6`.

````lean
/-!
# Metric BV measure scaling and probability normalization

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Transport.lean

[Current source](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/Transport.lean)

Original comment at line 5; old source SHA-256 `640d88eef97c35ff52db5d790b874f4d0c8c1357437af8acffec0f4b1c25711d`; original comment SHA-256 `994a6b47e426ed4bb2463b496ddcdb386f8a09b4ff1ff6668428b7f35eb3815c`.

````lean
/-!
# Metric BV subset restriction and closed-support laws

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/KLS/Letwin/CompactBound.lean

[Current source](../../formalization/FunctionalInequalities/KLS/Letwin/CompactBound.lean)

Original comment at line 6; old source SHA-256 `127c6856ff04db674661e9a08b1705d0b09fca9146874f6551ac59639b8ab162`; original comment SHA-256 `1946d8393b00dcec180f23053abf8a23de165771a7437cb3e8d6fab249b5f8c4`.

````lean
/-!
# The compact Letwin constant-eight bound

`KLS.LogConcave.Suspension.letwinCompactBound : LetwinCompactBound`: for every `n > 0`, every compactly supported isotropic
log-concave probability law on `EuclideanSpace ℝ (Fin n)` and every self-adjoint real operator (singular and indefinite included), the
variance of the quadratic form is at most `8` times its squared Hilbert–Schmidt norm. It follows from the regular-class bound through the
existing compact reduction `letwinCompactBound_of_regularClass`.

This is the exact compact counterpart of Letwin (arXiv:2607.24164v1), Theorem 1.2, as used by Bizeul–Klartag–Lehec
(arXiv:2610.05474v1), Lemma 4.2. It does not state the noncompact theorem and composes nothing further; `KLS.kls` is untouched.
-/
````

## formalization/FunctionalInequalities/Probability/Stein/HessianKernel.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Stein/HessianKernel.lean)

Original comment at line 10; old source SHA-256 `4a3914b6e99b9d70ff74c3c12e619a4b6c06887070d6d368d4746b63e32e496c`; original comment SHA-256 `f9edf0bdd88dfcedc8ee351391ada3bc9b6ed42c2273271d18663f9d2da3fa3e`.

````lean
/-!
# Hessian–Stein kernel, pushforward and inverse-map adapters

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/Probability/Stein/Kernel.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Stein/Kernel.lean)

Original comment at line 8; old source SHA-256 `4d08cd4d1cb07a6b97996c57b3238718f39b28490b0607dd346bcbd860c57785`; original comment SHA-256 `c82ab491e7ca4f690d28cf528c9d3704c338b8879fa06e85aea3d659b97df568`.

````lean
/-!
# Stein kernel object and compact-test identities

Existing statements, names and proof payloads are preserved.
-/
````

## formalization/FunctionalInequalities/Probability/Stein/SourceDualBound.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Stein/SourceDualBound.lean)

Original comment at line 6; old source SHA-256 `9b918bf53f9fb10273391197ba1d5717e2a73888f2f58498f40e477f2245a59c`; original comment SHA-256 `5ab52035450cdba0435cb8fa10a1310e671e22d2644f2d1f9daad9b6a33878a5`.

````lean
/-!
# Compact-test dual bound from a latent source identity

Existing statements, names and proof payloads are preserved.
-/
````
