# Weak Hessian bridge and R0 regular-class assembly

Date: 2026-10-13. The owner authorized the minimum R0 resume: reuse independently accepted N11e helpers, independently accept the weak Hessian bridge, and only then assemble R0. Other large tasks remain paused; no commit, push, tag, publication or remote CI is authorized.

## Target and mathematical scope

The pinned consumer is Letwin arXiv:2607.24164v1 Lemma 2.2 in the weak regular-class route toward Theorem 2.5 and compact Theorem 1.2 with constant 8. Source Lemma 2.2 is globally smooth with everywhere positive definiteness and a gradient diffeomorphism. The result here is its supporting C1,1/a.e. package, not the full source theorem.

The original R0 statement is retained: n > 0; compact convex K with nonempty interior; globally smooth W with W - (kappa/2)||.||^2 convex, kappa > 0; and the isotropic probability law mu = 1_K exp(-W) dx. The conclusion supplies a finite convex Lipschitz u, integral exp(-u) = 1, the actual gradient pushforward, C1 regularity, 16/kappa-Lipschitz gradient, and a.e. positive definite coordinate Hessian H, log det H = -u + W(grad u), and (16/kappa) Id - H positive semidefinite. No hypotheses, normalization, dimensional restriction or coefficient were changed.

## Placement and reuse

The bridge extends the existing coordinate Hessian owner, `Probability/Stein/HessianKernel.lean`. Its two public declarations identify `Matrix.toEuclideanLin (hessianMatrix u x)` with the derivative of the gradient and prove Hermitian symmetry, assuming only u in C1 and gradient differentiability at x, in every finite dimension including zero. The original N11e source prefix and its private helpers are unchanged. The new bridge reuses those pointwise coordinate and symmetry helpers; it does not require a weak third-derivative tensor or claim such a tensor exists.

R0 is a regular-class specialization in `KLS/CEK/MomentRegularity.lean`, next to the bounded moment-map producer. The original frozen `Analysis.exists_regular_moment_potential` name is retained. Imports point toward the existing convex-analysis, CEK producer and Hessian owners. No generic module imports the application, no names are migrated and no compatibility aliases are added.

The proof reuses the existing strong-API R0 round18 assembly. Codex replaces its unjustified C1-to-C2 adapters with the independently accepted pointwise bridge and corrects matrix representation/coercion, inner-product algebra, a missing constructor terminator and local-instance style. The old candidate and all failure diagnostics are unchanged. No new API invocation, weaker model, provider substitution or restart of an old loop occurred.

## Independent acceptance before assembly

The bridge was accepted before the R0 module was created. The current complete production scope was rebuilt into a fresh filtered compiled view. Strict source and frozen/consumer clients passed; six axiom reports use only propext, Classical.choice and Quot.sound; the affected Hessian module was replayed in the kernel. The client verifies both the supplied gradient derivative and the actual upper matrix-order bound used by R0.

The R0 source then passed strict compilation. Its entire declaration header is byte-identical to the original frozen source. Separate environments for the original frozen template and production declaration print identical full pp.all types; the elaborated type hash is 3225770193 with no universe parameters. The template containing the original placeholder is interface evidence only, not a proof. The canonical exact-statement and derivative-norm consumers passed strict compilation with only the three standard axioms. The new regularity module passed kernel replay.

The actual proof at Rademacher points constructs the second-order expansion using the unique subgradient of a C1 convex function. The existing viscosity/Alexandrov theorem gives the positive-definite Hessian and determinant identity. The derivative operator-norm bound gives the 16/kappa matrix cap. Global C2 is never inferred from C1.

## Snapshot evidence and remaining scope

Evidence is under `build/reviews/2026-10-13-r0-weak-hessian-bridge/`: `BASELINE.json`, placement plans, the two independent acceptance receipts, full interface comparison, strict logs and module replay logs. `COMPLETION.json`, when available, records the final full verifier receipt and snapshot checks. Earlier receipts cover only their recorded snapshots; the previous closeout receipt does not certify this new tree.

English HANDOFF, the paper mapping, Blueprint and generated progress views are synchronized. The already integrated bounded CEK producer is registered as an explicit prerequisite, with no new proof or general-source certificate. The support graph is separate from the four active exploratory KLS implication routes. All paper/main-theorem statuses and the 30 certificates retain their scopes.

R0 is now assembled, but generator symmetry, H1 testing/localization, the weak chain rule and Hessian evolution, the integrated PSD trace estimate, weak Brascamp-Lieb, Stein/H^-1 transport and spectral constant-8 assembly remain open. No other large task is resumed by this record. Letwin Theorems 2.5/1.2, unconditional BKL and dimension-free KLS remain open. The dated six-task failure analysis remains an accurate historical closeout record; this new result supersedes only R0's current unassembled status.
