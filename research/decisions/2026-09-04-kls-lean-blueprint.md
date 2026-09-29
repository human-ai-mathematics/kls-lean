# KLS Lean Blueprint architecture

**Decision date:** 2026-09-04 (Asia/Shanghai).

**User authorization:** after reviewing the canonical Basic direction and the need for a
Blueprint, the repository user instructed: “All right, submit Basic first, then create a Blueprint”.

**Repository baseline:** `509c42970dba78b9ffa31b793087a8fd1af57889` on `main`.  The
canonical Basic was published separately at `ea82a666e796fd4707c3ef9381a4885039ed6609`; the sharp
one-dimensional Gaussian certificate was published at the baseline commit.  This record does not
rewrite either accepted proof contract.

## Decision

The repository adopts a Lean Blueprint under `formalization/blueprint/`, inside the actual Lake
package.  The Blueprint is executable documentation, not a replacement for Lean or
`research/a-series/ledger.yaml` as the certification authority.

Its first version has six responsibilities:

1. state the classical KLS target and pin route provenance;
2. expose the canonical `L²`, extended-energy and Poincaré optimization Basic;
3. show the proved smooth-gradient and intrinsic-affine closed-quadratic chain;
4. name Dirichlet, `2 Ch`, raw/core, legacy/canonical and ambient/intrinsic bridges without
   treating them as premises already proved;
5. keep the four accepted legacy smooth-test certificates in a distinct graph layer;
6. record Eldan localization, moment-map spectral, moment-map CMH and conditional-fiber frame as
   alternative long routes to KLS.

The writing rule follows the repository's Formech-inspired convention: small public interfaces,
ordinary mathematical definitions, explicit non-claims, and copyable build commands.

## Status and dependency rules

- `\lean{...}` identifies a declaration; it does not by itself certify a proof.
- `\leanok` is used only when the mapped local statement or proof is accepted by Lean.
- Upstream `checked_by: agent` provenance never becomes `\leanok`.
- `\notready` means the public mathematical API is not frozen; an exact theorem with an open
  proof simply lacks `\leanok`.
- TeX `\uses{...}` always means logical AND.

The four KLS routes are therefore composed by the minimal JSON-subset sidecar
`route-composition.yaml`: the KLS target is `any_of`, and each route's real exit package is
`all_of`.  In particular, the conditional-fiber route uses the existing pair
`q:conditional-fiber-frame` plus `lem:conditional-fiber-form`; it does not invent a nonexistent
`thm:conditional-fiber-frame-suffices`.  The Eldan live gate uses the weaker tight-prefix package,
not the older all-cut assumption.

## Source and tooling pins

- Long-route mathematics: `kls-exploration@8185e46ffb040e04fea076953e5bcaeb4157d71a`.
- Blueprint builder: `leanblueprint==0.0.20`.
- Declaration checker: `PatrickMassot/checkdecls@3d425859e73fcfbef85b9638c2a91708ef4a22d4`.

Because the Lake package is nested under `formalization/`, local and CI builds use
`formalization/blueprint/build.py` and explicit working directories instead of assuming a
root-level Lake project.  The offline repository checker validates labels, `\uses` edges, route
composition and the four ledger-backed certificate mappings.

## Non-claims

This decision does not assert a Dirichlet witness, an identification with Cheeger energy, a raw
test/core theorem, equality of legacy and canonical constants, or any completed KLS route.  It
also does not deploy a public Blueprint website; CI only verifies and uploads temporary PDF and
web artifacts.
