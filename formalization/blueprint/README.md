# KLS Lean Blueprint

This Blueprint is the live dependency map for the canonical `L²`/energy foundation and the
remaining route to KLS. It is deliberately narrower than the upstream mathematical manuscript:
it records only interfaces that this repository intends to formalize, together with four audited
sufficient-route alternatives. The alternatives share analytic infrastructure; no logical or
probabilistic independence is asserted.

The graph has three status classes:

- `\lean{...}` plus statement and proof `\leanok`: the declaration and proof are certified by
  the local Lean build;
- an exact statement without `\leanok`: mathematically stated but not Lean-certified here;
- `\notready`: the theorem's public API or hypotheses are not frozen yet.

Upstream `checked_by: agent` metadata is provenance, never Lean certification. The legacy
smooth-test certificates are kept separate from the selected canonical closed-energy nodes until
the explicit relaxation/recovery bridge identifies their constants. That bridge does not require
raw-test/core agreement; raw/core is an optional stronger statement and is obstructed for general
singular measures.

The Blueprint keeps three constant levels visible:

- `C_P(μ; E)` is the energy-parametrized optimizer for an arbitrary extended `L²` energy;
- `C_P^can(μ)` selects the intrinsic-affine smooth-gradient relaxation used by this repository;
- `C_P^lit(μ)` is the locally Lipschitz constant used in the KLS literature.

Selection is a repository convention, not a proof of `E_can = 2 Ch`. Equality of the selected,
legacy, and literature constants is represented by named `\notready` proposal nodes whose proof
state is also open.

## Build

Create a Python environment and install the pinned web-builder dependency:

```bash
python3 -m venv /tmp/kls-blueprint-venv
/tmp/kls-blueprint-venv/bin/pip install -r formalization/blueprint/requirements.txt
```

Then, from the repository root:

```bash
python3 research/check_blueprint.py
(cd formalization && lake build)
/tmp/kls-blueprint-venv/bin/python formalization/blueprint/build.py all
```

The helper writes the PDF to `formalization/blueprint/print/print.pdf`, the website to
`formalization/blueprint/web/`, and the declaration list to
`formalization/blueprint/lean_decls`. It uses direct commands because the Lake package is nested
under `formalization/`.

`route-composition.yaml` is intentionally a JSON subset. TeX `\uses{...}` means logical AND;
the sidecar supplies the one required logical OR: any one of the four route alternatives may
discharge `conj:kls`. The `any_of` records alternative sufficiency only; it conveys neither route
independence nor certification.

The sidecar's `state: open` field is the mathematical proof/lifecycle axis. TeX `\notready` is the
separate repository-API axis: it says that the displayed hypotheses or normalization still await
human freeze review. A node may therefore be both `open` and `\notready` without contradiction.
