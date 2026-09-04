# KLS Lean Blueprint

This Blueprint is the live dependency map for the canonical `L²`/energy foundation and the
remaining route to KLS. It is deliberately narrower than the upstream mathematical manuscript:
it records only interfaces that this repository intends to formalize, together with four
audited route alternatives.

The graph has three status classes:

- `\lean{...}` plus statement and proof `\leanok`: the declaration and proof are certified by
  the local Lean build;
- an exact statement without `\leanok`: mathematically stated but not Lean-certified here;
- `\notready`: the theorem's public API or hypotheses are not frozen yet.

Upstream `checked_by: agent` metadata is provenance, never Lean certification. The legacy
smooth-test certificates are kept separate from the canonical closed-energy nodes until an
explicit core-agreement theorem identifies their constants.

## Build

Create a Python environment and install the pinned web-builder dependency:

```bash
python3 -m venv .venv-blueprint
.venv-blueprint/bin/pip install -r formalization/blueprint/requirements.txt
```

Then, from the repository root:

```bash
python3 research/check_blueprint.py
cd formalization && lake build
cd .. && .venv-blueprint/bin/python formalization/blueprint/build.py all
```

The helper writes the PDF to `formalization/blueprint/print/print.pdf`, the website to
`formalization/blueprint/web/`, and the declaration list to
`formalization/blueprint/lean_decls`. It uses direct commands because the Lake package is nested
under `formalization/`.

`route-composition.yaml` is intentionally a JSON subset. TeX `\uses{...}` means logical AND;
the sidecar supplies the one required logical OR: any one of the four route alternatives may
discharge `conj:kls`.
