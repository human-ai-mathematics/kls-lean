# KLS Lean Blueprint

The Blueprint is the mathematical dependency map of the statements this repository formalizes:
the `L²`/energy foundation, the source-paper targets and the exploratory routes to KLS. It
records statements, their Lean declarations and their logical prerequisites. It is not the live
progress report.

## Where the current state lives

- [Proof path](../../research/progress/PROOF-PATH.md): the four-stage main line and its exact inputs.
- [Literature register](../../research/progress/LITERATURE.md) and
  [progress hub](../../research/progress/README.md): per-paper coverage, generated status and diagrams.
- [Current handoff](../../HANDOFF.md): the active goal, evidence and next step.

## Markers in the TeX sources

- `\lean{...}` names the Lean declarations of a node.
- `\leanok` on a statement or proof is a recorded implementation marker for the named local
  declaration. The marker by itself does not establish a `sorry`-free transitive axiom closure,
  exact source fidelity or a registered certificate: a normal successful build accepts `sorry`,
  and that evidence comes only from current declaration checks, standard-axiom audits and
  snapshot-bound receipts (see the [verification guide](../../research/verification.md));
  certificates are registered separately in the [ledger](../../research/a-series/ledger.yaml).
- An exact statement without `\leanok` carries no recorded Blueprint proof marker. This does not
  by itself mean that no proof exists in the source; consult the actual declarations and
  receipts before concluding that a statement is open or proved.
- `\notready` marks an explicit unresolved choice in a statement (test domain, hypotheses or
  normalization), described in the nearby text. An open proof alone does not justify it, and
  removing it adds no proof evidence. See the [lifecycle](../../research/ledger-schema.md#lifecycle).

Public Lean interfaces may still change; certification does not promise signature stability.

## Logical structure

- `\uses{...}` means logical AND: every listed node is a prerequisite.
- [`route-composition.yaml`](route-composition.yaml) (a JSON subset) supplies the one logical OR:
  any one of the four route alternatives may discharge `conj:kls`. Its `any_of` records
  alternative sufficiency only; it asserts neither independence of the routes nor certification.
- `targets[].adapters` records interfaces that align imported route statements with this
  repository's constants and normalizations. Adapters are metadata, not logical prerequisites,
  and listing one creates no `\uses` edge; a logical use must be declared on the consuming node.
- Upstream provenance fields (such as `checked_by: agent` or `proofs.mode`) describe the source
  of a route statement, never Lean certification. A proved implication with open assumptions
  remains conditional.
- The sidecar `state` field is the mathematical lifecycle axis; `\notready` is a separate
  statement-choice marker. Neither supplies proof evidence.

## Workflow

Placement, naming and change checks follow [workflow.md](../../research/workflow.md) and
[naming.md](../../research/naming.md). Progress views are generated from these sources by
`research/progress/update.py`; do not edit generated blocks by hand.

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
