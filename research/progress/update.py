#!/usr/bin/env python3
"""Generate a documentation register from staged canonical records, without running Lean or CI."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'research'))
import atlas
import views


def staged(path):
    return subprocess.check_output(['git', 'show', ':' + path], cwd=ROOT)


def cell(value):
    return str(value).replace('|', '&#124;').replace('\n', ' ').strip()


def link(path, label='Source'):
    return f'[{label}](../../{path})'


def generate():
    paths = subprocess.check_output(['git', 'ls-files'], cwd=ROOT, text=True).splitlines()
    paths = [p for p in paths if p.startswith('formalization/blueprint/src/chapters/') and p.endswith('.tex')]
    paths += ['research/a-series/ledger.yaml', 'research/tasks.json',
              'formalization/blueprint/route-composition.yaml',
              'research/upstream/2026-09-12-kls-research.json']
    inputs = {p: staged(p) for p in sorted(paths)}
    with tempfile.TemporaryDirectory(prefix='kls-progress-') as directory:
        root = Path(directory)
        for name, data in inputs.items():
            p = root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(data)
        nodes, errors = atlas.parse_nodes(root)
        certificates, cert_errors = atlas.certificate_map(root)
        if errors or cert_errors:
            raise ValueError('\n'.join(errors + cert_errors))
    ledger = json.loads(inputs['research/a-series/ledger.yaml'])
    ledger = {n['id']: n for n in ledger['nodes']}
    tasks = json.loads(inputs['research/tasks.json'])['nodes']
    routes = json.loads(inputs['formalization/blueprint/route-composition.yaml'])
    upstream = json.loads(inputs['research/upstream/2026-09-12-kls-research.json'])
    claims = {c['node']: c for c in routes['claims']}
    cert_by_label = {c['label']: ledger[i] for i, c in certificates.items()}
    digest = hashlib.sha256(b''.join(name.encode() + b'\0' + data for name, data in inputs.items())).hexdigest()
    out = ['# Formalization progress register', '', '[Progress hub](README.md) · [Route diagrams](README.md#proof-progress-tree)', '',
           f'**{len(nodes)} local Blueprint nodes · {len(certificates)} registered Lean certificates.**', '',
           'Generated from staged canonical records. These are recorded proof/definition statuses,',
           'not a fresh Lean run or a remote CI receipt. A missing local proof means only that this',
           'register does not certify it; unregistered auxiliary progress appears in the diagram directory below.', '',
           '**✓** Formalized in Lean (proof or definition) · **○** Not recorded as complete.',
           'Upstream status is shown only where an explicit upstream mapping exists; no mapping is inferred',
           'from a similar title. Upstream `proved` does not mean Lean-proved.', '',
           '## Local nodes', '',
           'Descriptions explain the mathematical statement; the Lean column separately reports completion.',
           'See the linked statement for full hypotheses and scope.', '',
           '| Node ID | Plain-English description | Upstream / mathematical record | Our Lean record | Certificate / statement |',
           '| --- | --- | --- | --- | --- |']
    catalog = json.loads((ROOT / 'research/progress/nodes.json').read_text())
    portfolio = json.loads((ROOT / 'research/progress/portfolio.json').read_text())
    records = views.resolve(catalog, nodes, claims)
    views.validate_routes(catalog, records, routes)
    tree = views.render_tree(catalog, records)
    readme = views.render_readme((ROOT / 'research/progress/README.md').read_text(), tree, catalog, records, portfolio)
    descriptions = {r['blueprint']: r['description'] for r in records.values() if 'blueprint' in r}
    if descriptions.keys() != nodes.keys():
        raise ValueError('Update nodes.json to match the Blueprint node inventory.')
    if any(not isinstance(value, str) or not value.strip() for value in descriptions.values()):
        raise ValueError('Every local node needs a nonempty English description.')
    pending = []
    for name, node in sorted(nodes.items()):
        claim = claims.get(name, {})
        provenance = claim.get('provenance', {})
        meta = tasks.get(name, {})
        math = ('Upstream: ' + claim['state']) if provenance.get('source') == 'kls-exploration' else ('Local classification: ' + meta.get('mathematics', 'definition' if node['kind'] == 'definition' else 'not separately classified'))
        complete = records[name]['state'] == 'formalized'
        status = '✓ Formalized in Lean (definition)' if complete and node['kind'] == 'definition' else ('✓ Formalized in Lean' if complete else '○ Not yet formalized')
        excluded = claim.get('state') == 'refuted' or meta.get('mathematics') == 'refuted'
        if excluded:
            status = '— Excluded: refuted'
        if complete and provenance.get('source') != 'kls-exploration' and 'mathematics' not in meta:
            math = 'Local definition; no upstream mapping' if node['kind'] == 'definition' else 'Local Lean result; no upstream mapping'
        ref = node['statement_ref']
        source = link(ref['path'] + '#L' + str(ref['line']), 'Statement')
        cert = cert_by_label.get(name)
        if cert:
            assert complete and cert['checked_by'] == 'lean', name
            source += ' · ' + link(cert['lean_solution'], 'Lean certificate')
        out.append(f'| `{name}` | {cell(descriptions[name])} | {cell(math)} | {status} | {source} |')
        if not complete and not excluded:
            pending.append((name, node, meta))
    out += ['', '## Pending-node dependencies and infrastructure', '',
            'Dependencies below are statement dependencies, not a claim that each dependency is open.',
            'Infrastructure gaps are the recorded assessment and may cover a broader parent task.', '']
    for name, node, meta in pending:
        out += [f'### `{name}`', '']
        deps = node['dependencies']
        out.append('Dependencies: ' + (', '.join('`'+d+'`' for d in deps) if deps else 'none recorded') + '.')
        gaps = meta.get('infrastructure', {}).get('gaps', [])
        assumptions = meta.get('assumptions', [])
        if assumptions:
            out += ['', 'Retained assumptions: ' + ', '.join('`'+a+'`' for a in assumptions) + '.']
        if gaps:
            out += ['', 'Recorded gaps:', ''] + ['- '+cell(g) for g in gaps]
        else:
            out += ['', 'See the linked statement and task record for the remaining proof obligation.']
        out += ['', link('research/tasks.json', 'Task record'), '']
    out += ['## Diagram-level progress', '',
            'Generated from the same resolved records as the README diagram and result table.',
            'Blueprint mappings derive status from staged proof annotations. Auxiliary assessments',
            'retain their evidence source; generating this view does not run Lean.', '',
            '| Diagram node | Description | Our Lean record | Source |', '| --- | --- | --- | --- |']
    for record in records.values():
        if 'diagram' not in record:
            continue
        d = record['diagram']
        out.append(f'| `{d["id"]}` | {cell(record["description"])} | {views.STATES[record["state"]]} | [Source]({d["source"]}) |')
    diagram = tree
    out += ['', '## Provenance', '',
            f'Upstream revision: `{upstream["revision"]}`. The selected upstream snapshot contains',
            f'{len(upstream["records"])} records; this register is not an inventory of the entire upstream ledger.', '',
            f'Canonical input digest: `{digest}`.',
            f'Diagram digest: `{hashlib.sha256(diagram.encode()).hexdigest()}`.',
            f'View input digest: `{hashlib.sha256(json.dumps([catalog, portfolio], sort_keys=True).encode()).hexdigest()}`.', '',
            'Regenerate with `python3 research/progress/update.py` after staging the intended source and',
            'metadata updates. Unstaged unrelated metadata is deliberately excluded.', '']
    return {'STATUS.md': '\n'.join(out), 'README.md': readme, 'TREE.mmd': tree}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = generate()
    stale = [name for name, content in outputs.items()
             if not (ROOT / 'research/progress' / name).exists()
             or (ROOT / 'research/progress' / name).read_text() != content]
    if args.check:
        if stale:
            raise SystemExit('Generated progress views are stale: ' + ', '.join(stale))
        print('All progress views match the shared records.')
    else:
        for name, content in outputs.items():
            (ROOT / 'research/progress' / name).write_text(content)
        print('Generated README.md, STATUS.md, and TREE.mmd from shared records.')


if __name__ == '__main__':
    main()
