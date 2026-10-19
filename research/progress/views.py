"""Render progress views from one resolved node inventory; never infer Lean proofs from upstream status."""
from __future__ import annotations
import re
from html import escape

STATES = {'formalized': '✓ Formalized in Lean', 'partial': '◐ Partially formalized',
          'pending': '○ Not yet formalized', 'hypothesis': '◇ Open hypothesis, not a target',
          'superseded': '○ Not formalized, superseded route',
          'excluded': '— Excluded: refuted', 'logic': 'OR'}
STYLES = {'done': 'fill:#dbeafe,stroke:#2563eb,color:#1e3a8a',
          'partial': 'fill:#fff3df,stroke:#c88719,color:#66420d',
          'todo': 'fill:#fee2e2,stroke:#dc2626,color:#991b1b',
          'hypothesis': 'fill:#f1f5f9,stroke:#64748b,color:#334155',
          'superseded': 'fill:#f8fafc,stroke:#94a3b8,color:#475569,stroke-dasharray:5 4',
          'focus': 'fill:#fee2e2,stroke:#dc2626,color:#991b1b,stroke-width:3px',
          'logic': 'fill:#fff,stroke:#555,color:#222'}


BADGE_COLORS = {
    'formalized': ('#dbeafe', '#1e3a8a', '#60a5fa'),
    'pending': ('#fee2e2', '#991b1b', '#fca5a5'),
    'partial': ('#ffedd5', '#9a3412', '#fdba74'),
    'hypothesis': ('#f1f5f9', '#334155', '#94a3b8'),
    'superseded': ('#f8fafc', '#475569', '#cbd5e1'),
    'excluded': ('#f1f5f9', '#475569', '#cbd5e1'),
}


def status_cell(state):
    """Local SVG badges work as Markdown images; alt text preserves the status."""
    if state == 'logic':
        return STATES[state]
    return f'![{STATES[state]}](badges/{state}.svg)'


def status_legend():
    return " · ".join(status_cell(state) for state in BADGE_COLORS) + (
        '\n\nOpen hypotheses remain open mathematically; they are assumptions or questions, '
        'not current formalization targets. '
        'Superseded results and route junctions belong to historical exploratory routes. '
        'KLS is proved through the accepted BKL main line. The four exploratory routes '
        'are not current formalization targets and are retained as historical records; '
        'their unproved hypotheses remain open mathematically.')


def render_badges():
    outputs = {}
    for state, (background, foreground, border) in BADGE_COLORS.items():
        label = escape(STATES[state])
        width = max(172, len(STATES[state]) * 7 + 24)
        outputs[f'badges/{state}.svg'] = (
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="26" '
            f'viewBox="0 0 {width} 26" role="img" aria-label="{label}">\n'
            f'  <title>{label}</title>\n'
            f'  <rect x="0.5" y="0.5" width="{width-1}" height="25" rx="5" '
            f'fill="{background}" stroke="{border}"/>\n'
            f'  <text x="12" y="17" fill="{foreground}" font-family="DejaVu Sans,Arial,sans-serif" '
            f'font-size="12" font-weight="600">{label}</text>\n</svg>\n')
    return outputs


def cell(value):
    return str(value).replace('|', '&#124;').replace('\n', ' ').strip()


def superseded_records(catalog, blueprint, routes, resolved):
    """Use recorded route requirements and dependency edges, never names or upstream proof status."""
    policy = catalog.get('route_display')
    if policy is None:
        return set()
    if routes is None:
        raise ValueError('Route display classification needs route-composition records')
    records = catalog['nodes']
    accepted = policy['accepted_main_line']
    if accepted not in records:
        raise ValueError('Unknown accepted main-line record')
    by_blueprint = {r['blueprint']: k for k, r in records.items() if 'blueprint' in r}
    by_diagram = {r['diagram']['id']: k for k, r in records.items() if 'diagram' in r}
    incoming = {k: set() for k in records}
    for label, key in by_blueprint.items():
        incoming[key].update(by_blueprint[d] for d in blueprint[label]['dependencies'])
    for edge in catalog['diagram']['edges']:
        if edge['kind'] == 'dependency':
            incoming[by_diagram[edge['to']]].add(by_diagram[edge['from']])

    def closure(seeds):
        seen, todo = set(), list(seeds)
        while todo:
            key = todo.pop()
            if key not in seen:
                seen.add(key)
                todo.extend(incoming[key] - seen)
        return seen

    branches = {b['id']: b for b in routes['branches']}

    def requirements(expression):
        if 'node' in expression:
            return {by_blueprint[expression['node']]}
        return set().union(*(requirements(e) for e in expression['items']))

    route_inputs = {}
    for key, record in records.items():
        if 'route_branch' in record:
            branch = branches.get(record['route_branch'])
            if branch is None:
                raise ValueError(f'{key}: unknown route-composition branch')
            if branch['disposition'] != 'refuted':
                route_inputs[key] = closure(incoming[key] | requirements(branch['requires']))
        elif (record.get('assessment', {}).get('kind') == 'logic'
              and record.get('diagram', {}).get('shape') == 'diamond'
              and record['diagram']['label'].startswith('AND<br/>')):
            # Completed literature routes have separate AND junctions, outside the
            # pinned exploratory portfolio. Their recorded inputs still need proofs.
            route_inputs[key] = closure(incoming[key])
    completed = {key for key, inputs in route_inputs.items()
                 if inputs and all(resolved[i]['state'] == 'formalized' for i in inputs)}
    if completed != {accepted}:
        raise ValueError('Accepted main-line record must be the unique route branch '
                         'with an entirely formalized requirement closure')

    groups = {g['id']: g['nodes'] for g in catalog['diagram']['groups']}
    shared = set()
    for group in policy['shared_groups']:
        if group not in groups:
            raise ValueError(f'{group}: unknown shared analytic group')
        members = {by_diagram[i] for i in groups[group]}
        if any('route_branch' in records[k] or k in route_inputs for k in members):
            raise ValueError(f'{group}: shared analytic group must not contain a route-branch record')
        shared.update(members)
    protected = closure({accepted} | shared)

    historical = set()
    for key, record in records.items():
        if 'route_branch' not in record or key == accepted:
            continue
        branch = branches[record['route_branch']]
        # Refuted packages are handled separately by the exclusion state.
        if branch['disposition'] != 'refuted':
            historical.update(closure({key} | requirements(branch['requires'])))
    return historical - protected


def resolve(catalog, blueprint, claims, routes=None):
    records = catalog['nodes']
    mapped = {r['blueprint'] for r in records.values() if 'blueprint' in r}
    if mapped != blueprint.keys():
        raise ValueError('nodes.json must cover every Blueprint node exactly.')
    result = {}
    for key, record in records.items():
        if not record.get('description', '').strip():
            raise ValueError(f'{key}: missing English description')
        r = dict(record)
        if 'blueprint' in r:
            if 'assessment' in r:
                raise ValueError(f'{key}: Blueprint status must not be overridden')
            n = blueprint[r['blueprint']]
            complete = n['lean']['recorded'] and bool(n['lean']['declarations']) and (n['kind'] == 'definition' or n['proof_leanok'])
            r['state'] = 'formalized' if complete else 'pending'
            if claims.get(r['blueprint'], {}).get('state') == 'refuted':
                r['state'] = 'excluded'
        else:
            assessment = r['assessment']
            r['state'] = assessment['state']
            if not assessment.get('evidence', {}).get('source'):
                raise ValueError(f'{key}: assessment needs an evidence source')
            if assessment.get('kind') in ('route', 'logic') and r['state'] == 'formalized':
                raise ValueError(f'{key}: a completed route needs a Blueprint proof mapping')
        if r['state'] not in STATES:
            raise ValueError(f'{key}: unknown state')
        if r.get('display_state') not in (None, 'hypothesis'):
            raise ValueError(f'{key}: only an open-hypothesis display annotation is allowed')
        if r.get('display_state') == 'hypothesis' and 'blueprint' in r:
            raise ValueError(f'{key}: display_state: hypothesis is allowed only on unmapped assessment records')
        result[key] = r
    superseded = superseded_records(catalog, blueprint, routes, result)
    for key, r in result.items():
        if r['state'] not in ('formalized', 'excluded', 'logic'):
            kind = blueprint[r['blueprint']]['kind'] if 'blueprint' in r else r['assessment'].get('kind')
            if ('blueprint' in r and kind in ('assumption', 'question')) or r.get('display_state') == 'hypothesis':
                r['state'] = 'hypothesis'
            elif key in superseded and (
                    r['state'] == 'pending' and kind in ('theorem', 'lemma', 'corollary', 'proposition')
                    or kind == 'route' and r['state'] == 'pending'):
                r['state'] = 'superseded'
    return result


def render_tree(catalog, records):
    diagrams = {r['diagram']['id']: r for r in records.values() if 'diagram' in r}
    if len(diagrams) != sum('diagram' in r for r in records.values()):
        raise ValueError('Duplicate diagram IDs')
    lines = ['%%{init: {"themeVariables": {"fontSize": "20px"}, "flowchart": {"useMaxWidth": false, "nodeSpacing": 40, "rankSpacing": 65}}}%%', 'flowchart LR']
    def declaration(i):
        r = diagrams[i]; d = r['diagram']; state = r['state']
        if state == 'excluded':
            raise ValueError(f'{i}: refuted nodes cannot enter the active diagram')
        if '"' in d['label'] or '\n' in d['label']:
            raise ValueError(f'{i}: invalid Mermaid label')
        mark = '' if state == 'logic' else STATES[state][0] + ' '
        label = d['label']
        if label.startswith('AND<br/>'):
            label = 'AND<br/>' + mark + label[len('AND<br/>'):]
        else:
            label = mark + label
        left, right = ('{', '}') if d['shape'] == 'diamond' else ('[', ']')
        return f'    {i}{left}"{label}"{right}'
    used = set()
    for group in catalog['diagram']['groups']:
        lines.append(f'    subgraph {group["id"]}["{group["title"]}"]')
        for i in group['nodes']:
            if i in used:
                raise ValueError(f'{i}: duplicate group membership')
            used.add(i); lines.append(declaration(i))
        lines.append('    end')
    lines += [declaration(i) for i in diagrams if i not in used]
    adjacency = {i: [] for i in diagrams}
    for edge in catalog['diagram']['edges']:
        a, b = edge['from'], edge['to']
        if a not in diagrams or b not in diagrams:
            raise ValueError('Unknown diagram edge endpoint')
        adjacency[a].append(b)
        arrow = '-.->' if edge['kind'] == 'context' else '-->'
        lines.append(f'    {a} {arrow} {b}')
    def visit(i, stack):
        if i in stack:
            raise ValueError('Cycle in progress diagram')
        for j in adjacency[i]:
            visit(j, stack | {i})
    for i in diagrams:
        visit(i, set())
    classes = {style: [] for style in STYLES}
    for i, r in diagrams.items():
        style = {'formalized':'done', 'partial':'partial', 'pending':'todo', 'logic':'logic',
                 'hypothesis':'hypothesis', 'superseded':'superseded'}[r['state']]
        if r['diagram'].get('focus') and r['state'] in ('pending', 'partial'):
            style = 'focus'
        classes[style].append(i)
    for style, ids in classes.items():
        if ids:
            lines += [f'    classDef {style} {STYLES[style]};', f'    class {",".join(ids)} {style};']
    for i, r in diagrams.items():
        d = r['diagram']
        lines.append(f'    click {i} href "{d["source"]}" "{d["label"].replace("<br/>", " — ")}" _blank')
    return '\n'.join(lines) + '\n'


def replace_block(text, name, content):
    start, end = f'<!-- BEGIN GENERATED {name} -->', f'<!-- END GENERATED {name} -->'
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError(f'Missing or repeated generated block: {name}')
    return re.sub(re.escape(start) + r'.*?' + re.escape(end), lambda _: start+'\n'+content.strip()+'\n'+end, text, flags=re.S)


def render_readme(template, tree, catalog, records, portfolio):
    text = replace_block(template, 'TREE', '```mermaid\n'+tree+'```')
    text = replace_block(text, 'DATE', 'Last updated: **'+catalog['last_updated']+'**.\n\n'+status_legend())
    rows = ['| Family | Approach | Upstream state | Our Lean formalization | Objective / remaining work |', '| --- | --- | --- | --- | --- |']
    families = {'fam:eldan-localization':'Eldan', 'fam:mm-spectral':'Spectral', 'fam:mm-cmh':'CMH', 'fam:conditional-fiber':'Conditional fibers', 'fam:novel-routes':'Parked probes'}
    ids = set()
    for a in portfolio['approaches']:
        if a['id'] in ids:
            raise ValueError('Duplicate approach ID')
        ids.add(a['id'])
        state = records[a['local_record']]['state'] if a.get('local_record') else a['local_assessment']['state']
        if not a.get('local_record') and state == 'formalized':
            raise ValueError('A formalized approach needs an explicit local proof mapping')
        upstream = a['state'] + ('; '+a['scope_note'] if a.get('scope_note') else '')
        rows.append(f'| {families[a["family"]]} | [`{a["id"]}`]({portfolio["source"]}) | {cell(upstream)} | {status_cell(state)} | {cell(a["objective"])} |')
    intro = f'**{len(ids)} approaches in the [pinned upstream portfolio]({portfolio["source"]})** (`{portfolio["revision"][:7]}`).\nUpstream activity and local Lean formalization are separate. Supporting results appear below.\n'
    text = replace_block(text, 'APPROACHES', intro+'\n'+'\n'.join(rows))
    rows = ['| Result / step | Our Lean formalization | Source |', '| --- | --- | --- |']
    links = ['| Node | Source |', '| --- | --- |']
    for r in records.values():
        if 'diagram' not in r:
            continue
        d = r['diagram']; title = cell(d['label'].replace('<br/>',' — '))
        links.append(f'| {title} | [Source]({d["source"]}) |')
        if r.get('assessment',{}).get('kind') not in ('route','logic') and r.get('blueprint') != 'conj:kls':
            rows.append(f'| {title} | {status_cell(r["state"])} | [Source]({d["source"]}) |')
    text = replace_block(text, 'RESULTS', '\n'.join(rows))
    return replace_block(text, 'LINKS', '\n'.join(links))


def validate_routes(catalog, records, routes):
    active = {b['id']: b for b in routes['branches'] if b['disposition'] == 'active'}
    displayed = {r['route_branch']: r for r in records.values() if 'route_branch' in r}
    if active.keys() != displayed.keys():
        raise ValueError('Diagram must contain every active route exactly once')
    incoming = {}
    for e in catalog['diagram']['edges']:
        if e['kind'] == 'dependency':
            incoming.setdefault(e['to'], set()).add(e['from'])
    mappings = {r['diagram']['id']: r['blueprint'] for r in records.values() if 'blueprint' in r and 'diagram' in r}
    def ancestors(i, seen=None):
        seen = set() if seen is None else seen
        for j in incoming.get(i, set()) - seen:
            seen.add(j); ancestors(j, seen)
        return seen
    for name, branch in active.items():
        r = displayed[name]; diagram_id = r['diagram']['id']
        required = {i['node'] for i in branch['requires']['items']}
        represented = {mappings[i] for i in ancestors(diagram_id) if i in mappings}
        if not required <= represented:
            raise ValueError(f'{name}: missing required route inputs: {required - represented}')
        if diagram_id not in incoming.get('ANY', set()):
            raise ValueError(f'{name}: missing route-to-OR edge')
    if 'ANY' not in incoming.get('KLS', set()):
        raise ValueError('The OR junction must point to KLS')
