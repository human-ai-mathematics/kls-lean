"""Render literature provenance and local coverage without conflating the two."""
from __future__ import annotations

import re
import views


def validate(catalog, records):
    papers = {p['id']: p for p in catalog['papers']}
    if len(papers) != len(catalog['papers']):
        raise ValueError('Duplicate literature ID')
    groups = {g['id'] for g in catalog['groups']}
    for p in papers.values():
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]+', p['id']):
            raise ValueError('Invalid literature ID')
        if p['group'] not in groups or not p['url'].startswith('https://'):
            raise ValueError(f'{p["id"]}: missing group or primary source')
        for key in ('title', 'authors', 'date', 'publication', 'locator', 'result', 'remaining'):
            if not p.get(key, '').strip():
                raise ValueError(f'{p["id"]}: missing {key}')
        for item in p['local_results']:
            if item['node'] not in records or not item.get('scope'):
                raise ValueError(f'{p["id"]}: invalid local result mapping')
            if records[item['node']]['state'] in ('logic', 'excluded'):
                raise ValueError(f'{p["id"]}: a route junction or refutation is not a proved result')
        targets = p.get('target_declarations', [])
        if (targets or p.get('target_certificate')) and not p.get('target_review'):
            raise ValueError(f'{p["id"]}: target declarations need a scope review')
        for target in targets:
            if not target.get('name') or not target.get('source', '').startswith('formalization/'):
                raise ValueError(f'{p["id"]}: invalid target declaration')
    shown = [i for g in catalog['diagram_groups'] for i in g['papers']]
    if len(shown) != len(set(shown)) or any(i not in papers for i in shown):
        raise ValueError('Invalid literature diagram inventory')
    for i in shown:
        if not papers[i].get('diagram') or '"' in papers[i]['diagram']:
            raise ValueError(f'{i}: invalid diagram label')
    for e in catalog['diagram_edges']:
        if e['from'] not in shown or e['to'] not in shown or e['kind'] not in ('chronology', 'context'):
            raise ValueError('Invalid literature edge; these are not proof implications')
    ranks = set()
    for priority in catalog.get('priorities', []):
        rank = priority.get('rank')
        if type(rank) is not int or rank < 1 or rank in ranks:
            raise ValueError('Literature priorities need unique positive ranks')
        ranks.add(rank)
        if (not priority.get('papers') or any(i not in papers for i in priority['papers'])
                or not priority.get('target') or not priority.get('next_step')):
            raise ValueError('Literature priorities need source papers, target and next step')
    return papers


LEMMA_MARKS = {'formalized': '✓', 'partial': '◐', 'pending': '○', 'improved': '⇑'}
LEMMA_LABELS = {'formalized': 'Formalized in Lean', 'partial': 'Partial or statement only',
                'pending': 'Not yet formalized', 'improved': 'Stronger result or alternative route'}
LEMMA_STYLES = {'formalized': 'fill:#dbeafe,stroke:#2563eb,color:#1e3a8a',
                'partial': 'fill:#fff3df,stroke:#c88719,color:#66420d',
                'pending': 'fill:#fee2e2,stroke:#dc2626,color:#991b1b',
                'improved': 'fill:#dcfce7,stroke:#15803d,color:#14532d'}
RELATIONS = ('same', 'partial', 'stronger', 'alternative')
_DECLARATION_END = re.compile(r'^(?:@\[|/--|/-!|theorem |lemma |def |noncomputable |instance |'
                              r'structure |abbrev |private |protected |omit |variable |section|end |namespace )')


def declaration_body(source, name):
    """Return the text of one declaration, from its keyword to the next top-level item."""
    lines = source.splitlines()
    parts = name.split('.')
    for k in range(len(parts)):  # longest written suffix first, e.g. `def Intrinsic.constant`
        written = re.escape('.'.join(parts[k:]))
        head = re.compile(rf'^(?:noncomputable |private |protected )*(?:theorem|lemma|def|abbrev|structure) {written}(?:\s|$)')
        for i, line in enumerate(lines):
            if head.match(line):
                end = next((j for j in range(i + 1, len(lines)) if _DECLARATION_END.match(lines[j])), len(lines))
                return '\n'.join(lines[i:end])
    return None


def lemma_state(item, read_source):
    """Derive a lemma status; a textual sorry check is a view, verify.py stays authoritative."""
    if not item['declarations']:
        return 'pending'
    for target in item['declarations']:
        if re.search(r'\bsorry\b', declaration_body(read_source(target['source']), target['name'])):
            return 'partial'
    if item['relation'] == 'partial':
        return 'partial'
    return 'improved' if item['relation'] in ('stronger', 'alternative') else 'formalized'


def validate_lemma_map(paper, read_source):
    lemma_map = paper['lemma_map']
    for key in ('source_version', 'source_url', 'reviewed_on', 'items'):
        if not lemma_map.get(key):
            raise ValueError(f'{paper["id"]}: lemma map needs {key}')
    items = {i['id']: i for i in lemma_map['items']}
    if len(items) != len(lemma_map['items']):
        raise ValueError(f'{paper["id"]}: duplicate lemma ID')
    if sum(bool(i.get('main')) for i in items.values()) != 1:
        raise ValueError(f'{paper["id"]}: a lemma map needs exactly one main theorem')
    for i in items.values():
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]*', i['id']) or '"' in i['label']:
            raise ValueError(f'{paper["id"]}: invalid lemma ID or label')
        if not all(i.get(k) for k in ('locator', 'label', 'statement')) or i['relation'] not in RELATIONS:
            raise ValueError(f'{paper["id"]}/{i["id"]}: missing locator, label, statement or relation')
        if any(u not in items or u == i['id'] for u in i['uses']):
            raise ValueError(f'{paper["id"]}/{i["id"]}: unknown dependency')
        if i['relation'] in ('stronger', 'alternative') and not i.get('note'):
            raise ValueError(f'{paper["id"]}/{i["id"]}: a stronger or alternative result needs a note')
        for target in i['declarations']:
            if not target['source'].startswith(('formalization/', 'solutions/')):
                raise ValueError(f'{paper["id"]}/{i["id"]}: declarations must be library or certificate sources')
            if declaration_body(read_source(target['source']), target['name']) is None:
                raise ValueError(f'{paper["id"]}/{i["id"]}: {target["name"]} not found in {target["source"]}')
    return items


def hub_items(paper, states):
    """The main theorem's proof chain plus every item with local progress."""
    items = {i['id']: i for i in paper['lemma_map']['items']}
    chain, stack = set(), [i for i in items if items[i].get('main')]
    while stack:
        i = stack.pop()
        if i not in chain:
            chain.add(i)
            stack += items[i]['uses']
    return chain | {i for i, s in states.items() if s != 'pending'}


def render_lemma_graph(paper, states, indent='    ', keep=None):
    """Nodes and edges of one paper; styling is separate so several papers share one diagram."""
    items = [i for i in paper['lemma_map']['items'] if keep is None or i['id'] in keep]
    shown = {i['id'] for i in items}
    lines = [f'{indent}{paper["id"]}_{i["id"]}["{LEMMA_MARKS[states[i["id"]]]} {i["locator"]}<br/>{i["label"]}"]'
             for i in items]
    lines += [f'{indent}{paper["id"]}_{u} --> {paper["id"]}_{i["id"]}' for i in items for u in i['uses'] if u in shown]
    hidden = len(paper['lemma_map']['items']) - len(items)
    if hidden:
        lines.append(f'{indent}{paper["id"]}_more["+{hidden} further statements in the paper register"]')
    return lines


def render_lemma_styles(graphs, indent='    '):
    """Class styling for (paper, states, shown ids) triples, with a thick border on each main theorem."""
    lines = []
    for state, style in LEMMA_STYLES.items():
        members = [f'{p["id"]}_{i["id"]}' for p, states, shown in graphs for i in p['lemma_map']['items']
                   if states[i['id']] == state and i['id'] in shown]
        if members:
            lines += [f'{indent}classDef lemma_{state} {style};', f'{indent}class {",".join(members)} lemma_{state};']
    lines += [f'{indent}style {p["id"]}_{i["id"]} stroke-width:3px'
              for p, _, _ in graphs for i in p['lemma_map']['items'] if i.get('main')]
    more = [f'{p["id"]}_more' for p, _, shown in graphs if len(shown) < len(p['lemma_map']['items'])]
    if more:
        lines += [f'{indent}classDef lemma_more fill:#f8fafc,stroke:#94a3b8,color:#334155,stroke-dasharray:4 3;',
                  f'{indent}class {",".join(more)} lemma_more;']
    return lines


def lemma_legend():
    return ' · '.join(f'{LEMMA_MARKS[s]} {LEMMA_LABELS[s]}' for s in LEMMA_MARKS)


def render_lemma_maps(catalog, read_source, certificates=None):
    """Keep every register map. With a certificate mapping, limit the combined diagram to
    certified paper targets; without one (the default) the diagram keeps every paper."""
    papers = [p for p in catalog['papers'] if p.get('lemma_map')]
    sections = ['## Paper lemma maps', '',
                'Each map lists the numbered statements of one pinned source and the Lean declarations',
                'that state them. ✓, ◐ and ○ are derived from the declarations: no declaration is ○, a',
                'declaration whose body contains `sorry` or a recorded partial scope is ◐. ⇑ marks a',
                'reviewed stronger statement or a different proof route; dropping a hypothesis the paper',
                'never uses stays ✓. A paper is covered only by its certified main theorem (thick border).',
                '', lemma_legend(), '']
    hub, graphs = ['flowchart LR'], []
    for paper in papers:
        lemma_map = paper['lemma_map']
        states = {i['id']: lemma_state(i, read_source) for i in lemma_map['items']}
        sections += [f'### {paper["id"]} lemma map', '',
                     f'Source: [{paper["authors"]}, {lemma_map["source_version"]}]({lemma_map["source_url"]}),'
                     f' reviewed {lemma_map["reviewed_on"]}.', '']
        if lemma_map.get('standing_assumptions'):
            sections += [f'Standing assumptions: {lemma_map["standing_assumptions"]}', '']
        sections += ['```mermaid', 'flowchart LR', *render_lemma_graph(paper, states),
                     *render_lemma_styles([(paper, states, set(states))]), '```', '',
                     '| Item | Statement | Status | Lean declarations | Note |', '| --- | --- | --- | --- | --- |']
        for i in lemma_map['items']:
            state = states[i['id']]
            names = '<br/>'.join(f'[`{t["name"].rsplit(".", 1)[-1]}`](../../{t["source"]})' for t in i['declarations'])
            locator = f'**{i["locator"]}** (main)' if i.get('main') else i['locator']
            sections.append(f'| {locator} | {views.cell(i["statement"])} | {LEMMA_MARKS[state]} {LEMMA_LABELS[state]} | '
                            f'{names or "—"} | {views.cell(i.get("note", ""))} |')
        if lemma_map.get('omitted'):
            sections += ['', f'Not listed: {lemma_map["omitted"]}']
        sections.append('')
        if certificates is None or paper_certificate(paper, certificates):
            keep = hub_items(paper, states)
            hub += [f'    subgraph P_{paper["id"]}["{paper["authors"]} · {lemma_map["source_version"]}"]', '    direction LR',
                    *render_lemma_graph(paper, states, keep=keep), '    end']
            graphs.append((paper, states, keep))
    hub += render_lemma_styles(graphs)
    return sections, '\n'.join(hub) + '\n', papers


def paper_certificate(paper, certificates):
    """The registered certificate of the paper's selected main theorem, if any."""
    label = paper.get('target_certificate')
    return next(((key, cert) for key, cert in certificates.items() if label and cert['label'] == label), None)


def coverage(paper, records, certificates=None):
    """Only a registered paper-target certificate covers a paper; a fragment never does."""
    if paper_certificate(paper, certificates or {}):
        return 'formalized'
    return 'partial' if any(records[i['node']]['state'] in ('formalized', 'partial')
                            for i in paper['local_results']) else 'pending'


def result_link(key, records, blueprint):
    record = records[key]
    if record.get('blueprint'):
        ref = blueprint[record['blueprint']]['statement_ref']
        return '../../' + ref['path'] + '#L' + str(ref['line'])
    return record['assessment']['evidence']['source']


def render_tree(catalog, papers):
    lines = ['flowchart TB']
    for group in catalog['diagram_groups']:
        lines += [f'    subgraph L_{group["id"]}["{group["title"]}"]', '    direction LR']
        lines += [f'    L_{i}["{papers[i]["diagram"]}"]' for i in group['papers']]
        lines += ['    end']
    for edge in catalog['diagram_edges']:
        label = 'later milestone' if edge['kind'] == 'chronology' else 'related input / method'
        lines.append(f'    L_{edge["from"]} -. "{label}" .-> L_{edge["to"]}')
    shown = [i for group in catalog['diagram_groups'] for i in group['papers']]
    lines += ['    classDef literature fill:#eef2ff,stroke:#64748b,color:#172554;',
              '    classDef recent fill:#fff4dc,stroke:#b7791f,color:#663c00;',
              '    class '+','.join('L_'+i for i in shown)+' literature;',
              '    class L_ChenKlartag2026,L_Letwin2026 recent;']
    for i in shown:
        lines.append(f'    click L_{i} href "{papers[i]["url"]}" "Primary source" _blank')
    return '\n'.join(lines) + '\n'


def covered_sentence(catalog, certificates):
    covered = [p for p in catalog['papers'] if paper_certificate(p, certificates)]
    if not covered:
        return '**No complete paper target is currently registered as covered.**'
    def target(p):
        mains = [i['locator'] for i in p.get('lemma_map', {}).get('items', []) if i.get('main')]
        return mains[0] if mains else p['locator']
    names = ', '.join(f'{p["authors"]} ({target(p)})' for p in covered)
    return f'**Covered by a registered paper-target certificate: {names}.**'


def supporting_certificates(paper, records, certificates):
    """Report existing fragment certificates; never promote them to paper coverage."""
    labels = {records[item['node']].get('blueprint') for item in paper['local_results']}
    return {key: cert for key, cert in certificates.items() if cert['label'] in labels}


def render_priorities(catalog):
    papers = {p['id']: p for p in catalog['papers']}
    lines = ['These are source-review and proof priorities, not claims that the targets are proved.',
             'Every proof task must first pin its paper version, theorem, hypotheses and constants.', '',
             '| Priority | Sources / target | Next action |', '| --- | --- | --- |']
    for priority in sorted(catalog.get('priorities', []), key=lambda p: p['rank']):
        sources = ', '.join(f'[{papers[i]["authors"]}]({papers[i]["url"]})' for i in priority['papers'])
        lines.append(f'| {priority["rank"]} | {sources}<br/>{views.cell(priority["target"])} | '
                     f'{views.cell(priority["next_step"])} |')
    return '\n'.join(lines)


def render_proof_path(catalog, certificates, read_source):
    """A reading view of existing lemma maps, without a second proof-status database."""
    path = catalog['proof_path']
    papers = {p['id']: p for p in catalog['papers']}
    lines = [
        f'Pinned main source: [{papers[path["source"]]["authors"]}, '
        f'{papers[path["source"]]["lemma_map"]["source_version"]}]({papers[path["source"]]["url"]}).', '',
        'Read the main theorem first, then its analytic inputs and the separate',
        'Letwin/localization statements. This is a reading order, not a new dependency graph.',
        'Status comes from the existing paper lemma maps. A ✓ proves the displayed statement',
        'with its hypotheses; it does not discharge an input or cover the whole paper.', '',
        '| Source step | Lean entry | Local status | Input boundary / remaining work | Evidence |',
        '| --- | --- | --- | --- | --- |',
    ]
    seen = set()
    for step in path['steps']:
        key = (step['paper'], step['item'])
        if key in seen:
            raise ValueError('Duplicate proof-path step')
        seen.add(key)
        paper = papers[step['paper']]
        items = validate_lemma_map(paper, read_source)
        item = items[step['item']]
        if not step.get('boundary', '').strip():
            raise ValueError('Proof-path step needs its input boundary')
        declared = {d['name']: d for d in item['declarations']}
        names = step.get('entries', [])
        if any(name not in declared for name in names):
            raise ValueError('Proof-path entry is not in its canonical lemma map')
        entries = '<br/>'.join(f'[`{name}`](../../{declared[name]["source"]})' for name in names)
        if not entries:
            entries = 'No source-theorem entry' if not declared else 'Supporting declarations in the item map'
        state = lemma_state(item, read_source)
        evidence = f'[Item map](LITERATURE.md#{paper["id"].lower()}-lemma-map)'
        cert_label = step.get('certificate')
        if cert_label:
            cert = certificates.get(cert_label)
            if not cert or cert['declaration'] not in declared:
                raise ValueError('Proof-path certificate is not registered for the mapped item')
            evidence += f'<br/>[Certificate](../../{cert["module"].replace(".", "/")}.lean)'
        source = f'[{paper["authors"]}: {item["locator"]}]({paper["lemma_map"]["source_url"]})'
        lines.append(f'| {source} | {entries} | {LEMMA_MARKS[state]} {LEMMA_LABELS[state]} | '
                     f'{views.cell(step["boundary"])} | {evidence} |')
    lines += ['', 'Certificates and item maps identify statements and source reviews, not a fresh run.',
              'For snapshot-specific acceptance use [verification](../verification.md#receipts-and-trust-scope)',
              'and the [current handoff](../../HANDOFF.md). **`KLS.kls` is proved through BKL Theorem 1.1 (`thm:bkl-poincare`) and the affine/isotropic reduction.**']
    return '\n'.join(lines)


def render(catalog, records, blueprint, certificates=None, read_source=None):
    certificates = {} if certificates is None else certificates
    papers = validate(catalog, records)
    if read_source is not None:
        for paper in papers.values():
            if paper.get('lemma_map'):
                validate_lemma_map(paper, read_source)
        lemma_sections, lemma_hub, lemma_papers = render_lemma_maps(catalog, read_source, certificates)
    else:
        lemma_sections, lemma_hub, lemma_papers = [], '', []
    tree = render_tree(catalog, papers)
    c = views.cell
    header = [
        '# KLS literature and local formalization', '',
        '**Primary progress register** · [Progress hub](README.md) · [Route diagrams](README.md#proof-progress-tree) · [Node register](STATUS.md)', '',
        f'**Literature through July 2026 · Sources checked {catalog["checked_on"]} · {len(papers)} selected sources.**', '',
        catalog['scope'], '',
        'The literature has advanced to an inverse-Cheeger bound of order `(log n)^(1/4)` in the',
        '[July 2026 Letwin preprint](https://arxiv.org/html/2607.24164v1). Our repository currently',
        'formalizes selected analytic foundations and reductions, and the dimension-free KLS bound through',
        'Bizeul–Klartag–Lehec\'s Theorem 1.1; the dimension-dependent frontier proofs below are not formalized as such.', '',
        'Publication status and local Lean status are separate columns. **◐ means named fragments or',
        'restricted counterparts, never an entire paper; ○ means the selected main result is not',
        'locally formalized.** A ✓ beside an individual local result is derived from the existing',
        'Blueprint/progress records; see the [Blueprint marker rules](../../formalization/blueprint/README.md#markers-in-the-tex-sources).', '',
        '## When a paper is covered', '',
        'A selected paper target is covered only after its main theorem has a faithful Lean statement',
        '(including hypotheses, constants, normalization and dimensional scope), a proof without',
        'nonstandard axioms, and a registered certificate with verification evidence for that exact',
        'statement. A source review must identify the paper version and theorem being matched.',
        'Supporting lemmas, restricted cases and conditional reductions do not meet this criterion.',
        covered_sentence(catalog, certificates),
        'Existing fragment certificates are listed explicitly below; an unregistered proved target',
        'is still awaiting certification.', '',
        '## Current literature priorities', '', render_priorities(catalog), '',
        '## Constant conventions', '',
        'For isotropic log-concave laws, use `Var(f) ≤ C_P ∫‖∇f‖² dμ`, with no factor 1/2.',
        'Write `h` for the Cheeger lower-bound constant with denominator `min(μ(A), 1−μ(A))`,',
        'and `ψ = 1/h`, `ψₙ = sup_μ ψ(μ)` for the inverse convention. Some older papers use the',
        'symbol ψ for h instead; their bounds are translated here. The original KLS paper also',
        'uses a product denominator, so exact numerical constants cannot be copied unchanged.', '',
        'The literature comparison is `ψ²/π ≤ C_P ≤ 4ψ²`; consequently `ψₙ = O((log n)^a)`',
        'corresponds to `C_P = O((log n)^(2a))`. See [Letwin, introduction](https://arxiv.org/html/2607.24164v1#S1)',
        'and [De Ponti–Mondino](https://arxiv.org/abs/1902.03835). The numerical comparison',
        'for finite-dimensional log-concave laws is now a local Lean proof; the general RCD theorem',
        'is not formalized here. Logarithmic bounds below use `n ≥ 2` (Guan’s iterated-log bound uses `n ≥ 3`).', '',
        '## Literature map', '',
        'Every node links to its source. Dashed arrows show later milestones or related methods,',
        '**not logical implications, complete dependency lists, or Lean proof edges**. Blue is',
        'literature context; amber highlights July 2026. Neither color means formalized.', '',
        '```mermaid', tree.rstrip(), '```', '',
        'The older dates in the KLS chain refer to first circulation/conference presentation;',
        'the tables distinguish those dates from final journal publication. Slicing and thin shell',
        'are separate achievements; their resolution does not give dimension-free KLS.', '',
    ]
    tables = []
    for group in catalog['groups']:
        tables += [f'## {group["title"]}', '',
                   '| Source and target theorem | Main result / role | Lean statements | Local coverage | Certificate | Remaining scope |',
                   '| --- | --- | --- | --- | --- | --- |']
        for p in catalog['papers']:
            if p['group'] != group['id']:
                continue
            source = f'[{c(p["authors"])} — {c(p["title"])}]({p["url"]})<br/>{c(p["date"])} · {c(p["publication"])}<br/>{c(p["locator"])}'
            local = [views.status_cell(coverage(p, records, certificates))]
            for item in p['local_results']:
                state = records[item['node']]['state']
                mark = views.STATES[state][0]
                local.append(f'{mark} [{c(item["scope"])}]({result_link(item["node"], records, blueprint)})')
            statements = (f'[Statement inventory](#{p["id"].lower()}-lean-statements)'
                          if p['local_results'] or p.get('target_declarations')
                          else 'No local target statement registered')
            certs = supporting_certificates(p, records, certificates)
            own = paper_certificate(p, certificates)
            certificate = 'No paper-target certificate'
            if own:
                certs.pop(own[0], None)
                certificate = (f'**Paper-target certificate:** '
                               f'[`{c(own[0])}`](../../{own[1]["module"].replace(".", "/")}.lean)')
            if certs:
                certificate += '<br/>Supporting only: ' + ', '.join(
                    f'[`{c(key)}`](../../{cert["module"].replace(".", "/")}.lean)'
                    for key, cert in sorted(certs.items()))
            tables.append(f'| {source} | {c(p["result"])} | {statements} | '+ '<br/>'.join(local)
                          + f' | {certificate} | {c(p["remaining"])} |')
        tables.append('')
    statements = ['## Local Lean statement inventory', '',
                  'The links below retain the actual declarations and their full hypotheses.',
                  'Mappings labelled supporting are not the complete paper target.', '']
    for p in catalog['papers']:
        if not p['local_results'] and not p.get('target_declarations'):
            continue
        statements += [f'### {p["id"]} Lean statements', '']
        for target in p.get('target_declarations', []):
            statements.append(f'- Selected target: [`{target["name"]}`](../../{target["source"]}).')
        if p.get('target_review'):
            own_cert = paper_certificate(p, certificates)
            statements += [f'- [Target scope review](../../{p["target_review"]})'
                           + (f'; paper-target certificate `{own_cert[0]}`.' if own_cert else '; no registered target certificate.')]
        for item in p['local_results']:
            record = records[item['node']]
            declarations = blueprint[record['blueprint']]['lean']['declarations'] if record.get('blueprint') else []
            statements.append(f'- Supporting scope: [{item["scope"]}]({result_link(item["node"], records, blueprint)}).')
            statements += [f'  Declaration: `{name}`.' for name in declarations]
            if not declarations:
                statements.append('  This auxiliary assessment links to source; it has no separate Blueprint declaration inventory or ledger certificate.')
        statements.append('')
    footer = [
        '## What the July papers would require here', '',
        'Both July results need a local moment-measure construction and its regularity theory.',
        'The sharp thin-shell paper then needs the weighted Hessian identities and third-order',
        'tensor estimates. The quadratic-form paper additionally needs its matrix inequality,',
        'Stein/H⁻¹ argument and the conversion through the directional third-moment parameter.',
        'These are missing mathematical developments, despite our existing density, closed-form',
        'and Euclidean calculus infrastructure. The existing CMH and spectral route propositions',
        'are conditional research routes and do not certify either paper.', '',
        '## Source and coverage notes', '',
        '- July statements are pinned to `2607.23307v1` and `2607.24164v1`. Both are preprints;',
        '  this map checks bibliographic data, main statements and normalization, not every proof step.',
        '- The 2025 parallel-coupling preprint is read at `2507.15495v2` (23 February 2026).',
        '- The book’s coefficient 4 is a recorded statement; our one-dimensional proof is independent.',
        '  The original attribution remains distinct from mathematical proof and formal verification:',
        '  see the [one-dimensional scope review](one-dimensional-poincare.md).',
        '  Book metadata was checked on the publisher pages; detailed book-page correspondences',
        '  use the existing source audits, rather than a fresh reading of the complete monographs.',
        '- General auxiliary progress, such as locally Lipschitz coarea and smooth recovery, is listed',
        '  in the [supporting node register](STATUS.md); it is not automatically credited',
        '  as a completed fragment of every paper that could use it.',
        '- No percentage of a paper is reported: result counts do not measure proof coverage.', '',
        '### Additional primary-source metadata', '',
    ]
    for p in catalog['papers']:
        for i, url in enumerate(p.get('additional_sources', []), 1):
            footer.append(f'- {p["authors"]}, {p["date"]}: [additional primary source {i}]({url}).')
    footer += ['', '### Maintenance', '',
               'Edit [literature.json](literature.json), then run `python3 research/progress/update.py`',
               'with the intended canonical proof/metadata inputs staged. Coverage is derived from',
               'the same resolved node records as the route map. Generated files are not edited by hand.', '']
    readme = [f'**{len(papers)} selected sources, from foundational results to July 2026.**', '',
              'The [paper-by-paper literature register](LITERATURE.md) records statements, publication',
              'versions, exact local coverage and remaining work. The general KLS-bound milestones',
              'in this diagram are all still pending locally; completed supporting results appear in',
              'the paper and node registers. Dashed edges mean chronology or related methods, not proof.', '',
              '```mermaid', tree.rstrip(), '```', '',
              '| Latest source | Literature result | Our Lean status |', '| --- | --- | --- |']
    for key in ('ChenKlartag2026', 'Letwin2026'):
        p = papers[key]
        readme.append(f'| [{p["authors"]}, {p["date"]}]({p["url"]}) · {p["publication"]} | {c(p["result"])} | {views.status_cell(coverage(p, records, certificates))} |')
    readme += ['', 'Here ψ is the inverse Cheeger constant, so its logarithmic exponent is half the',
               'Poincaré exponent. The sharp thin-shell result does not resolve dimension-free KLS.',
               'See the [full tables and normalization](LITERATURE.md#constant-conventions).']
    outputs = {'LITERATURE.md': '\n'.join(header + tables + lemma_sections + statements + footer),
               'LITERATURE.mmd': tree}
    if lemma_hub:
        outputs['PAPERS.mmd'] = lemma_hub
    return outputs, '\n'.join(readme)


def render_lemma_hub(catalog, certificates, read_source):
    """Hub block: diagrams only for papers with a registered main-theorem certificate."""
    papers = [p for p in catalog['papers'] if p.get('lemma_map') and paper_certificate(p, certificates)]
    pointer = 'Full maps for every selected paper are in [LITERATURE.md](LITERATURE.md#paper-lemma-maps).'
    if not papers:
        return 'No covered paper has a reviewed lemma map yet. ' + pointer
    lines = [pointer, '',
             'Each diagram below shows a covered paper\'s main theorem (thick border, rightmost) with the statements its',
             'proof uses, plus every statement with local Lean progress. Arrows run from a statement to',
             'the results that use it.', '',
             lemma_legend(), '']
    for paper in papers:
        lemma_map = paper['lemma_map']
        states = {i['id']: lemma_state(i, read_source) for i in lemma_map['items']}
        keep = hub_items(paper, states)
        counts = ', '.join(f'{sum(s == k for s in states.values())} {LEMMA_MARKS[k]}'
                           for k in LEMMA_MARKS if any(s == k for s in states.values()))
        lines += [f'### {paper["authors"]} ({lemma_map["source_version"]})', '',
                  f'{len(states)} statements: {counts}. [Full map](LITERATURE.md#{paper["id"].lower()}-lemma-map).', '',
                  '```mermaid', 'flowchart LR', *render_lemma_graph(paper, states, keep=keep),
                  *render_lemma_styles([(paper, states, keep)]), '```', '']
    return '\n'.join(lines).rstrip()
