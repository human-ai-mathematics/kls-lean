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
        if targets and not p.get('target_review'):
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


def coverage(paper, records):
    """A matching local fragment cannot certify a whole article."""
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


def render(catalog, records, blueprint, certificates=None):
    certificates = {} if certificates is None else certificates
    papers = validate(catalog, records)
    tree = render_tree(catalog, papers)
    c = views.cell
    header = [
        '# KLS literature and local formalization', '',
        '**Primary progress register** · [Literature overview](README.md) · [Supporting node register](STATUS.md)', '',
        f'**Literature through July 2026 · Sources checked {catalog["checked_on"]} · {len(papers)} selected sources.**', '',
        catalog['scope'], '',
        'The literature has advanced to an inverse-Cheeger bound of order `(log n)^(1/4)` in the',
        '[July 2026 Letwin preprint](https://arxiv.org/html/2607.24164v1). Our repository currently',
        'formalizes selected analytic foundations and reductions; none of the general',
        'dimension-dependent frontier bounds below is yet proved here. Dimension-free KLS remains open.', '',
        'Publication status and local Lean status are separate columns. **◐ means named fragments or',
        'restricted counterparts, never an entire paper; ○ means the selected main result is not',
        'locally formalized.** A ✓ beside an individual local result is derived from the existing',
        'Blueprint/progress records. It is not a new certificate or a certification of the source paper.', '',
        '## When a paper is covered', '',
        'A selected paper target is covered only after its main theorem has a faithful Lean statement',
        '(including hypotheses, constants, normalization and dimensional scope), a proof without',
        'nonstandard axioms, and a registered certificate with verification evidence for that exact',
        'statement. A source review must identify the paper version and theorem being matched.',
        'Supporting lemmas, restricted cases and conditional reductions do not meet this criterion.',
        '**No complete paper target is currently registered as covered.** Existing fragment certificates',
        'are listed explicitly below; an unregistered proved target is still awaiting certification.', '',
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
            local = [views.status_cell(coverage(p, records))]
            for item in p['local_results']:
                state = records[item['node']]['state']
                mark = views.STATES[state][0]
                local.append(f'{mark} [{c(item["scope"])}]({result_link(item["node"], records, blueprint)})')
            statements = (f'[Statement inventory](#{p["id"].lower()}-lean-statements)'
                          if p['local_results'] or p.get('target_declarations')
                          else 'No local target statement registered')
            certs = supporting_certificates(p, records, certificates)
            certificate = 'No paper-target certificate'
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
            statements += [f'- [Target scope review](../../{p["target_review"]}); no registered target certificate.']
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
        'and Euclidean calculus infrastructure. Existing supporting tools do not certify either paper.', '',
        '## Source and coverage notes', '',
        '- July statements are pinned to `2607.23307v1` and `2607.24164v1`. Both are preprints;',
        '  this map checks bibliographic data, main statements and normalization, not every proof step.',
        '- The 2025 parallel-coupling preprint is read at `2507.15495v2` (23 February 2026).',
        '- The book’s coefficient 4 is a recorded statement; our one-dimensional proof is independent.',
        '  The original attribution remains distinct from mathematical proof and formal verification:',
        '  see the [source audit](../explorations/2026-09-11-poincare-constant-4-audit.md).',
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
        readme.append(f'| [{p["authors"]}, {p["date"]}]({p["url"]}) · {p["publication"]} | {c(p["result"])} | {views.status_cell(coverage(p, records))} |')
    readme += ['', 'Here ψ is the inverse Cheeger constant, so its logarithmic exponent is half the',
               'Poincaré exponent. The sharp thin-shell result does not resolve dimension-free KLS.',
               'See the [full tables and normalization](LITERATURE.md#constant-conventions).']
    return {'LITERATURE.md': '\n'.join(header + tables + statements + footer), 'LITERATURE.mmd': tree}, '\n'.join(readme)
