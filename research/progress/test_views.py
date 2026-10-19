"""Regression checks for proof-status propagation and generated-view drift."""
import json
import copy
from pathlib import Path
import tempfile
import unittest
import atlas
import update
import views

HERE = Path(__file__).resolve().parent


class ProgressViewsTests(unittest.TestCase):
    def route_fixture(self):
        kinds = {'hypothesis': 'assumption', 'question': 'question', 'result': 'theorem',
                 'lemma': 'lemma', 'corollary': 'corollary', 'proposition': 'proposition',
                 'yaml_only': 'lemma', 'proved': 'theorem', 'main': 'theorem',
                 'main_input': 'lemma', 'shared': 'lemma', 'unrelated': 'theorem',
                 'context': 'theorem'}
        proved = {'proved', 'main', 'main_input'}
        blueprint = {k: {'kind': kind, 'dependencies': [], 'lean': {
            'recorded': k in proved, 'declarations': ['Example'] if k in proved else []},
            'proof_leanok': k in proved} for k, kind in kinds.items()}
        blueprint['result']['dependencies'] = ['hypothesis', 'question', 'lemma', 'corollary',
                                               'proposition', 'proved']
        blueprint['main']['dependencies'] = ['main_input']
        records = {k: {'description': 'A fixture statement.', 'blueprint': k} for k in kinds}
        records['main']['route_branch'] = 'main-branch'
        for key in ('result', 'main', 'shared', 'context'):
            records[key]['diagram'] = {'id': key, 'label': key, 'shape': 'box', 'source': 'source'}
        records['old'] = {'description': 'Historical route.', 'route_branch': 'old-branch',
                          'assessment': {'kind': 'route', 'state': 'partial',
                                         'evidence': {'source': 'route-composition.yaml'}},
                          'diagram': {'id': 'OLD', 'label': 'AND<br/>Old route',
                                      'shape': 'diamond', 'source': 'source'}}
        catalog = {'nodes': records, 'route_display': {
            'accepted_main_line': 'main', 'shared_groups': ['SHARED']}, 'diagram': {
                'groups': [{'id': 'SHARED', 'title': 'Shared analysis', 'nodes': ['shared']}],
                'edges': [{'from': k, 'to': 'OLD', 'kind': 'dependency'}
                          for k in ('result', 'main', 'shared')] + [
                              {'from': 'context', 'to': 'OLD', 'kind': 'context'}]}}
        routes = {'branches': [
            {'id': 'main-branch', 'disposition': 'active', 'requires': {'node': 'main'}},
            {'id': 'old-branch', 'disposition': 'active', 'requires': {
                'operator': 'all_of', 'items': [{'node': 'result'}, {'node': 'yaml_only'}]}}]}
        return catalog, blueprint, routes

    def test_hypotheses_and_superseded_membership_preserve_proofs_and_shared_inputs(self):
        catalog, blueprint, routes = self.route_fixture()
        records = views.resolve(catalog, blueprint, {'result': {'state': 'proved'}}, routes)
        self.assertEqual({k for k, r in records.items() if r['state'] == 'hypothesis'},
                         {'hypothesis', 'question'})
        self.assertEqual({k for k, r in records.items() if r['state'] == 'superseded'},
                         {'result', 'lemma', 'corollary', 'proposition', 'yaml_only'})
        self.assertEqual(records['old']['state'], 'partial')
        for key in ('proved', 'main', 'main_input'):
            self.assertEqual(records[key]['state'], 'formalized', key)
        for key in ('shared', 'unrelated', 'context'):
            self.assertEqual(records[key]['state'], 'pending', key)
        self.assertEqual(catalog['nodes']['old']['assessment']['state'], 'partial')
        self.assertEqual(blueprint['result']['proof_leanok'], False)

    def test_refuted_state_takes_precedence_over_hypothesis_and_supersession(self):
        catalog, blueprint, routes = self.route_fixture()
        records = views.resolve(catalog, blueprint, {
            k: {'state': 'refuted'} for k in ('hypothesis', 'result')}, routes)
        for key in ('hypothesis', 'result'):
            self.assertEqual(records[key]['state'], 'excluded')

    def test_explicit_hypothesis_annotations_are_rejected_on_blueprint_records(self):
        for kind in ('theorem', 'lemma', 'corollary', 'proposition', 'definition',
                     'assumption', 'question'):
            for complete in (False, True):
                with self.subTest(kind=kind, complete=complete):
                    catalog = {'nodes': {'x': {'description': 'A mapped statement.',
                                              'blueprint': 'x', 'display_state': 'hypothesis'}}}
                    blueprint = {'x': {'kind': kind, 'lean': {
                        'recorded': complete, 'declarations': ['Example'] if complete else []},
                        'proof_leanok': complete}}
                    with self.assertRaisesRegex(ValueError, 'only on unmapped assessment records'):
                        views.resolve(catalog, blueprint, {})

    def test_explicit_hypothesis_annotations_can_mark_unmapped_assessments(self):
        catalog, blueprint, routes = self.route_fixture()
        catalog['nodes']['auxiliary_question'] = {
            'description': 'An explicitly recorded open question.',
            'display_state': 'hypothesis',
            'assessment': {'kind': 'approach', 'state': 'pending',
                           'evidence': {'source': 'research-note'}}}
        records = views.resolve(catalog, blueprint, {}, routes)
        self.assertEqual(records['auxiliary_question']['state'], 'hypothesis')
        self.assertEqual(records['result']['state'], 'superseded')

    def test_hypothesis_kinds_are_automatic_only_for_blueprint_records(self):
        catalog, blueprint, routes = self.route_fixture()
        for kind in ('assumption', 'question'):
            catalog['nodes'][f'auxiliary_{kind}'] = {
                'description': 'An unmapped assessment.',
                'assessment': {'kind': kind, 'state': 'pending',
                               'evidence': {'source': 'research-note'}}}
        records = views.resolve(catalog, blueprint, {}, routes)
        for kind in ('assumption', 'question'):
            self.assertEqual(records[f'auxiliary_{kind}']['state'], 'pending')

    def test_accepted_main_line_must_be_a_branch_with_a_formalized_requirement_closure(self):
        for accepted in ('old', 'proved', 'main'):
            with self.subTest(accepted=accepted):
                catalog, blueprint, routes = self.route_fixture()
                catalog['route_display']['accepted_main_line'] = accepted
                if accepted == 'main':
                    # A proved direct requirement cannot hide an unproved transitive input.
                    blueprint['main_input']['proof_leanok'] = False
                with self.assertRaisesRegex(ValueError, 'unique route branch.*entirely formalized'):
                    views.resolve(catalog, blueprint, {}, routes)

    def test_accepted_main_line_must_be_unique_from_recorded_route_requirements(self):
        catalog, blueprint, routes = self.route_fixture()
        for node in blueprint.values():
            node['lean'] = {'recorded': True, 'declarations': ['Example']}
            node['proof_leanok'] = True
        # The old branch's YAML-only input must count even though it has no diagram edge.
        blueprint['yaml_only']['proof_leanok'] = False
        views.resolve(catalog, blueprint, {}, routes)
        blueprint['yaml_only']['proof_leanok'] = True
        with self.assertRaisesRegex(ValueError, 'unique route branch.*entirely formalized'):
            views.resolve(catalog, blueprint, {}, routes)

    def test_shared_groups_cannot_hide_route_branch_records(self):
        for key in ('old', 'main', 'local_route'):
            with self.subTest(branch=key):
                catalog, blueprint, routes = self.route_fixture()
                if key == 'local_route':
                    catalog['nodes'][key] = {
                        'description': 'A separate literature route.',
                        'assessment': {'kind': 'logic', 'state': 'logic',
                                       'evidence': {'source': 'literature'}},
                        'diagram': {'id': 'LOCAL', 'label': 'AND<br/>Literature route',
                                    'shape': 'diamond', 'source': 'source'}}
                catalog['diagram']['groups'][0]['nodes'].append(
                    catalog['nodes'][key]['diagram']['id'])
                with self.assertRaisesRegex(ValueError, 'must not contain a route-branch record'):
                    views.resolve(catalog, blueprint, {}, routes)

    def test_route_classification_requires_records_and_does_not_guess_from_names(self):
        catalog, blueprint, routes = self.route_fixture()
        with self.assertRaisesRegex(ValueError, 'needs route-composition records'):
            views.resolve(catalog, blueprint, {})
        # Removing the recorded dependency removes membership even though the name is unchanged.
        blueprint['result']['dependencies'].remove('lemma')
        records = views.resolve(catalog, blueprint, {}, routes)
        self.assertEqual(records['lemma']['state'], 'pending')
        catalog['route_display']['shared_groups'] = ['missing']
        with self.assertRaisesRegex(ValueError, 'unknown shared analytic group'):
            views.resolve(catalog, blueprint, {}, routes)

    def test_new_badges_tree_classes_and_legend_agree_even_with_focus(self):
        catalog, blueprint, routes = self.route_fixture()
        records = views.resolve(catalog, blueprint, {}, routes)
        records['hypothesis']['diagram'] = {'id': 'HYP', 'label': 'Open question',
                                           'shape': 'box', 'source': 'source', 'focus': True}
        records['old']['diagram']['focus'] = True
        tree = views.render_tree(catalog, records)
        self.assertIn('HYP["◇ Open question"]', tree)
        self.assertIn('OLD{"AND<br/>◐ Old route"}', tree)
        self.assertIn('class HYP hypothesis;', tree)
        self.assertIn('class result superseded;', tree)
        self.assertIn('class OLD focus;', tree)
        badges = views.render_badges()
        for state in ('hypothesis', 'superseded'):
            self.assertIn(views.status_cell(state), views.status_legend())
            self.assertIn('aria-label="' + views.STATES[state] + '"', badges[f'badges/{state}.svg'])
            self.assertIn('classDef ' + state + ' ' + views.STYLES[state], tree)
            self.assertNotIn('#dc2626', views.STYLES[state])
        self.assertIn('accepted BKL main line', views.status_legend())
        self.assertIn('historical records', views.status_legend())
        self.assertIn('Open hypotheses remain open mathematically', views.status_legend())
        self.assertIn('their unproved hypotheses remain open mathematically', views.status_legend())

    def test_canonical_classification_has_no_formalization_status_changes(self):
        catalog = json.loads(update.staged('research/progress/nodes.json'))
        routes = json.loads(update.staged('formalization/blueprint/route-composition.yaml'))
        with tempfile.TemporaryDirectory(prefix='kls-view-test-') as directory:
            root = Path(directory)
            for name, content in update.load_inputs().items():
                if name.endswith('.tex'):
                    path = root / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(content)
            blueprint, errors = atlas.parse_nodes(root)
        self.assertFalse(errors)
        claims = {c['node']: c for c in routes['claims']}
        records = views.resolve(catalog, blueprint, claims, routes)
        baseline = copy.deepcopy(catalog)
        baseline.pop('route_display')
        original = views.resolve(baseline, blueprint, claims)
        for state in ('formalized', 'excluded'):
            self.assertEqual({k for k, r in records.items() if r['state'] == state},
                             {k for k, r in original.items() if r['state'] == state})
        self.assertEqual({k for k, r in records.items() if r['state'] == 'hypothesis'}, {
            'ass:cmh-recovery-envelope', 'ass:tight-prefix-carleson', 'q:conditional-fiber-frame',
            'q:mm-spectral-occupation', 'q:smooth-gradient-raw-core-agreement'})
        self.assertEqual({k for k, r in records.items() if r['state'] == 'superseded'}, {
            'cor:cmh-recovery-sequence-suffices', 'cor:tight-window-consumption',
            'prop:spectral-sufficiency', 'thm:cmh-recovery-affine-poincare-bound',
            'diagram:EAND', 'diagram:SAND', 'diagram:MAND'})
        self.assertEqual(records['diagram:FAND']['state'], 'partial')

    def test_upstream_proof_does_not_become_lean_proof(self):
        catalog = {'nodes': {'x': {'description': 'A claim.', 'blueprint': 'x'}}}
        node = {'kind': 'theorem', 'lean': {'recorded': False, 'declarations': []}, 'proof_leanok': False}
        records = views.resolve(catalog, {'x': node}, {'x': {'state': 'proved'}})
        self.assertEqual(records['x']['state'], 'pending')
        catalog['nodes']['x']['assessment'] = {'state': 'formalized'}
        with self.assertRaisesRegex(ValueError, 'must not be overridden'):
            views.resolve(catalog, {'x': node}, {})

    def test_one_proof_update_changes_tree_and_result_table(self):
        catalog = {'last_updated': '2026-09-15', 'nodes': {'x': {
            'description': 'An example claim.', 'blueprint': 'x',
            'diagram': {'id': 'X', 'label': 'Example', 'shape': 'box', 'source': 'https://example.org/proof'}}},
            'diagram': {'groups': [], 'edges': []}}
        node = {'kind': 'theorem', 'lean': {'recorded': True, 'declarations': ['Example']}, 'proof_leanok': False}
        template = '\n'.join(f'<!-- BEGIN GENERATED {k} -->\n<!-- END GENERATED {k} -->' for k in ['TREE','DATE','APPROACHES','RESULTS','LINKS'])
        portfolio = {'approaches': [], 'source': 'https://example.org', 'revision': '1234567'}
        for complete, marker in [(False, '○'), (True, '✓')]:
            node['proof_leanok'] = complete
            records = views.resolve(catalog, {'x': node}, {})
            tree = views.render_tree(catalog, records)
            readme = views.render_readme(template, tree, catalog, records, portfolio)
            self.assertIn(f'X["{marker} Example"]', tree)
            self.assertIn(f'| Example | {views.status_cell(records["x"]["state"])} |', readme)

    def test_missing_route_input_is_rejected(self):
        catalog = json.loads(update.staged('research/progress/nodes.json'))
        routes = json.loads(update.staged('formalization/blueprint/route-composition.yaml'))
        catalog['diagram']['edges'] = [e for e in catalog['diagram']['edges'] if e['from'] != 'EG']
        with self.assertRaisesRegex(ValueError, 'missing required route inputs'):
            views.validate_routes(catalog, catalog['nodes'], routes)

    def test_generated_outputs_are_current_and_repair_tampering(self):
        outputs = update.generate()
        for name, content in outputs.items():
            self.assertEqual((HERE / name).read_text(), content, name)
        original = outputs['README.md']
        damaged = original.replace('✓ Affine / isotropic', '○ Affine / isotropic', 1)
        self.assertNotEqual(original, damaged)
        # Generated tree replacement must repair the damaged block independently of its old content.
        repaired = views.replace_block(damaged, 'TREE', '```mermaid\n'+outputs['TREE.mmd']+'```')
        self.assertEqual(original, repaired)


if __name__ == '__main__':
    unittest.main()
