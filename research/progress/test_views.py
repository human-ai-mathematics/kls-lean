"""Regression checks for proof-status propagation and generated-view drift."""
import json
from pathlib import Path
import unittest
from unittest.mock import patch
import update
import views

HERE = Path(__file__).resolve().parent


class ProgressViewsTests(unittest.TestCase):
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
            readme = views.render_routes(template, tree, catalog, records, portfolio)
            self.assertIn(f'X["{marker} Example"]', tree)
            self.assertIn(f'| Example | {views.status_cell(records["x"]["state"])} |', readme)

    def test_missing_route_input_is_rejected(self):
        catalog = json.loads((HERE / 'nodes.json').read_text())
        routes = json.loads(update.staged('research/explorations/route-composition.yaml'))
        catalog['diagram']['edges'] = [e for e in catalog['diagram']['edges'] if e['from'] != 'EG']
        with self.assertRaisesRegex(ValueError, 'missing required route inputs'):
            views.validate_routes(catalog, catalog['nodes'], routes)

    def test_generated_outputs_are_current_and_repair_tampering(self):
        outputs = update.generate()
        for name, content in outputs.items():
            self.assertEqual((HERE / name).read_text(), content, name)
        original = outputs['../explorations/ROUTES.md']
        damaged = original.replace('✓ Affine / isotropic', '○ Affine / isotropic', 1)
        self.assertNotEqual(original, damaged)
        # Generated tree replacement must repair the damaged block independently of its old content.
        repaired = views.replace_block(damaged, 'TREE', '```mermaid\n'+outputs['../explorations/ROUTES.mmd']+'```')
        self.assertEqual(original, repaired)

    def test_primary_tree_uses_papers_and_exploratory_routes_stay_separate(self):
        outputs = update.generate()
        self.assertIn('L_KLS1995', outputs['TREE.mmd'])
        self.assertNotIn('ANY --> KLS', outputs['TREE.mmd'])
        self.assertNotIn('BEGIN GENERATED APPROACHES', outputs['README.md'])
        self.assertIn('ANY --> KLS', outputs['../explorations/ROUTES.mmd'])
        self.assertIn('not formalization targets', outputs['../explorations/ROUTES.md'])
        self.assertIn('../progress/badges/', outputs['../explorations/ROUTES.md'])

    def test_unstaged_view_metadata_cannot_change_generated_claims(self):
        expected = update.generate()
        original_read = Path.read_text
        canonical = {'nodes.json', 'portfolio.json', 'literature.json'}

        def poisoned_working_copy(path, *args, **kwargs):
            if path.parent in {HERE, HERE.parent / 'explorations'} and path.name in canonical:
                return 'unrelated unstaged content, deliberately invalid JSON'
            return original_read(path, *args, **kwargs)

        with patch.object(Path, 'read_text', poisoned_working_copy):
            self.assertEqual(update.generate(), expected)


if __name__ == '__main__':
    unittest.main()
