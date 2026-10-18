"""Regression checks for source-bound compiler API observations and safe rendering."""
from pathlib import Path
import json
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import api_index


class APIIndexTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        path = self.root / 'formalization/FunctionalInequalities/Analysis/Test.lean'
        path.parent.mkdir(parents=True)
        path.write_text('def value := 1\n')
        (self.root / 'formalization/FunctionalInequalities.lean').write_text('')
        self.inventory = {'count': 1, 'families': {'Analysis': 1}, 'modules': [
            {'module': 'FunctionalInequalities.Analysis.Test', 'path': 'Analysis/Test.lean'}]}
        self.row = {'name': 'FunctionalInequalities.Analysis.value', 'module': 'FunctionalInequalities.Analysis.Test',
                    'kind': 'definition', 'type': 'Nat', 'universes': [], 'unsafe': False, 'partial': False,
                    'source_line': 1, 'source_end_line': 1, 'docstring': 'A value.'}

    def payload(self, rows=None):
        return {'modules': ['FunctionalInequalities', 'FunctionalInequalities.Analysis.Test'],
                'declarations': rows if rows is not None else [dict(self.row)]}

    def test_ownership_and_source_link_are_derived_from_compiler_module(self):
        rows = api_index.validate_payload(self.payload(), self.root, self.inventory)
        self.assertEqual(rows[0]['source_path'], 'formalization/FunctionalInequalities/Analysis/Test.lean')
        self.assertEqual(rows[0]['family'], 'Analysis')

    def test_observation_imports_every_inventory_module_beyond_the_aggregate(self):
        driver = self.root / api_index.DRIVER
        driver.parent.mkdir(parents=True)
        driver.write_text('import Lean\n\nrun_cmd pure ()\n')
        source = api_index.observation_source(self.root, self.inventory)
        self.assertIn('import FunctionalInequalities.Analysis.Test\n', source)
        self.assertIn('import FunctionalInequalities\n', source)
        self.assertEqual(source.count('import Lean\n'), 1)
        self.assertIn('run_cmd pure ()', source)

    def test_missing_imported_module_rejects_partial_inventory(self):
        payload = self.payload()
        payload['modules'].pop()
        with self.assertRaisesRegex(ValueError, 'coverage'):
            api_index.validate_payload(payload, self.root, self.inventory)

    def test_duplicate_and_private_names_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            api_index.validate_payload(self.payload([self.row, self.row]), self.root, self.inventory)
        row = {**self.row, 'name': '_private.Test.0.value'}
        with self.assertRaisesRegex(ValueError, 'Private/internal'):
            api_index.validate_payload(self.payload([row]), self.root, self.inventory)

    def test_stale_source_ranges_are_rejected(self):
        for start, end in [(7, 8), (None, 1), (1, None)]:
            row = {**self.row, 'source_line': start, 'source_end_line': end}
            with self.assertRaisesRegex(ValueError, 'source range'):
                api_index.validate_payload(self.payload([row]), self.root, self.inventory)

    def test_generated_support_may_have_no_range_or_docstring(self):
        row = {**self.row, 'source_line': None, 'source_end_line': None, 'docstring': None}
        self.assertIsNone(api_index.validate_payload(self.payload([row]), self.root, self.inventory)[0]['source_line'])

    def test_script_termination_in_source_text_is_escaped(self):
        row = {**self.row, 'docstring': '</script><script>alert(1)</script>'}
        output = api_index.render_html([row], 'abc')
        self.assertNotIn('</script><script>alert', output)
        self.assertIn('\\u003c/script>', output)
        self.assertIn('textContent', output)
        self.assertIn("' :\\n'", output)
        data = re.search(r'<script type="application/json" id="data">(.*?)</script>', output, re.S)[1]
        self.assertEqual(json.loads(data), [row])

    def test_nested_output_source_links_use_the_actual_relative_root(self):
        output = api_index.render_html([self.row], 'abc', '../../../../')
        self.assertIn('sourcePrefix="../../../../"', output)
        self.assertIn('a.href=sourcePrefix+r.source_path', output)

    def test_generated_navigation_does_not_infer_proof_status(self):
        rows = api_index.validate_payload(self.payload(), self.root, self.inventory)
        output = api_index.render_entry(rows, self.inventory, 'abc')
        self.assertIn('assigns no proof, paper-coverage or certificate status', output)
        self.assertIn('build/api-index/index.html', output)
        self.assertNotIn('| proved |', output)

    def test_input_digest_changes_for_source_or_generator_change(self):
        self.assertNotEqual(api_index.digest({'module': 'a', 'generator': 'b'}),
                            api_index.digest({'module': 'a', 'generator': 'c'}))

    def test_output_cannot_overwrite_source_or_configuration(self):
        for value in ['formalization', '.cursor', 'build', 'build/../research']:
            with self.assertRaises(ValueError):
                api_index.output_path(self.root, value)
        self.assertEqual(api_index.output_path(self.root, 'build/api-index'), (self.root / 'build/api-index').resolve())


if __name__ == '__main__':
    unittest.main()
