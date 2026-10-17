"""Regressions for the BKL pilot's independence and definition-closure drift boundary."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / 'research/audits/BKL/IndependentTargets'
sys.path.insert(0, str(ROOT / 'research'))
import statement_snapshot
spec = importlib.util.spec_from_file_location('bkl_target_check_runner', HERE / 'run.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class BKLTargetCheckTests(unittest.TestCase):
    def test_mutation_requires_the_expected_type_error_not_an_import_or_tool_failure(self):
        self.assertTrue(runner.rejected_mutation('BKLIndependentChecks.lean:84:52: error: unsolved goals', 'factorial'))
        self.assertTrue(runner.rejected_mutation('BKLIndependentChecks.lean:1:2: error: Type mismatch', 'coefficient'))
        self.assertTrue(runner.rejected_mutation('BKLIndependentChecks.lean:1:2: error: Application type mismatch', 'dimension'))
        self.assertFalse(runner.rejected_mutation('error: missing module', 'dimension'))
        self.assertFalse(runner.rejected_mutation('BKLIndependentChecks.lean:1:2: error: unknown module', 'coefficient'))

    def test_standalone_specification_has_no_project_import_or_placeholder(self):
        source = (HERE / 'Specification.lean.in').read_text()
        self.assertTrue(all(m.startswith('Mathlib.') for m in runner.specification_guard(source)))
        for addition in ['\nimport solutions.ThmBklTaylorCriterion\n', '\naxiom fake : False\n',
                         '\ntheorem fake : True := by sorry\n']:
            with self.subTest(addition=addition), self.assertRaises(ValueError):
                runner.specification_guard(source + addition)

    def test_all_requested_roots_are_captured_in_the_reviewed_baseline(self):
        config = json.loads((HERE / 'config.json').read_text())
        golden = json.loads((HERE / 'golden.json').read_text())
        self.assertEqual(golden['roots'], config['roots'])
        self.assertTrue(set(config['roots']) <= {d['name'] for d in golden['declarations']})
        self.assertEqual(golden['decision'], statement_snapshot.decision_record(ROOT, config['review']))

    def test_key_definition_change_is_detected_even_without_changing_the_target_type(self):
        golden = json.loads((HERE / 'golden.json').read_text())
        changed = copy.deepcopy(golden)
        target = next(d for d in changed['declarations'] if d['name'] == 'BKLIndependent.Taylor')
        target['value'] += '\nchanged factorial encoding'
        errors = statement_snapshot.compare_snapshot(changed, golden)
        self.assertIn('statement dependency changed: BKLIndependent.Taylor', errors)

    def test_certificate_quantifier_or_hypothesis_drift_is_detected(self):
        golden = json.loads((HERE / 'golden.json').read_text())
        changed = copy.deepcopy(golden)
        target = next(d for d in changed['declarations'] if d['name'] == 'Solutions.PropBklSuspension.certificate')
        target['type'] += '\nchanged universal-dimensional hypothesis'
        errors = statement_snapshot.compare_snapshot(changed, golden)
        self.assertIn('statement dependency changed: Solutions.PropBklSuspension.certificate', errors)

    def test_named_boundary_definition_and_module_disappearance_are_detected(self):
        golden = json.loads((HERE / 'golden.json').read_text())
        changed = copy.deepcopy(golden)
        name = 'FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant'
        changed['declarations'] = [d for d in changed['declarations'] if d['name'] != name]
        self.assertIn('statement dependency removed: ' + name,
                      statement_snapshot.compare_snapshot(changed, golden))
        modules = runner.closure(['solutions.ThmBklTaylorCriterion', 'solutions.PropBklSuspension'])
        self.assertIn('FunctionalInequalities.KLS.LogConcave.Regular.Basic', modules)
        self.assertNotIn('FunctionalInequalities.KLS.Target', modules)


if __name__ == '__main__':
    unittest.main()
