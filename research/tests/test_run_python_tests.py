"""Check real unittest result accounting and the explicit Comparator opt-in."""
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from run_python_tests import comparator_bundled_enabled, run_tests, test_summary


class PythonCoverageTests(unittest.TestCase):
    def test_only_one_enables_bundled_comparator(self):
        for value in [None, "", "0", "false", "true", "1"]:
            with self.subTest(value=value), patch.dict("os.environ", {}, clear=True):
                if value is not None:
                    with patch.dict("os.environ", {"KLS_COMPARATOR_BUNDLED": value}):
                        self.assertEqual(comparator_bundled_enabled(), value == "1")
                else:
                    self.assertFalse(comparator_bundled_enabled())

    def run_fixture(self, code, *, require_no_skips=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tests = root / "research/tests"
            tests.mkdir(parents=True)
            # Different module names avoid unittest's import-path collision across fixtures.
            module = "test_" + root.name.replace("-", "_")
            (tests / (module + ".py")).write_text("import unittest\n" + code)
            output = root / "result.json"
            try:
                with redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()):
                    status = run_tests(root, output, require_no_skips=require_no_skips)
                return status, json.loads(output.read_text())
            finally:
                sys.modules.pop(module, None)
                if str(tests) in sys.path:
                    sys.path.remove(str(tests))

    def test_skip_counts_and_reasons_are_retained(self):
        code = '''class Probe(unittest.TestCase):
    def test_pass(self): pass
    @unittest.skip("explicit optional probe")
    def test_skip(self): pass
'''
        status, report = self.run_fixture(code)
        self.assertEqual(status, 0)
        self.assertEqual((report["tests_run"], report["skipped"]), (2, 1))
        self.assertEqual(report["skip_reasons"][0]["reason"], "explicit optional probe")
        status, report = self.run_fixture(code, require_no_skips=True)
        self.assertEqual(status, 1)
        self.assertEqual(report["status"], "failed")
        self.assertEqual(report["skipped"], 1)

    def test_failures_errors_and_expected_failures_are_distinct(self):
        status, report = self.run_fixture('''class Probe(unittest.TestCase):
    def test_failure(self): self.fail("failure")
    def test_error(self): raise RuntimeError("error")
    @unittest.expectedFailure
    def test_expected(self): self.fail("expected")
    @unittest.expectedFailure
    def test_unexpected_success(self): pass
''')
        self.assertEqual(status, 1)
        self.assertEqual(report["tests_run"], 4)
        for field in ["failures", "errors", "expected_failures", "unexpected_successes"]:
            self.assertEqual(report[field], 1, field)

    def test_import_failure_is_a_failed_test(self):
        status, report = self.run_fixture('raise RuntimeError("cannot import tests")\n')
        self.assertEqual(status, 1)
        self.assertEqual(report["errors"], 1)

    def test_empty_discovery_cannot_pass(self):
        status, report = self.run_fixture("")
        self.assertEqual((status, report["tests_run"]), (1, 0))

    def test_profile_records_the_actual_environment(self):
        result = unittest.TestResult()
        result.testsRun = 1
        with patch.dict("os.environ", {"KLS_COMPARATOR_BUNDLED": "0"}):
            self.assertEqual(test_summary(result)["profile"], "standard")
        with patch.dict("os.environ", {"KLS_COMPARATOR_BUNDLED": "1"}):
            self.assertEqual(test_summary(result)["profile"], "comparator-bundled")


if __name__ == "__main__":
    unittest.main()
