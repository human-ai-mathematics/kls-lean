"""Long-running gates expose live logs and retain nonzero exits and stdin behavior."""
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify import run_logged_command


class VerificationProgressTests(unittest.TestCase):
    def run_child(self, program, *, release_on_progress=False, **kwargs):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / "gate.log"
            observed = []

            def progress(metrics):
                observed.append(metrics)
                if release_on_progress and metrics["last_output"] == "building fixture":
                    # The child waits for this acknowledgment before it can finish.
                    self.assertNotIn("finished", log.read_text())
                    (root / "continue").touch()

            result = run_logged_command([sys.executable, "-u", "-c", program], cwd=root,
                                        logfile=log, env=dict(os.environ), interval=0.02,
                                        progress=progress, **kwargs)
            return result, log.read_text(), observed

    def test_live_output_is_observable_before_completion(self):
        result, output, observed = self.run_child(
            "import time\nfrom pathlib import Path\nprint('building fixture', flush=True)\n"
            "deadline = time.monotonic() + 5\n"
            "while not Path('continue').exists() and time.monotonic() < deadline: time.sleep(0.005)\n"
            "assert Path('continue').exists()\nprint('finished')",
            release_on_progress=True)
        self.assertEqual(result.returncode, 0)
        self.assertIn("finished", output)
        self.assertTrue(observed)
        self.assertTrue(any(m["last_output"] == "building fixture" for m in observed))
        self.assertTrue(all(m["free_disk_bytes"] > 0 for m in observed))

    def test_failure_exit_and_output_are_preserved(self):
        result, output, _ = self.run_child("import sys; print('rejected proof'); sys.exit(7)")
        self.assertEqual(result.returncode, 7)
        self.assertEqual(output, "rejected proof\n")

    def test_source_input_is_forwarded_without_shell_interpretation(self):
        payload = "literal `text` and $(not_a_command)\n"
        result, output, _ = self.run_child("import sys; sys.stdout.write(sys.stdin.read())",
                                         code=payload)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(output, payload)

    def test_silent_process_still_reports_progress(self):
        result, output, observed = self.run_child("import time; time.sleep(0.12)")
        self.assertEqual(result.returncode, 0)
        self.assertEqual(output, "")
        self.assertTrue(observed)
        self.assertTrue(all(m["last_output"] == "(no output yet)" for m in observed))


if __name__ == "__main__":
    unittest.main()
