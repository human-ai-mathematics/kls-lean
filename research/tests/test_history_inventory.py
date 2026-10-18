"""History indexes are optional local artifacts, never fresh-clone dependencies."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "inventory_artifacts.py"


class HistoryInventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        (self.root / "AGENTS.md").write_text("Current project rules.\n")
        (self.root / ".gitignore").write_text("/build/\n")

    def run_inventory(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), "--root", str(self.root),
                               "--output", "build/inventory", *args],
                              capture_output=True, text=True, timeout=20)

    def test_fresh_clone_needs_no_history_directory(self):
        result = self.run_inventory()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        output = self.root / "build/inventory"
        self.assertEqual(json.loads((output / "inventory.json").read_text())["index_candidates"], [])
        self.assertFalse((output / "decisions-index.md").exists())

    def test_explicit_archive_indexes_link_to_untouched_local_originals(self):
        history = self.root / "build/history/originals/research"
        originals = {}
        for name in ("decisions", "handoffs"):
            path = history / name / "record.md"
            path.parent.mkdir(parents=True)
            path.write_text("Original historical claim.\n")
            originals[path] = path.read_bytes()
        result = self.run_inventory("--history-root", str(history))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        output = self.root / "build/inventory"
        records = json.loads((output / "inventory.json").read_text())["index_candidates"]
        self.assertEqual(len(records), 2)
        self.assertTrue(all(row["local_only"] for row in records))
        for name in ("decisions", "handoffs"):
            self.assertIn(f"../history/originals/research/{name}/record.md",
                          (output / f"{name}-index.md").read_text())
        for path, original in originals.items():
            self.assertEqual(path.read_bytes(), original)
        self.assertFalse((self.root / "research").exists())

    def test_external_and_symlinked_history_roots_are_rejected(self):
        external = self.root / "external"
        external.mkdir()
        result = self.run_inventory("--history-root", str(external))
        self.assertNotEqual(result.returncode, 0)
        linked = self.root / "build/history/linked"
        linked.parent.mkdir(parents=True)
        linked.symlink_to(external, target_is_directory=True)
        result = self.run_inventory("--history-root", str(linked))
        self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
