"""Exercise the vendored-library provenance lock against local fixture upstream repositories."""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import vendor_lock


class TestVendorLock(unittest.TestCase):
    def setUp(self) -> None:
        self.real_pins = dict(vendor_lock.PINS)
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name) / "repo"
        self.root.mkdir()
        self.fake_pins, self.clones = self._build_fixture()
        self.pin_patch = patch.dict(vendor_lock.PINS, self.fake_pins, clear=True)
        self.pin_patch.start()

    def tearDown(self) -> None:
        self.pin_patch.stop()
        self.temp.cleanup()

    def _git(self, directory: Path, *arguments: str) -> str:
        result = subprocess.run(
            ["git", "-C", str(directory), *arguments],
            capture_output=True,
            check=True,
            text=True,
        )
        return result.stdout.strip()

    def _commit_repo(self, directory: Path) -> str:
        subprocess.run(
            ["git", "-C", str(directory), "add", "."],
            capture_output=True,
            check=True,
        )
        subprocess.run(
            [
                "git",
                "-C",
                str(directory),
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@t",
                "commit",
                "-qm",
                "fixture",
            ],
            capture_output=True,
            check=True,
        )
        return self._git(directory, "rev-parse", "HEAD")

    def _write(self, path: Path, data: bytes) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    def _build_fixture(self) -> tuple[dict[str, dict[str, str]], dict[str, Path]]:
        vendor = self.root / vendor_lock.VENDOR_DIR
        vendor.mkdir(parents=True)
        self._write(vendor / "README.md", b"fixture\n")
        self._write(
            vendor / ".gitattributes",
            b"# Unified-diff context lines for empty source lines are a single space.\n"
            b"port.patch -whitespace\n",
        )

        roots = ["LevyStochCalc", "BrownianMotion", "KolmogorovExtension4", "MathFin"]
        module_paths = {
            "LevyStochCalc": "LevyStochCalc/Basic.lean",
            "BrownianMotion": "BrownianMotion/Basic.lean",
            "KolmogorovExtension4": "KolmogorovExtension4/Basic.lean",
            "MathFin": "MathFin/Foundations/Basic.lean",
        }
        old_levy = b"module LevyStochCalc.Basic\n\nold\nend"
        new_levy = b"module LevyStochCalc.Basic\n\nnew\nend\n"
        module_bytes = {
            "LevyStochCalc": old_levy,
            "BrownianMotion": b"module BrownianMotion.Basic\n",
            "KolmogorovExtension4": b"module KolmogorovExtension4.Basic\n",
            "MathFin": b"module MathFin.Foundations.Basic\n",
        }

        clones: dict[str, Path] = {}
        commits: dict[str, str] = {}
        for name in roots:
            clone = self.root / "upstream" / name
            clone.mkdir(parents=True)
            subprocess.run(["git", "-C", str(clone), "init", "-q"], check=True)
            self._write(clone / "lean-toolchain", b"leanprover/lean4:v4.32.0\n")
            self._write(clone / "LICENSE", f"{name} license\n".encode())
            self._write(clone / module_paths[name], module_bytes[name])
            clones[name] = clone

        for name in ("BrownianMotion", "KolmogorovExtension4", "MathFin"):
            commits[name] = self._commit_repo(clones[name])

        mathlib_commit = "a" * 40
        manifest = {
            "packages": [
                {"name": "BrownianMotion", "rev": commits["BrownianMotion"]},
                {"name": "MathFin", "rev": commits["MathFin"]},
                {
                    "name": "kolmogorov_extension4",
                    "rev": commits["KolmogorovExtension4"],
                },
                {"name": "mathlib", "rev": mathlib_commit},
            ]
        }
        self._write(
            clones["LevyStochCalc"] / "lake-manifest.json",
            (json.dumps(manifest) + "\n").encode(),
        )
        commits["LevyStochCalc"] = self._commit_repo(clones["LevyStochCalc"])

        fake_pins = {
            name: {
                "repository": f"https://example.invalid/{name}",
                "commit": commits[name],
                "upstream_toolchain": "leanprover/lean4:v4.32.0",
                "upstream_mathlib": mathlib_commit,
                "license": "Apache-2.0",
            }
            for name in roots
        }

        for name in roots:
            vendor_root = vendor / name
            self._write(vendor_root / "LICENSE", f"{name} license\n".encode())
            self._write(
                vendor_root / module_paths[name],
                new_levy if name == "LevyStochCalc" else module_bytes[name],
            )

        patch = (
            b"--- a/LevyStochCalc/LevyStochCalc/Basic.lean\n"
            b"+++ b/LevyStochCalc/LevyStochCalc/Basic.lean\n"
            b"@@ -1,3 +1,3 @@\n"
            b" module LevyStochCalc.Basic\n"
            b" \n"
            b"-old\n"
            b"+new\n"
            b"@@ -4 +4 @@\n"
            b"-end\n"
            b"\\ No newline at end of file\n"
            b"+end\n"
        )
        self._write(vendor / "port.patch", patch)
        return fake_pins, clones

    def _generate_and_write(self) -> dict:
        lock = vendor_lock.generate_lock(self.root, self.clones)
        path = self.root / vendor_lock.VENDOR_DIR / vendor_lock.LOCK_NAME
        path.write_text(
            json.dumps(lock, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        return lock

    def _check(self) -> list[str]:
        _, errors = vendor_lock.check_lock(self.root, set(vendor_lock.PINS))
        return errors

    def _assert_error(self, text: str) -> None:
        errors = self._check()
        self.assertTrue(any(text in error for error in errors), errors)

    def test_generation_checking_and_determinism(self) -> None:
        first = self._generate_and_write()
        first_bytes = (
            self.root / vendor_lock.VENDOR_DIR / vendor_lock.LOCK_NAME
        ).read_bytes()
        second = vendor_lock.generate_lock(self.root, self.clones)
        second_bytes = (
            json.dumps(second, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
        ).encode()
        self.assertEqual(first, second)
        self.assertEqual(first_bytes, second_bytes)
        self.assertEqual(self._check(), [])
        self.assertEqual(vendor_lock.check_upstream(self.root, self.clones), [])

    def test_modified_vendored_file(self) -> None:
        self._generate_and_write()
        path = self.root / vendor_lock.VENDOR_DIR / "BrownianMotion/LICENSE"
        path.write_bytes(path.read_bytes() + b"changed\n")
        self._assert_error("vendored_sha256 mismatch")

    def test_declared_dependency_is_distinct_from_tested_vendor_override(self) -> None:
        original = vendor_lock.PINS["BrownianMotion"]["commit"]
        vendor_lock.PINS["LevyStochCalc"]["upstream_dependencies"] = {
            "BrownianMotion": original,
        }
        path = self.clones["BrownianMotion"] / "BrownianMotion/Basic.lean"
        path.write_bytes(path.read_bytes() + b"-- newer upstream revision\n")
        current = self._commit_repo(self.clones["BrownianMotion"])
        vendor_lock.PINS["BrownianMotion"]["commit"] = current
        target = self.root / vendor_lock.VENDOR_DIR / "BrownianMotion/BrownianMotion/Basic.lean"
        target.write_bytes(path.read_bytes())
        lock = self._generate_and_write()
        self.assertNotEqual(original, current)
        self.assertEqual(lock["libraries"]["LevyStochCalc"]["upstream_dependencies"],
                         {"BrownianMotion": original})
        self.assertEqual(self._check(), [])
        self.assertEqual(vendor_lock.check_upstream(self.root, self.clones), [])

    def test_tampered_declared_dependency_is_rejected_offline(self) -> None:
        vendor_lock.PINS["LevyStochCalc"]["upstream_dependencies"] = {
            "BrownianMotion": vendor_lock.PINS["BrownianMotion"]["commit"],
        }
        lock = self._generate_and_write()
        lock["libraries"]["LevyStochCalc"]["upstream_dependencies"]["BrownianMotion"] = "f" * 40
        path = self.root / vendor_lock.VENDOR_DIR / vendor_lock.LOCK_NAME
        path.write_text(json.dumps(lock))
        self._assert_error("upstream_dependencies does not match PINS")

    def test_incorrect_declared_upstream_dependency_is_rejected_online(self) -> None:
        vendor_lock.PINS["LevyStochCalc"]["upstream_dependencies"] = {
            "BrownianMotion": "f" * 40,
        }
        self._generate_and_write()
        errors = vendor_lock.check_upstream(self.root, self.clones)
        self.assertTrue(any("declared manifest pin mismatch: BrownianMotion" in e for e in errors),
                        errors)

    def test_extra_file(self) -> None:
        self._generate_and_write()
        self._write(
            self.root / vendor_lock.VENDOR_DIR / "MathFin/extra.txt",
            b"extra\n",
        )
        self._assert_error("extra vendored file")

    def test_missing_file(self) -> None:
        self._generate_and_write()
        (self.root / vendor_lock.VENDOR_DIR / "MathFin/LICENSE").unlink()
        self._assert_error("missing vendored file")

    def test_symlink(self) -> None:
        self._generate_and_write()
        target = self.root / vendor_lock.VENDOR_DIR / "MathFin/LICENSE"
        target.unlink()
        try:
            target.symlink_to("does-not-exist")
        except (OSError, NotImplementedError):
            self.skipTest("symlinks are unavailable")
        self._assert_error("symlink")

    def test_modified_patch_hash(self) -> None:
        self._generate_and_write()
        path = self.root / vendor_lock.VENDOR_DIR / "port.patch"
        path.write_bytes(path.read_bytes() + b"\n")
        self._assert_error("patch sha256 does not match")

    def test_patch_touches_file_not_marked_patched(self) -> None:
        lock = self._generate_and_write()
        lock["libraries"]["LevyStochCalc"]["files"][
            "LevyStochCalc/LevyStochCalc/Basic.lean"
        ]["patched"] = False
        (self.root / vendor_lock.VENDOR_DIR / vendor_lock.LOCK_NAME).write_text(
            json.dumps(lock, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        self._assert_error("patch file set does not match patched")

    def test_identical_file_marked_patched(self) -> None:
        lock = self._generate_and_write()
        entry = lock["libraries"]["BrownianMotion"]["files"][
            "BrownianMotion/LICENSE"
        ]
        entry["patched"] = True
        (self.root / vendor_lock.VENDOR_DIR / vendor_lock.LOCK_NAME).write_text(
            json.dumps(lock, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        self._assert_error("patched entries do not match differing")

    def test_wrong_upstream_sha256(self) -> None:
        lock = self._generate_and_write()
        lock["libraries"]["BrownianMotion"]["files"][
            "BrownianMotion/LICENSE"
        ]["upstream_sha256"] = "0" * 64
        (self.root / vendor_lock.VENDOR_DIR / vendor_lock.LOCK_NAME).write_text(
            json.dumps(lock, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        self._assert_error("unpatched file has differing hashes")

    def test_wrong_upstream_git_blob(self) -> None:
        lock = self._generate_and_write()
        lock["libraries"]["BrownianMotion"]["files"][
            "BrownianMotion/LICENSE"
        ]["upstream_git_blob"] = "0" * 40
        (self.root / vendor_lock.VENDOR_DIR / vendor_lock.LOCK_NAME).write_text(
            json.dumps(lock, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        self._assert_error("upstream_git_blob mismatch")

    def test_hunk_context_mismatch(self) -> None:
        self._generate_and_write()
        path = (
            self.root
            / vendor_lock.VENDOR_DIR
            / "LevyStochCalc/LevyStochCalc/Basic.lean"
        )
        path.write_bytes(path.read_bytes().replace(b"\nnew\n", b"\nchanged\n"))
        self._assert_error("reverse application failed")

    def test_wrong_commit_pin(self) -> None:
        lock = self._generate_and_write()
        lock["libraries"]["MathFin"]["commit"] = "0" * 40
        (self.root / vendor_lock.VENDOR_DIR / vendor_lock.LOCK_NAME).write_text(
            json.dumps(lock, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        self._assert_error("commit does not match PINS")

    def test_extra_top_level_file(self) -> None:
        self._generate_and_write()
        self._write(self.root / vendor_lock.VENDOR_DIR / "extra.txt", b"extra\n")
        self._assert_error("vendor top-level inventory")

    def test_upstream_blob_differs_from_lock(self) -> None:
        lock = self._generate_and_write()
        lock["libraries"]["BrownianMotion"]["files"][
            "BrownianMotion/LICENSE"
        ]["upstream_git_blob"] = "0" * 40
        (self.root / vendor_lock.VENDOR_DIR / vendor_lock.LOCK_NAME).write_text(
            json.dumps(lock, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        errors = vendor_lock.check_upstream(self.root, self.clones)
        self.assertTrue(any("upstream blob mismatch" in error for error in errors), errors)

    def test_generate_refuses_different_unpatched_file(self) -> None:
        path = self.root / vendor_lock.VENDOR_DIR / "MathFin/LICENSE"
        path.write_bytes(b"different\n")
        with self.assertRaisesRegex(ValueError, "unpatched file differs"):
            vendor_lock.generate_lock(self.root, self.clones)

    def test_parser_rejects_mismatched_paths(self) -> None:
        with self.assertRaises(ValueError):
            vendor_lock.parse_patch(
                "--- a/A\n+++ b/B\n@@ -1 +1 @@\n-x\n+y\n"
            )

    def test_parser_rejects_parent_path(self) -> None:
        with self.assertRaises(ValueError):
            vendor_lock.parse_patch(
                "--- a/../A\n+++ b/../A\n@@ -1 +1 @@\n-x\n+y\n"
            )

    def test_parser_rejects_dev_null(self) -> None:
        with self.assertRaises(ValueError):
            vendor_lock.parse_patch(
                "--- /dev/null\n+++ b/A\n@@ -0,0 +1 @@\n+x\n"
            )

    def test_parser_rejects_bad_counts(self) -> None:
        with self.assertRaises(ValueError):
            vendor_lock.parse_patch(
                "--- a/A\n+++ b/A\n@@ -1,2 +1 @@\n-x\n"
            )

    def test_separated_hunks_keep_the_lines_between_them(self) -> None:
        old = b"".join(b"line %d\n" % i for i in range(1, 21))
        new = old.replace(b"line 2\n", b"two\n").replace(b"line 18\n", b"eighteen\nextra\n")
        text = (
            "--- a/A\n+++ b/A\n"
            "@@ -1,3 +1,3 @@\n line 1\n-line 2\n+two\n line 3\n"
            "@@ -17,3 +17,4 @@\n line 17\n-line 18\n+eighteen\n+extra\n line 19\n"
        )
        hunks = vendor_lock.parse_patch(text)["A"]
        self.assertEqual(vendor_lock.apply_forward(old, hunks), new)
        self.assertEqual(vendor_lock.apply_reverse(new, hunks), old)
        with self.assertRaises(ValueError):
            vendor_lock.apply_reverse(new.replace(b"line 17\n", b"moved\n"), hunks)

    def test_pure_insertion_and_deletion_hunks(self) -> None:
        hunks = vendor_lock.parse_patch("--- a/A\n+++ b/A\n@@ -2,0 +3,2 @@\n+x\n+y\n")["A"]
        self.assertEqual(vendor_lock.apply_forward(b"a\nb\nc\n", hunks), b"a\nb\nx\ny\nc\n")
        self.assertEqual(vendor_lock.apply_reverse(b"a\nb\nx\ny\nc\n", hunks), b"a\nb\nc\n")
        hunks = vendor_lock.parse_patch("--- a/A\n+++ b/A\n@@ -1,2 +0,0 @@\n-a\n-b\n")["A"]
        self.assertEqual(vendor_lock.apply_forward(b"a\nb\n", hunks), b"")

    def test_carriage_return_stays_inside_its_line(self) -> None:
        hunks = vendor_lock.parse_patch(b"--- a/A\n+++ b/A\n@@ -1 +1 @@\n-a\rb\n+c\n")["A"]
        self.assertEqual(vendor_lock.apply_forward(b"a\rb\n", hunks), b"c\n")

    def test_parser_round_trips_no_newline_marker(self) -> None:
        text = (
            "--- a/A\n"
            "+++ b/A\n"
            "@@ -1 +1 @@\n"
            "-old\n"
            "\\ No newline at end of file\n"
            "+new\n"
        )
        parsed = vendor_lock.parse_patch(text)["A"]
        self.assertEqual(vendor_lock.apply_forward(b"old", parsed), b"new\n")
        self.assertEqual(vendor_lock.apply_reverse(b"new\n", parsed), b"old")

    def test_real_repository_lock(self) -> None:
        real_root = Path(__file__).resolve().parents[2]
        lock = real_root / vendor_lock.VENDOR_DIR / vendor_lock.LOCK_NAME
        if not lock.exists():
            self.skipTest("repository vendor lock is absent")
        with patch.dict(vendor_lock.PINS, self.real_pins, clear=True):
            _, errors = vendor_lock.check_lock(real_root, set(self.real_pins))
        self.assertEqual(errors, [])


if __name__ == "__main__":
    unittest.main()
