#!/usr/bin/env python3
"""Run local Python regressions and retain structured coverage, failures and skip reasons."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


def comparator_bundled_enabled() -> bool:
    return os.environ.get("KLS_COMPARATOR_BUNDLED") == "1"


def test_summary(result: unittest.TestResult, *, require_no_skips: bool = False) -> dict:
    accepted = result.wasSuccessful() and result.testsRun > 0 and not (
        require_no_skips and result.skipped)
    return {"version": 1, "status": "passed" if accepted else "failed",
            "profile": "comparator-bundled" if comparator_bundled_enabled() else "standard",
            "require_no_skips": require_no_skips, "tests_run": result.testsRun,
            "failures": len(result.failures), "errors": len(result.errors),
            "skipped": len(result.skipped), "expected_failures": len(result.expectedFailures),
            "unexpected_successes": len(result.unexpectedSuccesses),
            "skip_reasons": [{"test": test.id(), "reason": reason} for test, reason in result.skipped]}


def run_tests(root: Path, output: Path, *, require_no_skips: bool = False) -> int:
    suite = unittest.TestLoader().discover(str(root / "research/tests"), pattern="test_*.py")
    result = unittest.TextTestRunner().run(suite)
    summary = test_summary(result, require_no_skips=require_no_skips)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Python tests {summary['status']}: {summary['tests_run']} run, "
          f"{summary['skipped']} skipped ({summary['profile']}).", flush=True)
    return int(summary["status"] != "passed")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--require-no-skips", action="store_true",
                        help="reject skipped tests as well as failures and empty discovery")
    args = parser.parse_args()
    return run_tests(args.root.resolve(), args.output, require_no_skips=args.require_no_skips)


if __name__ == "__main__":
    raise SystemExit(main())
