#!/usr/bin/env python3
"""Run the full local verifier before a `milestone/**` tag is pushed; ignore other pushes."""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MILESTONE_PREFIX = 'refs/tags/milestone/'


def milestone_commits(root: Path, updates: str) -> list[str]:
    """Return the commits of outgoing milestone tags, requiring each to be the clean HEAD.

    Branch pushes, other tags and deletions need no verification. The local receipt is bound
    to the checked-out tree, so a milestone must point at HEAD and tracked files must match it.
    """
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=root, text=True).strip()

    commits = []
    for line in updates.splitlines():
        if not line.strip():
            continue
        local_ref, local_sha, remote_ref, _remote_sha = line.split()
        if not remote_ref.startswith(MILESTONE_PREFIX) or set(local_sha) == {'0'}:
            continue
        commit = git('rev-parse', local_sha + '^{commit}')
        if commit != git('rev-parse', 'HEAD'):
            raise ValueError(f'{local_ref}: check out the tagged commit before pushing the '
                             'milestone; the local verifier checks HEAD')
        commits.append(commit)
    if commits and git('diff', '--name-only', 'HEAD'):
        raise ValueError('Tracked files differ from HEAD; commit or set them aside before '
                         'verifying the milestone snapshot')
    return commits


def main() -> int:
    try:
        commits = milestone_commits(ROOT, sys.stdin.read())
    except (ValueError, subprocess.CalledProcessError) as exc:
        print(f'Milestone pre-push gate: {exc}', file=sys.stderr)
        return 1
    if not commits:
        return 0
    print(f'Milestone pre-push gate: full local verification of {commits[0][:7]} '
          'before remote Lean certification.', flush=True)
    return subprocess.call([sys.executable, str(ROOT / 'research/verify.py')], cwd=ROOT)


if __name__ == '__main__':
    raise SystemExit(main())
