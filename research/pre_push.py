#!/usr/bin/env python3
"""Gate pushes of the current committed checkout using the full local verifier."""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def check_checkout(root: Path, updates: str) -> bool:
    """Do not bind a receipt to HEAD while pushing another commit or dirty tracked files."""
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=root, text=True).strip()

    head = git('rev-parse', 'HEAD')
    outgoing = []
    for line in updates.splitlines():
        local_ref, local_sha, remote_ref, remote_sha = line.split()
        if set(local_sha) == {'0'}:
            continue  # Deleting a ref publishes no new source snapshot.
        commit = git('rev-parse', local_sha + '^{commit}')
        if commit != head:
            raise ValueError(f'{local_ref}: checkout the outgoing commit before pushing; '
                             'the local verifier checks HEAD')
        outgoing.append(commit)
    if updates and not outgoing:
        return False
    if git('diff', '--name-only', 'HEAD'):
        raise ValueError('Tracked files differ from HEAD; commit or preserve them separately '
                         'before verifying the outgoing snapshot')
    return True


def main() -> int:
    try:
        verify = check_checkout(ROOT, sys.stdin.read())
    except (ValueError, subprocess.CalledProcessError) as exc:
        print(f'Local pre-push gate: {exc}', file=sys.stderr)
        return 1
    if not verify:
        return 0
    print('Local pre-push gate: full verification of the current committed checkout.', flush=True)
    return subprocess.call([sys.executable, str(ROOT / 'research/verify.py')], cwd=ROOT)


if __name__ == '__main__':
    raise SystemExit(main())
