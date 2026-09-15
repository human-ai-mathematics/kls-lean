# Keep infrastructure evidence in versioned source paths

GitHub Lean certification run `34961991785` for commit `89068d6` failed before Lean compilation:
`research/tasks.json` referenced nine audit clients under ignored `build/audit/`. Those files
existed locally but were absent from a clean checkout. The local acceptance run therefore did
not establish that its infrastructure evidence was available in CI.

Copy the nine referenced Lean clients byte-for-byte to `research/audits/` and update only their
paths in the active task metadata. Their SHA-256 hashes remain unchanged. Historical exploration
records retain their original local artifact paths. Generated logs and receipts remain ignored.

This fixes evidence availability, without changing theorem statements, proofs, certificate
membership, infrastructure status, or open obligations. A clean index export must pass
`research/atlas.py check`; the full local acceptance workflow must also pass before publication.
Remote CI remains a separate check tied to the published repair commit.
