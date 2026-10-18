# Read-only project context MCP

Run from the repository root using Python and the pinned `mcp==2.3.0` SDK:

```sh
python -m pip install -r research/requirements-mcp.txt
python -B -m research.context_mcp --repo /absolute/path/to/KLS
```

A stdio client configuration, with absolute paths adapted to the local installation:

```json
{
  "mcpServers": {
    "kls-context": {
      "command": "/absolute/path/to/venv/bin/python",
      "args": ["-B", "-m", "research.context_mcp", "--repo", "/absolute/path/to/KLS"],
      "cwd": "/absolute/path/to/KLS",
      "env": {"PYTHONDONTWRITEBYTECODE": "1", "GIT_OPTIONAL_LOCKS": "0"}
    }
  }
}
```

The client performs the standard MCP initialization handshake. Exactly six tools are
registered: `project_snapshot`, `project_status`, `verification_status`, `claim_explain`,
`changes_review`, and `work_next`. All carry read-only, non-destructive, closed-world
annotations. The immutable resource is `project://kls/{full-40-hex-commit}/handoff`.

Begin with `project_snapshot`. `head` and explicit full-commit revisions read immutable
Git blobs and remain usable after branch changes. `index` reads staged blobs. `worktree`
retains source bytes from a double-checked capture, including nonignored untracked files
and missing tracked files. Index/worktree handles become stale after relevant changes.
Each response identifies the selected snapshot, currently observed HEAD and index hash,
observation time, full source fingerprint, and up to 20 global source references with the
complete reference count and truncation flag. Four handles are retained;
older handles expire. Status pages accept `offset` and `limit` (1–50), and every matched
registry record carries its own path, SHA-256 and JSON pointer. Papers and priorities are
separate. Current-work extraction preserves nested handoff headings.

Repository text is untrusted data. Public text reads use an explicit allowlist of current
root documents, library Lean/README files, toolchain/Lake files, Blueprint sources and
named progress registries. Complete bindings additionally hash safe public source files,
including verifier/API drivers, audit templates and tracked `.github`, `.githooks`, and
`.gitignore` files. Secret/configuration paths, Git internals, dated operational history,
and arbitrary build files are refused. Excluded source paths make binding incomplete and
prevent exact receipt acceptance. Filesystem reads reject symlinks in every component,
check descriptors before/after bounded reads, and never follow a resolved replacement.

Local receipts are trust-bound recorded claims, not fresh proof. Complete original receipt
maps are digested before exact missing/extra/changed comparison. `full` and the verifier's
exact `lean-only` binding are supported; `downstream` is explicitly unavailable. Newest
observed and newest scope-compatible artifacts are reported separately. Malformed or
unfinished latest evidence and incomplete receipt scans prevent acceptance. A later valid
run of another scope is displayed separately; it cannot clear an intervening malformed attempt
for the requested scope. A later valid attempt of that scope is required. Remote evidence is unavailable.

Optional compiler observations require the exact library-module/aggregate plus six fixed
producer inputs, canonical producer digest, genuine manifest counts and module inventory,
and the actual `public-api.json` output hash. The four output names/hashes must be present;
only the public API output is independently rehashed. Returned type text includes its
bound source origin and explicit clipping. Missing/stale artifacts yield limitations.
No tool invokes Lean, builds, network, APIs, workers, or arbitrary commands.

Bounds: 4,000 source paths, 8 MiB per source/receipt, 64 MiB total captured source,
32 MiB per fixed API output, JSON depth 32 and 250,000 nodes (500,000 for public API),
20-second Git reads, and the newest 50 sorted receipt directories. An incomplete scan
cannot yield exact acceptance. Responses page records and explicitly mark clipped text,
collections, source-reference lists and changes; queries are bounded literals.

Run regressions without Lean or network:

```sh
PYTHONDONTWRITEBYTECODE=1 python -B -m unittest discover -s research/tests -p test_project_context.py -v
```

Tests create temporary Git repositories. The optional SDK test exercises the actual
stdio wrapper, six tools, annotations and immutable resource; it skips when the pinned
SDK is absent. These regressions do not invoke Lean or certify mathematical claims.
