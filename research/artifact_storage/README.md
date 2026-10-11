# Compiled-artifact storage maintenance

This tool replaces verified duplicates with APFS copy-on-write clones at the same paths.
It retains evidence and source files. It does not change proof, certificate or paper-coverage
status. The inventory and explicit retention assessment are described by
[the file-management goal](../handoffs/2026-10-11-file-management-goal.md).

The layers have separate responsibilities: `filesystem.py` anchors descriptors and validates
bytes and metadata; `journal.py` preserves durable transaction/recovery history;
`transaction.py` validates a bounded manifest and performs clone or ordinary-copy replacement.
The [entry point](../deduplicate_artifacts.py) defaults to a read-only plan. Native reads may
update access times; the maintenance acceptance records timestamp-only restoration after
its final byte audit.

## Inputs and planning

Create a reviewed JSON manifest with `groups`, each containing a lowercase SHA-256, byte
`size`, and `files`. Each file supplies a root-relative `path`, `size`, `mtime_ns`, `ctime_ns`,
`inode`, and `device` from a stable inspection. Groups must contain byte-identical files.
The first file is the retained clone source; other files are replacement targets.

```sh
python3 research/deduplicate_artifacts.py --root . --manifest build/file-management/manifest.json
```

Candidates are ordinary files with one link, at least 24 hours old, on the same APFS volume,
under `build/reviews/` or `build/verification/`, with a supported compiled-artifact suffix.
The `2026-10-11-file-management` run is excluded. Symlinks, ACL-bearing files, stale hashes/fingerprints,
and unsupported filesystem flags are rejected. Hidden/document-tracking flags are retained;
all other flags remain outside the accepted storage scope.

## Applying a reviewed batch

Inspect actual writer processes and writable handles, then use an exclusive maintenance window.
The CLI also takes a root-scoped lock and never steals an existing lock. Supply explicit file
and byte bounds; the bound includes source files as well as targets.

```sh
python3 research/deduplicate_artifacts.py --root . \
  --manifest build/file-management/manifest.json \
  --journal build/file-management/artifact-storage.jsonl \
  --apply --exclusive-maintenance --max-files 384 --max-bytes 1073741824
```

The replacement preserves SHA-256, access/modification times, mode, owner/group, xattrs and
accepted flags. Inode and ctime change; creation time can change. Before/after fingerprints,
including creation time, remain in the journal. Clone data shares storage until a future write;
separate inode identities prevent a future source write from changing another candidate.

## Recovery and ordinary-copy restoration

Keep the original manifest and journal. Review a restore plan with `--restore-unique`; add the
same explicit apply controls to perform it. A restore creates an ordinary independent copy
from the verified current target bytes and preserves the specified metadata.

```sh
python3 research/deduplicate_artifacts.py --root . \
  --manifest build/file-management/manifest.json \
  --journal build/file-management/artifact-storage.jsonl --restore-unique
```

Recovery checks the named target, prepared temporary inode, bytes and metadata. A known
completed fingerprint must still match exactly. An installed interrupted clone remains
restorable; an installed ordinary restore has no further clone-restoration eligibility.
A failed pre-rename restore does not hide an older installed clone. Uncertain states stop
operations on affected paths. Installed bytes are never rolled back automatically.

The journal permits the automatic `UF_TRACKED` bit; other journal flags are rejected without
clearing them.

A torn final journal record is preserved as raw bytes. Apply repairs it only while holding the
maintenance lock, after a durable, identity/hash-checked full journal backup. Read-only planning
neither creates a journal nor repairs its tail. Refresh the manifest after successful restoration
before planning another clone operation; the restored inode is intentionally different.

Native and failure-injection evidence, original API candidates, independent corrections and
real-operation receipts are retained in `build/reviews/2026-10-11-file-management/`.
The tests simulate syscall/logging failures; they do not establish real power-loss behavior.
Logical duplicate bytes and observed volume free-space changes are separate measurements.

The actual 2026-10-12 batch acceptance is recorded in
`build/reviews/2026-10-11-file-management/storage-real/ACCEPTANCE.json`: 36 batches,
1,708 duplicate targets, complete before/after byte and metadata maps, plus real ordinary
restoration of the pilot and two interrupted batches. Original interruption journals remain
intact; explicitly reviewed derived histories preserve their original fingerprints and
revalidation evidence. The generic recovery path continues to reject stale fingerprints.
