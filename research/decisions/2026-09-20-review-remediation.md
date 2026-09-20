# Independent-review remediation (2026-09-20)

The independent review found a potential false-positive audit path, nonconforming namespace
syntax, stale current-status prose and navigation, and overbroad ignore rules. The previous
successful receipt remained valid for its actual snapshot; that did not eliminate these defects.
This batch fixes all five findings without changing mathematical scope or certificate status.

## Checked module provenance (LD-011)

Default Lake targets do not cover every current module. Audit elaboration previously ran before
the full replay-scope build and could import stale or orphaned `.olean` files. Verification now
builds every live library/solution/example module before inspecting declarations or audit clients.
It copies only those current modules into an initially empty `local-olean` view. The configured
local build directory is replaced, not appended, in the Lean search path. Audits, statement
snapshots, declaration audits and kernel replay all use this view. Audit elaboration invokes the
selected toolchain's Lean executable directly, so `lake env` cannot restore the old search path.
The receipt records the checked search path, module list and compiled artifact hashes.

Regression tests create real Lake fixtures with modules outside the default closure. They first
confirm that the old command accepts stale artifacts, then require the full-scope build to reject
broken current source and the filtered view to reject an import whose source was deleted. A reused
nonempty view is rejected. No existing cache files are deleted.

## Namespace syntax and unchanged interfaces (LD-008 follow-up)

All 48 absolute declaration heads are replaced by short heads inside actual Generated or
HeatSemigroup namespace blocks. Generic helpers retain their original namespaces. The Markov
section reintroduces its original variable context after leaving LpMarkov. Three generic `map_sub`
references are explicitly root-qualified to avoid shadowing by Generated.map_sub; this is a
reference qualification, not an absolute declaration head or a new alias.

A fresh elaboration of 220 public roots and their 337 project declarations matches the pre-fix
snapshot, including 514 external leaves. Public names, parameters, order, universe levels and
normalized types/definition bodies are unchanged. Generated theorem auxiliaries are compared by
identical complete types using proof irrelevance. The [location map](../api-migration/2026-09-20-namespace-blocks-map.json)
records the 48 revised declaration locations; older maps remain historical records.

## Status, navigation and source discovery

The current KLS navigation and design-guide boundary now state 26 registered certificates and the single intentional
library hole at KLS.Conjecture. General high-dimensional Buser with constant pi and dimension-free
KLS remain open. The current aggregate overview, design guide, audit docstrings and task notes
use the current module/API locations. This completes the additional LD-001/002 omissions;
dated historical records are not rewritten.

Python packaging directory patterns are rooted at the repository, preventing Target, Lib, Var,
Parts and Build families inside Lean source directories from being ignored on case-insensitive
Git configurations. Existing formalization/build artifacts remain explicitly ignored. The new
source-discovery gate separately scans production/audit directories and rejects on-disk Lean
files absent from the Git-aware snapshot, including omissions caused by other ignore files.
A case-insensitive Git fixture tests both the corrected rules and detection of a deliberately
hidden source. This resolves LD-012; discovery is no longer silently entrusted to ignore rules.

## Validation boundary

The default full build passes. All ten verifier tests, including the real stale/orphan and ignore
regressions, pass. Task evidence hashes and generated progress views are refreshed after checking
them against the saved dirty baseline. The complete verifier is then run on frozen final sources;
its separate snapshot-bound receipt is under build/verification. Research audit elaboration still
does not turn candidate #check propositions into proofs or add audit clients to kernel replay.
The original staging and unrelated changes are preserved; no commit or push is performed.
