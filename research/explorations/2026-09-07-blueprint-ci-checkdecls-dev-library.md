# Blueprint CI regression: `checkdecls` imports the unbuilt `Dev` library

Date: 2026-09-07 (Asia/Shanghai). Subject: commit `575c82c`, pushed to `origin/main`.

## Symptom

`gh run list` showed different outcomes for the commit's two workflows: `Lean certification`
(run 34136280187) succeeded; `Lean Blueprint` (run 34136280179) failed at "Check Blueprint
declaration links", namely `python3 formalization/blueprint/build.py checkdecls`:

```text
uncaught exception: unknown module prefix 'Dev'
No directory 'Dev' or file 'Dev.olean' in the search path entries
```

## Cause

`575c82c` added `[[lean_lib]] Dev` in `lakefile.toml` (root `Dev.Search`, a LeanSearchClient
query draft), deliberately excluding it from `defaultTargets` to keep network queries out of
reproducible builds. However, the pinned `PatrickMassot/checkdecls` `Main.lean` imports the
roots of **all** `lean_lib`s in the root package (`ws.root.leanLibs.flatMap (·.config.roots)`),
regardless of default-target status. CI only runs `lake build`; `Dev.olean` was absent and
`importModules` threw an exception. A previous manual local `lake build Dev` concealed the
issue from local `checkdecls`.

## Resolution

- Remove the `Dev` library declaration from `lakefile.toml`, retaining `formalization/Dev/Search.lean`. Explain the reason in both the lakefile and that file's documentation; load it via `lake env lean Dev/Search.lean` or directly in the editor instead. Update the directory comment in `formalization/README.md`.
- Reproduce the CI step locally: extract 136 declarations from Blueprint chapter `\lean{}` anchors into a temporary file and run `lake exe checkdecls <file>`. Exit code 0, no "missing" output. This temporary list is not the plastex-generated `lean_decls`; it only confirms that imports no longer fail and all current anchors (including the twelve added that day) exist in the built library.
- No further push was made; the remote CI failure for `575c82c` remains unchanged. The fix takes effect on the next push.

## Boundary

This is a build-configuration issue, with no mathematical statement, certificate, or ledger
status change. Neither the `Lean certification` workflow nor local `verify.py` was affected.
