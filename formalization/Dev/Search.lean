import LeanSearchClient
import FunctionalInequalities

/-!
# Development-only Mathlib search scratchpad

This module exists so that the `LeanSearchClient` query commands can be used while working on
this repository's proofs, without ever entering the certified build.

`LeanSearchClient` is already available: Mathlib requires it (`lake-manifest.json` pins
`LeanSearchClient` at `5f4d51b81cbd`, inherited) and re-exports it from
`Mathlib/Tactic/Common.lean`. No `require` was added to `lakefile.toml`; adding one would risk
a pin conflict with Mathlib's own `@ main` requirement.

## Why this file is isolated

The query commands (`#leansearch`, `#search`, `#statesearch`, `#loogle`) issue **network requests
at elaboration time**. A certified module containing one of them would make `lake build`
non-deterministic and network-dependent, which the verification pipeline
(`research/verify.py`, `solutions/FoundationAxiomAudit.lean`) assumes it is not.

Therefore:

* `Dev` is a `lean_lib` that is **deliberately absent from `defaultTargets`** in
  `lakefile.toml`. `lake build` never builds it; build it explicitly with `lake build Dev`.
* No module under `FunctionalInequalities/`, `solutions/`, or `examples/` may import
  `LeanSearchClient` or contain a query command.
* Query commands are exploratory notes. Delete or comment them out before committing; nothing in
  this file may be cited as evidence for a ledger status.

## Usage

Uncomment and edit, then let the editor elaborate the command (no `lake build` needed):

```
#leansearch "Lipschitz function mollified by a smooth kernel converges uniformly."
#loogle Continuous (fun x => Real.exp x)
```

`#statesearch` operates on an open goal, so it goes inside a tactic block:

```
example : True := by
  #statesearch
  trivial
```

Target the currently open blueprint nodes, e.g. the asymptotic-Lipschitz relaxation route for
`thm:smooth-gradient-relaxation-two-cheeger`, or the mollification step in
`lem:relative-perimeter-smoothing`.
-/

namespace FunctionalInequalities.Dev

-- Intentionally empty: this module carries no declarations, only the search-command scratchpad
-- documented above. Add query commands here temporarily; do not commit them.

end FunctionalInequalities.Dev
