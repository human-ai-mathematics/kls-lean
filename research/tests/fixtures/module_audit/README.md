# Module-visibility audit fixture (test data only)

Tiny Lean `module` files used only by `research/tests/test_verify.py`
(`ModuleVisibilityAuditTests`). The test copies them to a temporary directory, compiles them with
the pinned toolchain and runs the generated, non-module declaration audit of `research/verify.py`
against them. They are never imported by the library, its audits, examples, solutions or any
Lake target; the axioms in `PrivateAxiom.lean` and `UnusedPrivateAxiom.lean` are deliberate
rejection cases.
