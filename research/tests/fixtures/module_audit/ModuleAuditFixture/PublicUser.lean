module

public import ModuleAuditFixture.PrivateAxiom

/-! Test data only for `research/tests/test_verify.py`; never imported by the library, its audits
or any production client. A downstream public theorem whose only nonstandard axiom is private to
the imported module, reached through that module's exported axiom summary. -/

namespace ModuleAuditFixture

public theorem downstream : (0 : Nat) = 1 := publicUse

end ModuleAuditFixture
