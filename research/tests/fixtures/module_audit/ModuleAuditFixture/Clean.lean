module

/-! Test data only for `research/tests/test_verify.py`; never imported by the library, its audits
or any production client. A clean module: its unused private theorem must still be enumerated by
the generated declaration audit. -/

namespace ModuleAuditFixture

private theorem unusedPrivate : True := trivial

public theorem visible : True := trivial

end ModuleAuditFixture
