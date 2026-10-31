module

/-! Test data only for `research/tests/test_verify.py`; never imported by the library, its audits
or any production client. The nonstandard axiom is deliberate: it is private, a private theorem
uses it, and a public theorem depends on that private theorem. The generated audit must reject. -/

namespace ModuleAuditFixture

private axiom fixtureAxiom : False

private theorem privateUse : False := fixtureAxiom

public theorem publicUse : (0 : Nat) = 1 := privateUse.elim

end ModuleAuditFixture
