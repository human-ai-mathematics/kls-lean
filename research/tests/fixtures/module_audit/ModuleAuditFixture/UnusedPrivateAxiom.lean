module

/-! Test data only for `research/tests/test_verify.py`; never imported by the library, its audits
or any production client. The deliberate nonstandard axiom is used only by an unused private
theorem; the public theorem is clean. The generated audit must still reject. -/

namespace ModuleAuditFixture

private axiom unusedAxiom : False

private theorem unusedUse : (1 : Nat) = 2 := unusedAxiom.elim

public theorem clean : True := trivial

end ModuleAuditFixture
