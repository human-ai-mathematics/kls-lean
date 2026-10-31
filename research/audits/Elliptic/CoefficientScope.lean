module

public import examples.EllipticDrift

/-! Standard-axiom checks for the concrete skew-coefficient model and entry-bound counterexample. -/

@[expose] public section

#print axioms CNSCoefficientScopeAudit.quadratic_identity
#print axioms CNSCoefficientScopeAudit.symmetric_part_identity
#print axioms CNSCoefficientScopeAudit.trace_identity
#print axioms CNSCoefficientScopeAudit.coefficient_not_posSemidef
#print axioms CNSCoefficientScopeAudit.elliptic_quadratic_bounds_do_not_bound_original_entries
