import FunctionalInequalities

/-! A deliberately broken, KLS-independent fixture for the actor-reviewer baseline. -/

theorem add_comm_test (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b
