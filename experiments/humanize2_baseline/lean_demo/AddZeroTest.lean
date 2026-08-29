import FunctionalInequalities

/-! A deliberately broken, KLS-independent fixture for compiler-driven proof repair. -/

theorem add_zero_test (n : Nat) : n + 0 = n := by
  exact Nat.zero_add n
