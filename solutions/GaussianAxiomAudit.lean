import solutions.LemPoincareGaussianOneDimensional

/-!
# Transitive axiom audit for the Gaussian certificate

The pinned Lean/Mathlib environment is expected to use only the standard quotient,
propositional-extensionality, and classical-choice axioms for the accepted certificate.
`#guard_msgs` makes any change to that transitive set fail the default build.
-/

/--
info: 'Solutions.LemPoincareGaussianOneDimensional.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Solutions.LemPoincareGaussianOneDimensional.certificate
