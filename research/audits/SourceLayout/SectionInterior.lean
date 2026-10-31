module

public import FunctionalInequalities.Analysis.Convex.Section.Engulfing
public import Lean
meta import Lean
import all FunctionalInequalities.Analysis.BakryEmery.Calculus
import all FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
import all FunctionalInequalities.Analysis.BakryEmery.Hessian.Operator
import all FunctionalInequalities.Analysis.Convex.Alexandrov.ImageVolume
import all FunctionalInequalities.Analysis.Convex.Alexandrov.MaximumPrinciple
import all FunctionalInequalities.Analysis.Convex.Alexandrov.Transport
import all FunctionalInequalities.Analysis.Convex.Boundary
import all FunctionalInequalities.Analysis.Convex.Extension
import all FunctionalInequalities.Analysis.Convex.Legendre.AffineMaximum
import all FunctionalInequalities.Analysis.Convex.Legendre.Basic
import all FunctionalInequalities.Analysis.Convex.Legendre.SupportingPlane
import all FunctionalInequalities.Analysis.Convex.Legendre.Variation.Attainment
import all FunctionalInequalities.Analysis.Convex.Normalization
import all FunctionalInequalities.Analysis.Convex.Proximal
import all FunctionalInequalities.Analysis.Convex.Quadratic
import all FunctionalInequalities.Analysis.Convex.Section.Affine
import all FunctionalInequalities.Analysis.Convex.Section.Engulfing
import all FunctionalInequalities.Analysis.Convex.Section.Growth
import all FunctionalInequalities.Analysis.Convex.Subgradient.Basic
import all FunctionalInequalities.Analysis.Convex.Subgradient.Existence
import all FunctionalInequalities.Analysis.Convex.Subgradient.Image
import all FunctionalInequalities.Analysis.Convex.Subgradient.Measure
import all FunctionalInequalities.Analysis.Convex.Subgradient.Regularity
import all FunctionalInequalities.Analysis.Convex.Supremum
import all FunctionalInequalities.Analysis.Extremum
import all FunctionalInequalities.Analysis.Matrix.Positivity
import all FunctionalInequalities.Analysis.MetricCover
import all FunctionalInequalities.Analysis.Operator.Coordinates
import all FunctionalInequalities.Analysis.RingInverseDerivative
import all FunctionalInequalities.Probability.Basic
import all FunctionalInequalities.Probability.Covariance.Basic
import all FunctionalInequalities.Probability.Support.Affine
import all FunctionalInequalities.Probability.Transport

/-! Both affine-normalized section consumers use the common open-convex interior-ball step.
The private comparison producer is found by its mathematical namespace and suffix, independent
of the compiler's private-name prefix.
-/

@[expose] public section

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for suffix in [".SoftEngulfing.exists_bregman_comparison_core",
      ".Analysis.exists_section_volume_upper_bound"] do
    let consumers := env.constants.toList.filter fun (name, _) => name.toString.endsWith suffix
    unless consumers.length == 1 do
      throwError "Expected one section consumer for {suffix}"
    let (name, info) := consumers.head!
    let some proof := info.value? (allowOpaque := true)
      | throwError "Missing section-consumer proof: {name}"
    unless proof.getUsedConstants.contains
        `FunctionalInequalities.Analysis.closedBall_subset_of_ball_subset_closure do
      throwError "The section consumer must call the shared interior-ball producer: {name}"

#print axioms FunctionalInequalities.Analysis.closedBall_subset_of_ball_subset_closure
#print axioms FunctionalInequalities.Analysis.exists_section_volume_upper_bound
