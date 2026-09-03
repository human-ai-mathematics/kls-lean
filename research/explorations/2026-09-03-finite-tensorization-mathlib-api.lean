import FunctionalInequalities.Tensorization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Constructions.Pi
#check @PiLp.proj
#check @PiLp.norm_sq_eq_of_L2
#check @PiLp.norm_single
#check @LinearEquiv.piCongrLeft
#check @LinearEquiv.piOptionEquivProd
#check @LinearIsometryEquiv.piLpCongrLeft
#check @PiLp.sumPiLpEquivProdLpPiLp
#check @MeasureTheory.measurePreserving_eval
#check @MeasureTheory.Measure.pi_map_piOptionEquivProd
#check @MeasureTheory.measurePreserving_piCongrLeft
#check @Fintype.induction_empty_option
#check @ContinuousLinearMap.adjoint
#check @WithLp.fstL
#check @WithLp.sndL
#check @LinearIsometryEquiv.toContinuousLinearEquiv
#check @MeasureTheory.MemLp.comp_measurePreserving
#check @ProbabilityTheory.variance_map
section AmbientInstances
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
#synth InnerProductSpace ℝ (PiLp 2 E)
#synth CompleteSpace (PiLp 2 E)
#synth BorelSpace (PiLp 2 E)
#synth SecondCountableTopology (PiLp 2 E)
end AmbientInstances
