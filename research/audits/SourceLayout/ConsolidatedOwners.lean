import FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic
import FunctionalInequalities.Analysis.Newtonian.Potential
import FunctionalInequalities.KLS.Geometry.Cheeger.MinkowskiContent
import FunctionalInequalities.KLS.Geometry.Cheeger.DistanceCutoff
import FunctionalInequalities.Analysis.Tensor.Coefficients
import FunctionalInequalities.Analysis.Lipschitz.ZeroDerivative

open FunctionalInequalities FunctionalInequalities.Analysis MeasureTheory
open scoped ENNReal

namespace SourceLayout

/-- The coordinate conversion includes an empty index type, with no positive-dimension premise. -/
theorem two_coordinates {ι E : Type*} [Fintype ι] (b : ι → E) (u : E)
    (f : (Fin 3 → E) → ℝ) :
    ∑ J : Fin 2 → ι, f (Fin.cons u fun k => b (J k)) = ∑ i, ∑ j, f ![u, b i, b j] :=
  Tensor.sum_finTwo_arrow_cons b u f

#check BakryEmery.taylorTensor_succ_of_eq_inner
#check BakryEmery.integral_neg_weightedLaplacian_eq_inner
#check hasFDerivAt_setIntegral_comp_sub_mul
#check KLS.Isoperimetry.lintegral_minkowskiContent_superlevel_le_liminf_of_majorant
#check KLS.Isoperimetry.lintegral_minkowskiContent_superlevel_le_limsup_of_majorant
#check KLS.Isoperimetry.lintegral_enorm_distanceCutoff_sub_indicator_le
#check exists_lipschitzOnWith_cover_of_fderiv_eq_zero
#print axioms two_coordinates
end SourceLayout
