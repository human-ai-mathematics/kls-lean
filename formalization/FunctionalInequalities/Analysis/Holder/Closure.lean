import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Constructions.SumProd

/-!
# Hölder caps pass to the closure

`holderOnWith_closure_of_continuous`: if a continuous map `f` satisfies `HolderOnWith C α f s`,
then it satisfies the same cap `HolderOnWith C α f (closure s)`. The proof is a closedness
argument for `dist (f x) (f y) - C * dist x y ^ α ≤ 0` on `s × s`.

Generic support for the local-source cutoffs in Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Lemma 4.4, pp. 57–59, where a Hölder
cap stated on an open ball is needed on the closed ball. Continuity on the whole space is a
hypothesis; no Hölder extension theorem (e.g. McShane) is proved here.
-/
noncomputable section
open Set
open scoped NNReal
namespace FunctionalInequalities.Analysis

/-- A continuous function preserves a given Hölder cap on the closure. This
supports GT2001 local-source cutoffs and boundary nonuniformity clients. -/
theorem holderOnWith_closure_of_continuous {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {s : Set X} {C α : ℝ≥0} (h : HolderOnWith C α f s) (hf : Continuous f) :
    HolderOnWith C α f (closure s) := by
  let F : X → X → ℝ := fun x y => dist (f x) (f y) - (C:ℝ) * dist x y ^ (α:ℝ)
  have hF : Continuous (Function.uncurry F) := by
    exact ((hf.comp continuous_fst).dist (hf.comp continuous_snd)).sub
      (continuous_const.mul ((continuous_fst.dist continuous_snd).rpow_const (fun _ => Or.inr α.coe_nonneg)))
  intro x hx y hy
  have hm : F x y ∈ closure (Iic (0:ℝ)) := map_mem_closure₂ hF hx hy
    (fun a ha b hb => show F a b ∈ Iic (0:ℝ) from sub_nonpos.mpr (h.dist_le ha hb))
  have hlim : F x y ≤ 0 := by simpa only [isClosed_Iic.closure_eq,mem_Iic] using hm
  have hxy : dist (f x) (f y) ≤ (C:ℝ)*dist x y^(α:ℝ) := sub_nonpos.mp hlim
  rw [edist_dist,edist_dist,ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal hxy
end FunctionalInequalities.Analysis
