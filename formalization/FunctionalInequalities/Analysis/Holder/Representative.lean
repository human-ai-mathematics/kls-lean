import FunctionalInequalities.Analysis.EssentialExtrema.Basic
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Hölder and continuous a.e. representatives

Dense extension of Hölder functions; continuous Hölder representatives of a.e. bounded functions with power decay of their
essential widths, built on a common good set; and the gluing of continuous a.e. representatives along the exhaustion by balls
`B(0, m+1)`.
-/

/-! ## Representatives -/

noncomputable section HolderRepresentatives

open MeasureTheory Set Metric Filter
open scoped NNReal ENNReal

namespace FunctionalInequalities.Analysis

/-- The extension of a Hölder function (positive exponent) from a dense subset keeps the same Hölder constant and exponent. -/
theorem holderWith_dense_extension {X Y : Type*} [PseudoEMetricSpace X]
    [EMetricSpace Y] [CompleteSpace Y] {S : Set X} (hS : Dense S)
    {f : S → Y} {C η : ℝ≥0} (hη : 0 < η) (hf : HolderWith C η f) :
    HolderWith C η (hS.extend f) := by
  have hcont : Continuous (hS.extend f) :=
    (hS.uniformContinuous_extend (hf.uniformContinuous hη)).continuous
  have hc : IsClosed {p : X × X |
      edist (hS.extend f p.1) (hS.extend f p.2) ≤ (C : ℝ≥0∞)*edist p.1 p.2^(η:ℝ)} := by
    apply isClosed_le (by fun_prop)
    exact (ENNReal.continuous_const_mul (by simp)).comp
      (ENNReal.continuous_rpow_const.comp (by fun_prop))
  have hd : Dense {p : X × X |
      edist (hS.extend f p.1) (hS.extend f p.2) ≤ (C : ℝ≥0∞)*edist p.1 p.2^(η:ℝ)} := by
    apply (hS.prod hS).mono
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have Ax : hS.extend f x = f ⟨x,hx⟩ := hS.extend_eq (hf.continuous hη) ⟨x,hx⟩
    have Ay : hS.extend f y = f ⟨y,hy⟩ := hS.extend_eq (hf.continuous hη) ⟨y,hy⟩
    simp only [Set.mem_ofPred_eq,Ax,Ay]
    exact hf ⟨x,hx⟩ ⟨y,hy⟩
  simpa only [Dense,IsClosed.closure_eq,Set.mem_ofPred_eq,Prod.forall] using! hd

/-- A function that is Hölder on a full-measure set (open-positive measure) has a continuous Hölder representative with the
same constant, equal to it almost everywhere. -/
theorem exists_holder_representative_of_ae_holder {X : Type*} [PseudoEMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    (f : X → ℝ) (P : X → Prop) (hP : ∀ᵐ x ∂μ, P x)
    {C η : ℝ≥0} (hη : 0 < η)
    (hf : HolderWith C η (fun x : {x | P x} => f x)) :
    ∃ g : X → ℝ, HolderWith C η g ∧ Continuous g ∧ g =ᵐ[μ] f := by
  have hS : Dense {x | P x} := μ.dense_of_ae hP
  let g := hS.extend (fun x : {x | P x} => f x)
  have hg : HolderWith C η g := holderWith_dense_extension hS hη hf
  refine ⟨g,hg,hg.continuous hη,?_⟩
  filter_upwards [hP] with x hx
  exact hS.extend_eq (hf.continuous hη) ⟨x,hx⟩

/-- Pointwise Hölder estimate on a common good set: if `0 ≤ f ≤ K` there, every good point lies between the essential
extrema on each open neighbourhood, and the essential width on `B(x, r)` is at most `Q r^η` for `r ∈ (0,1]`, then
`|f x − f y| ≤ (Q + K) 2^η d(x,y)^η` on the good set. -/
theorem holder_estimate_on_common_good_set {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (S : Set X) {η Q K : ℝ}
    (hη : 0 < η) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hcap : ∀ x ∈ S, 0 ≤ f x ∧ f x ≤ K)
    (hgood : ∀ x ∈ S, ∀ V : Set X, IsOpen V → x ∈ V →
      essInf f (μ.restrict V) ≤ f x ∧ f x ≤ essSup f (μ.restrict V))
    (hpow : ∀ x ∈ S, ∀ r ∈ Ioc (0:ℝ) 1,
      essSup f (μ.restrict (ball x r))-essInf f (μ.restrict (ball x r)) ≤ Q*r^η) :
    ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ ((Q+K)*2^η)*dist x y^η := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simp only [dist_self]
    positivity
  have hd : 0 < dist x y := dist_pos.mpr hxy
  by_cases hsmall : dist x y ≤ 1/2
  · have hr : 0 < 2*dist x y := by positivity
    have hxr : x ∈ ball x (2*dist x y) := mem_ball_self hr
    have hyr : y ∈ ball x (2*dist x y) := by
      rw [mem_ball,dist_comm]
      linarith
    have hbx := hgood x hx _ isOpen_ball hxr
    have hby := hgood y hy _ isOpen_ball hyr
    have hdiff : dist (f x) (f y) ≤ essSup f (μ.restrict (ball x (2*dist x y)))-
        essInf f (μ.restrict (ball x (2*dist x y))) := by
      rw [Real.dist_eq,abs_sub_le_iff]
      constructor <;> linarith [hbx.1,hbx.2,hby.1,hby.2]
    calc
      _ ≤ essSup f (μ.restrict (ball x (2*dist x y)))-
          essInf f (μ.restrict (ball x (2*dist x y))) := hdiff
      _ ≤ Q*(2*dist x y)^η := hpow x hx _ ⟨hr,by linarith⟩
      _ = Q*(2^η*dist x y^η) := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) dist_nonneg]
      _ ≤ (Q+K)*(2^η*dist x y^η) := mul_le_mul_of_nonneg_right
        (by linarith) (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg dist_nonneg _))
      _ = _ := by ring
  · have hdiff : dist (f x) (f y) ≤ K := by
      rw [Real.dist_eq,abs_sub_le_iff]
      have hxcap := hcap x hx
      have hycap := hcap y hy
      constructor <;> linarith
    have hone : 1 ≤ (2*dist x y)^η := Real.one_le_rpow (by linarith) hη.le
    calc
      _ ≤ K := hdiff
      _ ≤ K*(2*dist x y)^η := le_mul_of_one_le_right hK hone
      _ ≤ (Q+K)*(2*dist x y)^η := mul_le_mul_of_nonneg_right
        (by linarith) (Real.rpow_nonneg (by positivity) _)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) dist_nonneg]; ring

/-- A real-distance Hölder bound `d(f x, f y) ≤ C d(x,y)^η` gives `HolderWith C η f`. -/
theorem holderWith_of_real_dist_bound {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (C η : ℝ≥0)
    (h : ∀ x y, dist (f x) (f y) ≤ (C:ℝ)*dist x y^(η:ℝ)) : HolderWith C η f := by
  intro x y
  rw [edist_dist,edist_dist,ENNReal.ofReal_rpow_of_nonneg dist_nonneg η.coe_nonneg]
  calc
    _ ≤ ENNReal.ofReal ((C:ℝ)*dist x y^(η:ℝ)) := ENNReal.ofReal_le_ofReal (h x y)
    _ = _ := by rw [ENNReal.ofReal_mul C.coe_nonneg,ENNReal.ofReal_coe_nnreal]

/-- Local Hölder representative: an a.e. bounded `0 ≤ f ≤ K` whose essential widths on `B(x, r)` are at most `Q r^η` for
every center `x` of an open `U` and `r ∈ (0,1]` has a continuous Hölder representative on `U` with constant `(Q + K) 2^η`,
equal to `f` almost everywhere on `U`. -/
theorem exists_local_holder_representative_of_essential_power {X : Type*} [MetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] (f : X → ℝ) (U : Set X) (hU : IsOpen U)
    {η : ℝ≥0} (hη : 0 < η) {Q K : ℝ} (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hfK : ∀ᵐ x ∂μ, f x ≤ K)
    (hpow : ∀ x ∈ U, ∀ r ∈ Ioc (0:ℝ) 1,
      essSup f (μ.restrict (ball x r))-essInf f (μ.restrict (ball x r)) ≤ Q*r^(η:ℝ)) :
    ∃ (C : ℝ≥0) (g : U → ℝ), (C:ℝ) = (Q+K)*2^(η:ℝ) ∧
      HolderWith C η g ∧ Continuous g ∧
      ∀ᵐ x ∂μ.restrict U, ∀ hx : x ∈ U, g ⟨x,hx⟩ = f x := by
  let P := fun x => 0 ≤ f x ∧ f x ≤ K ∧
    ∀ V : Set X, IsOpen V → x ∈ V →
      essInf f (μ.restrict V) ≤ f x ∧ f x ≤ essSup f (μ.restrict V)
  have hP : ∀ᵐ x ∂μ, P x := by
    filter_upwards [hf0,hfK,ae_forall_open_real_essential_bounds μ f hf0 hfK] with x hx0 hxK hx
    exact ⟨hx0,hxK,hx⟩
  have hηr : 0 < (η:ℝ) := by exact_mod_cast hη
  let C : ℝ≥0 := ⟨(Q+K)*2^(η:ℝ),by positivity⟩
  have hS : Dense {z : U | P z.val} :=
    (μ.dense_of_ae hP).preimage hU.isOpenMap_subtype_val
  have hHolder : HolderWith C η (fun z : {z : U | P z.val} => f z.val.val) := by
    apply holderWith_of_real_dist_bound
    intro x y
    change dist (f x.val.val) (f y.val.val) ≤ ((Q+K)*2^(η:ℝ))*dist x.val.val y.val.val^(η:ℝ)
    exact holder_estimate_on_common_good_set μ f {x | x ∈ U ∧ P x} hηr hQ hK
      (fun _ hx => ⟨hx.2.1,hx.2.2.1⟩) (fun _ hx => hx.2.2.2)
      (fun x hx => hpow x hx.1) x.val.val ⟨x.val.property,x.property⟩
      y.val.val ⟨y.val.property,y.property⟩
  let g := hS.extend (fun z : {z : U | P z.val} => f z.val.val)
  have hg : HolderWith C η g := holderWith_dense_extension hS hη hHolder
  refine ⟨C,g,rfl,hg,hg.continuous hη,?_⟩
  filter_upwards [ae_restrict_of_ae hP] with x hxP
  intro hxU
  exact hS.extend_eq (hHolder.continuous hη) ⟨⟨x,hxU⟩,hxP⟩

/-- Continuous a.e. representatives on the exhausting balls `B(0, m+1)` glue to one continuous function on the whole space
that is a.e. equal to `f` and agrees with every local representative on its entire ball (compatibility on the open overlaps
from a.e. equality and the open-positive measure). -/
theorem glue_continuous_ae_representatives_on_balls {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E) [μ.IsOpenPosMeasure]
    (f : E → ℝ)
    (g : (m : ℕ) → (ball (0:E) ((m:ℝ)+1)) → ℝ)
    (hg : ∀ m, Continuous (g m))
    (hAE : ∀ (m : ℕ), ∀ᵐ x ∂μ.restrict (ball (0:E) ((m:ℝ)+1)),
      ∀ hx : x ∈ ball (0:E) ((m:ℝ)+1), g m ⟨x,hx⟩ = f x) :
    ∃ F : E → ℝ, Continuous F ∧ F =ᵐ[μ] f ∧
      ∀ (m : ℕ) (x : ball (0:E) ((m:ℝ)+1)), F x = g m x := by
  classical
  let U := fun m : ℕ => ball (0:E) ((m:ℝ)+1)
  let A := fun m x => if hx : x ∈ U m then g m ⟨x,hx⟩ else 0
  have hRes (m : ℕ) : (U m).domRestrict (A m) = g m := by
    funext x
    dsimp only [Set.domRestrict_apply,A]
    rw [dif_pos x.property]
  have hAcont (m : ℕ) : ContinuousOn (A m) (U m) :=
    continuousOn_iff_continuous_domRestrict.mpr (by rw [hRes m]; exact hg m)
  have hAAE (m : ℕ) : A m =ᵐ[μ.restrict (U m)] f := by
    filter_upwards [ae_restrict_mem (μ := μ) (isOpen_ball.measurableSet),hAE m] with x hx hh
    dsimp only [A]
    rw [dif_pos hx]
    exact hh hx
  have hCompat (m j : ℕ) : EqOn (A m) (A j) (U m ∩ U j) := by
    have hm : A m =ᵐ[μ.restrict (U m ∩ U j)] f :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hAAE m)
    have hj : A j =ᵐ[μ.restrict (U m ∩ U j)] f :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hAAE j)
    exact μ.eqOn_open_of_ae_eq (hm.trans hj.symm) (isOpen_ball.inter isOpen_ball)
      ((hAcont m).mono inter_subset_left) ((hAcont j).mono inter_subset_right)
  let k := fun x : E => Classical.choose (exists_nat_gt ‖x‖)
  have hxk (x : E) : x ∈ U (k x) := by
    have h := Classical.choose_spec (exists_nat_gt ‖x‖)
    change dist x 0 < (k x:ℝ)+1
    rw [dist_zero_right]
    change ‖x‖ < (k x:ℝ) at h
    linarith
  let F := fun x => A (k x) x
  have hFA (m : ℕ) (x : E) (hx : x ∈ U m) : F x = A m x :=
    (hCompat m (k x) ⟨hx,hxk x⟩).symm
  have hFcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hc : ContinuousAt (A (k x)) x :=
      (hAcont (k x)).continuousAt (isOpen_ball.mem_nhds (hxk x))
    apply hc.congr_of_eventuallyEq
    exact eventually_of_mem (isOpen_ball.mem_nhds (hxk x)) fun y hy => hFA (k x) y hy
  have hFAE : F =ᵐ[μ] f := by
    have hAll : ∀ᵐ x ∂μ, ∀ m, x ∈ U m → A m x = f x :=
      ae_all_iff.mpr (fun m => ae_imp_of_ae_restrict (hAAE m))
    filter_upwards [hAll] with x hx
    exact hx (k x) (hxk x)
  refine ⟨F,hFcont,hFAE,fun m x => ?_⟩
  exact (hFA m x x.property).trans (congrFun (hRes m) x)

end FunctionalInequalities.Analysis

end HolderRepresentatives
