module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.ImageVolume
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Measure
public import FunctionalInequalities.Analysis.Convex.Dirichlet.Compactness
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

noncomputable section
open Set Metric MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
namespace LetwinDomainTotalMassAudit
open FunctionalInequalities.Analysis

/-- A genuinely nondifferentiable absolute-value source with exact finite
TOTAL domain support-image mass; no density upper bound is assumed. -/
theorem actual_absolute_total_mass_client :
    (volume : Measure ℝ) (subgradientImageOn (fun x : ℝ => |x| - 1) (Ioo (-1) 1) (Ioo (-1) 1)) =
        ENNReal.ofReal 2 ∧
      ∀ ε : ℝ,
        0 < ε →
          ∃ ρ : ℝ,
            0 < ρ ∧
              ∀ x ∈ Ioo (-1 : ℝ) 1, infDist x (frontier (Ioo (-1 : ℝ) 1)) < ρ → -ε ≤ |x| - 1 := by
  let Ω : Set ℝ := Ioo (-1) 1
  let u : ℝ → ℝ := fun x => |x| - 1
  have hΩ : IsOpen Ω := isOpen_Ioo
  have hconv : ConvexOn ℝ univ u := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have h := abs_add_le (a * x) (b * y)
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h
    change |a * x + b * y| - 1 ≤ a * (|x| - 1) + b * (|y| - 1)
    nlinarith
  have huc : Continuous u := by dsimp [u]; fun_prop
  have himage : subgradientImageOn u Ω Ω = Icc (-1 : ℝ) 1 := by
    ext p
    constructor
    · rintro ⟨z, hz, hp⟩
      have hall := subgradient_le_on_of_isOpen hconv hΩ (subset_univ _) hz hp
      have h1 := hall 1 (mem_univ _)
      have hm1 := hall (-1) (mem_univ _)
      change |z| - 1 + (1 - z) * p ≤ |1| - 1 at h1
      change |z| - 1 + (-1 - z) * p ≤ |-1| - 1 at hm1
      norm_num at h1 hm1
      have hz' : (-1 : ℝ) < z ∧ z < 1 := hz
      constructor
      · by_contra hn
        have hprod := mul_pos (show 0 < -1 - p by linarith) (show 0 < 1 + z by linarith)
        nlinarith [neg_le_abs z]
      · by_contra hn
        have hprod := mul_pos (show 0 < p - 1 by linarith) (show 0 < 1 - z by linarith)
        nlinarith [le_abs_self z]
    · intro hp
      refine ⟨0, by dsimp [Ω]; norm_num, ?_⟩
      intro y _hy
      change |(0 : ℝ)| - 1 + (y - 0) * p ≤ |y| - 1
      have hpabs : |p| ≤ 1 := abs_le.mpr hp
      have hm : |y * p| ≤ |y| := by
        rw [abs_mul]
        nlinarith [abs_nonneg y]
      norm_num
      linarith [le_abs_self (y * p)]
  have hmass : (volume : Measure ℝ) (subgradientImageOn u Ω Ω) = ENNReal.ofReal 2 := by
    rw [himage, Real.volume_Icc]
    norm_num
  have hfr : ∀ x ∈ frontier Ω, 0 ≤ u x := by
    intro x hx
    rw [frontier_Ioo (by norm_num : (-1 : ℝ) < 1)] at hx
    rcases hx with hx | hx
    · subst x
      norm_num [u]
    · simp only [mem_singleton_iff] at hx
      subst x
      norm_num [u]
  refine ⟨hmass, ?_⟩
  intro ε hε
  obtain ⟨ρ, hρ, hr⟩ :=
    exists_common_lower_boundary_modulus_of_domain_mass hΩ (convex_Ioo _ _)
      ((isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).isBounded.subset Ioo_subset_Icc_self) (M :=
      2) (by norm_num) hε
  refine ⟨ρ, hρ, ?_⟩
  exact
    hr u (hconv.subset (subset_univ _) (convex_Ioo (-1 : ℝ) 1).closure) huc.continuousOn hfr
      hmass.le
end LetwinDomainTotalMassAudit

namespace LetwinTotalBoundaryAudit
open FunctionalInequalities.Analysis

/-- The exact finite-mass absolute-value source uses the density-free common
absolute modulus, rather than supplying a positive lower MA density. -/
theorem absolute_value_total_boundary_client :
    ∀ ε : ℝ,
      0 < ε →
        ∃ ρ : ℝ,
          0 < ρ ∧
            ∀ x ∈ Ioo (-1 : ℝ) 1, infDist x (frontier (Ioo (-1 : ℝ) 1)) < ρ → |(|x| - 1)| ≤ ε := by
  have hconv : ConvexOn ℝ univ (fun x : ℝ => |x| - 1) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have h := abs_add_le (a * x) (b * y)
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h
    change |a * x + b * y| - 1 ≤ a * (|x| - 1) + b * (|y| - 1)
    nlinarith
  have hfr : ∀ x ∈ frontier (Ioo (-1 : ℝ) 1), |x| - 1 = 0 := by
    intro x hx
    rw [frontier_Ioo (by norm_num : (-1 : ℝ) < 1)] at hx
    rcases hx with hx | hx
    · subst x; norm_num
    · simp only [mem_singleton_iff] at hx
      subst x; norm_num
  intro ε hε
  obtain ⟨ρ, hρ, hr⟩ :=
    exists_common_boundary_modulus_of_domain_mass (E := ℝ) (Ω := Ioo (-1 : ℝ) 1) isOpen_Ioo
      (convex_Ioo _ _) (isBounded_Ioo _ _) (M := 2) (by norm_num) hε
  refine ⟨ρ, hρ, ?_⟩
  exact
    hr (fun x : ℝ => |x| - 1) (hconv.subset (subset_univ _) (convex_Ioo (-1 : ℝ) 1).closure)
      (show Continuous (fun x : ℝ => |x| - 1) from
          continuous_abs.sub continuous_const).continuousOn
      hfr (LetwinDomainTotalMassAudit.actual_absolute_total_mass_client.1.le)
end LetwinTotalBoundaryAudit


namespace LetwinPureBoundaryAudit
open FunctionalInequalities.Analysis
theorem real_abs_minus_one_client : ∀ x ∈ closure (Ioo (-1 : ℝ) 1), |x| - 1 ≤ 0 := by
  let u : ℝ → ℝ := fun x => |x| - 1
  have hΩ : IsOpen (Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have hΩconv : Convex ℝ (Ioo (-1 : ℝ) 1) := convex_Ioo _ _
  have hb : Bornology.IsBounded (Ioo (-1 : ℝ) 1) := isBounded_Ioo _ _
  have hcl : closure (Ioo (-1 : ℝ) 1) = Icc (-1 : ℝ) 1 := closure_Ioo (by norm_num)
  have hu : ConvexOn ℝ (closure (Ioo (-1 : ℝ) 1)) u := by
    rw [hcl]
    refine ⟨convex_Icc _ _, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have habs : |a * x + b * y| ≤ a * |x| + b * |y| := by
      calc
        |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
        _ = a * |x| + b * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    change |a * x + b * y| - 1 ≤ a * (|x| - 1) + b * (|y| - 1)
    nlinarith [habs, hab]
  have huc : ContinuousOn u (closure (Ioo (-1 : ℝ) 1)) := by
    exact (continuous_abs.sub continuous_const).continuousOn
  have hfr : ∀ x ∈ frontier (Ioo (-1 : ℝ) 1), u x ≤ 0 := by
    intro x hx
    change x ∈ closure (Ioo (-1 : ℝ) 1) \ interior (Ioo (-1 : ℝ) 1) at hx
    have hxcl : x ∈ Icc (-1 : ℝ) 1 := by
      rw [hcl] at hx
      exact hx.1
    have hxnot : x ∉ Ioo (-1 : ℝ) 1 := by
      intro hxi
      apply hx.2
      rw [isOpen_Ioo.interior_eq]
      exact hxi
    by_cases hxm : x = -1
    · subst x
      norm_num [u]
    · have hleft : -1 < x := lt_of_le_of_ne hxcl.1 (Ne.symm hxm)
      have hright : ¬x < 1 := by
        intro hxright
        exact hxnot ⟨hleft, hxright⟩
      have hxeq : x = 1 := le_antisymm hxcl.2 (le_of_not_gt hright)
      subst x
      norm_num [u]
  have hresult :=
    le_on_closure_of_le_frontier_of_convexOn (Ω := Ioo (-1 : ℝ) 1) (u := u) (b := 0) hΩ hΩconv
      hb hu huc hfr
  intro x hx
  simpa [u] using hresult x hx

theorem emptyOmega_client
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    {u : E → ℝ} {b : ℝ} :
    ∀ x ∈ closure (∅ : Set E), u x ≤ b := by
  apply le_on_closure_of_le_frontier_of_convexOn
      (Ω := (∅ : Set E)) (u := u) (b := b)
  · exact isOpen_empty
  · exact convex_empty
  · exact Bornology.isBounded_empty
  · rw [closure_empty]
    refine ⟨convex_empty, ?_⟩
    intro x hx y hy a c ha hc hac
    exact hx.elim
  · simp
  · simp

end LetwinPureBoundaryAudit
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.frontier_nonempty_of_isBounded
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.le_on_closure_of_le_frontier_of_convexOn
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_pos_boundary_power_bound_of_domain_mass
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_common_lower_boundary_modulus_of_domain_mass
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_common_boundary_modulus_of_domain_mass
set_option pp.fullNames true in
#print axioms LetwinDomainTotalMassAudit.actual_absolute_total_mass_client
set_option pp.fullNames true in
#print axioms LetwinTotalBoundaryAudit.absolute_value_total_boundary_client
set_option pp.fullNames true in
#print axioms LetwinPureBoundaryAudit.real_abs_minus_one_client
set_option pp.fullNames true in
#print axioms LetwinPureBoundaryAudit.emptyOmega_client

namespace LetwinTotalEquicontAudit
open FunctionalInequalities.Analysis

/-- Actual fixed nonsmooth finite-total-mass family; the exact support image
mass is constructed in the canonical audit, not a density premise. -/
theorem actual_abs_family :
    ∃ B : ℝ,
      0 < B ∧
        (∀ i : ℕ, ∀ x ∈ closure (Ioo (-1 : ℝ) 1), |(fun (_ : ℕ) (x : ℝ) => |x| - 1) i x| ≤ B) ∧
          EquicontinuousOn (fun (_ : ℕ) (x : ℝ) => |x| - 1) (closure (Ioo (-1 : ℝ) 1)) := by
  have hconv : ConvexOn ℝ univ (fun x : ℝ => |x| - 1) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have h := abs_add_le (a * x) (b * y)
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h
    change |a * x + b * y| - 1 ≤ a * (|x| - 1) + b * (|y| - 1)
    nlinarith
  have hfr : ∀ x ∈ frontier (Ioo (-1 : ℝ) 1), |x| - 1 = 0 := by
    intro x hx
    rw [frontier_Ioo (by norm_num : (-1 : ℝ) < 1)] at hx
    rcases hx with hx | hx
    · subst x; norm_num
    · simp only [mem_singleton_iff] at hx
      subst x; norm_num
  exact
    exists_uniform_bound_equicontinuousOn_of_domain_mass (E := ℝ) isOpen_Ioo (convex_Ioo _ _)
      (isBounded_Ioo _ _) (M := 2) (by norm_num) (fun (_ : ℕ) (x : ℝ) => |x| - 1)
      (fun _ => hconv.subset (subset_univ _) (convex_Ioo (-1 : ℝ) 1).closure)
      (fun _ => (continuous_abs.sub continuous_const).continuousOn) (fun _ => hfr)
      (fun _ => LetwinDomainTotalMassAudit.actual_absolute_total_mass_client.1.le)
end LetwinTotalEquicontAudit
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_uniform_bound_equicontinuousOn_of_domain_mass
set_option pp.fullNames true in
#print axioms LetwinTotalEquicontAudit.actual_abs_family

namespace LetwinDomainArzelaAudit
open FunctionalInequalities.Analysis

theorem actual_absolute_value_subsequence :
    ∃ (g : C(closure (Ioo (-1 : ℝ) 1), ℝ)) (φ : ℕ → ℕ),
      StrictMono φ ∧
        ∀ ε : ℝ,
          0 < ε →
            ∀ᶠ n in atTop,
              ∀ x : closure (Ioo (-1 : ℝ) 1),
                |(fun (_ : ℕ) (y : ℝ) => |y| - 1) (φ n) x - g x| < ε := by
  have hconv : ConvexOn ℝ univ (fun x : ℝ => |x| - 1) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have h := abs_add_le (a * x) (b * y)
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h
    change |a * x + b * y| - 1 ≤ a * (|x| - 1) + b * (|y| - 1)
    nlinarith
  have hfr : ∀ x ∈ frontier (Ioo (-1 : ℝ) 1), |x| - 1 = 0 := by
    intro x hx
    rw [frontier_Ioo (by norm_num : (-1 : ℝ) < 1)] at hx
    rcases hx with hx | hx
    · subst x; norm_num
    · simp only [mem_singleton_iff] at hx
      subst x; norm_num
  exact
    exists_subseq_uniform_on_closure_of_domain_mass (E := ℝ) isOpen_Ioo (convex_Ioo _ _)
      (isBounded_Ioo _ _) (M := 2) (by norm_num) (fun (_ : ℕ) (x : ℝ) => |x| - 1)
      (fun _ => hconv.subset (subset_univ _) (convex_Ioo (-1 : ℝ) 1).closure)
      (fun _ => (continuous_abs.sub continuous_const).continuousOn) (fun _ => hfr)
      (fun _ => LetwinDomainTotalMassAudit.actual_absolute_total_mass_client.1.le)
end LetwinDomainArzelaAudit
set_option pp.fullNames true in
#print axioms LetwinDomainArzelaAudit.actual_absolute_value_subsequence

namespace LetwinDomainLimitAudit
open FunctionalInequalities.Analysis

theorem actual_absolute_value_limit_convex :
    ∃ (g : ℝ → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
        ConvexOn ℝ (closure (Ioo (-1 : ℝ) 1)) g ∧
          ContinuousOn g (closure (Ioo (-1 : ℝ) 1)) ∧
            (∀ x ∈ frontier (Ioo (-1 : ℝ) 1), g x = 0) ∧
              ∀ ε : ℝ,
                0 < ε →
                  ∀ᶠ (n : ℕ) in atTop,
                    ∀ x ∈ closure (Ioo (-1 : ℝ) 1),
                      |(fun (_ : ℕ) (y : ℝ) => |y| - 1) (φ n) x - g x| < ε := by
  have hconv : ConvexOn ℝ univ (fun x : ℝ => |x| - 1) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have h := abs_add_le (a * x) (b * y)
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h
    change |a * x + b * y| - 1 ≤ a * (|x| - 1) + b * (|y| - 1)
    nlinarith
  have hfr : ∀ x ∈ frontier (Ioo (-1 : ℝ) 1), |x| - 1 = 0 := by
    intro x hx
    rw [frontier_Ioo (by norm_num : (-1 : ℝ) < 1)] at hx
    rcases hx with hx | hx
    · subst x; norm_num
    · simp only [mem_singleton_iff] at hx
      subst x; norm_num
  exact
    exists_convex_subseq_uniform_of_domain_mass (E := ℝ) isOpen_Ioo (convex_Ioo _ _)
      (isBounded_Ioo _ _) (M := 2) (by norm_num) (fun (_ : ℕ) (x : ℝ) => |x| - 1)
      (fun _ => hconv.subset (subset_univ _) (convex_Ioo (-1 : ℝ) 1).closure)
      (fun _ => (continuous_abs.sub continuous_const).continuousOn) (fun _ => hfr)
      (fun _ => LetwinDomainTotalMassAudit.actual_absolute_total_mass_client.1.le)

end LetwinDomainLimitAudit
#print axioms LetwinDomainLimitAudit.actual_absolute_value_limit_convex

namespace LetwinDomainMeasureAudit

open FunctionalInequalities.Analysis

/--
The producer applied to the genuine nonsmooth real source.
The total mass comes from the audit's proved actual domain-image calculation.
-/
theorem absolute_value_domain_measure :
    ∃ μ : Measure ℝ,
      μ (Ioo (-1 : ℝ) 1) = ENNReal.ofReal 2 ∧
      (∀ K : Set ℝ, IsCompact K →
        K ⊆ Ioo (-1 : ℝ) 1 → μ K < ⊤) := by
  have hv :
      ConvexOn ℝ (Ioo (-1 : ℝ) 1)
        (fun x : ℝ => |x| - 1) := by
    refine ⟨convex_Ioo _ _, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have h := abs_add_le (a * x) (b * y)
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h
    change |a * x + b * y| - 1 ≤
      a * (|x| - 1) + b * (|y| - 1)
    nlinarith

  have hvc :
      ContinuousOn (fun x : ℝ => |x| - 1)
        (Ioo (-1 : ℝ) 1) :=
    (continuous_abs.sub continuous_const).continuousOn

  obtain ⟨μ, hμ, hfin⟩ :=
    exists_domain_mongeAmpere_measure isOpen_Ioo hv hvc

  refine ⟨μ, ?_, hfin⟩
  rw [hμ _ isOpen_Ioo.measurableSet, inter_self]
  exact
    LetwinDomainTotalMassAudit.actual_absolute_total_mass_client.1


abbrev E0 := EuclideanSpace ℝ (Fin 0)

/--
Every ambient slope is an actual supporting slope in dimension zero.
This is proved from the support inequalities, rather than assumed.
-/
private theorem fin0_constant_domain_image :
    subgradientImageOn (fun _ : E0 => (0 : ℝ))
      (univ : Set E0) (univ : Set E0) = univ := by
  ext p
  constructor
  · intro _
    exact mem_univ p
  · intro _
    refine ⟨0, mem_univ _, ?_⟩
    intro y _hy
    have hy : y = (0 : E0) := Subsingleton.elim _ _
    have hp : p = (0 : E0) := Subsingleton.elim _ _
    simp [hy, hp]

/--
The zero-dimensional client has mass one, not mass zero.
No positive-dimensional hypothesis enters the producer or this client.
-/
theorem fin0_constant_domain_measure :
    ∃ μ : Measure E0,
      μ univ = 1 ∧
      (∀ K : Set E0, IsCompact K → μ K < ⊤) := by
  have hv :
      ConvexOn ℝ (univ : Set E0)
        (fun _ : E0 => (0 : ℝ)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b _ha _hb _hab
    simp

  have hvc :
      ContinuousOn (fun _ : E0 => (0 : ℝ)) (univ : Set E0) :=
    continuous_const.continuousOn

  obtain ⟨μ, hμ, hfin⟩ :=
    exists_domain_mongeAmpere_measure isOpen_univ hv hvc

  have hvolume : (volume : Measure E0) univ = 1 := by
    change (volume : Measure (EuclideanSpace ℝ (Fin 0))) univ = 1
    rw [volume_euclideanSpace_eq_dirac]
    simp

  refine ⟨μ, ?_, ?_⟩
  · calc
      μ univ =
          (volume : Measure E0)
            (subgradientImageOn (fun _ : E0 => (0 : ℝ))
              univ (univ ∩ univ)) :=
        hμ univ MeasurableSet.univ
      _ = (volume : Measure E0) univ := by
        rw [inter_self, fin0_constant_domain_image]
      _ = 1 := hvolume
  · intro K hK
    exact hfin K hK (subset_univ K)

end LetwinDomainMeasureAudit
set_option pp.fullNames true in
#print axioms LetwinDomainMeasureAudit.absolute_value_domain_measure
set_option pp.fullNames true in
#print axioms LetwinDomainMeasureAudit.fin0_constant_domain_measure
