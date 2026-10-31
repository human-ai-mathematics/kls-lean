module

public import FunctionalInequalities.Analysis.Convex.GaugeCone.PrescribedAtom
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open Set Metric MeasureTheory
open scoped RealInnerProductSpace Pointwise Topology
namespace LetwinGaugeConeAudit
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.GaugeCone

private lemma real_cone_formula : potential (ball (0 : ℝ) 1) 1 = (fun x : ℝ => |x| - 1) := by
  funext x
  simp only [potential, gauge_unit_ball, one_mul, Real.norm_eq_abs]

private lemma fin0_cone_formula :
    potential (univ : Set (EuclideanSpace ℝ (Fin 0))) 1 = (fun _ => (-1 : ℝ)) := by
  funext x
  have hx : x = 0 := Subsingleton.elim _ _
  simp [potential, hx]

/-- The actual real unit-ball cone is |x|-1; its vertex support identity
comes from the source construction, without assuming a polar formula. -/
theorem actual_real_abs_cone :
    ConvexOn ℝ univ (fun x : ℝ => |x| - 1) ∧
      Continuous (fun x : ℝ => |x| - 1) ∧
        (∀ z ∈ frontier (ball (0 : ℝ) 1), |z| - 1 = 0) ∧
          subgradientImageOn (fun x : ℝ => |x| - 1) (ball 0 1) {0} =
            {p : ℝ | ∀ y ∈ ball (0 : ℝ) 1, ⟪p, y⟫ ≤ 1} := by
  have ht :=
    geometry (E := ℝ) (D := ball 0 1) isOpen_ball (convex_ball _ _) (by simp) (h := 1)
      (by norm_num)
  rw [real_cone_formula] at ht
  dsimp only [polar] at ht
  exact ⟨ht.1, ht.2.1, ht.2.2.2.1, ht.2.2.2.2⟩

/-- On the true zero-dimensional carrier the actual vertex image is all of
the singleton space, not an empty set. No measure is mentioned. -/
theorem actual_fin0_vertex :
    subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (-1 : ℝ)) univ {0} = univ := by
  have ht :=
    geometry (E := EuclideanSpace ℝ (Fin 0)) (D := univ) isOpen_univ convex_univ (mem_univ _)
      (h := 1) (by norm_num)
  rw [fin0_cone_formula] at ht
  dsimp only [polar] at ht
  rw [ht.2.2.2.2]
  ext p
  simp only [mem_ofPred_eq, mem_univ, iff_true]
  intro y _hy
  have hy : y = 0 := Subsingleton.elim _ _
  simp [hy]

/-- A genuine positive-dimensional cone source has zero image mass on EVERY
nonvertex subset, with no measurability or MA input from the client. -/
theorem actual_real_nonvertex_zero {G : Set ℝ} (hG : G ⊆ ball (0 : ℝ) 1) (hG0 : (0 : ℝ) ∉ G) :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (subgradientImageOn (fun x : ℝ => |x| - 1) (ball 0 1) G) =
      0 := by
  have ht :=
    volume_image (E := ℝ) (D := ball 0 1) isOpen_ball (convex_ball _ _) (by simp) (h := 1)
      (by norm_num)
  have hv := ht G hG
  rw [real_cone_formula] at hv
  simpa only [ite_eq_right hG0] using hv

/-- The actual atomic raw equation on the true zero-dimensional source has
mass ONE. It is not an empty carrier or a zero-volume exception. -/
theorem actual_fin0_atomic_mass :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 0)))
        (subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (-1 : ℝ)) univ univ) =
      1 := by
  let E := EuclideanSpace ℝ (Fin 0)
  have ht :=
    volume_image (E := E) (D := univ) isOpen_univ convex_univ (mem_univ _) (h := 1)
      (by norm_num)
  have hP : {p : E | ∀ y ∈ (univ : Set E), ⟪p, y⟫ ≤ (1 : ℝ)} = univ := by
    ext p
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    intro y _hy
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  rw [fin0_cone_formula] at ht
  dsimp only [polar] at ht
  rw [hP] at ht
  have hv := ht univ subset_rfl
  rw [ite_eq_left (mem_univ _)] at hv
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure E) univ = 1 := by
    rw [volume_euclideanSpace_eq_dirac]
    simp
  rw [hvol] at hv
  exact hv


/-- Actual bounded unit-ball data and a desired weight of three produce the
cone; no atomic MA or reference-existence input is assumed. -/
theorem actual_mass_three :
    ∃ h : ℝ,
      0 < h ∧
        (∀ z ∈ frontier (ball (0 : EuclideanSpace ℝ (Fin 1)) 1), potential (ball 0 1) h z = 0) ∧
          (volume : Measure (EuclideanSpace ℝ (Fin 1)))
              (subgradientImageOn (potential (ball 0 1) h) (ball 0 1) (ball 0 1)) =
            3 := by
  obtain ⟨h, hh, _hc, _hct, hfr, hMA⟩ :=
    exists_height_of_mass (n := 1) (by norm_num) (D := ball (0 : EuclideanSpace ℝ (Fin 1)) 1)
      isOpen_ball (convex_ball _ _) (by simp) isBounded_ball (m := 3) (by norm_num)
  refine ⟨h, hh, hfr, ?_⟩
  have hv := hMA (ball 0 1) subset_rfl
  norm_num at hv
  exact hv

/-- The positive-dimensional unit-ball source generates its actual MA measure
of total mass three, retaining the actual Borel supporting-image formula. -/
theorem actual_measure_mass_three :
    ∃ (h : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin 1))),
      0 < h ∧
        μ univ = 3 ∧
          ∀ G : Set (EuclideanSpace ℝ (Fin 1)),
            MeasurableSet G →
              μ G =
                (volume : Measure (EuclideanSpace ℝ (Fin 1)))
                  (subgradientImageOn (potential (ball 0 1) h) (ball 0 1) (G ∩ ball 0 1)) := by
  obtain ⟨h, μ, hh, _hcv, _hct, _hfr, hμ, _hfin, hident⟩ :=
    exists_mongeAmpere_measure_of_mass (n := 1) (by norm_num) (D :=
      ball (0 : EuclideanSpace ℝ (Fin 1)) 1) isOpen_ball (convex_ball _ _) (by simp)
      isBounded_ball (m := 3) (by norm_num)
  refine ⟨h, μ, hh, ?_, hμ⟩
  rw [hident]
  norm_num


private def actualVertex : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
private def actualDomain : Set (EuclideanSpace ℝ (Fin 1)) := ball actualVertex 1

private theorem actual_geometry :
    IsOpen actualDomain ∧
      Convex ℝ actualDomain ∧
        Bornology.IsBounded actualDomain ∧ actualVertex ∈ actualDomain ∧ actualVertex ≠ 0 := by
  refine ⟨isOpen_ball, convex_ball _ _, isBounded_ball, ?_, ?_⟩
  · exact mem_ball_self (by norm_num)
  · intro hz
    have ht := congrArg (fun x : EuclideanSpace ℝ (Fin 1) => x 0) hz
    norm_num [actualVertex] at ht

/-- The atom is genuinely away from zero and its SAME generated measure
has the requested point mass and total mass; no source MA data are assumed. -/
theorem actual_translated_mass_two :
    ∃ (u : EuclideanSpace ℝ (Fin 1) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin 1))),
      ConvexOn ℝ univ u ∧
        Continuous u ∧
          (∀ z ∈ frontier actualDomain, u z = 0) ∧
            (∀ G,
                MeasurableSet G →
                  μ G = volume (subgradientImageOn u actualDomain (G ∩ actualDomain))) ∧
              μ { actualVertex } = 2 ∧ μ univ = 2 ∧ actualVertex ≠ 0 := by
  obtain ⟨ho, hc, hb, hx, hne⟩ := actual_geometry
  obtain ⟨u, μ, hcv, hct, hfr, hformula, _, heq⟩ :=
    exists_one_atom (by norm_num : 0 < 1) ho hc hb hx (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨u, μ, hcv, hct, hfr, hformula, ?_, ?_, hne⟩ <;> rw [heq] <;> simp

/-- Zero target weight is generated in positive dimension by the actual
constant source, and retains the all-Borel formula of the SAME measure. -/
theorem actual_zero_weight :
    ∃ (u : EuclideanSpace ℝ (Fin 1) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin 1))),
      ConvexOn ℝ univ u ∧
        Continuous u ∧
          (∀ z ∈ frontier actualDomain, u z = 0) ∧
            (∀ G,
                MeasurableSet G →
                  μ G = volume (subgradientImageOn u actualDomain (G ∩ actualDomain))) ∧
              μ univ = 0 := by
  obtain ⟨ho, hc, hb, hx, _⟩ := actual_geometry
  obtain ⟨u, μ, hcv, hct, hfr, hformula, _, heq⟩ :=
    exists_one_atom (by norm_num : 0 < 1) ho hc hb hx (le_refl (0 : ℝ))
  refine ⟨u, μ, hcv, hct, hfr, hformula, ?_⟩
  rw [heq]
  simp


end LetwinGaugeConeAudit
#print axioms LetwinGaugeConeAudit.actual_real_abs_cone
#print axioms LetwinGaugeConeAudit.actual_fin0_vertex
#print axioms LetwinGaugeConeAudit.actual_real_nonvertex_zero
#print axioms LetwinGaugeConeAudit.actual_fin0_atomic_mass

#print axioms LetwinGaugeConeAudit.actual_mass_three
#print axioms LetwinGaugeConeAudit.actual_measure_mass_three

#print axioms LetwinGaugeConeAudit.actual_translated_mass_two
#print axioms LetwinGaugeConeAudit.actual_zero_weight
