import FunctionalInequalities.Poincare.FiniteProduct.Tensorization
import FunctionalInequalities.Poincare.Product.Reverse

/-!
# Lean certificate for `lem:poincare-finite-tensorization`

Source for the Poincaré product identity: Theorem 3.4 (Tensorization) in the combined manuscript
at commit `cd4a894a0faf40c0180f80b1a31eec1fdb6cb576`:
https://github.com/numina-functional-inequalities/kls-exploration/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L59-L68
The original gives `C_P(⊗ᵢ μᵢ) = maxᵢ C_P(μᵢ)`. Its LSI and conditional-decomposition claims
are outside this entry point. The fixed-constant upper bound follows by finite iteration of the
binary bound corresponding to BGL (2014), Proposition 4.3.1; reverse bounds use local coordinate
lifts. The defining modules give the precise source links and distinguish local helper results.

The dependent `PiLp 2` Hilbert encoding, arbitrary Borel probability factors with the repository's
smooth L² finite-gradient-energy tests, `NNReal` fixed constants, `ENNReal` optimal constants,
and the empty/zero-dimensional cases are local specifications of the product statement. No
Dirichlet-domain equivalence, finite optimal constant, or attainment assumption is imposed.

This default-build entry point prints the 45 reusable public declarations, including
transport, geometry, binary reverse bounds, and finite tensorization. Eight classes of typed
Euclidean applications below retain the complete specialization statements without adding
duplicate declarations or proof obligations. Six further checks exercise concrete boundary cases.
The named certificate at the end packages the node-level binary, finite-product, and boundary
conclusions directly from this reusable API.
-/

set_option pp.universes true
set_option format.width 100

#check @FunctionalInequalities.Poincare.contDiff_comp_projection
#check @FunctionalInequalities.Poincare.gradient_comp_projection
#check @FunctionalInequalities.Poincare.norm_gradient_comp_projection
#check @FunctionalInequalities.Poincare.memLp_comp_projection
#check @FunctionalInequalities.Poincare.integrable_gradient_comp_projection
#check @FunctionalInequalities.Poincare.Admissible.comp_projection
#check @FunctionalInequalities.Poincare.variance_comp_projection
#check @FunctionalInequalities.Poincare.energy_comp_projection
#check @FunctionalInequalities.Poincare.admissible_map_linearIsometryEquiv_iff
#check @FunctionalInequalities.Poincare.variance_map_linearIsometryEquiv
#check @FunctionalInequalities.Poincare.energy_map_linearIsometryEquiv
#check @FunctionalInequalities.Poincare.holds_map_linearIsometryEquiv_iff
#check @FunctionalInequalities.Poincare.constant_map_linearIsometryEquiv
#check @FunctionalInequalities.Poincare.holds_zero_of_subsingleton
#check @FunctionalInequalities.Poincare.constant_eq_zero_of_subsingleton
#check @FunctionalInequalities.Poincare.isometry_adjoint_fstL
#check @FunctionalInequalities.Poincare.isometry_adjoint_sndL
#check @FunctionalInequalities.Poincare.measurePreserving_prod_fst
#check @FunctionalInequalities.Poincare.measurePreserving_prod_snd
#check @FunctionalInequalities.Poincare.Holds.of_prod_left
#check @FunctionalInequalities.Poincare.Holds.of_prod_right
#check @FunctionalInequalities.Poincare.constant_left_le_prod
#check @FunctionalInequalities.Poincare.constant_right_le_prod
#check @FunctionalInequalities.Poincare.constant_prod_eq
#check @FunctionalInequalities.Poincare.piMeasure
#check @FunctionalInequalities.Poincare.piMeasure_isProbabilityMeasure
#check @FunctionalInequalities.Poincare.adjoint_pi_proj
#check @FunctionalInequalities.Poincare.isometry_adjoint_pi_proj
#check @FunctionalInequalities.Poincare.measurePreserving_pi_proj
#check @FunctionalInequalities.Poincare.piCongrLeft
#check @FunctionalInequalities.Poincare.piCongrLeft_apply
#check @FunctionalInequalities.Poincare.map_piMeasure_piCongrLeft
#check @FunctionalInequalities.Poincare.piOptionEquivProd
#check @FunctionalInequalities.Poincare.piOptionEquivProd_apply
#check @FunctionalInequalities.Poincare.map_piMeasure_piOptionEquivProd
#check @FunctionalInequalities.Poincare.Holds.pi
#check @FunctionalInequalities.Poincare.Holds.of_pi
#check @FunctionalInequalities.Poincare.constant_le_pi
#check @FunctionalInequalities.Poincare.constant_pi_le
#check @FunctionalInequalities.Poincare.constant_pi_eq
#check @FunctionalInequalities.Poincare.holds_pi_empty
#check @FunctionalInequalities.Poincare.constant_pi_empty
#check @FunctionalInequalities.Poincare.constant_pi_unique
#check @FunctionalInequalities.Poincare.constant_pi_of_subsingleton
#check @FunctionalInequalities.Poincare.constant_pi_eq_top_of_factor

/-! ## Euclidean application checks

These anonymous typed applications check that the reusable candidate API specializes to the
eight former Euclidean statements. Each expression binds every assumption explicitly, so its
printed type exposes the complete statement. Their sources are the reusable declarations named
in each expression; the applications create no additional public declarations or certificates.
-/

set_option pp.funBinderTypes true

open MeasureTheory
open FunctionalInequalities

-- 1. Local Euclidean specialization of `Holds.pi`, the finite iteration of the BGL upper bound.
-- The empty index type and its zero fixed constant are included by the local formulation.
#check (fun {ι : Type*} [Fintype ι] {d : ι → ℕ}
    {μ : ∀ i, Measure (EuclideanSpace ℝ (Fin (d i)))}
    [∀ i, IsProbabilityMeasure (μ i)] {C : ι → NNReal}
    (h : ∀ i, Poincare.Holds (μ i) (C i : ℝ)) ↦
  (Poincare.Holds.pi h :
    Poincare.Holds (Poincare.piMeasure μ) ((Finset.univ.sup C : NNReal) : ℝ)))

-- 2. The Poincaré product formula of manuscript Theorem 3.4, via `constant_pi_eq`.
-- This local `ENNReal` formulation includes infinite constants and an empty index type.
#check (fun {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (μ : ∀ i, Measure (EuclideanSpace ℝ (Fin (d i))))
    [∀ i, IsProbabilityMeasure (μ i)] ↦
  (Poincare.constant_pi_eq (μ := μ) :
    Poincare.constant (Poincare.piMeasure μ) = ⨆ i, Poincare.constant (μ i)))

-- 3. Local coordinate-lift consequences `Holds.of_prod_left` and `Holds.of_prod_right`;
-- both independent factor probability assumptions are retained.
#check (fun {m n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin m))}
    {ν : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : ℝ} (h : Poincare.Holds (Poincare.prodMeasure μ ν) C) ↦
  (⟨Poincare.Holds.of_prod_left h, Poincare.Holds.of_prod_right h⟩ :
    Poincare.Holds μ C ∧ Poincare.Holds ν C))

-- 4. Binary specialization of the manuscript product formula, via `constant_prod_eq`,
-- with the local `ENNReal` convention and arbitrary natural dimensions.
#check (fun {m n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] ↦
  (Poincare.constant_prod_eq (μ := μ) (ν := ν) :
    Poincare.constant (Poincare.prodMeasure μ ν) =
      max (Poincare.constant μ) (Poincare.constant ν)))

-- 5. Local empty-product consequence of `holds_pi_empty` and `constant_pi_empty`.
-- An arbitrary empty dependent family needs no factor probability premise.
#check (fun {d : Fin 0 → ℕ}
    (μ : ∀ i, Measure (EuclideanSpace ℝ (Fin (d i)))) ↦
  letI : ∀ i : Fin 0, IsProbabilityMeasure (μ i) := fun i ↦ Fin.elim0 i
  (⟨Poincare.holds_pi_empty (μ := μ), Poincare.constant_pi_empty (μ := μ)⟩ :
    Poincare.Holds (Poincare.piMeasure μ) 0 ∧
      Poincare.constant (Poincare.piMeasure μ) = 0))

-- 6. Local singleton specialization `constant_pi_unique` of the product identity,
-- including a zero-dimensional sole factor.
#check (fun {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] ↦
  (Poincare.constant_pi_unique (μ := fun _ : Fin 1 ↦ μ) :
    Poincare.constant (Poincare.piMeasure (fun _ : Fin 1 ↦ μ)) = Poincare.constant μ))

-- 7. Local subsingleton-space consequences: every factor may be zero-dimensional,
-- and the index type may also be empty. These boundary cases are not explicit in the manuscript.
#check (fun {ι : Type*} [Fintype ι]
    (μ : ∀ _ : ι, Measure (EuclideanSpace ℝ (Fin 0)))
    [∀ i, IsProbabilityMeasure (μ i)] ↦
  (⟨Poincare.holds_zero_of_subsingleton (Poincare.piMeasure μ),
      Poincare.constant_pi_of_subsingleton (μ := μ)⟩ :
    Poincare.Holds (Poincare.piMeasure μ) 0 ∧
      Poincare.constant (Poincare.piMeasure μ) = 0))

-- 8. Local `constant_eq_zero_of_subsingleton` consequence for a selected zero-dimensional
-- factor in an otherwise arbitrary dependent family.
#check (fun {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (μ : ∀ i, Measure (EuclideanSpace ℝ (Fin (d i))))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) (hi : d i = 0) ↦
  letI : Subsingleton (EuclideanSpace ℝ (Fin (d i))) :=
    hi.symm ▸ (inferInstance : Subsingleton (EuclideanSpace ℝ (Fin 0)))
  (Poincare.constant_eq_zero_of_subsingleton (μ i) : Poincare.constant (μ i) = 0))

/-! ## Additional boundary applications

These six checks retain the concrete `(0, n)`, `(n, 0)`, singleton-zero, empty, and two-zero-factor
applications. They are local boundary specializations of the same candidate API; the manuscript
does not state these cases separately.
-/

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀]
    {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] ↦
  (Poincare.constant_prod_eq (μ := μ₀) (ν := ν) :
    Poincare.constant (Poincare.prodMeasure μ₀ ν) =
      max (Poincare.constant μ₀) (Poincare.constant ν)))

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀]
    {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] ↦
  (Poincare.constant_prod_eq (μ := ν) (ν := μ₀) :
    Poincare.constant (Poincare.prodMeasure ν μ₀) =
      max (Poincare.constant ν) (Poincare.constant μ₀)))

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀] ↦
  (Poincare.constant_pi_unique (μ := fun _ : Fin 1 ↦ μ₀) :
    Poincare.constant (Poincare.piMeasure (fun _ : Fin 1 ↦ μ₀)) = Poincare.constant μ₀))

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀] ↦
  (Poincare.constant_pi_empty (μ := fun _ : Fin 0 ↦ μ₀) :
    Poincare.constant (Poincare.piMeasure (fun _ : Fin 0 ↦ μ₀)) = 0))

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀] ↦
  (Poincare.holds_pi_empty (μ := fun _ : Fin 0 ↦ μ₀) :
    Poincare.Holds (Poincare.piMeasure (fun _ : Fin 0 ↦ μ₀)) 0))

#check (fun (μ₀ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ₀] ↦
  (Poincare.constant_pi_of_subsingleton (μ := fun _ : Fin 2 ↦ μ₀) :
    Poincare.constant (Poincare.piMeasure (fun _ : Fin 2 ↦ μ₀)) = 0))

namespace Solutions.LemPoincareFiniteTensorization

/-- Machine certificate for the node-level conclusions of finite Poincaré tensorization.

The first block packages binary fixed-constant recovery and exact optimal constants. The second
packages finite fixed-constant tensorization and recovery, both optimal-bound directions, exact
optimal constants, and all finite-family boundary cases. The final independent block records the
fixed and optimal constants on an arbitrary subsingleton Hilbert probability space. -/
theorem certificate :
    (∀ {E F : Type*}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
      (μ : Measure E) (ν : Measure F)
      [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      (∀ ⦃C : ℝ⦄, Poincare.Holds (Poincare.prodMeasure μ ν) C →
        Poincare.Holds μ C ∧ Poincare.Holds ν C) ∧
      Poincare.constant μ ≤ Poincare.constant (Poincare.prodMeasure μ ν) ∧
      Poincare.constant ν ≤ Poincare.constant (Poincare.prodMeasure μ ν) ∧
      Poincare.constant (Poincare.prodMeasure μ ν) =
        max (Poincare.constant μ) (Poincare.constant ν)) ∧
    (∀ {ι : Type*} [Fintype ι] {E : ι → Type*}
      [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
      [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)]
      [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
      (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)],
      (∀ C : ι → NNReal, (∀ i, Poincare.Holds (μ i) (C i : ℝ)) →
        Poincare.Holds (Poincare.piMeasure μ) ((Finset.univ.sup C : NNReal) : ℝ)) ∧
      (∀ ⦃C : ℝ⦄ (i : ι), Poincare.Holds (Poincare.piMeasure μ) C →
        Poincare.Holds (μ i) C) ∧
      (∀ i, Poincare.constant (μ i) ≤ Poincare.constant (Poincare.piMeasure μ)) ∧
      Poincare.constant (Poincare.piMeasure μ) ≤ ⨆ i, Poincare.constant (μ i) ∧
      Poincare.constant (Poincare.piMeasure μ) = ⨆ i, Poincare.constant (μ i) ∧
      (∀ _h : IsEmpty ι,
        Poincare.Holds (Poincare.piMeasure μ) 0 ∧
          Poincare.constant (Poincare.piMeasure μ) = 0) ∧
      (∀ h : Unique ι,
        Poincare.constant (Poincare.piMeasure μ) = Poincare.constant (μ h.default)) ∧
      ((∀ i, Subsingleton (E i)) → Poincare.constant (Poincare.piMeasure μ) = 0) ∧
      (∀ i, Poincare.constant (μ i) = ⊤ →
        Poincare.constant (Poincare.piMeasure μ) = ⊤)) ∧
    (∀ {E : Type*}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
      (μ : Measure E) [IsProbabilityMeasure μ] [Subsingleton E],
      Poincare.Holds μ 0 ∧ Poincare.constant μ = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro E F _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _
    refine ⟨?_, Poincare.constant_left_le_prod, Poincare.constant_right_le_prod,
      Poincare.constant_prod_eq⟩
    intro C h
    exact ⟨h.of_prod_left, h.of_prod_right⟩
  · intro ι _ E _ _ _ _ _ _ μ _
    refine ⟨(fun C h ↦ Poincare.Holds.pi h), (fun {_} i h ↦ h.of_pi i),
      (fun i ↦ Poincare.constant_le_pi i), Poincare.constant_pi_le,
      Poincare.constant_pi_eq, ?_, ?_, ?_, (fun i h ↦
        Poincare.constant_pi_eq_top_of_factor i h)⟩
    · intro h
      let _ : IsEmpty ι := h
      exact ⟨Poincare.holds_pi_empty, Poincare.constant_pi_empty⟩
    · intro h
      let _ : Unique ι := h
      exact Poincare.constant_pi_unique
    · intro h
      let _ : ∀ i, Subsingleton (E i) := h
      exact Poincare.constant_pi_of_subsingleton
  · intro E _ _ _ _ _ _ μ _ _
    exact ⟨Poincare.holds_zero_of_subsingleton μ,
      Poincare.constant_eq_zero_of_subsingleton μ⟩

end Solutions.LemPoincareFiniteTensorization
