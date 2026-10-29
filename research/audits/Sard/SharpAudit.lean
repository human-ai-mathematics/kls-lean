import FunctionalInequalities.Analysis.Sard.Sharp
import FunctionalInequalities.KLS.BKL.Poincare
/-!
# Scope audit for the sharp finite-regularity Sard theorem

**What is proved.**  Seven of the eight propositions of
`research/audits/Sard/SharpRouteStatements.lean` are restated **verbatim** below and discharged:
`M1`, `M1'`, `M3`, `M4`, `M5`, `M6` and the diagnostic `D1`.  In particular `route_M6` is the
contract `FunctionalInequalities.Analysis.sard` from `Analysis/Sard/Sharp.lean`, independently
restated with the route's full signature. This client separates that theorem from the original
mean value step contract of the route file and its repaired version.

**The original mean value step is not proved by this client; as written it is false.**  The route
file asks the mean value step along parametric segments to hold for an arbitrary `C¹`
parametrized map `φ`, with the route record stating that "the
antilipschitz constant of `φ` is not needed here".  It is needed.  Without it the hypothesis
controls `fderiv ℝ f` only *on the curve*, while the conclusion measures the increment of `f`
against the *chordal* distance `‖φ a - φ z‖`, and a curve may travel a long way and return close to
where it started.  Concretely, with `n = 2`, `p = 1`, `k = 0`, take for `φ` the `C¹` spiral
`φ t = (t³ cos (1/t), t³ sin (1/t))` (`φ 0 = 0`), take `S = {φ 0} ∪ {φ (1/(2πm)) | m ≥ 1}` — the
points where the spiral meets the positive `x`-axis, at radii `r m = (2πm)⁻³` — and take for `f` a
differentiable function whose gradient has size `m^(-1/2)` on the `m`-th turn and which increases
along the spiral.  The parametric segment between two points of `S` covers a whole stretch of the
spiral, so the hypothesis holds: the sup of `‖fderiv ℝ f‖` over it tends to `0` together with the
chordal distance between its endpoints.  But between consecutive points of `S` the spiral has
length `≈ 2π r m` while the chordal distance is only `r m - r (m+1) ≈ 3 r m / m`, so the increment
of `f` is `≈ 2π m^(-1/2) r m` against a right-hand side `3 ε r m / m`, and the ratio `m^(1/2)`
diverges.  **This refutation is a pen-and-paper argument; it is not formalized here**, so the
original statement is recorded as unproved rather than as formally false, and no statement named
`route_M2` is declared below.

**The repair is the antilipschitz constant, it is proved, and it is free on the route.**
`route_M2_antilipschitz` is the original statement verbatim with the disk's antilipschitz bound
added as a hypothesis, discharged from `Analysis.MorseSard.abs_sub_le_of_flat_fderiv`.  That
hypothesis is available wherever the route consumes the mean value step: the disks of a Morse
decomposition carry it by definition, as the Morse vanishing lemma `route_M3` itself states, so
`route_M4`, `route_M5` and `route_M6` are unaffected.  Nothing downstream is weakened, and the
route's conclusion is reached in full.

**Consistency checks.**  `route_M6` is strictly stronger than the three Sard statements already in
the repository, and `sard_smooth_recovered`, `sard_plane_recovered` and
`sard_finrank_le_one_recovered` derive their statements from it without naming them in the
proofs.  `dimension_zero` and `constant_function` are the two boundary cases.

The Cheeger comparisons, energy identifications and dimension-free KLS bound are outside this
client's scope. Its theorems concern finite-regularity Sard and the listed diagnostics.
-/

noncomputable section

open Set Metric MeasureTheory Filter Topology Module
open FunctionalInequalities FunctionalInequalities.Analysis
open scoped ContDiff

namespace SharpSardAudit

/-! ### The graph map is `1`-antilipschitz -/

/-- **Route obligation `M1'`**, copied verbatim from
`research/audits/Sard/SharpRouteStatements.lean` and discharged. -/
theorem route_M1' :
    (∀ {n : ℕ} (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ) (a b : Fin n → ℝ),
      ‖a - b‖ ≤ ‖Fin.insertNth (α := fun _ => ℝ) i (θ a) a
        - Fin.insertNth (α := fun _ => ℝ) i (θ b) b‖) :=
  fun i θ a b => MorseSard.norm_sub_le_insertNth i θ a b

/-! ### The `C^k` graph chart of a regular zero set -/

/-- **Route obligation `M1`**, copied verbatim from
`research/audits/Sard/SharpRouteStatements.lean` and discharged. -/
theorem route_M1 :
    (∀ {n k : ℕ}, 1 ≤ k → ∀ {w : (Fin (n + 1) → ℝ) → ℝ} {x₀ : Fin (n + 1) → ℝ},
      ContDiff ℝ k w → w x₀ = 0 → fderiv ℝ w x₀ ≠ 0 →
      ∃ (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ), ContDiff ℝ k θ ∧
        ∀ᶠ x in 𝓝 x₀, w x = 0 →
          x = Fin.insertNth (α := fun _ => ℝ) i (θ (Fin.removeNth i x)) (Fin.removeNth i x)) := by
  intro n k hk w x₀ hw hx₀ hd
  exact MorseSard.exists_graph hk hw hx₀ hd

/-! ### The mean value step, repaired with the antilipschitz constant -/

/-- **Route obligation `M2` of `research/audits/Sard/SharpRouteStatements.lean` with its missing
hypothesis restored.**  Verbatim the original statement, with the antilipschitz bound of the disk
added between the `C¹` hypothesis on `φ` and the hypothesis on the coordinates of `fderiv ℝ f`.
See the header for why the original statement without it is false, and why the repair costs the
route nothing. -/
theorem route_M2_antilipschitz :
    (∀ {n p k : ℕ} {φ : (Fin p → ℝ) → (Fin n → ℝ)}, ContDiff ℝ 1 φ →
      ∀ {κ : ℝ}, 0 ≤ κ →
      (∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
        ‖a - b‖ ≤ κ * ‖φ a - φ b‖) →
      ∀ {S : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}, Differentiable ℝ f →
      (∀ j : Fin n, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
          φ a ∈ S → φ b ∈ S → ‖φ a - φ b‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
            |fderiv ℝ f (φ (a + s • (b - a))) (Pi.single j (1 : ℝ))|
              ≤ ε * ‖φ a - φ (a + s • (b - a))‖ ^ k) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
          φ a ∈ S → φ b ∈ S → ‖φ a - φ b‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
            |f (φ (a + s • (b - a))) - f (φ a)|
              ≤ ε * ‖φ a - φ (a + s • (b - a))‖ ^ (k + 1)) := by
  intro n p k φ hφ κ hκ hanti S f hf hflat
  exact MorseSard.abs_sub_le_of_flat_fderiv ⟨hφ, hκ, hanti⟩ hf hflat

/-! ### The Morse vanishing lemma -/

/-- **Route obligation `M3`**, copied verbatim from
`research/audits/Sard/SharpRouteStatements.lean` and discharged.  This is the central step of
the route. -/
theorem route_M3 :
    (∀ (n k : ℕ) (A : Set (Fin n → ℝ)),
      ∃ (A₀ : Set (Fin n → ℝ))
        (P : Set (Set (Fin n → ℝ) × Σ p : ℕ, (Fin p → ℝ) → (Fin n → ℝ))),
        A₀.Countable ∧ P.Countable ∧ A ⊆ A₀ ∪ ⋃ q ∈ P, q.1 ∧
        (∀ q ∈ P, q.1 ⊆ A ∧ q.1 ⊆ q.2.2 '' closedBall (0 : Fin q.2.1 → ℝ) 1 ∧
          ContDiff ℝ 1 q.2.2 ∧
          ∃ κ : ℝ, 0 ≤ κ ∧ ∀ a ∈ closedBall (0 : Fin q.2.1 → ℝ) 1,
            ∀ b ∈ closedBall (0 : Fin q.2.1 → ℝ) 1, ‖a - b‖ ≤ κ * ‖q.2.2 a - q.2.2 b‖) ∧
        ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ k f → (∀ x ∈ A, f x = 0) → ∀ q ∈ P,
          ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
            ∀ a ∈ closedBall (0 : Fin q.2.1 → ℝ) 1, ∀ b ∈ closedBall (0 : Fin q.2.1 → ℝ) 1,
              q.2.2 a ∈ q.1 → q.2.2 b ∈ q.1 → ‖q.2.2 a - q.2.2 b‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
                |f (q.2.2 (a + s • (b - a)))| ≤ ε * ‖q.2.2 a - q.2.2 (a + s • (b - a))‖ ^ k) :=
  fun n k A => MorseSard.exists_decomp n k A

/-! ### The Morse criticality lemma -/

/-- **Route obligation `M4`**, copied verbatim from
`research/audits/Sard/SharpRouteStatements.lean` and discharged. -/
theorem route_M4 :
    (∀ {n k : ℕ} (A : Set (Fin n → ℝ)) {f : (Fin n → ℝ) → ℝ},
      ContDiff ℝ (k + 1) f → (∀ x ∈ A, fderiv ℝ f x = 0) →
      ∃ (A₀ : Set (Fin n → ℝ)) (P : Set (Set (Fin n → ℝ))), A₀.Countable ∧ P.Countable ∧
        A ⊆ A₀ ∪ ⋃₀ P ∧
        ∀ S ∈ P, Bornology.IsBounded S ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ (k + 1)) := by
  intro n k A f hf hA
  exact exists_cover_of_critical A hf hA

/-! ### Sard for `C^n` real-valued functions on `Fin n → ℝ` -/

/-- **Route obligation `M5`**, copied verbatim from
`research/audits/Sard/SharpRouteStatements.lean` and discharged. -/
theorem route_M5 :
    (∀ (n : ℕ) (u : (Fin n → ℝ) → ℝ), ContDiff ℝ n u →
      (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0) :=
  fun n u hu => sard_pi n u hu

/-! ### The target: `Analysis.sard`, verbatim -/

/-- **Route obligation `M6`**, copied verbatim from
`research/audits/Sard/SharpRouteStatements.lean` and discharged.  This is the statement of the
contract `Analysis.sard` of `Analysis/Sard/Sharp.lean`. -/
theorem route_M6 :
    (∀ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      {u : V → ℝ}, ContDiff ℝ (Module.finrank ℝ V) u →
      (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0) :=
  fun hu => sard hu

/-! ### The diagnostic: restriction to a `C^k` graph keeps only `C^k` -/

/-- **Route diagnostic `D1`**, copied verbatim from
`research/audits/Sard/SharpRouteStatements.lean` and discharged.  It is not a step of the route; it
records the regularity bookkeeping that makes the smooth descent fail at finite regularity. -/
theorem route_D1 :
    (∀ {n k : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ} {θ : (Fin n → ℝ) → ℝ} (i : Fin (n + 1)),
      ContDiff ℝ k u → ContDiff ℝ k θ →
      ContDiff ℝ k (fun y : Fin n → ℝ => u (Fin.insertNth (α := fun _ => ℝ) i (θ y) y))) :=
  fun i hu hθ => hu.comp (MorseSard.contDiff_insertNth i hθ)

#print axioms route_M1'
#print axioms route_M1
#print axioms route_M2_antilipschitz
#print axioms route_M3
#print axioms route_M4
#print axioms route_M5
#print axioms route_M6
#print axioms route_D1

section NormedSpace

variable {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-! ### Consistency: `route_M6` recovers the Sard statements already in the repository

The three statements are restated here and derived from `route_M6` (or from `route_M5`); no proof
below names `Analysis.sard_smooth`, `Analysis.sard_plane` or `Analysis.sard_of_finrank_le_one`. -/

/-- The statement of the `C^∞` Sard theorem of `Analysis/Sard/Smooth.lean`, recovered from the
sharp statement: `C^∞` implies `C^(finrank ℝ V)`. -/
theorem sard_smooth_recovered {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 :=
  sard (hu.of_le (by norm_cast; exact le_top))

/-- The statement of the planar Sard theorem of `Analysis/Sard/Planar.lean`, recovered from the
sharp statement in dimension two. -/
theorem sard_plane_recovered {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 :=
  sard_pi 2 u hu

/-- The statement of the low-dimensional Sard theorem of `Analysis/Sard/Basic.lean`, recovered from
the sharp statement: the dimension hypothesis is no longer needed. -/
theorem sard_finrank_le_one_recovered {u : V → ℝ} (_hdim : Module.finrank ℝ V ≤ 1)
    (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 :=
  sard hu

/-! ### Boundary cases -/

/-- Dimension zero: the domain is a single point, so the image of the critical set is a single
point and no regularity is needed. -/
theorem dimension_zero (hV : Module.finrank ℝ V = 0) (u : V → ℝ) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  have : Subsingleton V := Module.finrank_zero_iff.mp hV
  exact Set.Subsingleton.measure_zero
    (Set.Subsingleton.image (fun a _ b _ => Subsingleton.elim a b) u) _

end FiniteDimensional

/-- A constant function: every point is critical and the whole image is one value. -/
theorem constant_function
    [FiniteDimensional ℝ V] (c : ℝ) :
    (volume : Measure ℝ)
      ((fun _ : V => c) '' {x | fderiv ℝ (fun _ : V => c) x = 0}) = 0 := by
  refine measure_mono_null (t := {c}) ?_ (by simp)
  rintro _ ⟨x, _, rfl⟩
  simp

/-- The critical set of a constant function is everything, so the boundary case above is not
vacuous. -/
theorem constant_function_critical_set
    (c : ℝ) : {x : V | fderiv ℝ (fun _ : V => c) x = 0} = Set.univ := by
  ext x
  simp

#print axioms sard_smooth_recovered
#print axioms sard_plane_recovered
#print axioms sard_finrank_le_one_recovered
#print axioms dimension_zero
#print axioms constant_function
#print axioms constant_function_critical_set

end NormedSpace

end SharpSardAudit
