module

public import FunctionalInequalities.Analysis.Vector.RankDeficient.Stratification
public import FunctionalInequalities.Analysis.Vector.RankDeficient.RightInverseBound
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-! # The tangential small-Lipschitz estimate on fibres

A projected map has a Lipschitz constant proportional to the derivative approximation error along
fibres of its regular component.

**This is the analytic content the route turns on, and the step that replaces the one that fails.**
The proved vanishing-derivative argument covers the rank-zero layer because there the approximating
partition makes `u` itself `ε`-Lipschitz on each piece.  On a stratum of rank `r ≥ 1` it does not,
in any direction inside the range of the differential.  What small tangential Lipschitz control says
is that the **projected** map
`Q ∘ f` is nevertheless Lipschitz with a constant proportional to `ε` **along each fibre of
`P ∘ f`** — which is exactly what the Eilenberg bound needs inside a fibre.

**The estimate in one line.**  For `a`, `b` in one fibre, `P (f b) = P (f a)`, so the approximation
gives `‖P (A (b - a))‖ ≤ ‖P‖ ε ‖b - a‖`: the chord is *almost* in the kernel of `P ∘ A`, though not
in it.  The uniform right-inverse bound converts that into an actual kernel element `w` with `‖(b -
a) - w‖ ≤ C ‖P (A (b-a))‖`,
The kernel identity says `A w = 0`, and therefore `‖A (b - a)‖ ≤ ‖A‖ C ‖P‖ ε ‖b - a‖`.  Feeding this
back into the
approximation bounds `‖f b - f a‖`, and applying `Q` gives the constant
`‖Q‖ (1 + ‖A‖ C ‖P‖)`, which **does not depend on `ε`**.

That independence is the whole point: the `ε → 0` limit of the Eilenberg argument uses a different
approximating partition at every scale, so a constant that grew with the partition would be
useless.

No inner product, no measure, no completeness and no finite-dimensionality is used by small
tangential Lipschitz control itself;
the hypotheses are exactly the conclusions of the kernel identity and the uniform right-inverse
bound for the linear model, and
`exists_lipschitzOnWith_fibre` records what they combine to on a rank stratum.
-/

@[expose] public section

noncomputable section

open Set Module
open scoped NNReal

namespace FunctionalInequalities.Analysis

section Tangential

variable {V W W₁ W₂ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]

/-- A chord of a fibre of `P ∘ f` is almost annihilated by `P ∘ A`.  This is the only place the
fibre hypothesis is used, and it is where the estimate differs from the vanishing-derivative case:
the chord is **not** in the kernel, only within `‖P‖ ε ‖b - a‖` of being so. -/
theorem norm_comp_apply_sub_le_of_approximatesLinearOn {A : V →L[ℝ] W} {P : W →L[ℝ] W₁}
    {f : V → W} {S : Set V} {ε : ℝ≥0} (hf : ApproximatesLinearOn f A S ε) {s : W₁}
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hfa : P (f a) = s) (hfb : P (f b) = s) :
    ‖P (A (b - a))‖ ≤ ‖P‖ * (ε * ‖b - a‖) := by
  have hrw : P (f b - f a - A (b - a)) = - P (A (b - a)) := by
    rw [map_sub, map_sub, hfa, hfb, sub_self, zero_sub]
  calc ‖P (A (b - a))‖ = ‖P (f b - f a - A (b - a))‖ := by rw [hrw, norm_neg]
    _ ≤ ‖P‖ * ‖f b - f a - A (b - a)‖ := P.le_opNorm _
    _ ≤ ‖P‖ * (ε * ‖b - a‖) := mul_le_mul_of_nonneg_left (hf b hb a ha) (norm_nonneg P)

/--
**small tangential Lipschitz control: the tangential small-Lipschitz estimate.**  If the linear
model `A` dies on the kernel
of `P ∘ A` — the conclusion of the kernel identity — and vectors almost annihilated by `P ∘ A` are
close to that
kernel with constant `C` — the conclusion of the uniform right-inverse bound — then on every fibre
of `P ∘ f` the projected map
`Q ∘ f` is Lipschitz with constant proportional to the approximation parameter `ε`.

The constant `c = ‖Q‖ (1 + ‖A‖ C ‖P‖)` depends only on the linear data, **never on `ε`, on `f`, on
`S` or on the fibre**, which is what makes it usable in the `ε → 0` limit.

`f` is an arbitrary function, `S` an arbitrary set, and no finite-dimensionality, inner product,
measurability or completeness is assumed.  This is the **explicit-constant** form; the
existential statement is `exists_lipschitzOnWith_of_ker_bound` just below. -/
theorem lipschitzOnWith_of_ker_bound (A : V →L[ℝ] W) (P : W →L[ℝ] W₁) (Q : W →L[ℝ] W₂) (C : ℝ≥0)
    (hker : ∀ z : V, P (A z) = 0 → A z = 0)
    (hinv : ∀ z : V, ∃ w : V, P (A w) = 0 ∧ ‖z - w‖ ≤ C * ‖P (A z)‖) (ε : ℝ≥0) (f : V → W)
    (S : Set V) (s : W₁) (hf : ApproximatesLinearOn f A S ε) :
    LipschitzOnWith ((‖Q‖₊ * (1 + ‖A‖₊ * C * ‖P‖₊)) * ε) (fun x => Q (f x))
      (S ∩ {x : V | P (f x) = s}) := by
  refine
    LipschitzOnWith.of_dist_le_mul fun b hb a ha =>
      ?_
  -- the chord is almost in the kernel of `P ∘ A`

  have hPA : ‖P (A (b - a))‖ ≤ ‖P‖ * (ε * ‖b - a‖) :=
    norm_comp_apply_sub_le_of_approximatesLinearOn hf ha.1 hb.1 ha.2
      hb.2
  -- the uniform right-inverse bound replaces it by an honest kernel element, and the kernel
  -- identity kills the linear model there

  obtain ⟨w, hw, hwle⟩ := hinv (b - a)
  have hAw : A w = 0 := hker w hw
  have hAz : A (b - a) = A (b - a - w) := by rw [map_sub A (b - a) w, hAw, sub_zero]
  have hA : ‖A (b - a)‖ ≤ ‖A‖ * (C * (‖P‖ * (ε * ‖b - a‖))) := by
    rw [hAz]
    refine (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg A))
    exact
      hwle.trans
        (mul_le_mul_of_nonneg_left hPA C.coe_nonneg)
  -- feed it back into the approximation and apply `Q`

  have hfba : ‖f b - f a‖ ≤ ε * ‖b - a‖ + ‖A‖ * (C * (‖P‖ * (ε * ‖b - a‖))) := by
    have htri : ‖f b - f a‖ ≤ ‖f b - f a - A (b - a)‖ + ‖A (b - a)‖ := by
      simpa using norm_add_le (f b - f a - A (b - a)) (A (b - a))
    exact htri.trans (add_le_add (hf b hb.1 a ha.1) hA)
  have hcoe : ((‖Q‖₊ * (1 + ‖A‖₊ * C * ‖P‖₊) * ε : ℝ≥0) : ℝ) = ‖Q‖ * (1 + ‖A‖ * C * ‖P‖) * ε := by
    push_cast; ring
  rw [dist_eq_norm, dist_eq_norm, hcoe, ← map_sub]
  calc
    ‖Q (f b - f a)‖ ≤ ‖Q‖ * ‖f b - f a‖ := Q.le_opNorm _
    _ ≤ ‖Q‖ * (ε * ‖b - a‖ + ‖A‖ * (C * (‖P‖ * (ε * ‖b - a‖)))) :=
      mul_le_mul_of_nonneg_left hfba (norm_nonneg Q)
    _ = ‖Q‖ * (1 + ‖A‖ * C * ‖P‖) * ε * ‖b - a‖ := by ring

/-- **The tangential small-Lipschitz estimate, existential form.**  The
constant supplied by `lipschitzOnWith_of_ker_bound` is `‖Q‖ (1 + ‖A‖ C ‖P‖)`, which depends
only on the linear data and **never on `ε`, on `f`, on `S` or on the fibre**.  The explicit form is
what a per-stratum assembly needs, because the approximating partition produces a different linear
model on every piece and the constant has to be uniform over them. -/
theorem exists_lipschitzOnWith_of_ker_bound (A : V →L[ℝ] W) (P : W →L[ℝ] W₁) (Q : W →L[ℝ] W₂)
    (C : ℝ≥0) (hker : ∀ z : V, P (A z) = 0 → A z = 0)
    (hinv : ∀ z : V, ∃ w : V, P (A w) = 0 ∧ ‖z - w‖ ≤ C * ‖P (A z)‖) :
    ∃ c : ℝ≥0, ∀ (ε : ℝ≥0) (f : V → W) (S : Set V) (s : W₁),
      ApproximatesLinearOn f A S ε →
        LipschitzOnWith (c * ε) (fun x => Q (f x)) (S ∩ {x : V | P (f x) = s}) :=
  ⟨‖Q‖₊ * (1 + ‖A‖₊ * C * ‖P‖₊),
    fun ε f S s hf => lipschitzOnWith_of_ker_bound A P Q C hker hinv ε f S s hf⟩

end Tangential

section Stratum

variable {V W W₁ W₂ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [FiniteDimensional ℝ W₁]
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]

/--
**What the kernel identity, the uniform right-inverse bound and small tangential Lipschitz control
combine to on a rank stratum.**  If `P ∘ A` is surjective onto a
space of the same dimension as the range of `A` — the situation at a point of the rank stratum, with
`P` the projection onto the range of the differential — then the two hypotheses of small tangential
Lipschitz control are
available, and the projected map is `c ε`-Lipschitz along every fibre of `P ∘ f`.

This is a **corollary of the three proved obligations, not a new one**, and in particular it is
**not** fibrewise slicing: it says nothing about measures, slices or Hausdorff dimension, and the
approximating
partition that would supply `f` and `S` is not constructed here. -/
theorem exists_lipschitzOnWith_fibre {A : V →L[ℝ] W} {P : W →L[ℝ] W₁} (Q : W →L[ℝ] W₂)
    (hsurj : Function.Surjective (P.comp A))
    (hrank : finrank ℝ W₁ = finrank ℝ (LinearMap.range (A : V →ₗ[ℝ] W))) :
    ∃ c : ℝ≥0,
      ∀ (ε : ℝ≥0) (f : V → W) (S : Set V) (s : W₁),
        ApproximatesLinearOn f A S ε →
          LipschitzOnWith (c * ε) (fun x => Q (f x)) (S ∩ {x : V | P (f x) = s}) := by
  obtain ⟨C, hC⟩ := exists_rightInverse_bound hsurj
  exact
    exists_lipschitzOnWith_of_ker_bound A P Q C
      (fun z hz => apply_eq_zero_of_comp_apply_eq_zero A P hsurj hrank z hz) hC

end Stratum

end FunctionalInequalities.Analysis
