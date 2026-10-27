import FunctionalInequalities.Analysis.UpperSemicontinuity

/-! The source is an arbitrary topological space; no measurable or normed structure. -/
example {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : UpperSemicontinuous f) (hg : Continuous g) (hp : ∀ x, 0 < g x) :
    UpperSemicontinuous (fun x => f x * g x) :=
  FunctionalInequalities.Analysis.upperSemicontinuous_mul_of_continuous_pos hf hg hp
