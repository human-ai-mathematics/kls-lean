import FunctionalInequalities.Analysis.WeakDerivative

/-!
# Weak derivatives of finite matrix polynomials

Bounded weak matrix fields with compact-local L2 entry derivatives have exact
first directional derivatives of their determinants and trace quadratics.
Ambient and matrix dimensions may differ; zero dimensions and arbitrary real
constant matrices are retained. No C1/C2 regularity, symmetry, positivity or
invertibility of the rough field is assumed. Supporting interfaces for Letwin
arXiv:2607.24164v1 Theorem 2.5 and compact Theorem 1.2, constant 8; these do not
establish Hessian evolution, an integrated trace estimate or the main bound.
Proof bodies: independently accepted W3p5/W3p6 API candidates, verbatim;
private finite matrix identities: previously checked client algebra, verbatim.
-/

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators

namespace FunctionalInequalities.Analysis

private theorem reverse_triple_sum {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ d, ∑ c, ∑ b, f b c d) = ∑ b, ∑ c, ∑ d, f b c d := by
  calc
    (∑ d, ∑ c, ∑ b, f b c d) = ∑ d, ∑ b, ∑ c, f b c d := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ c, f b c d := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, f b c d := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm

private theorem trace_four_eq {n : ℕ} (A H B J : Matrix (Fin n) (Fin n) ℝ) :
    (A * H * B * J).trace =
      ∑ q : Fin n × Fin n × Fin n × Fin n,
        (A q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
          (H q.2.1 q.2.2.1 * J q.2.2.2 q.1) := by
  simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ d, ∑ c, ∑ b, A a b * H b c * B c d * J d a) =
        ∑ b, ∑ c, ∑ d, A a b * H b c * B c d * J d a :=
      reverse_triple_sum _
    _ = ∑ b, ∑ c, ∑ d, (A a b * B c d) * (H b c * J d a) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring

private theorem trace_product_derivative_eq {n : ℕ} (B H T : Matrix (Fin n) (Fin n) ℝ) :
    (∑ q : Fin n × Fin n × Fin n × Fin n,
      (B q.1 q.2.1 * B q.2.2.1 q.2.2.2) *
        (T q.2.1 q.2.2.1 * H q.2.2.2 q.1 +
          H q.2.1 q.2.2.1 * T q.2.2.2 q.1)) =
      2 * (B * H * B * T).trace := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← trace_four_eq B T B H, ← trace_four_eq B H B T]
  have hcycle : (B * T * B * H).trace = (B * H * B * T).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * T) (B * H)
  rw [hcycle]
  ring



/-- The determinant of a bounded weak matrix field has its exact signed
permutation-polynomial directional derivative, locally in L2. -/
theorem hasWeakDerivAlong_det_of_locally_memLp_two {d : ℕ} {ι : Type*}
    [instFintype : Fintype ι] [instDecidableEq : DecidableEq ι]
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix ι ι ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    HasWeakDerivAlong (fun x => (A x).det)
      (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  classical
  have hp (σ : Equiv.Perm ι) :=
    hasWeakDerivAlong_finsetProd_of_locally_memLp_two
      (Finset.univ : Finset ι)
      (f := fun i x => A x (σ i) i)
      (df := fun i x => DA x (σ i) i)
      (v := v)
      (fun i _ => hA (σ i) i)
      (fun i _ => hbound (σ i) i)
      (fun i _ => hDA2 (σ i) i)
  have hs :=
    hasWeakDerivAlong_finsetSum_mul
      (Finset.univ : Finset (Equiv.Perm ι))
      (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ))
      (f := fun σ x => ∏ i : ι, A x (σ i) i)
      (df := fun σ x => ∑ i : ι, DA x (σ i) i *
        ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j)
      (v := v)
      (fun σ _ => (hp σ).1)
      (fun σ _ => (hp σ).2)
  simpa only [Matrix.det_apply'] using hs

/-- A bounded weak matrix field has the exact first directional derivative
of trace(B A B A), with locally L2 density, for arbitrary constant real B. -/
theorem hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two {d n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
      (fun x => 2 * (B * A x * B * DA x).trace) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => 2 * (B * A x * B * DA x).trace) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  have hprod := fun q : Fin n × Fin n × Fin n × Fin n =>
    (hA q.2.1 q.2.2.1).mul_of_locally_memLp_two
      (hA q.2.2.2 q.1)
      (hbound q.2.1 q.2.2.1) (hbound q.2.2.2 q.1)
      (hDA2 q.2.1 q.2.2.1) (hDA2 q.2.2.2 q.1)
  have hsum := hasWeakDerivAlong_finsetSum_mul
    (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n))
    (fun q => B q.1 q.2.1 * B q.2.2.1 q.2.2.2)
    (f := fun q x => A x q.2.1 q.2.2.1 * A x q.2.2.2 q.1)
    (df := fun q x =>
      DA x q.2.1 q.2.2.1 * A x q.2.2.2 q.1 +
        A x q.2.1 q.2.2.1 * DA x q.2.2.2 q.1)
    (v := v)
    (fun q _ => (hprod q).1)
    (fun q _ => (hprod q).2)
  simpa only [← trace_four_eq, trace_product_derivative_eq] using hsum


end FunctionalInequalities.Analysis
