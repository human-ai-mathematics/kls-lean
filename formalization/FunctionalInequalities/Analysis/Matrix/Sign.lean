import Mathlib.Analysis.Matrix.Order
import FunctionalInequalities.Analysis.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Absolute value and sign of a real symmetric matrix

For a real symmetric matrix `M`: `M * M ≥ 0`; `|M| = CFC.sqrt (M * M)` and `S = CFC.sqrt |M|` agree with the real
continuous functional calculus and are positive semidefinite (`symmetric_matrix_sqrt_real_cfc_bridge`); with
`sign M = cfc sign M`, `S * S = |M|`, `S * sign M * S = M`, and `sign M ^ 2 = 1` when `M` is a unit
(`symmetric_matrix_sign_factorization`). Singular and indefinite `M` are included. Support for the covariance step
of the proof of Letwin, arXiv:2607.24164v1, Theorem 1.2 (p. 14, preceding (2.21)). Proof bodies: root-accepted API scratch (`MatrixSqrtBridgeFixed` 0378ae4d…,
`MatrixSignFixed` d6c0d1bd…), verbatim, with exactly their accepted imports.
-/

noncomputable section
open scoped MatrixOrder

namespace FunctionalInequalities.Analysis

private lemma matrix_sqrt_eq_real_cfc_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : 0 ≤ A) :
    CFC.sqrt A = cfc (fun x : ℝ => Real.sqrt x) A := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt A hA]
  apply cfc_congr
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA hx
  calc
    (↑(NNReal.sqrt x.toNNReal) : ℝ) =
        Real.sqrt (x.toNNReal : ℝ) := by
          simp
    _ = Real.sqrt x := by
      rw [Real.coe_toNNReal x hx0]

/-- Positivity-derived bridge from the nonunital CFC square root to the real
unital CFC, specialized exactly to the two matrices used by the sign factorization.
No positivity hypothesis on `M` is added. -/
theorem symmetric_matrix_sqrt_real_cfc_bridge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    0 ≤ M * M ∧
      CFC.sqrt (M * M) = cfc (fun x : ℝ => Real.sqrt x) (M * M) ∧
      0 ≤ CFC.sqrt (M * M) ∧
      CFC.sqrt (CFC.sqrt (M * M)) =
        cfc (fun x : ℝ => Real.sqrt x) (CFC.sqrt (M * M)) := by
    have hct : M.conjTranspose = M := by
      exact (Matrix.conjTranspose_eq_transpose_of_trivial M).trans hM.eq
    have hMM : 0 ≤ M * M := by
      change (M * M - 0).PosSemidef
      simpa only [hct, sub_zero] using (Matrix.posSemidef_conjTranspose_mul_self M)
    have hsqrt : CFC.sqrt (M * M) =
        cfc (fun x : ℝ => Real.sqrt x) (M * M) :=
      matrix_sqrt_eq_real_cfc_of_nonneg (M * M) hMM
    have hroot : 0 ≤ CFC.sqrt (M * M) :=
      CFC.sqrt_nonneg (M * M)
    have hsqrtroot :
        CFC.sqrt (CFC.sqrt (M * M)) =
          cfc (fun x : ℝ => Real.sqrt x) (CFC.sqrt (M * M)) :=
      matrix_sqrt_eq_real_cfc_of_nonneg (CFC.sqrt (M * M)) hroot
    exact ⟨hMM, hsqrt, hroot, hsqrtroot⟩

private lemma sign_sq_real (x : ℝ) (hx : x ≠ 0) :
    (SignType.sign x : ℝ) * (SignType.sign x : ℝ) = 1 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hnpos : ¬ 0 < x := not_lt_of_ge (le_of_lt hxneg)
    have hs : (SignType.sign x : ℝ) = -1 := by
      simp only [sign_neg hxneg, SignType.coe_neg_one]
    rw [hs]
    norm_num
  · have hnneg : ¬ x < 0 := not_lt_of_ge (le_of_lt hxpos)
    have hs : (SignType.sign x : ℝ) = 1 := by
      simp only [sign_pos hxpos, SignType.coe_one]
    rw [hs]
    norm_num

private lemma sqrt_sqrt_sq_mul_sign_sqrt_sqrt (x : ℝ) :
    Real.sqrt (Real.sqrt (x * x)) * (SignType.sign x : ℝ) *
        Real.sqrt (Real.sqrt (x * x)) = x := by
  have hsq :
      Real.sqrt (Real.sqrt (x * x)) ^ 2 = Real.sqrt (x * x) :=
    Real.sq_sqrt (Real.sqrt_nonneg (x * x))
  by_cases hx : x = 0
  · subst x
    simp [SignType.sign]
  · rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hnpos : ¬ 0 < x := not_lt_of_ge (le_of_lt hxneg)
      have hs : (SignType.sign x : ℝ) = -1 := by
        simp only [sign_neg hxneg, SignType.coe_neg_one]
      have hsqrt : Real.sqrt (x * x) = -x := by
        rw [show x * x = x ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_neg hxneg]
      rw [hs]
      nlinarith [hsq, hsqrt]
    · have hnneg : ¬ x < 0 := not_lt_of_ge (le_of_lt hxpos)
      have hs : (SignType.sign x : ℝ) = 1 := by
        simp only [sign_pos hxpos, SignType.coe_one]
      have hsqrt : Real.sqrt (x * x) = x := by
        rw [show x * x = x ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_pos hxpos]
      rw [hs]
      nlinarith [hsq, hsqrt]

/-- The spectral sign factorization used to absorb `sqrt |M|` into the random
vector. No PSD, basis, commutation, factorization, or sign-square identity is
supplied as an assumption. -/
theorem symmetric_matrix_sign_factorization
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    let AbsM : Matrix ι ι ℝ := CFC.sqrt (M * M)
    let S : Matrix ι ι ℝ := CFC.sqrt AbsM
    let SignM : Matrix ι ι ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    S * S = AbsM ∧ S * SignM * S = M ∧
      (IsUnit M → SignM * SignM = 1) := by
    dsimp
    obtain ⟨hMM, hsqrt, hroot, hsqrtroot⟩ :=
      symmetric_matrix_sqrt_real_cfc_bridge M hM
    have hspec : (spectrum ℝ M).Finite :=
      Matrix.finite_real_spectrum (A := M)
    have hcomp (g f : ℝ → ℝ) :
        cfc (fun x => g (f x)) M = cfc g (cfc f M) := by
      exact cfc_comp' g f M
        (hg := (hspec.image f).continuousOn g)
        (hf := hspec.continuousOn f)
    have hcfc_mul (f g : ℝ → ℝ) :
        cfc f M * cfc g M =
          cfc (fun x => f x * g x) M := by
      rw [← cfc_mul (hf := hspec.continuousOn f)
        (hg := hspec.continuousOn g)]
    have hid : cfc (fun x : ℝ => x) M = M := by
      change cfc id M = M
      exact cfc_id ℝ M hM
    have hone : cfc (fun _ : ℝ => (1 : ℝ)) M = 1 := by
      change cfc (1 : ℝ → ℝ) M = 1
      exact cfc_one ℝ M hM
    have hsq : cfc (fun x : ℝ => x * x) M = M * M := by
      calc
        cfc (fun x : ℝ => x * x) M =
            cfc (fun x : ℝ => x) M * cfc (fun x : ℝ => x) M :=
          (hcfc_mul (fun x : ℝ => x) (fun x : ℝ => x)).symm
        _ = M * M := by rw [hid]
    have hAbs :
        CFC.sqrt (M * M) =
          cfc (fun x : ℝ => Real.sqrt (x * x)) M := by
      calc
        CFC.sqrt (M * M) =
            cfc (fun x : ℝ => Real.sqrt x) (M * M) := hsqrt
        _ = cfc (fun x : ℝ => Real.sqrt x)
            (cfc (fun x : ℝ => x * x) M) := by rw [hsq]
        _ = cfc (fun x : ℝ => Real.sqrt (x * x)) M := by
          simpa [Function.comp_def] using
            (hcomp (fun x : ℝ => Real.sqrt x) (fun x : ℝ => x * x)).symm
    have hS :
        CFC.sqrt (CFC.sqrt (M * M)) =
          cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M := by
      calc
        CFC.sqrt (CFC.sqrt (M * M)) =
            cfc (fun x : ℝ => Real.sqrt x) (CFC.sqrt (M * M)) :=
          hsqrtroot
        _ = cfc (fun x : ℝ => Real.sqrt x)
            (cfc (fun x : ℝ => Real.sqrt (x * x)) M) := by rw [hAbs]
        _ = cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M := by
          simpa [Function.comp_def] using
            (hcomp (fun x : ℝ => Real.sqrt x)
              (fun x : ℝ => Real.sqrt (x * x))).symm
    have hprod :
        cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M *
            cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
            cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M =
          cfc
            (fun x : ℝ =>
              Real.sqrt (Real.sqrt (x * x)) * (SignType.sign x : ℝ) *
                Real.sqrt (Real.sqrt (x * x))) M := by
      calc
        cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M *
            cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
            cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M =
            cfc
                (fun x : ℝ =>
                  Real.sqrt (Real.sqrt (x * x)) * (SignType.sign x : ℝ)) M *
              cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M := by
                rw [hcfc_mul]
        _ = cfc
            (fun x : ℝ =>
              Real.sqrt (Real.sqrt (x * x)) * (SignType.sign x : ℝ) *
                Real.sqrt (Real.sqrt (x * x))) M := by
                rw [hcfc_mul]
    have hfactor :
        CFC.sqrt (CFC.sqrt (M * M)) *
            cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
            CFC.sqrt (CFC.sqrt (M * M)) = M := by
      calc
        CFC.sqrt (CFC.sqrt (M * M)) *
            cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
            CFC.sqrt (CFC.sqrt (M * M)) =
            cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M *
              cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
              cfc (fun x : ℝ => Real.sqrt (Real.sqrt (x * x))) M := by
                rw [hS]
        _ = cfc
            (fun x : ℝ =>
              Real.sqrt (Real.sqrt (x * x)) * (SignType.sign x : ℝ) *
                Real.sqrt (Real.sqrt (x * x))) M := hprod
        _ = cfc (fun x : ℝ => x) M := by
          apply cfc_congr
          intro x hx
          exact sqrt_sqrt_sq_mul_sign_sqrt_sqrt x
        _ = M := hid
    refine ⟨CFC.sqrt_mul_sqrt_self (CFC.sqrt (M * M)) hroot, hfactor, ?_⟩
    intro hunit
    have hzero : (0 : ℝ) ∉ spectrum ℝ M :=
      spectrum.zero_notMem ℝ hunit
    have hsignsq :
        cfc (fun x : ℝ => (SignType.sign x : ℝ) *
          (SignType.sign x : ℝ)) M =
          cfc (fun _ : ℝ => (1 : ℝ)) M := by
      apply cfc_congr
      intro x hx
      have hx0 : x ≠ 0 := by
        intro hx'
        subst x
        exact hzero hx
      exact sign_sq_real x hx0
    calc
      cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
          cfc (fun x : ℝ => (SignType.sign x : ℝ)) M =
          cfc (fun x : ℝ => (SignType.sign x : ℝ) *
            (SignType.sign x : ℝ)) M :=
        hcfc_mul (fun x : ℝ => (SignType.sign x : ℝ))
          (fun x : ℝ => (SignType.sign x : ℝ))
      _ = cfc (fun _ : ℝ => (1 : ℝ)) M := hsignsq
      _ = 1 := hone

section Jordan

/-! ### Jordan decomposition of a real symmetric matrix

For every real symmetric `B`, the continuous functional calculus parts `P = cfc (max · 0) B` and
`N = cfc (max (−·) 0) B` are positive semidefinite with `B = P − N`, `P N = N P = 0` and
`tr(B²) = tr(P²) + tr(N²)` (`symmetric_jordan_decomposition`; no decomposition is assumed, the empty index type
included); with the trace domination of `Matrix/Trace.lean` this gives `symmetric_jordan_trace_support`. Support for
Letwin, arXiv:2607.24164v1, Theorem 2.5; not the theorem itself. Proof bodies: strong-API candidate (gpt-6-astra,
`api-symmetric-compiler-patch-v3`, e735387e…), verbatim.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma scalar_jordan_identities (x : ℝ) :
    max x 0 - max (-x) 0 = x ∧ max x 0 * max (-x) 0 = 0 := by
  by_cases hx : 0 ≤ x
  · have hn : -x ≤ 0 := neg_nonpos.mpr hx
    simp [max_eq_left hx, max_eq_right hn]
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hn : 0 ≤ -x := neg_nonneg.mpr hx'
    simp [max_eq_right hx', max_eq_left hn]

/-- The positive and negative parts are constructed by the matrix CFC.
No Jordan identities or decomposition witnesses are hypotheses. This also
includes the empty index type. -/
theorem symmetric_jordan_decomposition (B : Matrix ι ι ℝ) (hB : B.IsSymm) :
    ∃ P N : Matrix ι ι ℝ,
      P.PosSemidef ∧ N.PosSemidef ∧ B = P - N ∧
      P * N = 0 ∧ N * P = 0 ∧
      (B * B).trace = (P * P).trace + (N * N).trace := by
  let P : Matrix ι ι ℝ := cfc (fun x : ℝ => max x 0) B
  let N : Matrix ι ι ℝ := cfc (fun x : ℝ => max (-x) 0) B
  have hP : P.PosSemidef :=
    cfc_posSemidef_of_nonneg B hB (fun x : ℝ => max x 0)
      (fun x => le_max_right x 0)
  have hN : N.PosSemidef :=
    cfc_posSemidef_of_nonneg B hB (fun x : ℝ => max (-x) 0)
      (fun x => le_max_right (-x) 0)
  have hspec : (spectrum ℝ B).Finite := Matrix.finite_real_spectrum (A := B)
  have hmul (f g : ℝ → ℝ) :
      cfc f B * cfc g B = cfc (fun x => f x * g x) B := by
    rw [← cfc_mul (hf := hspec.continuousOn f) (hg := hspec.continuousOn g)]
  have hdec : B = P - N := by
    calc
      B = cfc (fun x : ℝ => x) B := (cfc_id ℝ B hB).symm
      _ = cfc (fun x : ℝ => max x 0 - max (-x) 0) B := by
        apply cfc_congr
        intro x hx
        exact (scalar_jordan_identities x).1.symm
      _ = P - N := by
        dsimp [P, N]
        rw [cfc_sub
          (hf := hspec.continuousOn (fun x : ℝ => max x 0))
          (hg := hspec.continuousOn (fun x : ℝ => max (-x) 0))]
  have hPN : P * N = 0 := by
    change cfc (fun x : ℝ => max x 0) B *
      cfc (fun x : ℝ => max (-x) 0) B = 0
    rw [hmul]
    calc
      cfc (fun x : ℝ => max x 0 * max (-x) 0) B =
          cfc (fun _ : ℝ => 0) B := by
        apply cfc_congr
        intro x hx
        exact (scalar_jordan_identities x).2
      _ = 0 := by simp
  have hNP : N * P = 0 := by
    change cfc (fun x : ℝ => max (-x) 0) B *
      cfc (fun x : ℝ => max x 0) B = 0
    rw [hmul]
    calc
      cfc (fun x : ℝ => max (-x) 0 * max x 0) B =
          cfc (fun _ : ℝ => 0) B := by
        apply cfc_congr
        intro x hx
        exact (mul_comm (max (-x) 0) (max x 0)).trans
          (scalar_jordan_identities x).2
      _ = 0 := by simp
  have hsq : (P - N) * (P - N) = P * P + N * N := by
    calc
      (P - N) * (P - N) = P * P - P * N - N * P + N * N := by
        noncomm_ring
      _ = P * P + N * N := by rw [hPN, hNP]; simp
  have htrace : (B * B).trace = (P * P).trace + (N * N).trace := by
    rw [hdec, hsq, Matrix.trace_add]
  exact ⟨P, N, hP, hN, hdec, hPN, hNP, htrace⟩

/-- Derived Jordan witnesses together with their pointwise trace domination. -/
theorem symmetric_jordan_trace_support (B H : Matrix ι ι ℝ)
    (hB : B.IsSymm) (hH : H.IsSymm) :
    ∃ P N : Matrix ι ι ℝ,
      P.PosSemidef ∧ N.PosSemidef ∧ B = P - N ∧
      P * N = 0 ∧ N * P = 0 ∧
      (B * B).trace = (P * P).trace + (N * N).trace ∧
      ((P - N) * H * (P - N) * H).trace ≤
        (P * H * P * H).trace + (N * H * N * H).trace := by
  obtain ⟨P, N, hP, hN, hdec, hPN, hNP, htrace⟩ :=
    symmetric_jordan_decomposition B hB
  exact ⟨P, N, hP, hN, hdec, hPN, hNP, htrace,
    jordan_trace_domination hP hN hH⟩

end Jordan

end FunctionalInequalities.Analysis
