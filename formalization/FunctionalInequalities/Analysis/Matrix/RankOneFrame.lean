module

public import FunctionalInequalities.Analysis.Matrix.Positivity
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Fixed finite rank-one frames of positive definite matrices

Gilbarg–Trudinger (2001), Lemma 17.13 (statement pp. 454–455, proof pp. 462–463): for `n > 0` and `0
< lo < hi` there are
finitely many unit vectors `γ_k`, including every coordinate vector `e_i` and every normalized pair
`(e_i+e_j)/√2`, and a
uniform `lowerCoeff > 0`, all fixed before any matrix, such that every positive definite `A` with
`lo I ≤ A ≤ hi I` is
`∑ b_k γ_k γ_kᵀ` with `lowerCoeff ≤ b_k ≤ hi` for every `k`
(`exists_uniform_positive_rank_one_frame`).

Proof: each positive definite `A` is congruent to a fixed center
(`exists_invertible_congruence_of_posDef`, Eq. (17.55)); the
ordered-pair chart of the transported matrix is positive on an open neighbourhood; finitely many
neighbourhoods cover the
compact interval `[lo/2 I, hi I]` (ordinary entrywise topology); the concatenated frame with the
prescribed directions is
fixed, `lo/(2N)` is added to every coefficient, and testing `hi I − A ⪰ 0` against each unit
direction gives the cap `hi`
(`coefficient_le_cap`). The intermediate frame with the trace cap `n·hi` is kept as a private step.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis

section OrderedPairChart
open Matrix Finset
/--
The ordered-pair dyadic chart (Gilbarg–Trudinger 2001, proof of Lemma 17.13): expansion of
`(e_i+e_j)(e_i+e_j)ᵀ`. -/
private theorem pair_outer_eq {n : ℕ} (i j : Fin n) :
    Matrix.vecMulVec ((Pi.single i (1 : ℝ) : Fin n → ℝ) + Pi.single j 1)
        ((Pi.single i (1 : ℝ) : Fin n → ℝ) + Pi.single j 1) =
      Matrix.single i i (1 : ℝ) + Matrix.single i j 1 + Matrix.single j i 1 +
        Matrix.single j j 1 := by
  simp only [vecMulVec_add, add_vecMulVec, ← single_eq_single_vecMulVec_single]
  abel

private theorem symmetric_ordered_pair_chart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) :
    A =
      (∑ i : Fin n, (A i i - ∑ j ∈ Finset.univ.erase i, A i j) • Matrix.single i i 1) +
        ∑ i : Fin n,
          ∑ j ∈ Finset.univ.erase i,
            (A i j / 2) •
              Matrix.vecMulVec ((Pi.single i (1 : ℝ) : Fin n → ℝ) + Pi.single j 1)
                ((Pi.single i (1 : ℝ) : Fin n → ℝ) + Pi.single j 1) := by
  ext a b
  simp_rw [pair_outer_eq]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.single_apply, mul_add, Finset.sum_add_distrib]
  by_cases hab : a = b
  · subst b
    simp [ite_and, eq_comm, Finset.sum_ite, ← hA.apply, Finset.filter_ne,
      Finset.sum_erase_eq_sub, ← Finset.sum_div]
  · simp [ite_and, eq_comm, hab, Finset.sum_ite, hA.apply b a]
/-- The positive-coordinate chart is open in the ambient matrix space. -/
private theorem isOpen_positive_chart {n : ℕ} :
    IsOpen {A : Matrix (Fin n) (Fin n) ℝ |
      (∀ i, 0 < A i i - ∑ j ∈ Finset.univ.erase i, A i j) ∧
      ∀ i j, i ≠ j → 0 < A i j} := by
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (by fun_prop)
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt continuous_const (by fun_prop)

/--
At the chart center the diagonal coefficients equal one and all off-diagonal entries equal one. -/
private theorem center_chart_coefficients {n : ℕ} :
    let A : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = j then n else 1
    (∀ i, A i i - ∑ j ∈ Finset.univ.erase i, A i j = 1) ∧ ∀ i j, i ≠ j → A i j = 1 := by
  intro A
  constructor
  · intro i
    have hn : 0 < n := by have hi := i.isLt; omega
    have hoff : (∑ j ∈ Finset.univ.erase i, A i j) = (n : ℝ) - 1 := by
      calc
        _ = ∑ _j ∈ Finset.univ.erase i, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hji := (Finset.mem_erase.mp hj).1
          simp [A, Ne.symm hji]
        _ = _ := by simp [Nat.cast_sub hn]
    simp [A, hoff]
  · intro i j hij
    simp [A, hij]

/--
Nonnegative coefficients of unit rank-one directions are bounded by the trace, hence by n times a
diagonal cap. -/
private theorem coefficient_le_dimension_mul_cap {n N : ℕ} (γ : Fin N → Fin n → ℝ)
    (β : Fin N → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (hγ : ∀ k, ∑ i : Fin n, (γ k i) ^ 2 = 1)
    (hβ : ∀ k, 0 ≤ β k) (hA : A = ∑ k : Fin N, β k • Matrix.vecMulVec (γ k) (γ k)) {hi : ℝ}
    (hhi : ∀ i, A i i ≤ hi) (k : Fin N) : β k ≤ (n : ℝ) * hi := by
  have htrace : (∑ i : Fin n, A i i) = ∑ k : Fin N, β k := by
    rw [hA]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = β j * ∑ i : Fin n, (γ j i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = β j := by rw [hγ j, mul_one]
  calc
    β k ≤ ∑ j : Fin N, β j := Finset.single_le_sum (fun j _ => hβ j) (Finset.mem_univ k)
    _ = ∑ i : Fin n, A i i := htrace.symm
    _ ≤ ∑ _i : Fin n, hi := Finset.sum_le_sum fun i _ => hhi i
    _ = (n : ℝ) * hi := by simp

/--
The center of the positive chart is positive definite, including the vacuous zero-dimensional case.
-/
private theorem center_posDef {n : ℕ} :
    Matrix.PosDef
      ((fun i j : Fin n => if i = j then (n : ℝ) else 1) : Matrix (Fin n) (Fin n) ℝ) := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = j then n else 1
  change A.PosDef
  have hsym : A.IsSymm := by
    change Aᵀ = A
    ext i j
    change (if j = i then (n : ℝ) else 1) = (if i = j then (n : ℝ) else 1)
    simp only [eq_comm]
  obtain ⟨hd, -⟩ := center_chart_coefficients (n := n)
  have hd' : ∀ i, A i i - ∑ j ∈ Finset.univ.erase i, A i j = 1 := hd
  have heq := symmetric_ordered_pair_chart A hsym
  have hdiag :
    (∑ i : Fin n, (A i i - ∑ j ∈ Finset.univ.erase i, A i j) • Matrix.single i i (1 : ℝ)) = 1 := by
    simp_rw [hd', one_smul]
    exact Matrix.sum_single_one
  rw [hdiag] at heq
  rw [heq]
  apply Matrix.PosDef.one.add_posSemidef
  apply Matrix.posSemidef_sum
  intro i _
  apply Matrix.posSemidef_sum
  intro j hj
  apply Matrix.PosSemidef.smul
  · let v : Fin n → ℝ := Pi.single i 1 + Pi.single j 1
    have hv : star v = v := by
      funext k
      exact star_trivial (v k)
    have hp := Matrix.posSemidef_vecMulVec_self_star v
    rw [hv] at hp
    exact hp
  · have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    change 0 ≤ A i j / 2
    simp [A, hij]

/-- A unit rank-one positive matrix is at most the identity in Loewner order. -/
private theorem unit_rank_one_le_one {n : ℕ} (γ : Fin n → ℝ) (hγ : ∑ i : Fin n, (γ i) ^ 2 = 1) :
    (1 - Matrix.vecMulVec γ γ).PosSemidef := by
  have hpsd : (Matrix.vecMulVec γ γ).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star γ
  refine
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_one.sub hpsd.isHermitian)
      ?_
  intro x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ γ x
  rw [hγ, one_mul] at hcs
  have hdot : x ⬝ᵥ γ = γ ⬝ᵥ x := dotProduct_comm x γ
  rw [hdot]
  change 0 ≤ (∑ i : Fin n, x i * x i) - (∑ i : Fin n, γ i * x i) * (∑ i : Fin n, γ i * x i)
  simp only [pow_two] at hcs
  linarith only [hcs]

/-- The sum of N unit rank-one matrices lies between zero and N times the identity. -/
private theorem unit_frame_sum_bounds {n N : ℕ} (γ : Fin N → Fin n → ℝ)
    (hγ : ∀ k, ∑ i : Fin n, (γ k i) ^ 2 = 1) :
    (∑ k : Fin N, Matrix.vecMulVec (γ k) (γ k)).PosSemidef ∧
      ((N : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
          ∑ k : Fin N, Matrix.vecMulVec (γ k) (γ k)).PosSemidef := by
  constructor
  · apply Matrix.posSemidef_sum
    intro k _
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (γ k)
  · have h := Matrix.posSemidef_sum Finset.univ (fun k _ => unit_rank_one_le_one (γ k) (hγ k))
    convert h using 1
    rw [Finset.sum_sub_distrib]
    congr 1
    ext i j
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply]

/--
A uniform positive amount can be reserved for every unit direction while retaining half the
ellipticity floor. -/
private theorem subtract_uniform_frame_preserves_interval {n N : ℕ} (hN : 0 < N)
    (γ : Fin N → Fin n → ℝ) (hγ : ∀ k, ∑ i : Fin n, (γ k i) ^ 2 = 1) {lo hi : ℝ} (hlo : 0 < lo)
    (A : Matrix (Fin n) (Fin n) ℝ) (hloA : (A - lo • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hAhi : (hi • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef) :
    let G := ∑ k : Fin N, Matrix.vecMulVec (γ k) (γ k)
    let ε := lo / (2 * (N : ℝ))
    0 < ε ∧
      ((A - ε • G) - (lo / 2) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
        (hi • (1 : Matrix (Fin n) (Fin n) ℝ) - (A - ε • G)).PosSemidef := by
  intro G ε
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hε : 0 < ε := div_pos hlo (mul_pos (by norm_num) hNr)
  have hεN : ε * (N : ℝ) = lo / 2 := by
    dsimp [ε]
    field_simp
  obtain ⟨hG, hNG⟩ := unit_frame_sum_bounds γ hγ
  refine ⟨hε, ?_, ?_⟩
  · have h := hloA.add (hNG.smul hε.le)
    convert h using 1
    rw [smul_sub, smul_smul, hεN]
    module
  · have h := hAhi.add (hG.smul hε.le)
    convert h using 1
    abel

end OrderedPairChart

section SpectralInterval
open Matrix Finset Set
/-- Compactness input for Gilbarg–Trudinger (2001), Lemma 17.13: the real PSD cone is closed. -/
private theorem isClosed_posSemidef_real {n : ℕ} :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · change IsClosed {A : Matrix (Fin n) (Fin n) ℝ | star A = A}
    exact isClosed_eq continuous_star continuous_id
  · apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const (by fun_prop)

/--
A positive semidefinite matrix whose diagonal entries are at most hi has every entry in [-hi,hi]. -/
private theorem entry_bounds_of_posSemidef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) {hi : ℝ} (hhi : ∀ i, A i i ≤ hi) (i j : Fin n) :
    -hi ≤ A i j ∧ A i j ≤ hi := by
  have he (i j : Fin n) : (Pi.single i (1 : ℝ) : Fin n → ℝ) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
    simp
  have hp := hA.dotProduct_mulVec_nonneg ((Pi.single i (1 : ℝ) : Fin n → ℝ) + Pi.single j 1)
  have hm := hA.dotProduct_mulVec_nonneg ((Pi.single i (1 : ℝ) : Fin n → ℝ) - Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, he] at hp hm
  have hsym : A j i = A i j := by simpa only [star_trivial] using hA.isHermitian.apply i j
  constructor <;> linarith [hhi i, hhi j]

/--
Fixed real Loewner intervals with nonnegative lower endpoint are compact, in the usual matrix
topology. -/
private theorem isCompact_spectral_interval {n : ℕ} {lo hi : ℝ} (hlo : 0 ≤ lo) :
    IsCompact
      {A : Matrix (Fin n) (Fin n) ℝ |
        (A - lo • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (hi • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef} := by
  have hc :
    IsClosed
      {A : Matrix (Fin n) (Fin n) ℝ |
        (A - lo • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (hi • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef} :=
    (isClosed_posSemidef_real.preimage (by fun_prop)).inter
      (isClosed_posSemidef_real.preimage (by fun_prop))
  have hb : IsCompact (Set.Icc (fun _ _ : Fin n => -hi) (fun _ _ : Fin n => hi)) :=
    isCompact_Icc
  have hbounds (A : Matrix (Fin n) (Fin n) ℝ)
    (hlow : (A - lo • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hup : (hi • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef) :
    ∀ i j, -hi ≤ A i j ∧ A i j ≤ hi := by
    have hp : A.PosSemidef := by
      have h := hlow.add (Matrix.PosSemidef.one.smul hlo)
      simpa only [sub_add_cancel] using h
    have hd : ∀ i, A i i ≤ hi := by
      intro i
      have h := hup.diag_nonneg (i := i)
      have h' : 0 ≤ hi - A i i := by simpa using h
      linarith
    exact entry_bounds_of_posSemidef A hp hd
  apply hb.of_isClosed_subset hc
  intro A hA
  exact ⟨fun i j => (hbounds A hA.1 hA.2 i j).1, fun i j => (hbounds A hA.1 hA.2 i j).2⟩
end SpectralInterval

section UnitNormalization
open Matrix Finset
/-- Unit normalization of nonzero rank-one directions (Gilbarg–Trudinger 2001, Lemma 17.13). -/
private theorem exists_unit_rank_one_normalization {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) :
    ∃ (γ : Fin n → ℝ) (c : ℝ),
      0 < c ∧ (∑ i : Fin n, (γ i) ^ 2 = 1) ∧ Matrix.vecMulVec v v = c • Matrix.vecMulVec γ γ := by
  have hsum : 0 < ∑ i : Fin n, (v i) ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    change v i ≠ 0 at hi
    exact
      Finset.sum_pos' (fun j _ => sq_nonneg (v j)) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  let r := Real.sqrt (∑ i : Fin n, (v i) ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr hsum
  have hrr : r ^ 2 = ∑ i : Fin n, (v i) ^ 2 := Real.sq_sqrt hsum.le
  refine ⟨fun i => v i / r, r ^ 2, sq_pos_of_pos hr, ?_, ?_⟩
  · simp_rw [div_pow, ← Finset.sum_div]
    rw [← hrr, div_self (ne_of_gt (sq_pos_of_pos hr))]
  · ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
end UnitNormalization

section CongruenceChart
open Matrix Finset
/--
Transport the explicit positive dyadic chart by a fixed real congruence; Gilbarg–Trudinger (2001),
Eq. (17.55). -/
private theorem congruence_ordered_pair_chart {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    S * A * Sᵀ =
      (∑ i : Fin n,
          (A i i - ∑ j ∈ Finset.univ.erase i, A i j) •
            Matrix.vecMulVec (S *ᵥ Pi.single i 1) (S *ᵥ Pi.single i 1)) +
        ∑ i : Fin n,
          ∑ j ∈ Finset.univ.erase i,
            (A i j / 2) •
              Matrix.vecMulVec (S *ᵥ ((Pi.single i (1 : ℝ) : Fin n → ℝ) + Pi.single j 1))
                (S *ᵥ ((Pi.single i (1 : ℝ) : Fin n → ℝ) + Pi.single j 1)) := by
  have h :=
    congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => S * B * Sᵀ)
      (symmetric_ordered_pair_chart A hA)
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.single_eq_single_vecMulVec_single, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose] using h
end CongruenceChart

section TraceCapFrame
open Matrix Finset

/-- Ordered-pair chart directions: `e_i` on the diagonal, `e_i + e_j` off it. -/
private def chartVec {n : ℕ} (p : Fin n × Fin n) : Fin n → ℝ :=
  if p.1 = p.2 then Pi.single p.1 1 else Pi.single p.1 1 + Pi.single p.2 1

/-- Ordered-pair chart coefficients of a matrix `C`. -/
private def chartCoeff {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (p : Fin n × Fin n) : ℝ :=
  if p.1 = p.2 then C p.1 p.1 - ∑ j ∈ Finset.univ.erase p.1, C p.1 j else C p.1 p.2 / 2

private theorem chartVec_ne_zero {n : ℕ} (p : Fin n × Fin n) : chartVec p ≠ 0 := by
  intro h
  have h1 := congrFun h p.1
  by_cases hp : p.1 = p.2
  · simp [chartVec, hp] at h1
  · simp [chartVec, hp] at h1

private theorem sum_prod_eq_diag_add_offDiag {n : ℕ}
    (F : Fin n × Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∑ p, F p = ∑ i, F (i, i) + ∑ i, ∑ j ∈ Finset.univ.erase i, F (i, j) := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

/-- The congruence-transported ordered-pair chart, indexed by all ordered pairs. -/
private theorem congruence_chart_sum {n : ℕ} (S C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm) :
    S * C * Sᵀ =
      ∑ p : Fin n × Fin n, chartCoeff C p • vecMulVec (S *ᵥ chartVec p) (S *ᵥ chartVec p) := by
  rw [congruence_ordered_pair_chart S C hC, sum_prod_eq_diag_add_offDiag]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by simp [chartCoeff, chartVec]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    simp [chartCoeff, chartVec, hij]

/--
Local frame at a positive definite matrix: an open neighbourhood and fixed unit directions such that
every symmetric
matrix of the neighbourhood is a nonnegative combination of them. -/
private theorem exists_local_frame {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    ∃ (U : Set (Matrix (Fin n) (Fin n) ℝ)) (γ : Fin n × Fin n → Fin n → ℝ),
      IsOpen U ∧
        A ∈ U ∧
          (∀ p, ∑ i : Fin n, (γ p i) ^ 2 = 1) ∧
            ∀ B ∈ U,
              B.IsSymm →
                ∃ b : Fin n × Fin n → ℝ,
                  (∀ p, 0 ≤ b p) ∧ B = ∑ p, b p • vecMulVec (γ p) (γ p) := by
  classical
  let A₀ : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = j then (n : ℝ) else 1
  obtain ⟨S, hSu, hAS⟩ := exists_invertible_congruence_of_posDef hn A A₀ hA center_posDef
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
  have hL : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hdet
  have hR : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hdet
  have hv : ∀ p : Fin n × Fin n, S *ᵥ chartVec p ≠ 0 := by
    intro p h
    apply chartVec_ne_zero p
    have h' := congrArg (fun v => S⁻¹ *ᵥ v) h
    simpa [Matrix.mulVec_mulVec, hL] using h'
  choose γ c hc hγ hvv using fun p =>
    exists_unit_rank_one_normalization (S *ᵥ chartVec p) (hv p)
  let P : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {C | (∀ i, 0 < C i i - ∑ j ∈ Finset.univ.erase i, C i j) ∧ ∀ i j, i ≠ j → 0 < C i j}
  refine
    ⟨(fun B => S⁻¹ * B * S⁻¹ᵀ) ⁻¹' P, γ, isOpen_positive_chart.preimage (by fun_prop), ?_, hγ,
      ?_⟩
  · have hTA : S⁻¹ * A * S⁻¹ᵀ = A₀ := by
      rw [hAS]
      calc
        S⁻¹ * (S * A₀ * Sᵀ) * S⁻¹ᵀ = (S⁻¹ * S) * A₀ * (S⁻¹ * S)ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = A₀ := by rw [hL, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    obtain ⟨hd, ho⟩ := center_chart_coefficients (n := n)
    have hd' : ∀ i, A₀ i i - ∑ j ∈ Finset.univ.erase i, A₀ i j = 1 := hd
    have ho' : ∀ i j, i ≠ j → A₀ i j = 1 := ho
    change S⁻¹ * A * S⁻¹ᵀ ∈ P
    rw [hTA]
    exact
      ⟨fun i => by rw [hd' i]; exact one_pos, fun i j hij => by rw [ho' i j hij]; exact one_pos⟩
  · intro B hB hBs
    let C := S⁻¹ * B * S⁻¹ᵀ
    have hCP : C ∈ P := hB
    have hCs : C.IsSymm := by
      change (S⁻¹ * B * S⁻¹ᵀ)ᵀ = S⁻¹ * B * S⁻¹ᵀ
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hBs.eq,
        Matrix.mul_assoc]
    have hBC : B = S * C * Sᵀ := by
      change B = S * (S⁻¹ * B * S⁻¹ᵀ) * Sᵀ
      calc
        B = (S * S⁻¹) * B * (S * S⁻¹)ᵀ := by
          rw [hR, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    refine ⟨fun p => chartCoeff C p * c p, fun p => mul_nonneg ?_ (hc p).le, ?_⟩
    · by_cases hp : p.1 = p.2
      · simpa [chartCoeff, hp] using (hCP.1 p.1).le
      · simpa [chartCoeff, hp] using (div_pos (hCP.2 p.1 p.2 hp) two_pos).le
    · rw [hBC, congruence_chart_sum S C hCs]
      exact Finset.sum_congr rfl fun p _ => by rw [hvv p, smul_smul]

/-- Prescribed directions: `e_i` on the diagonal and `(e_i + e_j)/√2` off it. -/
private def prescribed {n : ℕ} (p : Fin n × Fin n) : Fin n → ℝ :=
  if p.1 = p.2 then Pi.single p.1 1
  else fun a =>
    ((Pi.single p.1 (1 : ℝ) : Fin n → ℝ) a + (Pi.single p.2 (1 : ℝ) : Fin n → ℝ) a) /
      Real.sqrt 2

private theorem prescribed_unit {n : ℕ} (p : Fin n × Fin n) :
    ∑ i : Fin n, (prescribed p i) ^ 2 = 1 := by
  by_cases hp : p.1 = p.2
  · simp [prescribed, hp, Pi.single_apply]
  · have hterm :
      ∀ i : Fin n,
        (prescribed p i) ^ 2 =
          ((Pi.single p.1 (1 : ℝ) : Fin n → ℝ) i + (Pi.single p.2 (1 : ℝ) : Fin n → ℝ) i) / 2 := by
      intro i
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      simp only [prescribed, hp, ite_false, div_pow, h2]
      by_cases h1 : i = p.1
      · subst h1
        simp [hp]
      · by_cases h2' : i = p.2
        · subst h2'
          simp [h1]
        · simp [h1, h2']
    simp_rw [hterm, ← Finset.sum_div, Finset.sum_add_distrib]
    simp [Pi.single_apply]

/--
The frame with the trace coefficient cap (Gilbarg–Trudinger 2001, Lemma 17.13, with `upperCoeff =
n·hi`):
fixed finitely many unit directions, including every coordinate direction and every
normalized pair direction, and uniform coefficient bounds `0 < lowerCoeff < upperCoeff`, chosen
before every matrix, such
that every `A` with `lo I ≤ A ≤ hi I` has coefficients in `[lowerCoeff, upperCoeff]` in EVERY
direction. Here
`lowerCoeff = lo/(2N)` and `upperCoeff = n·hi`. -/
private theorem exists_uniform_positive_rank_one_frame_trace_cap {n : ℕ} (hn : 0 < n)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi) :
    ∃ (N : ℕ) (γ : Fin N → Fin n → ℝ) (lowerCoeff upperCoeff : ℝ),
      0 < lowerCoeff ∧
        lowerCoeff < upperCoeff ∧
          (∀ k, ∑ i : Fin n, (γ k i) ^ 2 = 1) ∧
            (∀ i : Fin n, ∃ k : Fin N, γ k = Pi.single i 1) ∧
              (∀ i j : Fin n,
                  i ≠ j →
                    ∃ k : Fin N,
                      γ k = fun a =>
                        ((Pi.single i (1 : ℝ) : Fin n → ℝ) a +
                            (Pi.single j (1 : ℝ) : Fin n → ℝ) a) /
                          Real.sqrt 2) ∧
                ∀ A : Matrix (Fin n) (Fin n) ℝ,
                  A.PosDef →
                    (A - lo • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef →
                      (hi • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef →
                        ∃ β : Fin N → ℝ,
                          (∀ k, lowerCoeff ≤ β k ∧ β k ≤ upperCoeff) ∧
                            A = ∑ k : Fin N, β k • Matrix.vecMulVec (γ k) (γ k) := by
  classical
  -- the compact interval `[lo/2 I, hi I]` of positive definite matrices

  let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {A |
      (A - (lo / 2) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
        (hi • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef}
  have hK : IsCompact K := isCompact_spectral_interval (half_pos hlo).le
  have hKpd : ∀ A ∈ K, A.PosDef := by
    intro A hA
    have h := (Matrix.PosDef.one.smul (half_pos hlo)).add_posSemidef hA.1
    rwa [add_sub_cancel] at h
  -- local frames at every point of `K`, and a finite subcover

  choose U γl hUo hAU hγl hrep using fun A : K => exists_local_frame hn A.1 (hKpd A.1 A.2)
  obtain ⟨t, ht⟩ :=
    hK.elim_finite_subcover U hUo
      (fun A hA => Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hAU ⟨A, hA⟩⟩)
  -- the concatenated frame, fixed before every matrix

  let Γ : ({ a // a ∈ t } × (Fin n × Fin n)) ⊕ (Fin n × Fin n) → Fin n → ℝ :=
    Sum.elim (fun q => γl q.1.1 q.2) prescribed
  let e := Fintype.equivFin (({ a // a ∈ t } × (Fin n × Fin n)) ⊕ (Fin n × Fin n))
  let N := Fintype.card (({ a // a ∈ t } × (Fin n × Fin n)) ⊕ (Fin n × Fin n))
  let γ : Fin N → Fin n → ℝ := fun k => Γ (e.symm k)
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨Sum.inr (⟨0, hn⟩, ⟨0, hn⟩)⟩
  have hΓ : ∀ j, ∑ i : Fin n, (Γ j i) ^ 2 = 1 := by
    rintro (q | p)
    · exact hγl q.1.1 q.2
    · exact prescribed_unit p
  have hγ : ∀ k, ∑ i : Fin n, (γ k i) ^ 2 = 1 := fun k => hΓ (e.symm k)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hhi : 0 < hi := hlo.trans hlohi
  refine
    ⟨N, γ, lo / (2 * (N : ℝ)), (n : ℝ) * hi, div_pos hlo (by positivity), ?_, hγ, ?_, ?_, ?_⟩
  · -- `lo/(2N) ≤ lo/2 < lo < hi ≤ n·hi`

    have h1 : lo / (2 * (N : ℝ)) ≤ lo / 2 := by
      apply div_le_div_of_nonneg_left hlo.le (by norm_num)
      nlinarith
    have h2 : hi ≤ (n : ℝ) * hi := le_mul_of_one_le_left hhi.le hn1
    linarith
  · intro i
    refine ⟨e (Sum.inr (i, i)), ?_⟩
    simp [γ, Γ, prescribed]
  · intro i j hij
    refine ⟨e (Sum.inr (i, j)), ?_⟩
    simp [γ, Γ, prescribed, hij]
  · intro A _hA hloA hAhi
    have hsub := subtract_uniform_frame_preserves_interval hN γ hγ hlo A hloA hAhi
    dsimp only at hsub
    obtain ⟨_hε, hB1, hB2⟩ := hsub
    let G := ∑ k : Fin N, Matrix.vecMulVec (γ k) (γ k)
    let ε := lo / (2 * (N : ℝ))
    have hε0 : 0 ≤ ε := (div_pos hlo (by positivity)).le
    let B := A - ε • G
    have hBK : B ∈ K := ⟨hB1, hB2⟩
    obtain ⟨a, hat, hBa⟩ := Set.mem_iUnion₂.mp (ht hBK)
    have hBsymm : B.IsSymm := by
      have h := hB1.isHermitian.add (Matrix.PosSemidef.one.smul (half_pos hlo).le).isHermitian
      rw [sub_add_cancel] at h
      exact Matrix.isHermitian_iff_isSymm.mp h
    obtain ⟨b, hb0, hBrep⟩ :=
      hrep a B hBa
        hBsymm
    -- coefficients: `ε` everywhere, plus the local representation on the frame of `a`

    let x : ({ a // a ∈ t } × (Fin n × Fin n)) ⊕ (Fin n × Fin n) → ℝ :=
      Sum.elim (fun q => if q.1 = ⟨a, hat⟩ then b q.2 else 0) (fun _ => 0)
    have hx0 : ∀ j, 0 ≤ x j := by
      rintro (q | p)
      · by_cases hq : q.1 = ⟨a, hat⟩
        · simpa [x, hq] using hb0 q.2
        · simp [x, hq]
      · simp [x]
    let β : Fin N → ℝ := fun k => ε + x (e.symm k)
    have hxsum : ∑ k : Fin N, x (e.symm k) • Matrix.vecMulVec (γ k) (γ k) = B := by
      have hc := e.symm.sum_comp (fun j => x j • Matrix.vecMulVec (Γ j) (Γ j))
      change ∑ k : Fin N, x (e.symm k) • Matrix.vecMulVec (Γ (e.symm k)) (Γ (e.symm k)) = B
      rw [hc, Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [x, Γ, Sum.elim_inl, Sum.elim_inr, zero_smul, Finset.sum_const_zero, add_zero,
        ite_smul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact hBrep.symm
    have hAeq : A = ∑ k : Fin N, β k • Matrix.vecMulVec (γ k) (γ k) := by
      simp only [β, add_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
      rw [hxsum]
      change A = ε • G + (A - ε • G)
      abel
    have hβ0 : ∀ k, 0 ≤ β k := fun k => add_nonneg hε0 (hx0 _)
    have hdiag : ∀ i, A i i ≤ hi := by
      intro i
      have h := hAhi.diag_nonneg (i := i)
      have h' : 0 ≤ hi - A i i := by simpa using h
      linarith
    refine ⟨β, fun k => ⟨le_add_of_nonneg_right (hx0 _), ?_⟩, hAeq⟩
    exact coefficient_le_dimension_mul_cap γ β A hγ hβ0 hAeq hdiag k

end TraceCapFrame

section Frame
open Matrix Finset
private theorem quadratic_rank_one {n : ℕ} (v g : Fin n → ℝ) :
    dotProduct v ((vecMulVec g g).mulVec v) = (dotProduct g v) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, pow_two, Finset.mul_sum,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/--
**Coefficient cap.** If `A = ∑ b_k γ_k γ_kᵀ` with unit `γ_k`, `b ≥ 0` and `A ≤ hi I`, then every
`b_k ≤ hi`:
test `hi I − A ⪰ 0` against `γ_k`. -/
theorem coefficient_le_cap {n N : ℕ} (γ : Fin N → Fin n → ℝ) (b : Fin N → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) {hi : ℝ} (hγ : ∀ k, ∑ i, (γ k i) ^ 2 = 1) (hb : ∀ k, 0 ≤ b k)
    (hAe : A = ∑ k, b k • vecMulVec (γ k) (γ k))
    (hcap : (hi • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef) (k : Fin N) : b k ≤ hi := by
  have hq (v : Fin n → ℝ) : dotProduct v (A.mulVec v) = ∑ j, b j * (dotProduct (γ j) v) ^ 2 := by
    rw [hAe, Matrix.sum_mulVec, dotProduct_sum]
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, quadratic_rank_one]
  have hunit : dotProduct (γ k) (γ k) = 1 := by simpa only [dotProduct, ← pow_two] using hγ k
  have hu : dotProduct (γ k) (A.mulVec (γ k)) ≤ hi := by
    have h := hcap.dotProduct_mulVec_nonneg (γ k)
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, hunit, mul_one] at h
    linarith
  calc
    b k = b k * (dotProduct (γ k) (γ k)) ^ 2 := by rw [hunit]; ring
    _ ≤ ∑ j, b j * (dotProduct (γ j) (γ k)) ^ 2 :=
      Finset.single_le_sum (f := fun j => b j * (dotProduct (γ j) (γ k)) ^ 2)
        (fun j _ => mul_nonneg (hb j) (sq_nonneg _)) (mem_univ k)
    _ = dotProduct (γ k) (A.mulVec (γ k)) := (hq _).symm
    _ ≤ hi := hu

/--
**Gilbarg–Trudinger (2001), Lemma 17.13.** For `n > 0` and `0 < lo < hi` there are finitely many
unit vectors
`γ_k`, containing every coordinate vector and every normalized pair `(e_i+e_j)/√2` (`i ≠ j`), and
`lowerCoeff > 0`
(with `lowerCoeff < hi`), all fixed before any matrix, such that every positive definite `A` with
`lo I ≤ A ≤ hi I` is `∑ b_k γ_k γ_kᵀ` with `lowerCoeff ≤ b_k ≤ hi` for EVERY `k`. -/
theorem exists_uniform_positive_rank_one_frame {n : ℕ} (hn : 0 < n) {lo hi : ℝ} (hlo : 0 < lo)
    (hlohi : lo < hi) :
    ∃ (N : ℕ) (γ : Fin N → Fin n → ℝ) (lowerCoeff : ℝ),
      0 < lowerCoeff ∧
        lowerCoeff < hi ∧
          (∀ k, ∑ i : Fin n, (γ k i) ^ 2 = 1) ∧
            (∀ i : Fin n, ∃ k : Fin N, γ k = Pi.single i 1) ∧
              (∀ i j : Fin n,
                  i ≠ j →
                    ∃ k : Fin N,
                      γ k = fun a =>
                        ((Pi.single i (1 : ℝ) : Fin n → ℝ) a +
                            (Pi.single j (1 : ℝ) : Fin n → ℝ) a) /
                          Real.sqrt 2) ∧
                ∀ A : Matrix (Fin n) (Fin n) ℝ,
                  A.PosDef →
                    (A - lo • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef →
                      (hi • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef →
                        ∃ b : Fin N → ℝ,
                          (∀ k, lowerCoeff ≤ b k ∧ b k ≤ hi) ∧
                            A = ∑ k, b k • vecMulVec (γ k) (γ k) := by
  obtain ⟨N, γ, lc, _uc, hlc, _hluc, hγ, hcoord, hpair, hrep⟩ :=
    exists_uniform_positive_rank_one_frame_trace_cap hn hlo hlohi
  have hz : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef := Matrix.PosSemidef.zero
  have htop :
    (hi • (1 : Matrix (Fin n) (Fin n) ℝ) - lo • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
    rw [← sub_smul]
    exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hlohi.le)
  obtain ⟨b0, hb0, hA0⟩ :=
    hrep (lo • (1 : Matrix (Fin n) (Fin n) ℝ)) (Matrix.PosDef.one.smul hlo)
      (by simpa only [sub_self] using hz) htop
  obtain ⟨k0, -⟩ := hcoord ⟨0, hn⟩
  have hle : lc ≤ lo :=
    (hb0 k0).1.trans
      (coefficient_le_cap γ b0 _ hγ (fun k => hlc.le.trans (hb0 k).1) hA0
        (by simpa only [sub_self] using hz) k0)
  refine ⟨N, γ, lc, hlc, hle.trans_lt hlohi, hγ, hcoord, hpair, fun A hA hloA hAhi => ?_⟩
  obtain ⟨b, hb, hAe⟩ := hrep A hA hloA hAhi
  exact
    ⟨b, fun k =>
      ⟨(hb k).1, coefficient_le_cap γ b A hγ (fun j => hlc.le.trans (hb j).1) hAe hAhi k⟩, hAe⟩
end Frame

end FunctionalInequalities.Analysis

/-! ## Quadratic forms of frame directions: bounds, coordinates and normalized pairs -/

section FrameQuadratics

open Matrix Finset

namespace FunctionalInequalities.Analysis

/--
For a positive semidefinite `A` with `A ≤ K·I` and a unit vector `v`, the quadratic form `vᵀ A v`
lies in `[0, K]`. -/
theorem unit_quadratic_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) {K : ℝ}
    (hA : A.PosSemidef) (hK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
    (hv : ∑ i, (v i) ^ 2 = 1) :
    0 ≤ (∑ i, ∑ j, v i * v j * A i j) ∧ (∑ i, ∑ j, v i * v j * A i j) ≤ K := by
  have hq (P : Matrix (Fin n) (Fin n) ℝ) :
    dotProduct v (P.mulVec v) = ∑ i, ∑ j, v i * v j * P i j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hunit : dotProduct v v = 1 := by simpa only [dotProduct, ← pow_two] using hv
  have h0 := hA.dotProduct_mulVec_nonneg v
  have h1 := hK.dotProduct_mulVec_nonneg v
  simp only [star_trivial] at h0 h1
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul, hunit, mul_one, hq] at h1
  rw [hq] at h0
  exact ⟨h0, by linarith⟩

/-- The quadratic form of a coordinate vector `e_i` is the diagonal entry `A i i`. -/
theorem quadratic_coordinate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∑ a : Fin n,
        ∑ b : Fin n,
          (Pi.single i (1 : ℝ) : Fin n → ℝ) a * (Pi.single i (1 : ℝ) : Fin n → ℝ) b * A a b) =
      A i i := by
  simp [Pi.single_apply]

/--
For symmetric `A` and the normalized pair `(e_i + e_j)/√2`, the quadratic form is `A i j + (A i i +
A j j)/2`; with the
coordinate forms this recovers every off-diagonal entry (no `e_i − e_j` directions are needed). -/
theorem quadratic_normalized_pair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (i j : Fin n) :
    (∑ a : Fin n,
        ∑ b : Fin n,
          (((Pi.single i (1 : ℝ) : Fin n → ℝ) a + (Pi.single j (1 : ℝ) : Fin n → ℝ) a) /
                Real.sqrt 2) *
              (((Pi.single i (1 : ℝ) : Fin n → ℝ) b + (Pi.single j (1 : ℝ) : Fin n → ℝ) b) /
                Real.sqrt 2) *
            A a b) =
      A i j + (A i i + A j j) / 2 := by
  have he (a b : Fin n) :
    (((Pi.single i (1 : ℝ) : Fin n → ℝ) a + (Pi.single j (1 : ℝ) : Fin n → ℝ) a) /
            Real.sqrt 2) *
          (((Pi.single i (1 : ℝ) : Fin n → ℝ) b + (Pi.single j (1 : ℝ) : Fin n → ℝ) b) /
            Real.sqrt 2) *
        A a b =
      (((Pi.single i (1 : ℝ) : Fin n → ℝ) a + (Pi.single j (1 : ℝ) : Fin n → ℝ) a) *
          (((Pi.single i (1 : ℝ) : Fin n → ℝ) b + (Pi.single j (1 : ℝ) : Fin n → ℝ) b) *
            A a b)) /
        2 := by
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [div_mul_div_comm, mul_div_assoc, hs]
    ring
  calc
    _ =
        ∑ a : Fin n,
          ∑ b : Fin n,
            (((Pi.single i (1 : ℝ) : Fin n → ℝ) a + (Pi.single j (1 : ℝ) : Fin n → ℝ) a) *
                (((Pi.single i (1 : ℝ) : Fin n → ℝ) b + (Pi.single j (1 : ℝ) : Fin n → ℝ) b) *
                  A a b)) /
              2 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact he a b
    _ = _ := by
      simp only [← Finset.sum_div]
      simp [Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib]
      rw [hA.apply i j]
      ring

end FunctionalInequalities.Analysis

end FrameQuadratics
