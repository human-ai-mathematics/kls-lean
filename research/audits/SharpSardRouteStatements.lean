import FunctionalInequalities.Analysis.Sard.QuadraticCover
import FunctionalInequalities.Analysis.Sard.Smooth

/-!
# Route statements for the sharp finite-regularity Sard theorem

**This file contains only `#check`s. A proposition that type-checks is not a proof.**
It preserves the finite-regularity Sard route contracts using Mathlib notions, without auxiliary
structures, definitions or placeholder proofs. See `Analysis/Sard/Sharp.lean` and
`research/audits/SharpSardAudit.lean` for the source and client; the latter distinguishes the
original `M2` contract from its repaired antilipschitz version.

Same convention as `RankDeficientRouteStatements.lean`, `AreaFormulaRouteStatements.lean` and
`WeightedCoareaRouteStatements.lean`.

## The target and why the smooth descent does not reach it

The target is `Analysis.sard` in `Analysis/Sard/Sharp.lean`: the critical values of a
`C^n` real-valued function on an `n`-dimensional real normed space are Lebesgue-null.  `C^n` is the
sharp regularity for a real target (Whitney).  The proved `C^∞` theorem `sard_smooth`
(`Analysis/Sard/Smooth.lean`) stratifies the critical set by the order of vanishing of the
derivatives and, on the layer where the derivatives of order `≤ j` vanish but the order `j + 1` does
not, restricts `u` to the regular zero set of a `j`-th derivative component — a `C^{n-j}`
hypersurface — and inducts on the dimension.  At finite regularity the restriction is only
`C^{n-j}` (`D1` below), while the induction in dimension `n - 1` needs `C^{n-1}`: the descent loses
`j - 1` derivatives and fails for every `j ≥ 2`.  Any route that restricts `u` first pays this.

## The route: Morse's decomposition of an arbitrary set

A. P. Morse, *The behavior of a function on its critical set*, Ann. of Math. 40 (1939) 62–70, in the
`C^k` formulation of A. Norton, *The Zygmund Morse–Sard theorem*, J. Geom. Anal. 4 (1994) 403–424.
Nothing is restricted: instead every set `A ⊆ ℝⁿ` is decomposed, for every order `k`, into a
countable set and countably many pieces carried by `C¹` parametrized disks, so that **every** `C^k`
function vanishing on `A` is flat of order `k` along each piece (`M3`, the Morse vanishing lemma).
The proof is a double induction on `(n, k)`; the critical step `k → k + 1` differentiates
(`M2`, the mean value step along parametric segments), and the regular step `n → n + 1` pushes the
decomposition of a preimage forward along a `C^k` graph chart (`M1`) which is `1`-antilipschitz
(`M1'`) — at the **same** `k`, so no regularity is lost.  Applied to `A = {fderiv f = 0}` with
`f ∈ C^{k+1}`, whose derivative coordinates are `C^k` and vanish on `A`, it gives the Morse
criticality lemma `M4`: the critical set is covered by a countable set and countably many bounded
pieces with a uniform `o(‖y - x‖^{k+1})` modulus.  With `k + 1 = n` the proved covering count
`volume_image_eq_zero_of_oscillation_pow` (`M0`) finishes on `Fin n → ℝ` (`M5`), and the transport of
`sard_smooth` gives the target (`M6`).

The disks and the flatness predicate are internal to `M2`/`M3` and are spelled out inline below.
-/

noncomputable section

open Set Metric Filter Topology MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis

/-! ### M0 — proved: the covering count

A bounded subset of `Fin n → ℝ` on which `f` has a uniform `o(‖y - x‖ⁿ)` modulus has Lebesgue-null
image.  Already in the repository (`Analysis/Sard/QuadraticCover.lean`); recorded here because `M5`
consumes it with the exponent `n = k + 1`. -/

#check @FunctionalInequalities.Analysis.volume_image_eq_zero_of_oscillation_pow

/-! ### Reference — proved, smooth category

The `C^∞` graph chart and the `C^∞` Sard theorem whose finite-regularity counterparts are `M1` and
`M6`.  The transport in `sard_smooth` from `Fin n → ℝ` to an arbitrary space is exactly the
transport `M6` needs. -/

#check @FunctionalInequalities.Analysis.exists_local_graph
#check @FunctionalInequalities.Analysis.sard_smooth

/-! ### M1 — the `C^k` graph chart of a regular zero set

Near a regular zero `x₀` of a `C^k` function `w` (`1 ≤ k`), every zero of `w` is the graph point
`insertNth i (θ (removeNth i x)) (removeNth i x)` of a `C^k` function `θ` of the other `n`
coordinates.  The `C^k` inverse function theorem `ContDiffAt.to_localInverse` applied to the map
replacing the `i`-th coordinate by `w`, as in the smooth `exists_local_graph`; no manifold
framework. -/

#check (∀ {n k : ℕ}, 1 ≤ k → ∀ {w : (Fin (n + 1) → ℝ) → ℝ} {x₀ : Fin (n + 1) → ℝ},
    ContDiff ℝ k w → w x₀ = 0 → fderiv ℝ w x₀ ≠ 0 →
    ∃ (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ), ContDiff ℝ k θ ∧
      ∀ᶠ x in 𝓝 x₀, w x = 0 →
        x = Fin.insertNth (α := fun _ => ℝ) i (θ (Fin.removeNth i x)) (Fin.removeNth i x))

/-! ### M1' — the graph map is `1`-antilipschitz

Dropping a coordinate does not increase the sup norm.  This is what keeps every constant of a
decomposition unchanged when it is pushed forward along a graph chart in `M3`. -/

#check (∀ {n : ℕ} (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ) (a b : Fin n → ℝ),
    ‖a - b‖ ≤ ‖Fin.insertNth (α := fun _ => ℝ) i (θ a) a
      - Fin.insertNth (α := fun _ => ℝ) i (θ b) b‖)

/-! ### M2 — the mean value step along a `C¹` parametrized disk

`φ : Fin p → ℝ → Fin n → ℝ` is `C¹`; `S` is a set of points of `Fin n → ℝ`; the parametric segment
from `φ a` to `φ b` is the image of `[a, b]`.  If every coordinate `fderiv ℝ f · (Pi.single j 1)` is
flat of order `k` along the disk on `S` — `|·| ≤ ε ‖φ a - φ z‖ ^ k` at points `φ z` of short
parametric segments between points of `S` — then `f (φ z) - f (φ a)` is `o(‖φ a - φ z‖ ^ (k + 1))`
along the same segments.  The mean value inequality on the segment `[a, b]` and the derivative bound
of `φ` on the compact unit ball; the antilipschitz constant of `φ` is not needed here. -/

#check (∀ {n p k : ℕ} {φ : (Fin p → ℝ) → (Fin n → ℝ)}, ContDiff ℝ 1 φ →
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
            ≤ ε * ‖φ a - φ (a + s • (b - a))‖ ^ (k + 1))

/-! ### M3 — the Morse vanishing lemma

Every set `A ⊆ Fin n → ℝ` and every order `k` admit a Morse decomposition: a countable set `A₀`
and countably many pieces `q.1 ⊆ A`, each carried by a `C¹` parametrized disk `q.2.2` of some
parameter dimension `q.2.1`, antilipschitz on the closed unit ball with `q.1` inside its body,
such that **every** `C^k` function vanishing on `A` is flat of order `k` along the disk on the piece.
The single high-risk item of the route: a double induction on `(n, k)` in which the critical step
uses `M2` and the regular step pushes the decomposition of a preimage forward along the graph chart
of `M1`, using `M1'` to keep the antilipschitz constants. -/

#check (∀ (n k : ℕ) (A : Set (Fin n → ℝ)),
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
              |f (q.2.2 (a + s • (b - a)))| ≤ ε * ‖q.2.2 a - q.2.2 (a + s • (b - a))‖ ^ k)

/-! ### M4 — the Morse criticality lemma

The set `A` on which a `C^(k+1)` function `f` is critical is covered by a countable set and
countably many bounded pieces, on each of which `f` has a uniform `o(‖y - x‖ ^ (k + 1))` modulus.
`M3` applied to `A` at order `k`: the coordinates of `fderiv ℝ f` are `C^k` and vanish on `A`, so they
are flat of order `k` along each disk, and `M2` raises the order for `f` itself; the disks are then
forgotten.  Nothing but Mathlib notions survives in the statement. -/

#check (∀ {n k : ℕ} (A : Set (Fin n → ℝ)) {f : (Fin n → ℝ) → ℝ},
    ContDiff ℝ (k + 1) f → (∀ x ∈ A, fderiv ℝ f x = 0) →
    ∃ (A₀ : Set (Fin n → ℝ)) (P : Set (Set (Fin n → ℝ))), A₀.Countable ∧ P.Countable ∧
      A ⊆ A₀ ∪ ⋃₀ P ∧
      ∀ S ∈ P, Bornology.IsBounded S ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ (k + 1))

/-! ### M5 — Sard for `C^n` real-valued functions on `Fin n → ℝ`

`M4` with `k + 1 = n`, then `M0` on each piece; the image of the countable set is countable; a
countable union of null sets is null.  For `n = 0` the image is a single point.  The critical set is
not assumed measurable. -/

#check (∀ (n : ℕ) (u : (Fin n → ℝ) → ℝ), ContDiff ℝ n u →
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0)

/-! ### M6 — the target: `Analysis.sard`, verbatim

The contract of `Analysis.sard` in `Analysis/Sard/Sharp.lean`, restated independently. The
transport from `Fin (finrank ℝ V) → ℝ` along `ContinuousLinearEquiv.ofFinrankEq` is the one in
`sard_smooth`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {u : V → ℝ}, ContDiff ℝ (Module.finrank ℝ V) u →
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0)

/-! ### D1 — diagnostic, true and trivial: the regularity bookkeeping of the descent

Restricting a `C^k` function to a `C^k` graph yields a `C^k` function and nothing better.  In the
smooth descent the graph is that of a `j`-th derivative component of `u ∈ C^n`, so `k = n - j`,
while the next dimension needs `C^{n-1}`.  This is not a step of the route; it records why the
route does not restrict `u`. -/

#check (∀ {n k : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ} {θ : (Fin n → ℝ) → ℝ} (i : Fin (n + 1)),
    ContDiff ℝ k u → ContDiff ℝ k θ →
    ContDiff ℝ k (fun y : Fin n → ℝ => u (Fin.insertNth (α := fun _ => ℝ) i (θ y) y)))
