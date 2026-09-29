# Handover Prompt: Gap Two — Markov Property of the Log-Concave Law Heat Semigroup

> This file is a task prompt that can be directly pasted into the next session (style similar to 2026-09-19's `S5` task).
> Written on 2026-09-19, after the completion of the semigroup path `S1`–`S8` and the specific instantiation of `T`. The owner has not yet started this task.

---

Task: Prove the Markov property (preservation of positivity, sub-Markov, preservation of constants) of the log-concave law heat semigroup `P_t` in Lean 4 / Mathlib.

## Goal

In repository `KLS` (`/Users/lyuyuwei/Documents/ChatGPT/KLS`), add a module to prove the `P_t = hν.heatSemigroup m B hi ht : L²(ν) →L[ℝ] L²(ν)` defined by `KLS/LogConcave/HeatSemigroup.lean`:

* **M-A (positive preservation)** `0 ≤ f` ⟹ `0 ≤ P_t f` (the order of `Lp`, `MeasureTheory.Lp.coeFn_nonneg`);
* **M-B (sub-Markov)** `0 ≤ f ≤ 1` ⟹ `0 ≤ P_t f ≤ 1`;
* **M-C (constant preservation)** `P_t 1 = 1`, where `1 = L2.const ν 1` (`ν` is a probability measure so `1 ∈ L²`);
* **M-D (corollary)** `∫ P_t f dν = ∫ f dν` (symmetry + M-C: `⟪P_t f, 1⟫ = ⟪f, P_t 1⟫`), `|P_t f| ≤ P_t |f|`, and when `f ∈ L² ∩ L^∞` then `‖P_t f‖_∞ ≤ ‖f‖_∞`.

This is the **form gap two** in `tasks.json`'s `thm:logconcave-cheeger-poincare-comparison`. Without it, the pointwise bound in Ponti–Mondino's proof strategy Ledoux/De cannot be established.
Proving it is not part of any step in the Buser inequality; nodes will not receive progress markers. Form gap three (Γ calculus), four (heat estimate) are outside the scope of this task.

## Environment

* Lean `leanprover/lean4:v4.33.0`, Mathlib `v4.33.0` (pinned, no upgrade, no change to lakefile). Work directory `formalization/`.
* Compile each file with `lake env lean -DwarningAsError=true <relative-path>.lean`; require 0 errors and 0 warnings.
* New module suggestion to place `formalization/FunctionalInequalities/Analysis/Semigroup/Markov*.lean` (abstract part) and
  `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroupMarkov.lean` (specific part).

## Existing API (all hole-free, `#print axioms` standard)

Semigroup (`Analysis/Semigroup/`, 14 modules):
* `resolventCLM T hT hs` = `J_s = (1 + sT†T)⁻¹`, characterized by the weak equation `WeakResolvent T s f u : ∀ v ∈ D(T), ⟪u,v⟫ + s⟪Tu,Tv⟫ = ⟪f,v⟫`
  (`Resolvent.lean`: `resolventDomain_spec`, `eq_resolventDomain` (uniqueness), `resolventCLM_apply` (rfl), `norm_resolventCLM_le`, `resolventCLM_symm`).
* `yosida T hT hs` = `L_s = s⁻¹(1 − J_s)` (`YosidaApproximation.lean`, `yosida_apply`).
* `semigroupApply T hT hd t f` = `P_t f` (`Generated.lean`), `semigroupApply_spec`: `exp(−t•L_s) f → P_t f` (ε–δ);
  `semigroupCLM` (`SemigroupLaws.lean`), `eq_semigroupApply_of_tendsto` (uniqueness of limit), `norm_semigroupApply_le`, `inner_semigroupApply_left`, `semigroupApply_add`.
* `exp(−t•L_s)` related: `Yosida.lean`'s `norm_exp_neg_smul_apply_le` (contraction), `SemigroupLimit.lean`'s `norm_exp_neg_smul_sub_le`.
  Note `NormedSpace.exp_add_of_commute` lacks an instance on `H₀ →L[ℝ] H₀`, use `exp_add_of_commute_of_mem_ball (𝕂 := ℝ)` + `expSeries_radius_eq_top ℝ _`;
  `exp(a•1) x = Real.exp a * x` use `NormedSpace.map_exp` to transmit along `algebraMap`.

Concrete operators (`KLS/LogConcave/WeightedGradient.lean`, `HeatSemigroup.lean`; base `Energy/WeightedGradient/{Basic,Core,Closable}.lean`, operator defined on `Basic.lean`'s `Energy.WeightedGradient.operator`):
* `hν.weightedOperator m B hi : L²(ν) →ₗ.[ℝ] L²(ν; V)`, the domain is a globally Lipschitz class of `L²` test function class, acting `g ↦ B ∘ ∇g`;
  `weightedOperator_isClosable`, `dense_domain_weightedOperator`. Read `Energy/WeightedGradient/Basic.lean` (`operator`) and `Core.lean` (`smoothCore`, `constantSmoothCore`) to clarify the precise definitions of domain and action.
* `hν.closedWeightedOperator m B hi` = closure `T̄`; `heatSemigroup hν m B hi ht` = `semigroupCLM T̄ …`; `heatSemigroup_apply` (rfl).
* Relaxation: `weighted_relaxation_of_mem`: `f ∈ D(T̄)` ⟹ `(PreEnergy.ofLinearPMap T).sequentialRelaxation f = ‖T̄ f‖₊²`;
  `weighted_relaxation_of_notMem`: `f ∉ D(T̄)` implies `= ⊤`. `sequentialRelaxation x = ⨅ (approximating sequences f), sequenceEnergy f`
  (`Energy/Relaxation/Basic.lean`, `sequenceEnergy`) is the liminf. **This is the key tool for M1**, see below.
* Constants: `Energy.WeightedGradient.constantSmoothCore ν = smoothCore ν ⊔ span {L2.const ν 1}`, constants belong to the domain of the operator and have zero gradient—verify the exact lemma name of `T 1 = 0`.

Mathlib's `Lp` order structure: `MeasureTheory.Lp.instLattice` (`LpOrder.lean`), `Lp.coeFn_le`, `Lp.coeFn_nonneg`, `Lp.coeFn_sup`, `Lp.coeFn_inf`,
`Lp.posPart`/`coeFn_posPart`, `LipschitzWith.compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) : Lp E p μ → Lp F p μ`,
`L2.const`/`Lp.const`/`indicatorConstLp`.

## Recommended proof: Beurling–Deny, via resolvent

**M1 (The form is Markovian: normal contraction acts on `D(T̄)`).** For `φ : ℝ → ℝ` 1-Lipschitz, `φ 0 = 0` (this task only requires `φ = max(·, 0)`, `φ = min(·, 1)`, and `φ = min(max(·,0),1)`; the latter two require first translation or preprocessing of `φ 0 ≠ 0`—`min(·,1)` is 0 at 0, which is unobstructed), `u ∈ D(T̄)` ⟹ `φ ∘ u ∈ D(T̄)` and `‖T̄(φ∘u)‖ ≤ ‖T̄ u‖`.

Recommended route (avoiding the almost everywhere chain rule for Lipschitz functions and the "gradient is zero on level sets" lemma):
1. For a **smooth** 1-Lipschitz `ψ` (`ψ 0 = 0`, `|ψ'| ≤ 1`), and test function `g` (globally Lipschitz), `ψ ∘ g` remains a test function,
   The classical chain rule gives `∇(ψ∘g) = ψ'(g)∇g`, hence `‖B∇(ψ∘g)‖ ≤ ‖B∇g‖` pointwise, `‖T(ψ∘g)‖ ≤ ‖T g‖`.
2. Take smooth 1-Lipschitz `ψ_n → φ` uniformly (by mollification; or, for `max(·,0)`, an explicit family such as `ψ_n(x) = (√(x²+1/n²) + x)/2 − 1/(2n)`,
   The explicit family omits the smoothing machine).
3. For `u ∈ D(T̄)`, take test function `g_k → u` (`L²`) and `T g_k → T̄ u` (definition of closure). Diagonalization: `ψ_{n(k)} ∘ g_k → φ ∘ u` on `L²`
   (`‖ψ_n∘g_k − φ∘g_k‖₂ ≤ ‖ψ_n − φ‖_∞`, `‖φ∘g_k − φ∘u‖₂ ≤ ‖g_k − u‖₂`), energy `‖T(ψ_{n(k)}∘g_k)‖² ≤ ‖T g_k‖² → ‖T̄ u‖²`.
4. By the definition of `sequentialRelaxation` (the liminf of the energy of an approximating sequence), `relaxation(φ∘u) ≤ ‖T̄ u‖² < ⊤`,
   By the contrapositive of `weighted_relaxation_of_notMem` we obtain `φ∘u ∈ D(T̄)`, and then by `weighted_relaxation_of_mem` we obtain `‖T̄(φ∘u)‖ ≤ ‖T̄ u‖`.

This step contains the only genuine analytical content of the task; the rest involves Hilbert space algebra and limits.

**M2 (`J_s` positive).** `J_s f` is the unique minimizer of `F(u) = ‖u − f‖² + s‖T̄ u‖²` on `D(T̄)`: by direct pointwise calculation from the weak equation,
`F(v) − F(u) = ‖v − u‖² + s‖T̄(v−u)‖² ≥ 0` (without requiring compactness). If `f ≥ 0`, define `u = J_s f` and `u⁺ = u ⊔ 0`:
pointwise `|u⁺ − f| ≤ |u − f|` (since `f ≥ 0`), M1 gives `‖T̄ u⁺‖ ≤ ‖T̄ u‖`, hence `F(u⁺) ≤ F(u)`, uniqueness ⟹ `u⁺ = u` ⟹ `u ≥ 0`.

**M3 (`J_s`-th Markov).** By the same method, `φ = min(·,1)`: `f ≤ 1` ⟹ `J_s f ≤ 1`.

**M4 (`J_s 1 = 1`).** `1 ∈ D(T̄)`, `T̄ 1 = 0` (constants are test functions, gradient zero), so `u = 1` satisfies the weak equation with data `1`, uniqueness.
Corollary `L_s 1 = 0`, `exp(−t•L_s) 1 = 1` (the series of `exp` is term-by-term zero, or the derivative of `exp(−t•L_s) 1 − 1` is zero).

**M5 (`exp(−t•L_s)` positive, sub-Markov).** `−t•L_s = (−t/s)•1 + (t/s)•J_s`, the two commute,
`exp(−t•L_s) = e^{−t/s} · exp((t/s)•J_s) = e^{−t/s} Σ_k (t/s)^k/k! · J_s^k` (`NormedSpace.exp_eq_tsum`, `expSeries_apply_eq`,
acting on `f` via the continuous linear image of `ContinuousLinearMap.map_tsum` or `tsum`). For each `J_s^k f ≥ 0` (M2 iteration), the partial sum `≥ 0`,
the limit `≥ 0`—requires **the positive cone of `L²` to be closed**: for `Lp`, `{f | 0 ≤ f}` closed. In Mathlib, look up `Lp` on `OrderClosedTopology`/[`isClosed_le`];
if not, use the dual characterization `0 ≤ f ↔ ∀ g ≥ 0, 0 ≤ ⟪f, g⟫` (in one direction use `g = f⁻`). Sub-Markov: `Σ e^{−t/s}(t/s)^k/k! · J_s^k f ≤ Σ e^{−t/s}(t/s)^k/k! · 1 = 1`.

**M6 (`P_t`).** `exp(−t•L_s) f → P_t f` (`semigroupApply_spec`), positive cone closed ⟹ `P_t f ≥ 0`; similarly `≤ 1` (taking limit of `1 − exp(−t•L_s) f ≥ 0`);
`P_t 1 = 1` follows from M4 and limit uniqueness (`eq_semigroupApply_of_tendsto`).

**M7 (Corollary M-D).** `⟪P_t f, 1⟫ = ⟪f, P_t 1⟫ = ⟪f, 1⟫` i.e. `∫ P_t f = ∫ f`; `|P_t f| ≤ P_t |f|` by `−|f| ≤ f ≤ |f|` and positivity, linearity;
`L^∞` bound by sub-Markov `f/‖f‖_∞` scaling.

## Known dead ends / friction

1. Do not attempt to prove the almost everywhere chain rule for composition of Lipschitz functions (requires "the gradient of Lipschitz `g` to be almost everywhere zero on `{g = c}`",
   Mathlib does not have it, nor does the coarea machinery in repository provide it directly. Proceed with the smooth approximation above + relaxed definition.
2. `ContinuousLinearMap` Universal `norm_*`/`dist_*` lemma on types often fails due to rhombus mismatch; preserves pointwise form.
3. `push_neg`, `ContinuousLinearMap.mul_apply`, `.smul_apply`, `.neg_apply`, `.one_apply` are deprecated in this pin and will cause an error; `abs_add` is `abs_add_le`;
   `Dense.exists_dist_lt` does not exist (using `Metric.mem_closure_iff`); `div_le_div_iff` → `div_le_div_iff₀`; `real_inner_comm x y : ⟪y,x⟫ = ⟪x,y⟫`.
4. `-DwarningAsError` Gate: `unusedSectionVars` (`omit … in` written in docstring **before**), `unusedSimpArgs`, `unnecessarySimpa`, `haveI` used for Prop changing `have`.
5. The abstract part (the Hilbert space skeleton of M2–M6) suggests parametrization: for any closed dense `T` and the assumption of a "normal contraction acting on `D(T)`" `hM` (i.e. the conclusion of M1)
   Prove `P_t` for positive and sub-Markov, then in the specific module eliminate `hM` using M1. Thus M1 and M2–M6 can be run in parallel for two proof sessions.

## Delivery and Acceptance

1. First write the route statement file `research/audits/MarkovRouteStatements.lean` (containing only `#check`, each line with a proof draft), compile and pass before distributing the proof.
2. New module zero `sorry`, zero placeholder axioms, `-DwarningAsError=true` under 0 error 0 warning, each public declaration has a docstring, module documentation states this is a gap two, does not provide gap three/four, and is not any step of Buser's.
3. Audit client verbatim rephrases and resolves the route statements and eliminates, `#print axioms` all `[propext, Classical.choice, Quot.sound]`.
4. Honestly report which route assumptions are unused, and differences between the proof and draft. If any route statement is false (example: `S6`'s abstract form is false, see `2026-09-19-yosida-limit-route.md`'s `Y0`),
   the route file remains unchanged in bytes, prove the correct version and record it.
5. Integration performed by the main session: aggregate root import, `lake build`, `tasks.json` evidence hash and `note`/`gap` appended, decision record, `verify.py`.
   `infrastructure.status` remains `missing` until gaps three and four are also closed.

## Things not to do

* Do not modify `FunctionalInequalities.lean`, `lakefile.toml`, `tasks.json`, Blueprint `.tex`, do not `git add/commit/push`, do not `lake build`, do not `verify.py` (proof session).
* Do not touch gap three (Γ calculus, `‖∇P_t f‖ ≤ P_t‖∇f‖`) and gap four (`‖P_t f − f‖₁ ≤ C√t·TV(f)`, `‖∇P_t f‖_∞ ≤ Ct^{−1/2}‖f‖_∞`), nor claim this statement is closer to the Buser inequality than it actually is.
