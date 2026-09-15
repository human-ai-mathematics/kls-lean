# kls-lean

Public API short names omit information already expressed by their namespaces; see the [naming guide](research/naming.md).

Lean formalization of functional inequalities toward the KLS conjecture, with separate
statement review and proof stages. Lean and Mathlib are pinned to **v4.33.0**.

Public Lean interfaces may evolve during this exploratory stage, including interfaces of proved
results. Proof work does not require a prior freeze. `proved` and `\leanok` certify the current
statement and proof, without promising signature stability. Mathematical scope changes are
recorded explicitly and checked against the original goal; see the
[current lifecycle](research/ledger-schema.md#lifecycle). Earlier freeze records remain dated
review snapshots.

## Current status (2026-09-15)

The ledger contains **24 Lean-certified nodes**. Three isolated WIP modules retain **10 explicit
`sorry` proofs** (2/3/5); some downstream proof bodies also depend transitively on those holes.
The proved infrastructure now includes global Gauss–Green, smooth recovery sequences, the
Minkowski coarea inequality, smooth Sard, level-set integral measurability, critical-slice nullity,
weighted graph area on open domains, and C¹ coarea on regular open domains.

The general C¹ and Lipschitz weighted coarea formulas and the reverse Cheeger comparison remain
open. So do the universal conditional-fiber frame bound and the dimension-free KLS bound.
The one-dimensional certificate proves the `4 Var` upper bound; it does not separately certify
optimality of the coefficient `4` across all laws. The identity `E^can = 2 Ch` uses the local-slope
convention and holds when the intrinsic law is absolutely continuous, hence for log-concave laws.
See the [current handoff](HANDOFF.md) for precise scopes and remaining obligations.

## Proof progress tree

Last updated: **2026-09-15**. All four active sufficient routes in the
[route composition](formalization/blueprint/route-composition.yaml) are shown below.
The upstream roadmap is pinned to `34b5fcd57fef17089e781616005fe6d3641bd11e`, as recorded in
[the September 12 synchronization](research/decisions/2026-09-12-upstream-research-sync.md).
This is a complete overview of those four routes, not an enumeration of every upstream lemma.

**Read from left to right, toward KLS.** Solid arrows carry required inputs toward a consumer or
route assembly. All inputs to an **AND** diamond are required; the **OR** diamond means any one
completed route suffices. Dotted arrows show supporting context or frontend alignment, not
additional sufficient implications. An arrow records how an input would be used; it does not
assert that an open input or an unformalized consumer has been proved. Only selected dependencies
are displayed; the Blueprint and route composition retain the precise statements and dependencies.

**Legend:** ✓ Completed in Lean · ◐ Partially formalized · ○ Not yet completed in Lean.
Green marks completed results, amber marks partial progress, gray marks pending work, and the
orange outline highlights the next proof step. These symbols describe **our formalization
progress**. An upstream mathematical proof or conditional argument alone does not earn a ✓;
its provenance is noted separately. A ✓ does not imply a separate ledger certificate.

### Four routes converging on KLS

```mermaid
flowchart LR
    KLS["○ KLS conjecture<br/>Dimension-free bound"]
    ANY{"OR<br/>Any one completed route"}
    DENS["✓ Log-concave densities<br/>Intrinsic affine support"]
    NORM["✓ Centering and whitening<br/>Affine ⇔ Covariance-normalized ⇔ Isotropic"]
    FORMS["✓ Closed quadratic energies<br/>Normal contractions and Dirichlet property"]
    ENERGY["✓ Canonical energy = 2 × Cheeger energy<br/>For log-concave laws; local-slope convention"]
    CONST["✓ Smooth, intrinsic and local-slope<br/>Poincaré constants agree for log-concave laws"]
    CB["○ Cheeger–Buser comparison<br/>Not yet Lean-certified"]
    EG["○ Tight-prefix absorptive<br/>Carleson estimate"]
    EC["○ Tight-window consumption<br/>Upstream reviewed implication; not Lean"]
    EAND{"○ Eldan localization route<br/>All required inputs (AND)"}
    SG["○ Fixed-eigenfunction<br/>Full-damping occupation bound"]
    SC["○ Full-damping sufficiency<br/>Upstream reviewed implication; not Lean"]
    SAND{"○ Moment-map spectral route<br/>All required inputs (AND)"}
    MH["○ W₂ lower semicontinuity<br/>and CMH → affine Poincaré bound<br/>Upstream reviewed; not Lean"]
    MG["○ Uniformly bounded<br/>CMH recovery envelope"]
    MT["✓ Affine Poincaré constant<br/>Translation invariance and closed form"]
    MC["○ One CMH recovery sequence suffices<br/>Upstream reviewed implication; not Lean"]
    MAND{"○ Moment-map CMH route<br/>All required inputs (AND)"}
    FC["✓ Conditional-fiber<br/>Closed Dirichlet form"]
    ONE["✓ One-dimensional log-concave bound<br/>Poincaré constant ≤ 4 × variance"]
    FLOG["✓ Almost-everywhere<br/>Fiber log-concavity"]
    FP["✓ Energy comparison<br/>Given a fiber Poincaré bound"]
    F4["✓ Fiber energy<br/>≤ 4 × gradient energy"]
    FG["○ Test-independent frame<br/>Universal bound Var ≤ C × fiber energy"]
    FAND{"◐ Conditional-fiber frame route<br/>All required inputs (AND)"}

    DENS --> NORM
    DENS --> FLOG
    FORMS -.->|energy foundation| FC
    FORMS -.->|energy foundation| ENERGY
    CONST -.->|frontend alignment, not an extra gate| KLS
    CB --> EAND
    EG --> EAND
    EC --> EAND
    SG --> SAND
    SC --> SAND
    NORM --> SAND
    MH --> MAND
    MG --> MAND
    MT --> MAND
    MC --> MAND
    NORM --> MAND
    ONE --> F4
    FLOG --> F4
    FP --> F4
    FC --> FAND
    FP --> FAND
    F4 --> FAND
    FG --> FAND
    NORM --> FAND
    EAND --> ANY
    SAND --> ANY
    MAND --> ANY
    FAND --> ANY
    ANY --> KLS

    classDef done fill:#e8f5e9,stroke:#388e3c,color:#183b1c;
    classDef partial fill:#fff3df,stroke:#c88719,color:#66420d;
    classDef todo fill:#f2f2f2,stroke:#888,color:#333;
    classDef focus fill:#fff0dc,stroke:#d47b13,color:#663800,stroke-width:3px;
    classDef logic fill:#ffffff,stroke:#555,color:#222;
    class DENS,NORM,FORMS,ENERGY,CONST,MT,FC,ONE,FLOG,FP,F4 done;
    class CB,MH todo;
    class EC,SC,MC todo;
    class KLS,EG,SG,MG,FG todo;
    class ANY logic;
    class EAND,SAND,MAND todo;
    class FAND partial;
    click KLS href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Statement.lean" "○ KLS conjecture — Dimension-free bound" _blank
    click ANY href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml" "OR — Any one completed route" _blank
    click DENS href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/BorellRepresentation.lean" "✓ Log-concave densities — Intrinsic affine support" _blank
    click NORM href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean" "✓ Centering and whitening — Affine ⇔ Covariance-normalized ⇔ Isotropic" _blank
    click FORMS href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean" "✓ Closed quadratic energies — Normal contractions and Dirichlet property" _blank
    click ENERGY href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/Cheeger.lean" "✓ Canonical energy = 2 × Cheeger energy — For log-concave laws; local-slope convention" _blank
    click CONST href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Poincare.lean" "✓ Smooth, intrinsic and local-slope — Poincaré constants agree for log-concave laws" _blank
    click CB href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex" "○ Cheeger–Buser comparison — Not yet Lean-certified" _blank
    click EG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Tight-prefix absorptive — Carleson estimate" _blank
    click EC href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Tight-window consumption — Upstream reviewed implication; not Lean" _blank
    click EAND href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml" "○ Eldan localization route — All required inputs (AND)" _blank
    click SG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Fixed-eigenfunction — Full-damping occupation bound" _blank
    click SC href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Full-damping sufficiency — Upstream reviewed implication; not Lean" _blank
    click SAND href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml" "○ Moment-map spectral route — All required inputs (AND)" _blank
    click MH href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ W₂ lower semicontinuity — and CMH → affine Poincaré bound — Upstream reviewed; not Lean" _blank
    click MG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Uniformly bounded — CMH recovery envelope" _blank
    click MT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Poincare/CovarianceGradient/Translation.lean" "✓ Affine Poincaré constant — Translation invariance and closed form" _blank
    click MC href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ One CMH recovery sequence suffices — Upstream reviewed implication; not Lean" _blank
    click MAND href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml" "○ Moment-map CMH route — All required inputs (AND)" _blank
    click FC href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber/Closed.lean" "✓ Conditional-fiber — Closed Dirichlet form" _blank
    click ONE href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean" "✓ One-dimensional log-concave bound — Poincaré constant ≤ 4 × variance" _blank
    click FLOG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean" "✓ Almost-everywhere — Fiber log-concavity" _blank
    click FP href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean" "✓ Energy comparison — Given a fiber Poincaré bound" _blank
    click F4 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean" "✓ Fiber energy — ≤ 4 × gradient energy" _blank
    click FG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Test-independent frame — Universal bound Var ≤ C × fiber energy" _blank
    click FAND href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml" "◐ Conditional-fiber frame route — All required inputs (AND)" _blank
```

The four AND nodes describe unfinished route assemblies. The conditional-fiber route is ◐
because its route-specific form and comparison results are proved; the universal frame gate is
still ○. The other three route assemblies remain ○: shared foundations or upstream arguments
alone do not amount to completed local route proofs.
In particular, no upstream theorem named `thm:conditional-fiber-frame-suffices` is invented:
the fiber route assembles the named form, comparison, one-dimensional bound, frame gate, and
normalization inputs. The CMH route requires a regular recovery sequence; it is a sufficient
condition, not an equivalence with KLS. The metric Cheeger **energy** identity is distinct from
the isoperimetric Cheeger **constant** comparison.

### Shared analytic progress: coarea and isoperimetric comparison

The endpoint below is the Cheeger–Buser input to the Eldan assembly above. Completing this
analytic chain alone does not complete that route: the tight-prefix gate and its formalized
consumer are still needed. Here `h_M` is the Minkowski Cheeger constant and `h_S` the
smooth-boundary Cheeger constant. Multiple incoming solid arrows are joint inputs.

```mermaid
flowchart LR
    GG["✓ Global Gauss–Green"]
    REC["✓ Smooth recovery sequences"]
    FWD["✓ Forward comparison<br/>h_M ≤ h_S"]
    MINK["✓ Minkowski coarea inequality"]
    SARD["✓ Smooth Sard theorem<br/>Regular superlevel sets"]
    MEAS["✓ Level-set integral measurability"]
    GRAPH["✓ Weighted graph area<br/>On open domains"]
    REG["✓ Coarea on regular open domains<br/>Parametric inverse and substitution"]
    CRIT["✓ Critical slices are null<br/>For almost every level"]
    C1["○ Assemble general C¹ coarea<br/>Next proof step"]
    WHIT["○ Whitney extension<br/>Exact Lipschitz-to-C¹ pieces"]
    LIP["○ General Lipschitz<br/>Weighted coarea formula"]
    SCI["○ Smooth coarea inequality"]
    CUT["✓ Distance-cutoff estimates<br/>and smooth approximation"]
    REV["○ Reverse comparison<br/>h_S ≤ h_M"]
    EQ["◐ Equality h_M = h_S<br/>Lean proof still incomplete"]
    FRONT["○ Density Cheeger<br/>Frontend identification; not Lean"]
    CB["○ Cheeger–Buser comparison<br/>Not yet Lean-certified"]

    GG --> REC
    REC --> FWD
    GRAPH --> REG
    MEAS -.->|localized measurability| REG
    REG --> C1
    CRIT --> C1
    C1 --> LIP
    WHIT --> LIP
    MEAS --> LIP
    C1 --> SCI
    SARD --> SCI
    SCI --> REV
    CUT --> REV
    FWD --> EQ
    REV --> EQ
    EQ --> FRONT
    FRONT --> CB

    classDef done fill:#e8f5e9,stroke:#388e3c,color:#183b1c;
    classDef partial fill:#fff3df,stroke:#c88719,color:#66420d;
    classDef todo fill:#f2f2f2,stroke:#888,color:#333;
    classDef focus fill:#fff0dc,stroke:#d47b13,color:#663800,stroke-width:3px;
    classDef logic fill:#ffffff,stroke:#555,color:#222;
    class GG,REC,FWD,MINK,SARD,MEAS,GRAPH,REG,CRIT,CUT done;
    class FRONT,CB todo;
    class EQ partial;
    class WHIT,LIP,SCI,REV todo;
    class C1 focus;
    click GG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/GaussGreen.lean" "✓ Global Gauss–Green" _blank
    click REC href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean" "✓ Smooth recovery sequences" _blank
    click FWD href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean" "✓ Forward comparison — h_M ≤ h_S" _blank
    click MINK href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean" "✓ Minkowski coarea inequality" _blank
    click SARD href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/SmoothSard.lean" "✓ Smooth Sard theorem — Regular superlevel sets" _blank
    click MEAS href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/LevelSetMeasurable.lean" "✓ Level-set integral measurability" _blank
    click GRAPH href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/OpenGraphIntegral.lean" "✓ Weighted graph area — On open domains" _blank
    click REG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/RegularCoarea.lean" "✓ Coarea on regular open domains — Parametric inverse and substitution" _blank
    click CRIT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CriticalSlice.lean" "✓ Critical slices are null — For almost every level" _blank
    click C1 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l11" "○ Assemble general C¹ coarea — Next proof step" _blank
    click WHIT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l6" "○ Whitney extension — Exact Lipschitz-to-C¹ pieces" _blank
    click LIP href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l12" "○ General Lipschitz — Weighted coarea formula" _blank
    click SCI href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean" "○ Smooth coarea inequality" _blank
    click CUT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/DistanceCutoff.lean" "✓ Distance-cutoff estimates — and smooth approximation" _blank
    click REV href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean" "○ Reverse comparison — h_S ≤ h_M" _blank
    click EQ href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean" "◐ Equality h_M = h_S — Lean proof still incomplete" _blank
    click FRONT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex" "○ Density Cheeger — Frontend identification; not Lean" _blank
    click CB href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex" "○ Cheeger–Buser comparison — Not yet Lean-certified" _blank
```

The general C¹ formula combines regular-region coarea with critical-slice nullity. The Lipschitz
extension has its own Whitney/decomposition obligations and is not a prerequisite for the C¹
specialization used by smooth coarea. The proved Minkowski coarea inequality is shown separately;
it is not the still-open weighted coarea equality. Smooth Sard here means the C∞ theorem, not
the still-open sharp finite-regularity Sard statement.

### Benchmarks and upstream research beyond the four route gates

These results calibrate or investigate the program. They do not provide additional completed
routes to KLS, and no solid implication arrow from a model calculation to a universal gate is intended.

| Result or research direction | Recorded status and boundary | Source |
| --- | --- | --- |
| Sharp one-dimensional Gaussian constant | ✓ Lean-proved; Gaussian laws only | [Lean source](formalization/FunctionalInequalities/Poincare/Gaussian/Real.lean) |
| Finite Poincaré tensorization | ✓ Lean-proved; independent-product infrastructure | [Lean source](formalization/FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean) |
| Spectral restart and fourth-moment estimates | Upstream reviewed; not Lean; do not close uniform-time occupation | [Synchronization record](research/decisions/2026-09-12-upstream-research-sync.md) |
| Letwin-dependent short-time spectral chain | Conditional upstream result; not Lean; not dimension-free KLS | [Synchronization record](research/decisions/2026-09-12-upstream-research-sync.md) |
| Screened localization on a regular split class | Restricted upstream result; the universal gate remains open | [Synchronization record](research/decisions/2026-09-12-upstream-research-sync.md) |
| CMH linear spectral resolution and third-moment decomposition | Upstream reviewed weak/closed-form statements; no universal higher-order remainder bound | [Synchronization record](research/decisions/2026-09-12-upstream-research-sync.md) |
| Sharp gate-zero matrix bound | Upstream conjecture; not proved or Lean-certified | [Synchronization record](research/decisions/2026-09-12-upstream-research-sync.md) |
| Exponential-cone and cube-cone models | Exact restricted models; not a universal CMH or recovery-envelope bound | [Synchronization record](research/decisions/2026-09-12-upstream-research-sync.md) |
| Simplex root-frame degree-two result | Upstream reviewed polynomial-sector result; not a full L² frame bound | [Synchronization record](research/decisions/2026-09-12-upstream-research-sync.md) |
| Historical weighted near-Cheeger package | REFUTED upstream by the exponential-spectator obstruction; excluded from the four active routes | [Historical branch](formalization/blueprint/src/chapters/50-kls-routes.tex) |

Click a node to open its source in a new tab. Links follow `main`; the upstream provenance remains
pinned as stated above. If diagram links are disabled in your viewer, use the directory below.

<details>
<summary>Node links: Lean sources and documentation</summary>

| Node | Source |
| --- | --- |
| ○ KLS conjecture — Dimension-free bound | [Open source](formalization/FunctionalInequalities/KLS/Statement.lean) |
| OR — Any one completed route | [Open source](formalization/blueprint/route-composition.yaml) |
| ✓ Log-concave densities — Intrinsic affine support | [Open source](formalization/FunctionalInequalities/KLS/LogConcave/BorellRepresentation.lean) |
| ✓ Centering and whitening — Affine ⇔ Covariance-normalized ⇔ Isotropic | [Open source](formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean) |
| ✓ Closed quadratic energies — Normal contractions and Dirichlet property | [Open source](formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean) |
| ✓ Canonical energy = 2 × Cheeger energy — For log-concave laws; local-slope convention | [Open source](formalization/FunctionalInequalities/Energy/Cheeger.lean) |
| ✓ Smooth, intrinsic and local-slope — Poincaré constants agree for log-concave laws | [Open source](formalization/FunctionalInequalities/KLS/LogConcave/Poincare.lean) |
| ○ Cheeger–Buser comparison — Not yet Lean-certified | [Open source](formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex) |
| ○ Tight-prefix absorptive — Carleson estimate | [Open source](formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ○ Tight-window consumption — Upstream reviewed implication; not Lean | [Open source](formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ○ Eldan localization route — All required inputs (AND) | [Open source](formalization/blueprint/route-composition.yaml) |
| ○ Fixed-eigenfunction — Full-damping occupation bound | [Open source](formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ○ Full-damping sufficiency — Upstream reviewed implication; not Lean | [Open source](formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ○ Moment-map spectral route — All required inputs (AND) | [Open source](formalization/blueprint/route-composition.yaml) |
| ○ W₂ lower semicontinuity — and CMH → affine Poincaré bound — Upstream reviewed; not Lean | [Open source](formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ○ Uniformly bounded — CMH recovery envelope | [Open source](formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ✓ Affine Poincaré constant — Translation invariance and closed form | [Open source](formalization/FunctionalInequalities/Poincare/CovarianceGradient/Translation.lean) |
| ○ One CMH recovery sequence suffices — Upstream reviewed implication; not Lean | [Open source](formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ○ Moment-map CMH route — All required inputs (AND) | [Open source](formalization/blueprint/route-composition.yaml) |
| ✓ Conditional-fiber — Closed Dirichlet form | [Open source](formalization/FunctionalInequalities/KLS/ConditionalFiber/Closed.lean) |
| ✓ One-dimensional log-concave bound — Poincaré constant ≤ 4 × variance | [Open source](formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean) |
| ✓ Almost-everywhere — Fiber log-concavity | [Open source](formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| ✓ Energy comparison — Given a fiber Poincaré bound | [Open source](formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean) |
| ✓ Fiber energy — ≤ 4 × gradient energy | [Open source](formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| ○ Test-independent frame — Universal bound Var ≤ C × fiber energy | [Open source](formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ◐ Conditional-fiber frame route — All required inputs (AND) | [Open source](formalization/blueprint/route-composition.yaml) |
| ✓ Global Gauss–Green | [Open source](formalization/FunctionalInequalities/KLS/Geometry/GaussGreen.lean) |
| ✓ Smooth recovery sequences | [Open source](formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean) |
| ✓ Forward comparison — h_M ≤ h_S | [Open source](formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean) |
| ✓ Minkowski coarea inequality | [Open source](formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean) |
| ✓ Smooth Sard theorem — Regular superlevel sets | [Open source](formalization/FunctionalInequalities/Analysis/SmoothSard.lean) |
| ✓ Level-set integral measurability | [Open source](formalization/FunctionalInequalities/KLS/Geometry/LevelSetMeasurable.lean) |
| ✓ Weighted graph area — On open domains | [Open source](formalization/FunctionalInequalities/Analysis/OpenGraphIntegral.lean) |
| ✓ Coarea on regular open domains — Parametric inverse and substitution | [Open source](formalization/FunctionalInequalities/KLS/Geometry/RegularCoarea.lean) |
| ✓ Critical slices are null — For almost every level | [Open source](formalization/FunctionalInequalities/KLS/Geometry/CriticalSlice.lean) |
| ○ Assemble general C¹ coarea — Next proof step | [Open source](research/decisions/2026-09-15-weighted-coarea-route.md#l11) |
| ○ Whitney extension — Exact Lipschitz-to-C¹ pieces | [Open source](research/decisions/2026-09-15-weighted-coarea-route.md#l6) |
| ○ General Lipschitz — Weighted coarea formula | [Open source](research/decisions/2026-09-15-weighted-coarea-route.md#l12) |
| ○ Smooth coarea inequality | [Open source](formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| ✓ Distance-cutoff estimates — and smooth approximation | [Open source](formalization/FunctionalInequalities/KLS/Geometry/DistanceCutoff.lean) |
| ○ Reverse comparison — h_S ≤ h_M | [Open source](formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| ◐ Equality h_M = h_S — Lean proof still incomplete | [Open source](formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| ○ Density Cheeger — Frontend identification; not Lean | [Open source](formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex) |

</details>

**Maintenance:** Review both diagrams after every proof update. Update the affected labels,
✓/◐/○ markers, colors, dependencies, date, source links, directory, and current-status summary together
with the proof and its verification records. Preserve prerequisite-to-conclusion arrow direction,
AND within routes, OR between routes, and the distinction between upstream mathematics and
local Lean proofs. Keep the diagrams and their surrounding documentation in English.

## Mathematical API organization (2026-09-08)

The public frontends are `SmoothTest`, `SmoothGradient`, `WeightedGradient`,
`CovarianceGradient`, and `LocalSlope`; `Ambient` and `Intrinsic` identify the carrier construction.
Probability pushforwards and L² pullbacks occupy their own layers. See [the naming guide](research/naming.md) and [the migration record](research/decisions/2026-09-08-mathematical-api-organization.md).

## Where to look

| Purpose | Entry point |
| --- | --- |
| Lean source layout, imports, and build instructions | [formalization/README.md](formalization/README.md) |
| Executable theorem map and long-route alternatives | [formalization/blueprint/README.md](formalization/blueprint/README.md) |
| `L²`/energy foundation guide | [Poincare/README.md](formalization/FunctionalInequalities/Poincare/README.md) |
| Compiled foundation examples and boundary cases | [PoincareFoundation.lean](examples/PoincareFoundation.lean) |
| Proved ambient/intrinsic and smooth-test/relaxed comparisons | [Comparison guide](formalization/FunctionalInequalities/Poincare/Euclidean/README.md) |
| Mathematical definitions and scope | [LEAN_DESIGN.md](LEAN_DESIGN.md) |
| Current work and proof handoff | [HANDOFF.md](HANDOFF.md) |
| Node statements and certification status | [research/a-series/ledger.yaml](research/a-series/ledger.yaml) |
| Node-specific Lean entry points | [solutions/README.md](solutions/README.md) |
| Review history | [research/decisions/](research/decisions/) and [research/explorations/](research/explorations/) |
| Proof corrections, stronger bounds, and simpler arguments | [Proof Corrections and Improvements](research/proof-corrections-and-improvements.md) |
| Literal Lean KLS target | [KLS/Statement.lean](formalization/FunctionalInequalities/KLS/Statement.lean) |
| Local task atlas and snapshot-bound verification | [research/verification.md](research/verification.md) |

The linear-test/covariance lower bound ([#2](https://github.com/numina-functional-inequalities/kls-lean/issues/2))
and binary tensorization upper bound ([#6](https://github.com/numina-functional-inequalities/kls-lean/issues/6))
are proved. Finite tensorization and optimal-constant equality
([#7](https://github.com/numina-functional-inequalities/kls-lean/issues/7)) have completed human
acceptance and semantic review, with a node certificate and `proved` / `checked_by: lean` status.
The [freeze record](research/decisions/2026-09-03-finite-tensorization-freeze.md) preserves the
approved statements, and the [acceptance record](research/explorations/2026-09-03-finite-tensorization-acceptance.md)
records the review and validation. The publication commit and its matching CI result are tracked
in Issue #7.

The sharp one-dimensional Gaussian Poincaré constant has also completed proof and human
semantic review. Its 20 library declarations are proof-complete, and
`Solutions.LemPoincareGaussianOneDimensional.certificate` certifies the two main conclusions;
the node is `proved` / `checked_by: lean`. Start with the
[Gaussian reading guide](formalization/FunctionalInequalities/Poincare/Gaussian/README.md)
for the mathematical meaning, proof architecture, examples and file map. The earlier
[candidate statements](research/decisions/2026-09-04-gaussian-poincare-candidate.md) remain an
append-only record of the review stage rather than the current status. Finite tensorization
supplies infrastructure for the independent-product subclass; it is not a complete product-case
proof for arbitrary one-dimensional log-concave factors. The accepted Gaussian theorem covers
Gaussian factors only and is another certified node toward the broader program.

The [Gaussian freeze](research/decisions/2026-09-04-gaussian-poincare-freeze.md) records the
approved contract and the two permitted tail-API generalizations. The
[Gaussian acceptance record](research/explorations/2026-09-04-gaussian-poincare-acceptance.md)
records the final module split, certificate, axiom audit and local validation gates.

The reusable foundation now also provides intrinsic real `L²` variance, extended energies,
sequential relaxation and recovery, quadratic closure, and affine-support coordinates. The
compactly supported `C∞` gradient realization is dense, and both its direct relaxation and its
intrinsic-affine pullback are proved densely defined closed quadratic energies. Here ordinary
`C∞` is correctly encoded by Mathlib's `ContDiff ℝ ∞`; `ContDiff ℝ ⊤` is analytic and is not an
assumption. The Markov/Dirichlet property of both relaxations is now a proved theorem; agreement
with every raw gradient test and identification with Cheeger energy `2 Ch` remain explicit later
theorems rather than hidden premises; raw/core agreement is now proved for every law with a local
density (`Energy/SmoothGradient/Core.lean`), while the Dirac and normal-direction obstructions show
why it cannot hold unconditionally for the ambient pre-energy. The sharp one-dimensional bound `C_P^lit(ν) ≤ 4 Var_ν` for
every log-concave law on the real line, zero variance included, is now a local Lean theorem (Bobkov's
`12 Var` is a corollary) rather than an imported published input. The conditional-fiber form of the frame route is a proved
Dirichlet energy on `L²(μ)` for every Borel law and every direction law
(`KLS/ConditionalFiber/Closed.lean`), through its symmetric two-point jump representation, and its
comparison with the gradient energy under a fiber Poincaré input `κ`
(`D_{μ,ρ}(f) ≤ κ ∫‖∇f‖² dμ`, hence a form-gap bound `C` gives `C_P^lit(μ) ≤ κ C`) is proved in
`KLS/ConditionalFiber/EnergyComparison.lean`.

The 12 comparison theorems are now proved, with two additional ledger certificates and guarded
transitive axiom checks. They identify arbitrary pre-energy optima with their relaxations and
connect the finite-dimensional legacy, ambient and selected intrinsic frontends. They are exported
by `Poincare.Foundation`; the Gaussian bound and exact constant now transfer through the proved
bridge. See the [comparison guide](formalization/FunctionalInequalities/Poincare/Euclidean/README.md)
for sources, generality and examples. The locally Lipschitz literature comparison has an analytic
argument in Blueprint Appendix A. Its weighted approximation input and all eight constant-comparison
interfaces are Lean-certified under explicit intrinsic absolute continuity. The general
log-concave extension now derives that premise and proves the same constant equality for every
finite-dimensional log-concave probability law, including singular and zero-dimensional support.
See the [general proof record](research/decisions/2026-09-06-general-logconcave-comparison.md).
KLS remains open.

The [Lean Blueprint](formalization/blueprint/README.md) is the navigable mathematical map for
this program. It displays the certified canonical spine, records the remaining bridges and their
mathematical and formalization status, and presents four sufficient KLS route alternatives. The
Blueprint does not replace Lean or the ledger as the source of certification status: a rendered
PDF or web page is documentation, while `\leanok` is reserved for statements and proofs backed by
checked local declarations and, for ledger-backed certificate nodes, matching ledger records.

## Verify

For a quick structural/task check, run `python3 research/atlas.py check`.
For the complete local acceptance workflow, including the statement/definition golden comparison,
all certificate axiom reports and local module kernel replay, run `python3 research/verify.py`. Then run
`python3 research/atlas.py export` and `python3 research/atlas.py ready` to inspect tasks against
the verified source snapshot. See the [workflow guide](research/verification.md).
The KLS statement remains a proposition declaration. The general log-concave constant-comparison
pilot is proved; it supplies no dimension-free bound.

From the repository root:

```bash
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
(cd formalization && lake build)
```

To validate declaration links and build both rendered Blueprint formats, follow the exact local
commands in the [formalization guide](formalization/README.md#lean-blueprint). CI publishes the
PDF and web tree as workflow artifacts; it deliberately does not deploy GitHub Pages.

The `Solutions` default target builds all twenty-four proved certificates and the twenty-five named
definition checks of `StatementChecks.lean`, including the zero-dimensional and Euclidean checks for
the implemented affine covariance Poincaré constant `def:affine-poincare-constant` (a definition
node, not a ledger theorem). The certificates include all four weighted
approximation contracts; see their [acceptance record](research/decisions/2026-09-06-weighted-approximation-acceptance.md).
The eighth certificate packages the eight proved smooth/literature comparison interfaces;
two further certificates cover intrinsic absolute continuity and the general log-concave equality.
The [smooth comparison proof record](research/decisions/2026-09-06-smooth-literature-proofs.md) records
the hypotheses, proof route and local evidence. All eight components have axiom guards.
The reusable-library root
also exports the accepted Gaussian implementation, organized as density calculus, Hardy/Tonelli
estimates, and the final sharp real-line theorem. Default-build audits pin the Gaussian certificate
and 27 foundation and comparison declarations to the transitive axioms `propext`, `Classical.choice`, and
`Quot.sound`. The `Examples` target compiles the foundation's usage and boundary examples.
All proved certificates and their local imports are free of proof escapes.
See the [ledger contract](research/ledger-schema.md).
