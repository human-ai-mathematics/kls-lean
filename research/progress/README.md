# KLS progress

| View | Purpose |
| --- | --- |
| [Route diagrams](#proof-progress-tree) | Compact overview, route details, and current analytic work |
| [Progress table](STATUS.md) | Local node IDs, mathematical provenance, recorded Lean status, certificates, dependencies, and gaps |

These views describe our formalization work. Upstream mathematical proofs and conditional
arguments remain separate from local Lean proofs. A completed auxiliary result is not necessarily
a separately registered certificate. KLS remains open.

## Proof progress tree

Last updated: **2026-09-15**. **✓** Completed in Lean · **◐** Partially formalized · **○** Pending.
The orange outline marks the next proof step. Upstream mathematical proofs alone do not earn a ✓.

### Overview

Each route below still has open obligations. The label names its central gap; the detailed graphs
list the other required inputs. **Any one completed route suffices for KLS.** Click a route to jump
to its details.

```mermaid
flowchart LR
    OV_E["○ Eldan localization<br/>Gap: Carleson estimate"]
    OV_S["○ Spectral route<br/>Gap: occupation bound"]
    OV_M["○ CMH route<br/>Gap: recovery envelope"]
    OV_F["◐ Conditional fibers<br/>Gap: universal frame"]
    ANY{"OR<br/>Any completed route"}
    KLS["○ KLS<br/>Dimension-free bound"]

    OV_E --> ANY
    OV_S --> ANY
    OV_M --> ANY
    OV_F --> ANY
    ANY --> KLS

    classDef partial fill:#fff3df,stroke:#c88719,color:#66420d;
    class OV_F partial;
    classDef todo fill:#f2f2f2,stroke:#888,color:#333;
    class OV_E,OV_S,OV_M,KLS todo;
    classDef logic fill:#ffffff,stroke:#555,color:#222;
    class ANY logic;
    click OV_E href "https://github.com/numina-functional-inequalities/kls-lean/tree/main/research/progress#eldan-localization" "○ Eldan localization — Gap: Carleson estimate" _blank
    click OV_S href "https://github.com/numina-functional-inequalities/kls-lean/tree/main/research/progress#moment-map-spectral" "○ Spectral route — Gap: occupation bound" _blank
    click OV_M href "https://github.com/numina-functional-inequalities/kls-lean/tree/main/research/progress#moment-map-cmh" "○ CMH route — Gap: recovery envelope" _blank
    click OV_F href "https://github.com/numina-functional-inequalities/kls-lean/tree/main/research/progress#conditional-fiber-frames" "◐ Conditional fibers — Gap: universal frame" _blank
    click ANY href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml" "OR — Any completed route" _blank
    click KLS href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Statement.lean" "○ KLS — Dimension-free bound" _blank
```

### Eldan localization

All three inputs are needed. Tight-window consumption has an upstream reviewed argument,
but no local Lean proof. The Cheeger–Buser bridge is expanded under [analytic progress](#analytic-progress).

```mermaid
flowchart LR
    EG["○ Tight-prefix<br/>Carleson estimate"]
    EC["○ Tight-window<br/>Consumption"]
    CB["○ Cheeger–Buser<br/>Comparison"]
    EAND{"AND<br/>○ Eldan route"}

    EG --> EAND
    EC --> EAND
    CB --> EAND

    classDef todo fill:#f2f2f2,stroke:#888,color:#333;
    class EG,EC,CB,EAND todo;
    click EG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Tight-prefix — Carleson estimate" _blank
    click EC href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Tight-window — Consumption" _blank
    click CB href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex" "○ Cheeger–Buser — Comparison" _blank
    click EAND href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml" "AND — ○ Eldan route" _blank
```

### Moment-map spectral

The occupation estimate is open. Spectral sufficiency is an upstream implication from that
estimate, still awaiting Lean formalization. The affine/isotropic reduction is already proved.

```mermaid
flowchart LR
    SG["○ Full-damping<br/>Occupation bound"]
    SC["○ Spectral<br/>Sufficiency"]
    NORM["✓ Affine / isotropic<br/>Reduction"]
    SAND{"AND<br/>○ Spectral route"}

    SG --> SAND
    SC --> SAND
    NORM --> SAND

    classDef done fill:#e8f5e9,stroke:#388e3c,color:#183b1c;
    class NORM done;
    classDef todo fill:#f2f2f2,stroke:#888,color:#333;
    class SG,SC,SAND todo;
    click SG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Full-damping — Occupation bound" _blank
    click SC href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Spectral — Sufficiency" _blank
    click NORM href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean" "✓ Affine / isotropic — Reduction" _blank
    click SAND href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml" "AND — ○ Spectral route" _blank
```

### Moment-map CMH

The recovery envelope is open. The W₂/CMH comparison and recovery-sequence implication have
upstream mathematical arguments, not local Lean proofs. The source requires a regular recovery
sequence. This route is sufficient for KLS, not an equivalent reformulation.

```mermaid
flowchart LR
    MH["○ W₂ limit and<br/>CMH comparison"]
    MG["○ Bounded CMH<br/>Recovery envelope"]
    MT["✓ Affine constant<br/>Translation invariance"]
    MC["○ Recovery-sequence<br/>Sufficiency"]
    NORM["✓ Affine / isotropic<br/>Reduction"]
    MAND{"AND<br/>○ CMH route"}

    MH --> MAND
    MG --> MAND
    MT --> MAND
    MC --> MAND
    NORM --> MAND

    classDef done fill:#e8f5e9,stroke:#388e3c,color:#183b1c;
    class MT,NORM done;
    classDef todo fill:#f2f2f2,stroke:#888,color:#333;
    class MH,MG,MC,MAND todo;
    click MH href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ W₂ limit and — CMH comparison" _blank
    click MG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Bounded CMH — Recovery envelope" _blank
    click MT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Poincare/CovarianceGradient/Translation.lean" "✓ Affine constant — Translation invariance" _blank
    click MC href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Recovery-sequence — Sufficiency" _blank
    click NORM href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean" "✓ Affine / isotropic — Reduction" _blank
    click MAND href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml" "AND — ○ CMH route" _blank
```

### Conditional-fiber frames

The fiber form and comparisons are proved. What remains is a universal frame, chosen independently
of the test function, controlling variance by fiber energy. The form-bound constant would then give
the isotropic `4C` Poincaré bound; the reduction handles general affine support and zero dimension.

```mermaid
flowchart LR
    ONE["✓ One-dimensional<br/>Poincaré ≤ 4 Var"]
    FLOG["✓ Fiber log-concavity"]
    FP["✓ Fiber-bound<br/>Energy comparison"]
    F4["✓ Fiber energy<br/>≤ 4 × gradient energy"]
    FC["✓ Fiber Dirichlet form"]
    FG["○ Universal<br/>Frame bound"]
    NORM["✓ Affine / isotropic<br/>Reduction"]
    FAND{"AND<br/>◐ Fiber route"}

    ONE --> F4
    FLOG --> F4
    FP --> F4
    FC --> FAND
    F4 --> FAND
    FG --> FAND
    NORM --> FAND

    classDef done fill:#e8f5e9,stroke:#388e3c,color:#183b1c;
    class ONE,FLOG,FP,F4,FC,NORM done;
    classDef partial fill:#fff3df,stroke:#c88719,color:#66420d;
    class FAND partial;
    classDef todo fill:#f2f2f2,stroke:#888,color:#333;
    class FG todo;
    click ONE href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean" "✓ One-dimensional — Poincaré ≤ 4 Var" _blank
    click FLOG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean" "✓ Fiber log-concavity" _blank
    click FP href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean" "✓ Fiber-bound — Energy comparison" _blank
    click F4 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean" "✓ Fiber energy — ≤ 4 × gradient energy" _blank
    click FC href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber/Closed.lean" "✓ Fiber Dirichlet form" _blank
    click FG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex" "○ Universal — Frame bound" _blank
    click NORM href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean" "✓ Affine / isotropic — Reduction" _blank
    click FAND href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml" "AND — ◐ Fiber route" _blank
```

### Shared foundations

The density, normalization, energy, and frontend results support the routes. Dotted arrows show
context, not a standalone implication to KLS. The energy identity uses the local-slope convention
for log-concave laws; it is distinct from comparison of isoperimetric constants.

```mermaid
flowchart LR
    DENS["✓ Log-concave density<br/>Intrinsic support"]
    NORM["✓ Affine / isotropic<br/>Reduction"]
    FORMS["✓ Closed forms<br/>Dirichlet property"]
    ENERGY["✓ Canonical energy<br/>= 2 × Cheeger energy"]
    CONST["✓ Poincaré frontend<br/>Equivalence"]

    DENS --> NORM
    FORMS -.-> ENERGY

    classDef done fill:#e8f5e9,stroke:#388e3c,color:#183b1c;
    class DENS,NORM,FORMS,ENERGY,CONST done;
    click DENS href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/BorellRepresentation.lean" "✓ Log-concave density — Intrinsic support" _blank
    click NORM href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean" "✓ Affine / isotropic — Reduction" _blank
    click FORMS href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean" "✓ Closed forms — Dirichlet property" _blank
    click ENERGY href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/Cheeger.lean" "✓ Canonical energy — = 2 × Cheeger energy" _blank
    click CONST href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Poincare.lean" "✓ Poincaré frontend — Equivalence" _blank
```

### Analytic progress

#### Coarea: the next proof step

General C¹ coarea combines the regular region with critical-slice nullity. The later Lipschitz
extension additionally needs Whitney extension and exact C¹ pieces; it is not a prerequisite for
the smooth C¹ application below.

```mermaid
flowchart LR
    MEAS["✓ Slice measurability"]
    GRAPH["✓ Open-domain<br/>Graph area"]
    REG["✓ Regular-domain<br/>Coarea"]
    CRIT["✓ Critical-slice nullity"]
    C1["○ General C¹ coarea<br/>Next step"]
    WHIT["○ Whitney extension<br/>Exact C¹ pieces"]
    LIP["○ Lipschitz coarea"]

    GRAPH --> REG
    MEAS -.-> REG
    REG --> C1
    CRIT --> C1
    C1 --> LIP
    WHIT --> LIP
    MEAS --> LIP

    classDef done fill:#e8f5e9,stroke:#388e3c,color:#183b1c;
    class MEAS,GRAPH,REG,CRIT done;
    classDef todo fill:#f2f2f2,stroke:#888,color:#333;
    class WHIT,LIP todo;
    classDef focus fill:#fff0dc,stroke:#d47b13,color:#663800,stroke-width:3px;
    class C1 focus;
    click MEAS href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/LevelSetMeasurable.lean" "✓ Slice measurability" _blank
    click GRAPH href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/OpenGraphIntegral.lean" "✓ Open-domain — Graph area" _blank
    click REG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/RegularCoarea.lean" "✓ Regular-domain — Coarea" _blank
    click CRIT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CriticalSlice.lean" "✓ Critical-slice nullity" _blank
    click C1 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l11" "○ General C¹ coarea — Next step" _blank
    click WHIT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l6" "○ Whitney extension — Exact C¹ pieces" _blank
    click LIP href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l12" "○ Lipschitz coarea" _blank
```

#### Isoperimetric comparison

`h_M` is the Minkowski Cheeger constant; `h_S` is the smooth-boundary constant. The forward
comparison is proved. The reverse comparison needs smooth coarea and cutoff arguments.
Smooth Sard means C∞ Sard here; sharp finite-regularity Sard remains a separate open obligation.

```mermaid
flowchart TB
    GG["✓ Global Gauss–Green"]
    REC["✓ Smooth recovery"]
    FWD["✓ h_M ≤ h_S"]
    C1["○ General C¹ coarea<br/>Next step"]
    SARD["✓ Smooth Sard"]
    SCI["○ Smooth coarea<br/>Inequality"]
    CUT["✓ Distance cutoffs"]
    REV["○ h_S ≤ h_M"]
    EQ["◐ h_M = h_S"]
    FRONT["○ Density Cheeger<br/>Identification"]
    CB["○ Cheeger–Buser<br/>Comparison"]

    GG --> REC
    REC --> FWD
    C1 --> SCI
    SARD --> SCI
    SCI --> REV
    CUT --> REV
    FWD --> EQ
    REV --> EQ
    EQ --> FRONT
    FRONT --> CB

    classDef done fill:#e8f5e9,stroke:#388e3c,color:#183b1c;
    class GG,REC,FWD,SARD,CUT done;
    classDef partial fill:#fff3df,stroke:#c88719,color:#66420d;
    class EQ partial;
    classDef todo fill:#f2f2f2,stroke:#888,color:#333;
    class SCI,REV,FRONT,CB todo;
    classDef focus fill:#fff0dc,stroke:#d47b13,color:#663800,stroke-width:3px;
    class C1 focus;
    click GG href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/GaussGreen.lean" "✓ Global Gauss–Green" _blank
    click REC href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean" "✓ Smooth recovery" _blank
    click FWD href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean" "✓ h_M ≤ h_S" _blank
    click C1 href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l11" "○ General C¹ coarea — Next step" _blank
    click SARD href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/SmoothSard.lean" "✓ Smooth Sard" _blank
    click SCI href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean" "○ Smooth coarea — Inequality" _blank
    click CUT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/DistanceCutoff.lean" "✓ Distance cutoffs" _blank
    click REV href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean" "○ h_S ≤ h_M" _blank
    click EQ href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean" "◐ h_M = h_S" _blank
    click FRONT href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex" "○ Density Cheeger — Identification" _blank
    click CB href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex" "○ Cheeger–Buser — Comparison" _blank
```

The resulting Cheeger–Buser bridge feeds the Eldan route; it does not by itself prove KLS.
The following related inequality is already proved and is distinct from the weighted coarea equality:

```mermaid
flowchart LR
    MINK["✓ Minkowski coarea"]


    classDef done fill:#e8f5e9,stroke:#388e3c,color:#183b1c;
    class MINK done;
    click MINK href "https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean" "✓ Minkowski coarea" _blank
```

### Benchmarks and upstream research beyond the four route gates

These results calibrate or investigate the program. They do not provide additional completed
routes to KLS, and no solid implication arrow from a model calculation to a universal gate is intended.

| Result or research direction | Recorded status and boundary | Source |
| --- | --- | --- |
| Sharp one-dimensional Gaussian constant | ✓ Lean-proved; Gaussian laws only | [Lean source](../../formalization/FunctionalInequalities/Poincare/Gaussian/Real.lean) |
| Finite Poincaré tensorization | ✓ Lean-proved; independent-product infrastructure | [Lean source](../../formalization/FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean) |
| Spectral restart and fourth-moment estimates | Upstream reviewed; not Lean; do not close uniform-time occupation | [Synchronization record](../../research/decisions/2026-09-12-upstream-research-sync.md) |
| Letwin-dependent short-time spectral chain | Conditional upstream result; not Lean; not dimension-free KLS | [Synchronization record](../../research/decisions/2026-09-12-upstream-research-sync.md) |
| Screened localization on a regular split class | Restricted upstream result; the universal gate remains open | [Synchronization record](../../research/decisions/2026-09-12-upstream-research-sync.md) |
| CMH linear spectral resolution and third-moment decomposition | Upstream reviewed weak/closed-form statements; no universal higher-order remainder bound | [Synchronization record](../../research/decisions/2026-09-12-upstream-research-sync.md) |
| Sharp gate-zero matrix bound | Upstream conjecture; not proved or Lean-certified | [Synchronization record](../../research/decisions/2026-09-12-upstream-research-sync.md) |
| Exponential-cone and cube-cone models | Exact restricted models; not a universal CMH or recovery-envelope bound | [Synchronization record](../../research/decisions/2026-09-12-upstream-research-sync.md) |
| Simplex root-frame degree-two result | Upstream reviewed polynomial-sector result; not a full L² frame bound | [Synchronization record](../../research/decisions/2026-09-12-upstream-research-sync.md) |
| Historical weighted near-Cheeger package | REFUTED upstream by the exponential-spectator obstruction; excluded from the four active routes | [Historical branch](../../formalization/blueprint/src/chapters/50-kls-routes.tex) |

### Reading the diagrams

Solid arrows point from inputs toward consumers; all inputs to an AND diamond are required.
The overview joins the four alternatives with OR. Arrows through pending nodes describe the
planned proof route, not an already established implication. Only selected dependencies are shown.
The [route composition](../../formalization/blueprint/route-composition.yaml) and Blueprint give
precise statements. The upstream roadmap remains pinned to
`34b5fcd57fef17089e781616005fe6d3641bd11e`; this is a route-level overview, not every upstream lemma.

Every node has a link. If diagram links are disabled in your viewer, use this directory.

<details>
<summary>Node links: Lean sources and documentation</summary>

| Node | Source |
| --- | --- |
| ○ KLS — Dimension-free bound | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Statement.lean) |
| OR — Any completed route | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| ✓ Log-concave density — Intrinsic support | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/BorellRepresentation.lean) |
| ✓ Affine / isotropic — Reduction | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean) |
| ✓ Closed forms — Dirichlet property | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean) |
| ✓ Canonical energy — = 2 × Cheeger energy | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/Cheeger.lean) |
| ✓ Poincaré frontend — Equivalence | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Poincare.lean) |
| ○ Cheeger–Buser — Comparison | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex) |
| ○ Tight-prefix — Carleson estimate | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ○ Tight-window — Consumption | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| AND — ○ Eldan route | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| ○ Full-damping — Occupation bound | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ○ Spectral — Sufficiency | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| AND — ○ Spectral route | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| ○ W₂ limit and — CMH comparison | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ○ Bounded CMH — Recovery envelope | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| ✓ Affine constant — Translation invariance | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Poincare/CovarianceGradient/Translation.lean) |
| ○ Recovery-sequence — Sufficiency | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| AND — ○ CMH route | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| ✓ Fiber Dirichlet form | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber/Closed.lean) |
| ✓ One-dimensional — Poincaré ≤ 4 Var | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean) |
| ✓ Fiber log-concavity | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| ✓ Fiber-bound — Energy comparison | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean) |
| ✓ Fiber energy — ≤ 4 × gradient energy | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| ○ Universal — Frame bound | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| AND — ◐ Fiber route | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| ✓ Global Gauss–Green | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/GaussGreen.lean) |
| ✓ Smooth recovery | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean) |
| ✓ h_M ≤ h_S | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean) |
| ✓ Minkowski coarea | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean) |
| ✓ Smooth Sard | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/SmoothSard.lean) |
| ✓ Slice measurability | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/LevelSetMeasurable.lean) |
| ✓ Open-domain — Graph area | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/OpenGraphIntegral.lean) |
| ✓ Regular-domain — Coarea | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/RegularCoarea.lean) |
| ✓ Critical-slice nullity | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CriticalSlice.lean) |
| ○ General C¹ coarea — Next step | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l11) |
| ○ Whitney extension — Exact C¹ pieces | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l6) |
| ○ Lipschitz coarea | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l12) |
| ○ Smooth coarea — Inequality | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| ✓ Distance cutoffs | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/DistanceCutoff.lean) |
| ○ h_S ≤ h_M | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| ◐ h_M = h_S | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| ○ Density Cheeger — Identification | [Open source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex) |
| ○ Eldan localization — Gap: Carleson estimate | [Open source](https://github.com/numina-functional-inequalities/kls-lean/tree/main/research/progress#eldan-localization) |
| ○ Spectral route — Gap: occupation bound | [Open source](https://github.com/numina-functional-inequalities/kls-lean/tree/main/research/progress#moment-map-spectral) |
| ○ CMH route — Gap: recovery envelope | [Open source](https://github.com/numina-functional-inequalities/kls-lean/tree/main/research/progress#moment-map-cmh) |
| ◐ Conditional fibers — Gap: universal frame | [Open source](https://github.com/numina-functional-inequalities/kls-lean/tree/main/research/progress#conditional-fiber-frames) |

</details>

## Where the records come from

- [Blueprint](../../formalization/blueprint/src/chapters/) supplies local node statements,
  dependencies, and Lean annotations.
- [Ledger](../a-series/ledger.yaml) supplies registered certificate records.
- [Task metadata](../tasks.json) supplies mathematical classifications and infrastructure gaps.
- [Route composition](../../formalization/blueprint/route-composition.yaml) supplies explicit
  upstream provenance and the four sufficient-route alternatives.
- [Selected upstream snapshot](../upstream/2026-09-12-kls-research.json) preserves additional
  pinned research records. It is a selection, not the complete upstream ledger.

The table is a derived documentation view, not a new source of proof status. It does not execute
Lean or attest to the latest remote CI result. Follow the [verification guide](../verification.md)
for those checks. The diagrams remain a reviewed summary; their auxiliary nodes need not have
individual Blueprint IDs.

## Updating after proof work

1. Update the relevant source, ledger/Blueprint annotations, and task metadata with the appropriate
   proof evidence. Review [the overview and detail diagrams](#proof-progress-tree), their links, and the next-step highlight.
2. Stage only the intended proof and metadata changes, then run from the repository root:

   ```sh
   python3 research/progress/update.py
   ```

   The generator reads canonical records from the Git index, so unrelated unstaged changes do not
   silently enter the published table. It reads `README.md` from the working tree for the diagram
   node directory. Input hashes in the table identify the records used.
3. Review and stage `STATUS.md`, `README.md`, and the adjacent root README status summary as needed.
   Use `python3 research/progress/update.py --check` to check that the table is current.

Commits containing only non-Lean files do not trigger CI, as requested by the owner. Both
GitHub workflows automatically run only when `**/*.lean` changes. Keep `[skip ci]` on this initial
non-Lean publication as well. Commits containing Lean changes follow the normal verification and
CI workflow; do not add `[skip ci]` to those commits. Blueprint retains its existing manual trigger.
