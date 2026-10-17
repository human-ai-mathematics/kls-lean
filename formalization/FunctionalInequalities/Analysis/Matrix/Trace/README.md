# Matrix trace tools

| Module | Actual role |
| --- | --- |
| [Algebra](Algebra.lean) | Finite real trace expansions, contractions, conjugations and elementary trace-energy bound |
| [Power](Power.lean) | Real spectral powers and the Lee--Vempala/Eldan trace inequality |
| [Energy](Energy.lean) | Spectral positivity, Jordan trace domination and the pointwise Letwin tensor comparison |

Statements retain their individual finite-index, natural-dimension, symmetry, positivity and
exponent hypotheses. Elementary identities have no added symmetry premise. The tensor proof
keeps its shared private supports with the spectral-energy arguments. The existing
[TraceGram](../TraceGram.lean) owns the separate analytic/Gram integration boundary.

Qualified declaration names are unchanged. See the
[placement decision](../../../../../research/decisions/2026-10-18-trace-proximal-layout.md) and
[complete map](../../../../../research/api-migration/2026-10-18-trace-proximal-map.json).
