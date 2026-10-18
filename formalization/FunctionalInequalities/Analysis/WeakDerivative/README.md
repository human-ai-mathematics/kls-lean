# Weak directional derivatives

These modules retain the existing `FunctionalInequalities.Analysis` declarations and their
actual hypotheses. They support the weak regular-class Letwin chain; they do not by themselves
construct a moment potential, prove Hessian evolution or establish the constant-8 theorem.

| Module | Responsibility |
| --- | --- |
| [Basic](Basic.lean) | Weak directional derivative, uniqueness, classical/a.e. identification and the C1 product |
| [Mollification](Mollification.lean) | Convolution and weak derivatives from difference bounds |
| [Approximation](Approximation.lean) | Cutoff gluing and common-support smooth approximations |
| [Calculus](Calculus.lean) | Rough products, exponential chain rule, compact/bounded tests and weak divergence |

`Calculus` retains the chain rule's and product proof's shared private test helpers. Local L2, global L2 and bounded
hypotheses remain distinct. The generic [smooth ball cutoff](../Cutoff/SmoothBall.lean) and
[Lipschitz ball cutoff](../Cutoff/LipschitzBall.lean) have different profiles and regularity.
