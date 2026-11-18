# Tau Ceti dependency review

The Lean v4.35.0 package adds Tau Ceti at
[4705013d](https://github.com/lyw-ops/TauCeti/tree/4705013d2da8bac010289af92000f4a5b8ffca00).
Mathlib stays at `56a005855ea17e0b0958f73ec801ae140b0a1679` and the other package
revisions stay fixed. The new Lake manifest digest is
`c61532e8a9bed38f35c7f255cf1f1f5330b324e01bf895056766dc92d60275c4`.

The four proof substitutions apply to the dyadic Doob estimate, the Laplace
noise law of BKL arXiv:2610.05474v1, Gaussian even moments, and the
Fenchel–Moreau identity used in CEK uniqueness. The Doob estimate keeps its
dyadic endpoint and its squared constant 4. The Laplace bridge uses location
zero and scale `β⁻¹` for rate `β > 0`. The Gaussian bridge uses variance
`σ²`. The Fenchel–Moreau bridge uses the original inner product pairing and
retains the finite-value hypothesis of the KLS interface.

The KLS and independent BKL statement baselines retain their existing roots,
elaborated declarations and external leaves. This dependency review updates
the recorded manifest digest. The KLS statement check and the independent
BKL target checker compare the resulting statement closures against those
baselines.
