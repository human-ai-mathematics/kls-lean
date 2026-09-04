import FunctionalInequalities.Poincare.Basic
import FunctionalInequalities.Poincare.Foundation
import FunctionalInequalities.Poincare.LinearTest
import FunctionalInequalities.Poincare.Product.Tensorization
import FunctionalInequalities.Poincare.Product.Reverse
import FunctionalInequalities.Poincare.FiniteProduct.Tensorization
import FunctionalInequalities.Poincare.Gaussian.Real

/-!
# Functional inequalities

Root module for the proved Poincaré definitions, linear-test lower bounds, binary tensorization,
finite Hilbert-product optimal-constant equality, and the sharp one-dimensional Gaussian
Poincaré constant. It also exports the layered `L²`/extended-energy foundation for future
developments. Node certificates are compiled separately from `solutions/`.

The imported modules record their sources beside the declarations: manuscript Definition 2.1
for the normalization, Remark 3.8 for the linear-test lower bound, BGL (2014), Proposition 4.3.1
for the binary fixed-constant upper bound, manuscript Theorem 3.4 for the finite-product identity,
and the manuscript Gaussian covariance family for the one-dimensional sharp constant. Their
comments also identify the local test-domain specifications, extended-real conventions, and
auxiliary results. `Poincare.Foundation` deliberately coexists with the accepted smooth-test API;
both now use ordinary `C∞` regularity. The foundation additionally exports sequential
lower-semicontinuity and recovery theorems, quadratic closure of dense pre-energies, the closed
smooth-gradient relaxation, and intrinsic affine-support coordinates. No Cheeger-energy,
Dirichlet, raw-test core, or spectral-gap identification is asserted by this aggregate.
-/
