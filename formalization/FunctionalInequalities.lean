import FunctionalInequalities.Poincare.Basic
import FunctionalInequalities.Poincare.Foundation
import FunctionalInequalities.Poincare.LinearTest
import FunctionalInequalities.Poincare.Product.Tensorization
import FunctionalInequalities.Poincare.Product.Reverse
import FunctionalInequalities.Poincare.FiniteProduct.Tensorization

/-!
# Functional inequalities

Root module for the proved Poincaré definitions, linear-test lower bounds, binary tensorization,
and finite Hilbert-product optimal-constant equality. Node certificates are compiled separately
from `solutions/`.

The imported modules record their sources beside the declarations: manuscript Definition 2.1
for the normalization, Remark 3.8 for the linear-test lower bound, and BGL (2014), Proposition
4.3.1 for the binary fixed-constant upper bound, and manuscript Theorem 3.4 for the finite product
identity. Their comments also identify the local test-domain specifications, extended-real
conventions, and auxiliary results.
-/
