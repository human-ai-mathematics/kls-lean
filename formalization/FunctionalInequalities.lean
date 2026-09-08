import FunctionalInequalities.Poincare.Basic
import FunctionalInequalities.Poincare.Foundation
import FunctionalInequalities.Poincare.LinearTest
import FunctionalInequalities.Poincare.Product.Tensorization
import FunctionalInequalities.Poincare.Product.Reverse
import FunctionalInequalities.Poincare.FiniteProduct.Tensorization
import FunctionalInequalities.Poincare.Gaussian.Real
import FunctionalInequalities.KLS.Statement
import FunctionalInequalities.Poincare.Euclidean.LogConcaveComparison
import FunctionalInequalities.KLS.LogConcave.Borel
import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.KLS.Isoperimetry
import FunctionalInequalities.KLS.ConditionalFiber
import FunctionalInequalities.Poincare.Euclidean.RawEnergyObstruction
import FunctionalInequalities.KLS.LogConcave.BorellRepresentation
import FunctionalInequalities.Probability.IntrinsicCovariance
import FunctionalInequalities.KLS.LogConcave.AffineCovariance
import FunctionalInequalities.KLS.LogConcave.CovarianceClosure
import FunctionalInequalities.KLS.LogConcave.AffineClosedForm
import FunctionalInequalities.KLS.LogConcave.AffineTranslation
import FunctionalInequalities.KLS.LogConcave.IsotropicReduction

/-!
# Functional inequalities

Root module for functional-inequality definitions, proved results, and explicit draft statements.
The proved results include linear-test lower bounds, binary tensorization,
finite Hilbert-product optimal-constant equality, and the sharp one-dimensional Gaussian
Poincaré constant. It also exports the layered `L²`/extended-energy foundation for future
developments. Node certificates are compiled separately from `solutions/`.

The compact/Borel log-concavity equivalence, the six conditional-fiber contracts, the Borell
density-representative, local-bound and moment conclusions of
`KLS/LogConcave/BorellRepresentation.lean`, and the ambient/intrinsic covariance comparison are
proved. `Poincare.Affine.constant` implements the affine covariance Poincaré constant as a
definition, with its log-concave well-definedness contracts in
`KLS/LogConcave/AffineCovariance.lean`. `KLS/LogConcave/CovarianceClosure.lean` proves that the
weighted gradient operator of a full-dimensional log-concave law is densely defined and closable,
with smooth core and relaxation identified with its closure (`lem:covariance-core-closure`), and
`KLS/LogConcave/AffineClosedForm.lean` identifies the affine relaxation with the closed covariance
form of the CMH source (`thm:affine-covariance-relaxation-closed`), and
`KLS/LogConcave/AffineTranslation.lean` with `Poincare/Euclidean/AffineTranslation.lean` prove that
ambient translation keeps log-concavity and the affine constant
(`lem:affine-poincare-translation-invariance`), and `KLS/LogConcave/IsotropicReduction.lean` proves
the equivalence of the isotropic, covariance-normalized and affine KLS formulations for each fixed
`K` (`thm:affine-isotropic-reduction`); no statement that any of them holds for some `K`, and no
KLS proof, is included. Importing this aggregate certifies nothing by itself.

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

The proved comparison modules identify the ambient and intrinsic relaxations and the
finite-dimensional legacy optimum, so the accepted Gaussian bounds and constants can be
transported to the selected frontend through explicit equalities and fixed-constant equivalences.
-/
