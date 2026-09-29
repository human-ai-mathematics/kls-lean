<!-- Source: audit document supplied by a collaborator and given to this repository by lyuyuwei on 2026-09-11 as the source for reconstructing the one-dimensional Poincaré coefficient-4 proof; original file ~/Downloads/poincare_constant_4_audit.md. The original content was retained; this version translates its prose into English. For the Lean formalization, see research/decisions/2026-09-11-one-dimensional-logconcave-poincare-four.md. -->

# Coefficient 4 in the log-concave Poincaré inequality: literature audit and full mathematical reconstruction

## Conclusions and evidence levels

The literature search should be classified as follows: a reliable explicit statement and a usable original localization theorem were found, but no original source containing a complete, step-by-step Poincaré proof with the exact coefficient 4 has yet been located. This does not justify calling the result a misquotation or an error.

Mathematical verification can proceed further: below is a complete independent derivation in the general one-dimensional case, followed by a reconstruction of the higher-dimensional bound using the four-integral localization form of Kannan–Lovász–Simonovits (1995), Theorem 2.7:

\[
C_P(\mu)\le4\inf_a\mathbb E|X-a|^2=4\operatorname{tr}(\operatorname{Cov}\mu).
\]

Here, “reconstruction” does not mean that the calculations below appear verbatim in the original KLS paper. Historical attribution and mathematical proof must be recorded separately. This report contains no Lean code and makes no claim of machine verification.

## 1. Literature and scope of the audit

| Source/version | Location | Precise content | Proof and access status |
|---|---|---|---|
| KLS, DCG 13 (1995), 541–559 | p.542, (1.1)–(1.2) | Product-normalized isoperimetric constant; comparison with min normalization | Original PDF page images checked |
| Same source | pp.547–550, Lemma 2.6, Theorem 2.7 | Product inequality for integrals of four nonnegative continuous functions, reducible to exponential needles | Original proof present; key page images checked |
| Same source | pp.554–556, Theorems 5.1–5.2 | \(\psi(K)\ge\log2/M_1(K)\) | Original proof present; not a ready-made coefficient-4 Poincaré derivation |
| Same source | p.557, Theorem 5.3 | \(\psi(K)\ge1/\chi(K)\) | Original proof present; related subsequent Theorem 5.4/Lemma 5.5 on p.558 also checked |
| Cattiaux–Guillin, arXiv v1, 2018 | p.11, (2.25) | \(C_P\le4\mathbb E|X-\mathbb EX|^2\) | Explicit statement; refers to p.11 of the monograph without proving this constant there |
| Cattiaux–Guillin, revision dated 2019-05-19 | p.12, (2.13) | Same higher-dimensional coefficient 4 | Page images checked; the final sentence of Remark 2.13 concerns the spherically symmetric application |
| Alonso-Gutiérrez–Bastero, LNM 2131 (2015) | p.11; pp.18–21, Theorem 1.5 | The former states 4; the latter gives a one-dimensional proof with 12 | No readable full-text PDF obtained in this round; specific page information follows the supplied audit and is not claimed as an independent rereading. The citation location on p.11 is confirmed by the CG original |
| Same authors, Convex inequalities, isoperimetry and spectral gap, 2014 course manuscript, published 2017 | Manuscript pp.14–15, Theorem 4.1 | \(C_P\le C\mathbb E|X-\mathbb EX|^2\), with C unspecified | Text readable, page images failed to load; not a proof of exact 4 |

Original links and full bibliographic details appear at the end. No verifiable erratum or alternative version explicitly supplying the complete proof of the exact coefficient 4 at the cited location was found.

## 2. Constant conventions

Let
\[
C_P=\inf\{C\ge0:\operatorname{Var}_\mu f\le C\int|\nabla f|^2d\mu\},\qquad\lambda_1=C_P^{-1}.
\]
The spectral gap follows the convention above, without taking a square root.

The min and product normalizations of the Cheeger constant are, respectively,
\[
h=\inf_A\frac{\mu^+(A)}{\min(\mu A,1-\mu A)},\qquad
\psi=\inf_A\frac{\mu^+(A)}{\mu A(1-\mu A)}.
\]
Since \(pq\le\min(p,q)\le2pq\), we have \(h\le\psi\le2h\). If \(1/h\) is called the Cheeger constant, the usual Cheeger–Poincaré bound reads \(C_P\le4(1/h)^2\).

Thus KLS Theorem 5.1 and the comparison above alone indeed give only
\[
C_P\le\frac{16}{\psi^2}\le\frac{16M_1^2}{(\log2)^2}\le\frac{16}{(\log2)^2}\mathbb E|X-\mathbb EX|^2.
\]
The argument below does not use this route, which loses constants. The two substantive improvements are four-integral localization with a second-moment weight, and the direct implication from product normalization to \(C_P\le4/\psi^2\).

## 3. One-dimensional structure and quantile density

A non-Dirac one-dimensional log-concave probability measure has a density \(\rho=e^v\), strictly positive on its open support interval \(I=(l,r)\), where \(v\) is a finite concave function. Endpoints may be finite or infinite. This is the structural theorem used to pass from the measure definition to the density definition; see the explicit statement of Borell's theorem on p.2 of Huet's manuscript.

A finite concave function is locally Lipschitz on an open interval. If the right endpoint is infinite, integrability of the density guarantees \(x_0<x_1\) with \(v(x_1)<v(x_0)\). Concavity then gives
\[
v(x)\le v(x_1)+\frac{v(x_1)-v(x_0)}{x_1-x_0}(x-x_1),\quad x\ge x_1.
\]
Hence the right tail decays exponentially; likewise for the left tail. In particular, \(0<\sigma^2:=\operatorname{Var}_\mu X<\infty\).

Let \(F\) be the cumulative distribution function, \(Q=F^{-1}:(0,1)\to I\) the quantile function, and define the quantile density profile by
\[
J(u)=\rho(Q(u)).
\]
Then \(Q'(u)=1/J(u)\), and \(J\) is positive and concave. This remains valid in the nonsmooth case: on any compact subinterval, \(Q\) is locally bi-Lipschitz; the chain rule gives \(J'(u)=v'(Q(u))\) almost everywhere. The right-hand side is nonincreasing, so local absolute continuity implies concavity. No twice-differentiability assumption on \(v\) is needed.

## 4. Variance lower bound for affine quantile models

Fix \(p\in(0,1)\). Let
\[
\ell(u)=A(1-u)+Bu>0\quad(0<u<1),\qquad A,B\ge0,
\]
where \(A,B\) are not both zero, and define
\[
q(u)=\int_p^u\frac{dt}{\ell(t)},\qquad U\sim\operatorname{Unif}(0,1).
\]
Then
\[
\boxed{\operatorname{Var}(q(U))\ge\frac1{(\sqrt A+\sqrt B)^4}.}\tag{4.1}
\]

If \(A=B=c>0\), the variance is \(1/(12c^2)\), and the right-hand side is \(1/(16c^2)\).

If \(A=0<B\), then \(q(u)=(\log u-\log p)/B\). From
\(\int_0^1\log u\,du=-1\) and \(\int_0^1(\log u)^2du=2\), the variance is \(1/B^2\), exactly the right-hand side. The case \(B=0<A\) follows by reflection.

If \(0<A<B\), put \(\beta=B-A\). Integration gives
\[
q(u)=\frac1\beta\log\frac{A+\beta u}{A+\beta p},
\]
and
\[
\operatorname{Var}(q(U))=\frac1{\beta^2}-\frac{AB\log^2(B/A)}{\beta^4}.\tag{4.2}
\]
This follows directly by evaluating
\[
\int\log x\,dx=x(\log x-1),\quad
\int\log^2x\,dx=x(\log^2x-2\log x+2)
\]
on \([A,B]\).

Write \(D=\sqrt B-\sqrt A\), \(S=\sqrt B+\sqrt A\), so \(\beta=DS\). For \(z\ge1\),
\[
\frac d{dz}(z-z^{-1}-2\log z)=\frac{(z-1)^2}{z^2}\ge0,
\]
so taking \(z=(B/A)^{1/4}\) gives
\[
\log(B/A)\le\frac{2D}{(AB)^{1/4}}.
\]
Therefore
\[
AB\log^2(B/A)\le4\sqrt{AB}D^2=D^2(S^2-D^2),
\]
and substituting into (4.2) yields
\[
\operatorname{Var}(q(U))\ge\frac{D^4}{D^4S^4}=S^{-4}.
\]
Use reflection when \(B<A\). This covers all affine models.

## 5. Full profile estimate for general log-concave densities

We prove
\[
\boxed{J(u)\ge\frac{u(1-u)}\sigma\quad(0<u<1).}\tag{5.1}
\]

Fix \(p\). The concave function \(J\) has an affine supporting majorant \(\ell\) at this interior point, satisfying \(\ell\ge J\) and \(\ell(p)=J(p)\). Write it in the preceding section's form. Positivity inside the interval gives \(A,B\ge0\), not both zero.

Since \(Q'=1/J\ge1/\ell=q'\), for \(u>v\),
\[
Q(u)-Q(v)\ge q(u)-q(v)\ge0.
\]
The independent-copy variance identity gives
\[
\sigma^2=\frac12\int_0^1\!\int_0^1[Q(u)-Q(v)]^2\,du\,dv
\ge\operatorname{Var}(q(U))\ge\frac1{(\sqrt A+\sqrt B)^4}.
\]
On the other hand, Cauchy–Schwarz gives
\[
\frac{\ell(p)}{p(1-p)}=\frac A p+\frac B{1-p}\ge(\sqrt A+\sqrt B)^2\ge\frac1\sigma.
\]
Using \(\ell(p)=J(p)\) proves (5.1).

This extension does not assume that a general law can simply be replaced by an exponential law; it follows from the supporting majorant and pointwise comparison of all quantile differences. The anchor \(p\) is arbitrary and need not be the mean or median.

## 6. Sharp weighted Hardy calculation

Write \(w(u)=u(1-u)\). First prove: if \(g\) is bounded with mean zero and \(G(u)=\int_0^u g(v)dv\), then
\[
\boxed{\int_0^1\frac{G(u)^2}{w(u)^2}du\le4\int_0^1g(u)^2du.}\tag{6.1}
\]

Taking \(\eta(u)=\sqrt{w(u)}\), direct differentiation gives
\[
-\frac{\eta''(u)}{\eta(u)}=\frac1{4u^2(1-u)^2}.
\]
Integrating by parts on \([\varepsilon,1-\varepsilon]\), then letting \(\varepsilon\downarrow0\), gives the ground-state transform identity
\[
\int_0^1G'^2du-\frac14\int_0^1\frac{G^2}{w^2}du
=\int_0^1w\left[\left(\frac G{\sqrt w}\right)'\right]^2du\ge0.
\]
The boundary term is \((\eta'/\eta)G^2\). Since \(G(0)=G(1)=0\) and \(g\) is bounded, \(G(u)=O(u)\) and \(G(u)=O(1-u)\); thus the boundary term does tend to zero.

Now first take \(g\) locally Lipschitz and constant near both endpoints, then subtract its mean. Integration by parts and Cauchy–Schwarz give
\[
\int g^2=-\int Gg'
\le\left(\int\frac{G^2}{w^2}\right)^{1/2}\left(\int w^2g'^2\right)^{1/2}
\le2\left(\int g^2\right)^{1/2}\left(\int w^2g'^2\right)^{1/2}.
\]
Consequently,
\[
\boxed{\operatorname{Var}_{U(0,1)}g\le4\int_0^1u^2(1-u)^2|g'(u)|^2du.}\tag{6.2}
\]

The extension details are as follows. First extend a bounded locally Lipschitz function by its endpoint values on \((0,\varepsilon)\) and \((1-\varepsilon,1)\). The functions converge in \(L^2\), and the derivative energy is exactly the original energy restricted to \((\varepsilon,1-\varepsilon)\). Then truncate the values of a general \(L^2\) function via \(g_N=(-N)\vee(g\wedge N)\), using \(|g_N'|\le|g'|\) and \(L^2\) convergence. Thus (6.2) holds for all required functions; infinite energy is immediate.

## 7. Completing the general one-dimensional Poincaré inequality

Let \(g=f\circ Q\). Change of variables and the chain rule give
\[
\operatorname{Var}_\mu f=\operatorname{Var}_{U(0,1)}g,\qquad
\int_I|f'|^2\rho\,dx=\int_0^1J(u)^2|g'(u)|^2du.
\]
Hence
\[
\operatorname{Var}_\mu f
\le4\int_0^1w^2|g'|^2du
\le4\sigma^2\int_0^1J^2|g'|^2du
=4\operatorname{Var}_\mu(X)\int|f'|^2d\mu.
\]

Asymmetry, nonsmooth log densities, and finite, half-infinite, or full-line support are all included. Real-line endpoints create no additional integration-by-parts boundary terms, because the Hardy calculation first uses constant extension on the quantile interval.

If \(\sigma^2=0\), then \(X=\mathbb EX\) almost everywhere, so \(\mu\) is Dirac. Every function has zero variance, and \(C_P=0\). A locally Lipschitz function need not have a classical derivative at the atom, so this branch should be stated separately; under the intrinsic-energy convention on zero-dimensional support, the energy is zero, with no need to assign a value to \(0\cdot\infty\).

## 8. Higher-dimensional reconstruction: exact weights for four-integral localization

### 8.1 From the one-dimensional profile to a separated-set inequality

For a one-dimensional law \(\nu\), let \(\sigma_\nu\) be its standard deviation. By (5.1), for any locally Lipschitz function \(r\), Tonelli gives
\[
\mathbb E|r(Y)-r(Y')|
\le2\int F_\nu(t)(1-F_\nu(t))|r'(t)|dt
\le2\sigma_\nu\int|r'|d\nu.
\]

If \(A,B\) are at distance at least \(d>0\), put \(C=(A\cup B)^c\) and take
\(r(x)=\min(1,\operatorname{dist}(x,A)/d)\). It is zero on \(A\), one on \(B\), and its derivative is almost everywhere nonzero only in \(C\), with magnitude at most \(1/d\). Therefore
\[
\boxed{\nu(A)\nu(B)\le\frac{\sigma_\nu}{d}\nu(C).}\tag{8.1}
\]
The proof applies to arbitrary separated measurable sets, not only two half-lines.

### 8.2 Fixing the second-moment weight; no requirement that needles preserve the mean

Fix \(a\in\mathbb R^n\), \(s>0\), and define
\[
W_{a,s}(x)=\frac{|x-a|^2+s^2}{2s}.
\]
For any normalized exponential needle \(\nu\), compute its one-dimensional standard deviation in a unit arc-length coordinate. Then
\[
\mathbb E_\nu W_{a,s}
\ge\sqrt{\mathbb E_\nu|Y-a|^2}
\ge\sqrt{\mathbb E_\nu|Y-\mathbb E_\nu Y|^2}
=\sigma_\nu.
\]
This uses only the arithmetic–geometric mean inequality and variance decomposition, regardless of whether the needle's mean equals \(a\).

Thus every exponential needle satisfies
\[
\nu(A)\nu(B)\le\nu(C)\,\nu(W_{a,s}/d).
\]
Canceling the needle normalization constants gives precisely the four-integral inequality
\[
\left(\int_E1_A\right)\left(\int_E1_B\right)
\le\left(\int_E1_C\right)\left(\int_EW_{a,s}/d\right).\tag{8.2}
\]

The external lemma used is exactly KLS Theorem 2.7 with exponents \(\alpha=\beta=1\). It says that if four nonnegative continuous functions satisfy this product comparison on every exponential needle, then they also do so for any compactly supported log-concave weight. The theorem and proof are on pp.549–550; the reduction to one-dimensional exponential needles is on pp.547–549.

### 8.3 Meeting the continuity requirements

First take closed sets \(A,B\) at distance \(d>0\). Let
\[
a_\varepsilon(x)=\max(0,1-\operatorname{dist}(x,A)/\varepsilon),\quad
b_\varepsilon(x)=\max(0,1-\operatorname{dist}(x,B)/\varepsilon),
\]
where \(2\varepsilon<d\). Their nonzero regions are separated by at least \(d-2\varepsilon\), and
\(c_\varepsilon=1-a_\varepsilon-b_\varepsilon\ge0\) is continuous.

On any needle, apply (8.1) to the level sets \(\{a_\varepsilon>u\}\) and \(\{b_\varepsilon>v\}\), then integrate over \((u,v)\in(0,1)^2\) to obtain
\[
\nu(a_\varepsilon)\nu(b_\varepsilon)
\le\nu(c_\varepsilon)\,\nu(W_{a,s}/(d-2\varepsilon)).
\]
All four functions now satisfy the continuity requirements of KLS Theorem 2.7. After localization, let \(\varepsilon\downarrow0\) to obtain
\[
\mu(A)\mu(B)\le\frac{\mu(W_{a,s})}{d}\mu(C).
\]
For general separated measurable sets, first take closures: each set's mass can only increase, and the complement's mass can only decrease. Thus the closed-set inequality implies the original inequality.

What is preserved here is the four-integral product comparison (8.2), rather than artificially prescribed mean constraints. Fix \(a,s\) before localization and optimize only afterward.

### 8.4 Optimization and unbounded support

\[
\mu(W_{a,s})=\frac{\mathbb E|X-a|^2+s^2}{2s}.
\]
First set \(s=\sqrt{\mathbb E|X-a|^2}\), then \(a=\mathbb EX\), to obtain
\[
\mu(C)\ge\frac dS\mu(A)\mu(B),\qquad S^2=\mathbb E|X-\mathbb EX|^2.\tag{8.3}
\]

Remove the compact-support restriction using \(\mu_R=\mu(\cdot\mid B(0,R))\). The truncated density remains log-concave; for fixed \(a,s\), the set masses and \(\mu_R(W_{a,s})\) converge. Optimize after this limit, without assuming the truncated means are fixed.

For closed \(A\), take \(B_t=\{x:\operatorname{dist}(x,A)\ge t\}\) and let \(t\downarrow0\). From (8.3), in the standard one-sided outer Minkowski perimeter sense,
\[
\boxed{\mu^+(A)\ge S^{-1}\mu(A)(1-\mu(A)).}\tag{8.4}
\]
Thus the product-normalized constant satisfies \(\psi\ge1/S\). Passing from separation distance \(t\) to one-sided outer perimeter introduces no additional factor 2.

## 9. Bypassing min normalization: a direct proof of C_P ≤ 4/ψ²

First let \(\mu\) have a smooth positive density and \(f\in C_c^\infty\). Set \(Z=f(X)-\mathbb E f(X)\), with distribution function \(F_Z\) and generalized quantile \(Q_Z\). Define
\[
H(t)=\mathbb E[Z1_{\{Z\le t\}}],\qquad G(u)=\int_0^u Q_Z(v)dv.
\]
We have \(H(t)\le0\) and \(H(t)=G(F_Z(t))\); applying the tail-integral formula on each side of \(t=0\) yields
\[
\operatorname{Var}Z=-\int_{\mathbb R}H(t)dt.
\]

At non-atomic values of \(Z\), if \(0<F_Z(t)<1\), define
\[
B(t)=\frac{|H(t)|}{F_Z(t)(1-F_Z(t))};
\]
Set \(B=0\) at atoms and where the denominator vanishes. Quantile coupling and (6.1) give
\[
\mathbb EB(Z)^2\le\int_0^1\frac{G(u)^2}{u^2(1-u)^2}du\le4\operatorname{Var}Z.\tag{9.1}
\]
Atoms in \(Z\) are allowed. They correspond to constant intervals of \(Q_Z\); setting \(B\) to zero at these values merely removes nonnegative contributions, while the remaining quantile ranks still satisfy \(F_Z(Q_Z(u))=u\) almost everywhere. Atomic values are countable and do not change the Lebesgue integral in \(t\).

For almost every regular level \(t\), write \(P(t)\) for its weighted perimeter. The product isoperimetric bound gives
\[
P(t)\ge\psi F_Z(t)(1-F_Z(t)).
\]
Using the coarea formula and (9.1),
\[
\begin{aligned}
\operatorname{Var}_\mu f
&=\int|H(t)|dt\\
&\le\psi^{-1}\int B(t)P(t)dt\\
&=\psi^{-1}\int B(Z)|\nabla f|d\mu\\
&\le\psi^{-1}(\mathbb EB(Z)^2)^{1/2}\left(\int|\nabla f|^2d\mu\right)^{1/2}\\
&\le\frac2\psi\sqrt{\operatorname{Var}_\mu f}\left(\int|\nabla f|^2d\mu\right)^{1/2}.
\end{aligned}
\]
Therefore,
\[
\boxed{C_P(\mu)\le4/\psi^2\le4S^2=4\operatorname{tr}(\operatorname{Cov}\mu).}\tag{9.2}
\]

The precise coarea formula used here is
\[
\int b(f(x))|\nabla f(x)|\rho(x)dx
=\int_{\mathbb R}b(t)\left(\int_{f^{-1}(t)}\rho\,d\mathcal H^{n-1}\right)dt
\]
for nonnegative measurable \(b\). Sard's theorem ensures that critical values of a smooth function do not affect the right-hand integral. Nontrivial regular levels have compact smooth boundaries, so the inner area is the corresponding one-sided Minkowski perimeter.

## 10. Higher-dimensional nonsmooth densities and the function class

Let \(\mu_\varepsilon=\mu*N(0,\varepsilon I_n)\). By the marginal-integration property of Prékopa–Leindler, convolution preserves log-concavity and gives a smooth positive density. Its total variance is
\[
\operatorname{tr}\operatorname{Cov}(\mu_\varepsilon)=\operatorname{tr}\operatorname{Cov}(\mu)+n\varepsilon.
\]
For \(C_c^\infty\) test functions, \(f,f^2,|\nabla f|^2\) are bounded and continuous, so we can let \(\varepsilon\downarrow0\) in (9.2).

To extend from smooth compactly supported functions to locally Lipschitz \(L^2\) functions, first truncate values to obtain \(f_N\), then multiply by a spatial cutoff \(\chi_R\), with \(\chi_R=1\) on the ball of radius R, supported in the ball of radius 2R, with \(|\nabla\chi_R|\le c/R\). When energy is finite,
\[
\|\nabla(\chi_Rf_N)-\nabla f_N\|_{L^2(\mu)}
\le\|(\chi_R-1)\nabla f_N\|_2+Nc/R\longrightarrow0.
\]
Approximate compactly supported Lipschitz functions by ordinary smooth convolution. Gradients converge almost everywhere and are uniformly bounded, so dominated convergence applies under an absolutely continuous measure. Remove convolution, spatial truncation, and value truncation in order to obtain the required function class.

If the measure is supported on a proper affine subspace, first prove the result in Euclidean coordinates on that affine hull. The trace is the total variance in the intrinsic space. Dimension zero is Dirac and is handled separately.

## 11. Sharpness and checking the median route

For the unit one-sided exponential law, take \(f_c(x)=e^{cx}\), \(0<c<1/2\). Direct integration gives
\[
\frac{\operatorname{Var}(f_c)}{\int|f_c'|^2d\mu}=\frac1{(1-c)^2}\longrightarrow4.
\]
This law has \(\operatorname{Var}X=1\), so the constant 4 in the general one-dimensional result cannot be decreased.

For a uniform interval of length L, \(\rho(m)=1/L\) and \(\operatorname{Var}X=L^2/12\). Thus \(\operatorname{Var}X\ge1/(4\rho(m)^2)\) is indeed false. This text does not use that incorrect substitution; it uses the full profile \(J(u)\) and (6.2), rather than only the density at the median.

## 12. External dependencies and the unresolved historical question

The external structural input to the one-dimensional argument is the density representation of log-concave measures. The remaining inputs are local regularity and supporting lines for finite concave functions, inverse functions and change of variables, Tonelli/Fubini, dominated convergence, Cauchy–Schwarz, and integration by parts for absolutely continuous functions. All estimates determining the constant are proved in the text.

The higher-dimensional argument additionally uses KLS Theorem 2.7, preservation of log-concavity under marginals/convolution via Prékopa–Leindler, the coarea formula, and Sard's theorem. The four functions in localization, the continuity approximation, needle estimates, global parameter optimization, and compact-support limit are all explicit. No assumption that needles preserve means or variances is made.

The unresolved question is historical: which original source first wrote out the exact coefficient-4 proof in full? The most targeted next source would be an explanation by the monograph's two authors of the original derivation on p.11: whether 4 comes from second-moment four-function localization, the sharp conversion from product normalization, or another unlisted proof. The authors' websites list the monograph and contact channels, but this round obtained neither the complete monograph nor an erratum. This reconstruction must not be presented as an original verbatim proof that has been located.

## Sources

1. R. Kannan, L. Lovász, M. Simonovits. *Isoperimetric Problems for Convex Bodies and a Localization Lemma*. Discrete & Computational Geometry 13 (1995), 541–559. DOI 10.1007/BF02574061. [Publisher's original PDF](https://link.springer.com/content/pdf/10.1007/BF02574061.pdf).
2. P. Cattiaux, A. Guillin. *On the Poincaré constant of log-concave measures*. [2018 arXiv v1 PDF](https://arxiv.org/pdf/1810.08369v1), p.11, (2.25); [Authors' revision dated 2019-05-19](https://perso.math.univ-toulouse.fr/cattiaux/files/2013/11/cattiaux-guillin-GAFA-revised21.pdf), p.12, (2.13).
3. D. Alonso-Gutiérrez, J. Bastero. *Approaching the Kannan–Lovász–Simonovits and Variance Conjectures*. Lecture Notes in Mathematics 2131. Springer, 2015. DOI 10.1007/978-3-319-13263-1. [Publisher's page](https://link.springer.com/book/10.1007/978-3-319-13263-1). No full-text PDF was obtained in this round; supplied page information is not claimed as independently read.
4. D. Alonso-Gutiérrez, J. Bastero. *Convex inequalities, isoperimetry and spectral gap*. 2014 course manuscript; published in Advanced Courses of Mathematical Analysis VI, 2017, pp.3–24. [Manuscript](https://anamat.unizar.es/bastero/archivos/convex.pdf); [Authors' publications page](https://anamat.unizar.es/bastero/index.html). Theorem 4.1 on manuscript pp.14–15 uses an unspecified C; page-image access failed.
5. N. Huet. *Spectral gap for some invariant log-concave probability measures*. [Author preprint arXiv:1003.4839](https://arxiv.org/pdf/1003.4839), p.2 states equivalence between the measure definition and a log-concave density on the affine hull, referring to Borell.
6. C. Borell. *Convex measures on locally convex spaces*. Arkiv för Matematik 12 (1974), 239–252. [Publisher's page](https://link.springer.com/article/10.1007/BF02384761). This round obtained metadata only, without reading the original proof.
7. C. Borell. *Convex set functions in d-space*. Periodica Mathematica Hungarica 6 (1975), 111–136. [Publisher's page](https://link.springer.com/article/10.1007/BF02018814). This round obtained metadata only, without reading the original proof.
