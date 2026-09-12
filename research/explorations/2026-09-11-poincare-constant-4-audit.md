<!-- 来源：合作者提供的审计文档，2026-09-11 由 lyuyuwei 交给本仓库作为一维 Poincaré 系数 4 证明重构的出处；原文件 ~/Downloads/poincare_constant_4_audit.md，内容未改。Lean 形式化见 research/decisions/2026-09-11-one-dimensional-logconcave-poincare-four.md。 -->

# 对数凹 Poincaré 不等式系数 4：文献核查与完整数学重构

## 结论与证据等级

文献检索应归类为：找到了可靠的明确陈述及可用的原始局部化定理，但尚未定位到一份原始文献中已经逐步写出的、带精确系数 4 的完整 Poincaré 证明。不能据此称结论为误引或错误。

数学核验则可以继续向前：下文给出一般一维情形的完整独立推导，并利用 Kannan–Lovász–Simonovits（1995）Theorem 2.7 的四积分局部化形式，重构高维界

\[
C_P(\mu)\le4\inf_a\mathbb E|X-a|^2=4\operatorname{tr}(\operatorname{Cov}\mu).
\]

这里的“重构”不表示以下计算已经逐字出现在 KLS 原文。历史归属与数学证明须分开记录。本报告不含 Lean 代码，也不声称已经机器核验。

## 1. 文献与核查范围

| 文献/版本 | 位置 | 精确内容 | 证明与访问状态 |
|---|---|---|---|
| KLS，DCG 13 (1995), 541–559 | p.542, (1.1)–(1.2) | 乘积归一化等周常数；与 min 归一化比较 | 原始 PDF 页图已检查 |
| 同上 | pp.547–550, Lemma 2.6、Theorem 2.7 | 四个非负连续函数的积分乘积不等式，可归约到指数针 | 原文有证明；关键页图已检查 |
| 同上 | pp.554–556, Theorems 5.1–5.2 | \(\psi(K)\ge\log2/M_1(K)\) | 原文有证明；不是现成的系数 4 Poincaré 推导 |
| 同上 | p.557, Theorem 5.3 | \(\psi(K)\ge1/\chi(K)\) | 原文有证明；p.558 的 Theorem 5.4/Lemma 5.5 相关后续亦检查 |
| Cattiaux–Guillin，arXiv v1，2018 | p.11, (2.25) | \(C_P\le4\mathbb E|X-\mathbb EX|^2\) | 明确陈述；该处转引专著 p.11，不给该常数的证明 |
| Cattiaux–Guillin，2019-05-19 修订稿 | p.12, (2.13) | 同一高维系数 4 | 页图已检查；Remark 2.13 末句针对球对称应用 |
| Alonso-Gutiérrez–Bastero，LNM 2131 (2015) | p.11；pp.18–21, Theorem 1.5 | 前者陈述 4，后者一维证明为 12 | 本轮未取得可读取的正文 PDF；具体书页信息沿用已提供的核对，不标为独立重读。p.11 的引用位置由 CG 原文确认 |
| 同两作者，Convex inequalities, isoperimetry and spectral gap，2014 课程作者稿，2017 出版 | 作者稿 pp.14–15, Theorem 4.1 | \(C_P\le C\mathbb E|X-\mathbb EX|^2\)，未指定 C | 正文可读取，页图加载失败；不能作为精确 4 的证明 |

原始链接与完整书目信息见文末。未找到可核实的勘误或另一版本，将精确系数 4 的全部证明明确补在引用位置。

## 2. 常数约定

设
\[
C_P=\inf\{C\ge0:\operatorname{Var}_\mu f\le C\int|\nabla f|^2d\mu\},\qquad\lambda_1=C_P^{-1}.
\]
谱隙（spectral gap）按上述约定，不取平方根。

切格常数（Cheeger constant）的 min 归一化与乘积归一化（product normalization）分别为
\[
h=\inf_A\frac{\mu^+(A)}{\min(\mu A,1-\mu A)},\qquad
\psi=\inf_A\frac{\mu^+(A)}{\mu A(1-\mu A)}.
\]
因为 \(pq\le\min(p,q)\le2pq\)，有 \(h\le\psi\le2h\)。若将 \(1/h\) 称作 Cheeger 常数，则通常的 Cheeger–Poincaré 界写作 \(C_P\le4(1/h)^2\)。

因此，仅使用 KLS Theorem 5.1 和上述比较，确实只能得到
\[
C_P\le\frac{16}{\psi^2}\le\frac{16M_1^2}{(\log2)^2}\le\frac{16}{(\log2)^2}\mathbb E|X-\mathbb EX|^2.
\]
下文不使用这条损失常数的路线。两项实质改进分别是：二次矩权重的四积分局部化，以及直接从乘积归一化推出 \(C_P\le4/\psi^2\)。

## 3. 一维结构与分位数密度

非 Dirac 的一维对数凹概率测度（log-concave probability measure）有密度 \(\rho=e^v\)，在其开支撑区间 \(I=(l,r)\) 内严格正，且 \(v\) 为有限凹函数。端点可有限或无限。这是从测度定义转为密度定义时使用的结构定理；见 Huet 作者稿 p.2 对 Borell 定理的明确表述。

有限凹函数在开区间内局部 Lipschitz 连续。若右端点无限，密度可积保证存在 \(x_0<x_1\) 满足 \(v(x_1)<v(x_0)\)。凹性于是给出
\[
v(x)\le v(x_1)+\frac{v(x_1)-v(x_0)}{x_1-x_0}(x-x_1),\quad x\ge x_1.
\]
因此右尾指数衰减；左尾同理。特别地 \(0<\sigma^2:=\operatorname{Var}_\mu X<\infty\)。

令分布函数（cumulative distribution function）为 \(F\)，分位数函数（quantile function）为 \(Q=F^{-1}:(0,1)\to I\)，分位数密度（quantile density profile）为
\[
J(u)=\rho(Q(u)).
\]
则 \(Q'(u)=1/J(u)\)，且 \(J\) 是正凹函数。非光滑情形同样成立：在任意紧子区间上 \(Q\) 局部双 Lipschitz，链式法则给出 \(J'(u)=v'(Q(u))\) 几乎处处；右端为非增函数，局部绝对连续性遂给出凹性。无需假定 \(v\) 二阶可微。

## 4. 仿射分位数模型的方差下界

固定 \(p\in(0,1)\)。设
\[
\ell(u)=A(1-u)+Bu>0\quad(0<u<1),\qquad A,B\ge0,
\]
其中 \(A,B\) 不全为零，并定义
\[
q(u)=\int_p^u\frac{dt}{\ell(t)},\qquad U\sim\operatorname{Unif}(0,1).
\]
则
\[
\boxed{\operatorname{Var}(q(U))\ge\frac1{(\sqrt A+\sqrt B)^4}.}\tag{4.1}
\]

若 \(A=B=c>0\)，方差为 \(1/(12c^2)\)，右侧为 \(1/(16c^2)\)。

若 \(A=0<B\)，则 \(q(u)=(\log u-\log p)/B\)。由
\(\int_0^1\log u\,du=-1\)、\(\int_0^1(\log u)^2du=2\)，方差为 \(1/B^2\)，恰等于右侧。\(B=0<A\) 由反射得到。

若 \(0<A<B\)，令 \(\beta=B-A\)。积分得到
\[
q(u)=\frac1\beta\log\frac{A+\beta u}{A+\beta p},
\]
以及
\[
\operatorname{Var}(q(U))=\frac1{\beta^2}-\frac{AB\log^2(B/A)}{\beta^4}.\tag{4.2}
\]
此式可直接由
\[
\int\log x\,dx=x(\log x-1),\quad
\int\log^2x\,dx=x(\log^2x-2\log x+2)
\]
在 \([A,B]\) 上计算得到。

写 \(D=\sqrt B-\sqrt A\)、\(S=\sqrt B+\sqrt A\)，于是 \(\beta=DS\)。对 \(z\ge1\)，
\[
\frac d{dz}(z-z^{-1}-2\log z)=\frac{(z-1)^2}{z^2}\ge0,
\]
故取 \(z=(B/A)^{1/4}\) 有
\[
\log(B/A)\le\frac{2D}{(AB)^{1/4}}.
\]
因此
\[
AB\log^2(B/A)\le4\sqrt{AB}D^2=D^2(S^2-D^2),
\]
代回 (4.2) 即得
\[
\operatorname{Var}(q(U))\ge\frac{D^4}{D^4S^4}=S^{-4}.
\]
\(B<A\) 用反射。所有仿射模型均已覆盖。

## 5. 一般对数凹密度的完整轮廓估计

证明
\[
\boxed{J(u)\ge\frac{u(1-u)}\sigma\quad(0<u<1).}\tag{5.1}
\]

固定 \(p\)。凹函数 \(J\) 在内部点有仿射上支撑线（affine supporting majorant）\(\ell\)，满足 \(\ell\ge J\)、\(\ell(p)=J(p)\)。写为前节形式。由区间内部正性知 \(A,B\ge0\)，不全为零。

因为 \(Q'=1/J\ge1/\ell=q'\)，对 \(u>v\) 有
\[
Q(u)-Q(v)\ge q(u)-q(v)\ge0.
\]
独立双样本方差恒等式（independent-copy variance identity）给出
\[
\sigma^2=\frac12\int_0^1\!\int_0^1[Q(u)-Q(v)]^2\,du\,dv
\ge\operatorname{Var}(q(U))\ge\frac1{(\sqrt A+\sqrt B)^4}.
\]
另一方面，Cauchy–Schwarz 不等式给出
\[
\frac{\ell(p)}{p(1-p)}=\frac A p+\frac B{1-p}\ge(\sqrt A+\sqrt B)^2\ge\frac1\sigma.
\]
由 \(\ell(p)=J(p)\) 得到 (5.1)。

这一推广并未假定“一般律可直接换成某个指数律”；它由上支撑线和所有分位数差的逐点比较完成。锚点 \(p\) 任取，不要求它是均值或中位数。

## 6. 尖锐加权 Hardy 计算

写 \(w(u)=u(1-u)\)。先证明：若 \(g\) 有界且均值为零，\(G(u)=\int_0^u g(v)dv\)，则
\[
\boxed{\int_0^1\frac{G(u)^2}{w(u)^2}du\le4\int_0^1g(u)^2du.}\tag{6.1}
\]

取 \(\eta(u)=\sqrt{w(u)}\)，直接求导可得
\[
-\frac{\eta''(u)}{\eta(u)}=\frac1{4u^2(1-u)^2}.
\]
在 \([\varepsilon,1-\varepsilon]\) 上分部积分，然后令 \(\varepsilon\downarrow0\)，得到基态变换（ground-state transform）恒等式
\[
\int_0^1G'^2du-\frac14\int_0^1\frac{G^2}{w^2}du
=\int_0^1w\left[\left(\frac G{\sqrt w}\right)'\right]^2du\ge0.
\]
边界项为 \((\eta'/\eta)G^2\)。由 \(G(0)=G(1)=0\) 且 \(g\) 有界，\(G(u)=O(u)\)、\(G(u)=O(1-u)\)，所以边界项确实趋于零。

现在先令 \(g\) 局部 Lipschitz 并在两端邻域为常数，再减去均值。分部积分和 Cauchy–Schwarz 给出
\[
\int g^2=-\int Gg'
\le\left(\int\frac{G^2}{w^2}\right)^{1/2}\left(\int w^2g'^2\right)^{1/2}
\le2\left(\int g^2\right)^{1/2}\left(\int w^2g'^2\right)^{1/2}.
\]
因而
\[
\boxed{\operatorname{Var}_{U(0,1)}g\le4\int_0^1u^2(1-u)^2|g'(u)|^2du.}\tag{6.2}
\]

推广细节如下。有界的局部 Lipschitz 函数先在 \((0,\varepsilon)\) 与 \((1-\varepsilon,1)\) 上按端值常数延拓。函数在 \(L^2\) 中收敛，导数能量恰为原能量在 \((\varepsilon,1-\varepsilon)\) 的限制。然后对一般 \(L^2\) 函数作值截断 \(g_N=(-N)\vee(g\wedge N)\)，利用 \(|g_N'|\le|g'|\) 和 \(L^2\) 收敛。因此 (6.2) 对全部所需函数成立，能量无限时直接成立。

## 7. 完成一般一维 Poincaré 不等式

令 \(g=f\circ Q\)。换元和链式法则给出
\[
\operatorname{Var}_\mu f=\operatorname{Var}_{U(0,1)}g,\qquad
\int_I|f'|^2\rho\,dx=\int_0^1J(u)^2|g'(u)|^2du.
\]
于是
\[
\operatorname{Var}_\mu f
\le4\int_0^1w^2|g'|^2du
\le4\sigma^2\int_0^1J^2|g'|^2du
=4\operatorname{Var}_\mu(X)\int|f'|^2d\mu.
\]

非对称性、非光滑对数密度、有限/半无限/全实线支撑均已包含。实线端点不会产生额外分部积分边界项，因为 Hardy 计算在分位数区间上先经常数延拓处理。

若 \(\sigma^2=0\)，则 \(X=\mathbb EX\) 几乎处处，即 \(\mu\) 是 Dirac 测度。所有函数方差为零，\(C_P=0\)。局部 Lipschitz 函数在原子处可能没有经典导数，因此这一分支应单独陈述；在零维支撑的内在能量约定下能量为零，不需要给 \(0\cdot\infty\) 赋值。

## 8. 高维重构：四积分局部化的精确权重

### 8.1 从一维轮廓到分离集合不等式

对一维律 \(\nu\)，设其标准差为 \(\sigma_\nu\)。由 (5.1)，对任意局部 Lipschitz 函数 \(r\)，Tonelli 定理给出
\[
\mathbb E|r(Y)-r(Y')|
\le2\int F_\nu(t)(1-F_\nu(t))|r'(t)|dt
\le2\sigma_\nu\int|r'|d\nu.
\]

若 \(A,B\) 距离至少 \(d>0\)，\(C=(A\cup B)^c\)，取
\(r(x)=\min(1,\operatorname{dist}(x,A)/d)\)。它在 \(A\) 上为零、在 \(B\) 上为一，且导数几乎处处只可能在 \(C\) 非零，大小至多 \(1/d\)。因此
\[
\boxed{\nu(A)\nu(B)\le\frac{\sigma_\nu}{d}\nu(C).}\tag{8.1}
\]
该证明适用于任意分离的可测集合，不限于两个半直线。

### 8.2 固定二次矩权重；不要求针保留均值

固定 \(a\in\mathbb R^n\)、\(s>0\)，定义
\[
W_{a,s}(x)=\frac{|x-a|^2+s^2}{2s}.
\]
对任意归一化指数针 \(\nu\)，以单位弧长坐标计算其一维标准差，则
\[
\mathbb E_\nu W_{a,s}
\ge\sqrt{\mathbb E_\nu|Y-a|^2}
\ge\sqrt{\mathbb E_\nu|Y-\mathbb E_\nu Y|^2}
=\sigma_\nu.
\]
这只用算术—几何平均不等式及方差分解，与针的均值是否等于 \(a\) 无关。

故每条指数针都满足
\[
\nu(A)\nu(B)\le\nu(C)\,\nu(W_{a,s}/d).
\]
取消针的归一化常数，恰好得到四积分不等式
\[
\left(\int_E1_A\right)\left(\int_E1_B\right)
\le\left(\int_E1_C\right)\left(\int_EW_{a,s}/d\right).\tag{8.2}
\]

所用外部引理正是 KLS Theorem 2.7，取指数 \(\alpha=\beta=1\)。它说四个非负连续函数若在每条指数针上满足这个乘积比较，则对任意紧支撑对数凹权函数同样成立。原文在 pp.549–550 给出定理与证明；其一维指数针归约见 pp.547–549。

### 8.3 连续性要求的补齐

先取闭集 \(A,B\)，距离 \(d>0\)。令
\[
a_\varepsilon(x)=\max(0,1-\operatorname{dist}(x,A)/\varepsilon),\quad
b_\varepsilon(x)=\max(0,1-\operatorname{dist}(x,B)/\varepsilon),
\]
其中 \(2\varepsilon<d\)。它们非零区域分离至少 \(d-2\varepsilon\)，而
\(c_\varepsilon=1-a_\varepsilon-b_\varepsilon\ge0\) 连续。

对任意针，对水平集 \(\{a_\varepsilon>u\}\)、\(\{b_\varepsilon>v\}\) 使用 (8.1)，再对 \((u,v)\in(0,1)^2\) 积分，得到
\[
\nu(a_\varepsilon)\nu(b_\varepsilon)
\le\nu(c_\varepsilon)\,\nu(W_{a,s}/(d-2\varepsilon)).
\]
四个函数现在均满足 KLS Theorem 2.7 的连续性要求。局部化后令 \(\varepsilon\downarrow0\)，便得
\[
\mu(A)\mu(B)\le\frac{\mu(W_{a,s})}{d}\mu(C).
\]
一般可测分离集合可先取闭包：两边集合质量只增，补集质量只减，因此闭集不等式蕴含原不等式。

这一步保留的不是若干人为指定的均值约束，而是 (8.2) 这个四积分乘积比较。参数 \(a,s\) 在局部化前固定，在局部化完成后才优化。

### 8.4 优化与无界支撑

\[
\mu(W_{a,s})=\frac{\mathbb E|X-a|^2+s^2}{2s}.
\]
先令 \(s=\sqrt{\mathbb E|X-a|^2}\)，再令 \(a=\mathbb EX\)，得
\[
\mu(C)\ge\frac dS\mu(A)\mu(B),\qquad S^2=\mathbb E|X-\mathbb EX|^2.\tag{8.3}
\]

紧支撑限制用 \(\mu_R=\mu(\cdot\mid B(0,R))\) 去除。截断密度仍对数凹；固定 \(a,s\) 时集合质量与 \(\mu_R(W_{a,s})\) 均收敛。应在这一极限完成后优化，不需假设截断均值固定。

对闭集 \(A\)，取 \(B_t=\{x:\operatorname{dist}(x,A)\ge t\}\)，令 \(t\downarrow0\)。由 (8.3) 得到标准单侧 Minkowski 外周长意义下
\[
\boxed{\mu^+(A)\ge S^{-1}\mu(A)(1-\mu(A)).}\tag{8.4}
\]
因此乘积归一化常数 \(\psi\ge1/S\)。从分离距离 \(t\) 到单侧外周长未引入额外因子 2。

## 9. 不经 min 归一化：直接证明 C_P ≤ 4/ψ²

先令 \(\mu\) 有光滑正密度，\(f\in C_c^\infty\)。设 \(Z=f(X)-\mathbb E f(X)\)，\(F_Z\) 为其分布函数，\(Q_Z\) 为广义分位数。定义
\[
H(t)=\mathbb E[Z1_{\{Z\le t\}}],\qquad G(u)=\int_0^u Q_Z(v)dv.
\]
有 \(H(t)\le0\)、\(H(t)=G(F_Z(t))\)，且按 \(t=0\) 两侧使用尾积分公式可得
\[
\operatorname{Var}Z=-\int_{\mathbb R}H(t)dt.
\]

在 \(Z\) 的非原子值处，若 \(0<F_Z(t)<1\)，定义
\[
B(t)=\frac{|H(t)|}{F_Z(t)(1-F_Z(t))};
\]
在原子值及分母为零处令 \(B=0\)。分位数耦合与 (6.1) 给出
\[
\mathbb EB(Z)^2\le\int_0^1\frac{G(u)^2}{u^2(1-u)^2}du\le4\operatorname{Var}Z.\tag{9.1}
\]
这里允许 \(Z\) 有原子。原子对应 \(Q_Z\) 的常值区间；将 \(B\) 在这些值处置零只会删去非负积分，其余分位数秩仍满足 \(F_Z(Q_Z(u))=u\) 几乎处处。原子值可数，也不改变对 \(t\) 的 Lebesgue 积分。

对几乎每个正则水平 \(t\)，记其加权周长为 \(P(t)\)。乘积等周界给出
\[
P(t)\ge\psi F_Z(t)(1-F_Z(t)).
\]
使用余面积公式（coarea formula）以及 (9.1)，
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
因此
\[
\boxed{C_P(\mu)\le4/\psi^2\le4S^2=4\operatorname{tr}(\operatorname{Cov}\mu).}\tag{9.2}
\]

这里余面积公式使用的精确形式为
\[
\int b(f(x))|\nabla f(x)|\rho(x)dx
=\int_{\mathbb R}b(t)\left(\int_{f^{-1}(t)}\rho\,d\mathcal H^{n-1}\right)dt
\]
对非负可测 \(b\) 成立。Sard 定理保证光滑函数的临界值不影响右边积分；非平凡正则水平的边界紧且光滑，故内层面积即相应单侧 Minkowski 周长。

## 10. 高维非光滑密度与函数类

令 \(\mu_\varepsilon=\mu*N(0,\varepsilon I_n)\)。由 Prékopa–Leindler 的边缘积分性质，卷积仍对数凹，并具有光滑正密度。其总方差为
\[
\operatorname{tr}\operatorname{Cov}(\mu_\varepsilon)=\operatorname{tr}\operatorname{Cov}(\mu)+n\varepsilon.
\]
对 \(C_c^\infty\) 测试函数，\(f,f^2,|\nabla f|^2\) 均有界连续，故可在 (9.2) 中令 \(\varepsilon\downarrow0\)。

从光滑紧支撑函数推广到局部 Lipschitz 的 \(L^2\) 函数：先作值截断 \(f_N\)，再乘空间截断 \(\chi_R\)，其中 \(\chi_R=1\) 于半径 R 的球内、支撑于半径 2R 的球内、\(|\nabla\chi_R|\le c/R\)。当能量有限时，
\[
\|\nabla(\chi_Rf_N)-\nabla f_N\|_{L^2(\mu)}
\le\|(\chi_R-1)\nabla f_N\|_2+Nc/R\longrightarrow0.
\]
紧支撑 Lipschitz 函数再经通常的光滑卷积逼近；梯度几乎处处收敛且有一致界，故在绝对连续测度下可用控制收敛。依次移去卷积、空间截断和值截断，得到所需函数类。

测度若支撑在真仿射子空间上，可先在该仿射包的欧氏坐标中进行证明。迹等于该内在空间的总方差。零维情形即 Dirac，单独处理。

## 11. 锐性及中位数路线的核对

对单位单边指数律，取 \(f_c(x)=e^{cx}\)、\(0<c<1/2\)。直接积分得
\[
\frac{\operatorname{Var}(f_c)}{\int|f_c'|^2d\mu}=\frac1{(1-c)^2}\longrightarrow4.
\]
此律 \(\operatorname{Var}X=1\)，所以一般一维结论中的常数 4 不能再减小。

对于长度 L 的均匀区间，\(\rho(m)=1/L\)、\(\operatorname{Var}X=L^2/12\)。因此 \(\operatorname{Var}X\ge1/(4\rho(m)^2)\) 确实为假。本文没有使用这一错误替换；它使用整个 \(J(u)\) 的轮廓与 (6.2)，不是只使用中位数处一个密度值。

## 12. 外部依赖与尚未闭合的历史问题

一维部分的外部结构依赖是对数凹测度的密度表示；其余依赖为有限凹函数的局部正则性与支撑线、反函数与换元、Tonelli/Fubini、控制收敛、Cauchy–Schwarz、绝对连续函数分部积分。所有决定常数的估计均已在正文证明。

高维部分另外依赖 KLS Theorem 2.7、Prékopa–Leindler 边缘/卷积保持对数凹性、余面积公式及 Sard 定理。四积分局部化所用的四个函数、连续化过程、针内估计、全局参数优化和紧支撑极限均明确给出，没有假定针保留均值或方差。

尚未闭合的是“最早哪份原始文献完整写出了精确 4”的历史问题。最有针对性的下一来源是专著两位作者对 p.11 的原始推导说明：应询问其系数 4 是否来自二次矩四函数局部化、乘积归一化的尖锐转换，或另一份未列出的证明。作者网页列出了专著及联系渠道，但本轮未取得专著完整正文或勘误。本文证明重构不能被冒充为已经找到的原始逐字证明。

## 来源

1. R. Kannan, L. Lovász, M. Simonovits. *Isoperimetric Problems for Convex Bodies and a Localization Lemma*. Discrete & Computational Geometry 13 (1995), 541–559. DOI 10.1007/BF02574061. [出版社原文 PDF](https://link.springer.com/content/pdf/10.1007/BF02574061.pdf)。
2. P. Cattiaux, A. Guillin. *On the Poincaré constant of log-concave measures*. [2018 arXiv v1 PDF](https://arxiv.org/pdf/1810.08369v1)，p.11, (2.25)；[2019-05-19 作者修订稿 PDF](https://perso.math.univ-toulouse.fr/cattiaux/files/2013/11/cattiaux-guillin-GAFA-revised21.pdf)，p.12, (2.13)。
3. D. Alonso-Gutiérrez, J. Bastero. *Approaching the Kannan–Lovász–Simonovits and Variance Conjectures*. Lecture Notes in Mathematics 2131. Springer, 2015. DOI 10.1007/978-3-319-13263-1. [出版社页面](https://link.springer.com/book/10.1007/978-3-319-13263-1)。本轮未取得正文 PDF，不把已提供的书页信息标为独立读取。
4. D. Alonso-Gutiérrez, J. Bastero. *Convex inequalities, isoperimetry and spectral gap*. 2014 课程作者稿；2017 收入 Advanced Courses of Mathematical Analysis VI, pp.3–24. [作者稿](https://anamat.unizar.es/bastero/archivos/convex.pdf)；[作者出版物页面](https://anamat.unizar.es/bastero/index.html)。作者稿 pp.14–15 的 Theorem 4.1 使用未指定常数 C；页图访问失败。
5. N. Huet. *Spectral gap for some invariant log-concave probability measures*. [作者预印本 arXiv:1003.4839](https://arxiv.org/pdf/1003.4839)，p.2 给出测度定义与仿射包上对数凹密度定义的等价，并指向 Borell。
6. C. Borell. *Convex measures on locally convex spaces*. Arkiv för Matematik 12 (1974), 239–252. [出版社页面](https://link.springer.com/article/10.1007/BF02384761)。本轮只取得元数据，未读取原文证明。
7. C. Borell. *Convex set functions in d-space*. Periodica Mathematica Hungarica 6 (1975), 111–136. [出版社页面](https://link.springer.com/article/10.1007/BF02018814)。本轮只取得元数据，未读取原文证明。
