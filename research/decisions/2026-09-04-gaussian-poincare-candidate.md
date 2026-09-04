# 一维 Gaussian Poincaré：候选声明审阅包

日期：2026-09-04（Asia/Shanghai）。
基线：`10e4c707491830ebe9d07f7bfc5e65efeddc7e2e`，分支 `main`。
节点：`lem:poincare-gaussian-one-dimensional`。
状态：**drafted / checked_by: null；尚未冻结或证明。**

用户本轮要求：“那就这么干，依旧先做statement，标清楚来源，做好用户体验，学习formech的风格”。
本文件落实陈述准备授权，不把它解释为对尚未展示的完整签名的批准。20 项新数学声明
全部保留 `by sorry`。本轮不创建 GitHub Issue，不提交或推送。

## 先看目标与例子

两个主入口都覆盖任意实均值 m 和非负方差 v：

```lean
theorem holds_gaussianReal (m : ℝ) (v : NNReal) :
    Holds (ProbabilityTheory.gaussianReal m v) (v : ℝ)

theorem constant_gaussianReal (m : ℝ) (v : NNReal) :
    constant (ProbabilityTheory.gaussianReal m v) = (v : ENNReal)
```

命名空间为 `FunctionalInequalities.Poincare`。前者表示 v 是有效常数，后者表示 v
也是最优常数。例子：标准 Gaussian 的常数为 1；均值 3、方差 4 的常数为 4；
方差 0 时是均值处的点质量，常数为 0。所有例子均通过同一通用接口检查。

阅读入口：

- [数学说明、例子、文件树与构建步骤](../../formalization/FunctionalInequalities/Poincare/Gaussian/README.md)。
- [逐项来源、Mathlib API 和依赖路线](../explorations/2026-09-04-gaussian-poincare-design.md)。
- [Lean 实际输出的 20 项完整签名](../explorations/2026-09-04-gaussian-poincare-signatures.txt)。
- [唯一 statement 入口及 7 项类型应用](../../solutions/LemPoincareGaussianOneDimensional.lean)。
- [本轮验证与语义审阅记录](../explorations/2026-09-04-gaussian-poincare-validation.md)。

## 请审阅的接口选择

1. 继续使用现有 `Admissible`：全局光滑、Gaussian L²、平方梯度能量可积。
2. 两个主结论不加正方差假设；只有密度证明的辅助接口使用 `v ≠ 0`。
3. 锐常数是方差 v。下界使用恒等函数，最优常数沿用 `ENNReal` 下确界。
4. 20 项声明由 2 个主结果与 18 个辅助接口组成。有限区间估计使用全局 C¹；
   Tonelli 接口允许非负被积函数取无穷，实积分步骤显式保留可积性。
5. 库文件分为 `Gaussian/Density.lean` 与 `Gaussian/Real.lean`；通用区间辅助引理
   先放在 Real 内。solution 只检查类型，证明完成后再组装一个 named certificate。

这些是候选契约。审阅可调整辅助接口；一旦批准冻结，独立证明阶段应保持批准的完整
签名、语义定义和 ledger 陈述。如需改变，先追加问题记录供人工处理。

## 来源与项目扩展

手稿的 [Gaussian covariance family](https://github.com/numina-functional-inequalities/kls-exploration/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/03-tier1-gaussian.tex#L10-L37)
是中心、正定协方差 Gaussian 的来源；本次取其一维 Poincaré 部分。归一化来自
[Definition 2.1](https://github.com/numina-functional-inequalities/kls-exploration/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L17-L25)，线性测试下界见
[Remark 3.8](https://github.com/numina-functional-inequalities/kls-exploration/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L108-L117)。

任意均值、零方差、精确光滑有限能量测试域和 `ENNReal` 编码是项目内的扩展或选择。
直接密度/区间积分路线是本地推导；手稿的上界通过 Bakry–Émery/LSI 得到。
每条 Lean docstring 标注具体归属，不把辅助引理假称为文献中的原定理。

Formech 仅作为阅读体验参考：数学含义、文件图、量词、例子、模型边界、可复制构建命令。
固定参考与具体采用方式见来源/API 记录；逐条引用与冻结流程沿用 KLS 自己的规范。

## 完整源码签名

以下按源文件列出全部候选签名，省略统一的 `:= by sorry`。所有新声明位于
`FunctionalInequalities.Poincare`；`Admissible.` 和 `Holds.` 是相应子命名空间。
实际 elaboration 输出另见完整签名快照，包含隐式参数、类型类及 universe 信息。

### Density.lean（7 项）

```lean
theorem hasDerivAt_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v)
      (-((x - m) / (v : ℝ)) * gaussianPDFReal m v x) x

theorem tendsto_gaussianPDFReal_atTop (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Tendsto (gaussianPDFReal m v) atTop (𝓝 0)

theorem tendsto_gaussianPDFReal_atBot (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Tendsto (gaussianPDFReal m v) atBot (𝓝 0)

theorem integrable_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Integrable (fun x : ℝ ↦ (x - m) * gaussianPDFReal m v x) volume

theorem integral_Ioi_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    (t : ℝ) (ht : m ≤ t) :
    (∫ x in Set.Ioi t, (x - m) * gaussianPDFReal m v x) =
      (v : ℝ) * gaussianPDFReal m v t

theorem integral_Iio_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    (t : ℝ) (ht : t ≤ m) :
    (∫ x in Set.Iio t, (m - x) * gaussianPDFReal m v x) =
      (v : ℝ) * gaussianPDFReal m v t

theorem integrable_gaussianReal_iff (m : ℝ) {v : NNReal} (hv : v ≠ 0) (f : ℝ → ℝ) :
    Integrable f (gaussianReal m v) ↔
      Integrable (fun x ↦ gaussianPDFReal m v x * f x) volume
```

### Real.lean（13 项）

```lean
theorem interval_sq_sub_le_integral_sq_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (a b : ℝ) (hab : a ≤ b) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ t in a..b, (deriv f t) ^ 2

theorem Admissible.variance_le_integral_sq_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Admissible μ f) (c : ℝ) :
    variance f μ ≤ ∫ x, (f x - c) ^ 2 ∂μ

theorem Admissible.integrable_gaussianPDFReal_mul_sq_sub {m : ℝ} {v : NNReal}
    {f : ℝ → ℝ} (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) (c : ℝ) :
    Integrable (fun x ↦ gaussianPDFReal m v x * (f x - c) ^ 2) volume

theorem Admissible.integrable_gaussianPDFReal_mul_sq_deriv {m : ℝ} {v : NNReal}
    {f : ℝ → ℝ} (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    Integrable (fun x ↦ gaussianPDFReal m v x * (deriv f x) ^ 2) volume

theorem lintegral_gaussian_right_triangle (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    (g : ℝ → ENNReal) (hg : Measurable g) :
    (∫⁻ x in Set.Ioi m,
      ENNReal.ofReal (x - m) * gaussianPDF m v x * ∫⁻ t in Set.Ioo m x, g t) =
      (v : ENNReal) * ∫⁻ t in Set.Ioi m, gaussianPDF m v t * g t

theorem lintegral_gaussian_left_triangle (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    (g : ℝ → ENNReal) (hg : Measurable g) :
    (∫⁻ x in Set.Iio m,
      ENNReal.ofReal (m - x) * gaussianPDF m v x * ∫⁻ t in Set.Ioo x m, g t) =
      (v : ENNReal) * ∫⁻ t in Set.Iio m, gaussianPDF m v t * g t

theorem Admissible.integral_Ioi_sq_sub_gaussian_le {m : ℝ} {v : NNReal} {f : ℝ → ℝ}
    (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    (∫ x in Set.Ioi m, gaussianPDFReal m v x * (f x - f m) ^ 2) ≤
      (v : ℝ) * ∫ x in Set.Ioi m, gaussianPDFReal m v x * (deriv f x) ^ 2

theorem Admissible.integral_Iio_sq_sub_gaussian_le {m : ℝ} {v : NNReal} {f : ℝ → ℝ}
    (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    (∫ x in Set.Iio m, gaussianPDFReal m v x * (f x - f m) ^ 2) ≤
      (v : ℝ) * ∫ x in Set.Iio m, gaussianPDFReal m v x * (deriv f x) ^ 2

theorem Admissible.integral_sq_sub_gaussian_le {m : ℝ} {v : NNReal} {f : ℝ → ℝ}
    (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    (∫ x, (f x - f m) ^ 2 ∂gaussianReal m v) ≤
      (v : ℝ) * energy (gaussianReal m v) f

theorem holds_gaussianReal_zero (m : ℝ) : Holds (gaussianReal m 0) 0

theorem holds_gaussianReal (m : ℝ) (v : NNReal) :
    Holds (gaussianReal m v) (v : ℝ)

theorem Holds.gaussianReal_variance_le {m : ℝ} {v : NNReal} {C : ℝ}
    (h : Holds (gaussianReal m v) C) : (v : ℝ) ≤ C

theorem constant_gaussianReal (m : ℝ) (v : NNReal) :
    constant (gaussianReal m v) = (v : ENNReal)
```

## 完整 ledger 快照

下面是本轮实际新增的节点。`checked_by: null` 是有意保留的未认证状态。

```json
{
  "id": "lem:poincare-gaussian-one-dimensional",
  "kind": "lemma",
  "status": "drafted",
  "source": "Gaussian covariance family fam:gaussian-covariance, modules/03-tier1-gaussian.tex lines 10-37, at kls-exploration commit cd4a894a0faf40c0180f80b1a31eec1fdb6cb576; Poincare normalization from Definition 2.1 and sharpness from Remark 3.8. Arbitrary means, the zero-variance Dirac case, the smooth finite-energy test domain, and the direct density proof route are explicit local specifications. Exact source correspondence and helper provenance: research/explorations/2026-09-04-gaussian-poincare-design.md.",
  "statement": "For every real mean m and every nonnegative variance v : NNReal, let gamma = ProbabilityTheory.gaussianReal m v, a probability measure on the real line. For the unchanged Poincare.Admissible class of globally smooth real-valued functions f with MemLp f 2 gamma and integrable squared canonical gradient, Poincare.Holds gamma (v : Real): for every such f, Var_gamma(f) <= (v : Real) * integral ||gradient f||^2 dgamma. On the real line the canonical gradient equals the ordinary derivative. Moreover Poincare.constant gamma = (v : ENNReal), where constant is the existing ENNReal infimum over finite NNReal constants satisfying Holds. The parameter v is the variance, not the standard deviation; the energy has no extra factor. No restriction on m or positivity premise on v occurs in either conclusion. At v = 0, gamma is Measure.dirac m and the fixed and optimal constants are zero. The identity test is admissible, has variance v and energy one, and supplies the matching lower bound for every finite valid constant. Positive-variance density helpers are used only under v != 0. No boundedness, compact support, additional derivative-integrability, test-function decay, or infimum-attainment assumption is imposed. This claim concerns the current smooth L2 finite-energy domain; it does not identify a closed Sobolev or spectral-gap domain or assert a multivariate, log-Sobolev, or transport-entropy theorem.",
  "lean_solution": "solutions/LemPoincareGaussianOneDimensional.lean",
  "checked_by": null
}
```

## 审阅版本标识与下一步

- 完整编译签名文件 SHA-256：`8103fa2acdfa4f2ed7df32b3d72496c65863de9c34da8b3c8c3148a893c763ca`。
- ledger 的 `statement` 字符串 SHA-256（UTF-8，不附加换行）：`07fa78f7a1a97217da6726a4f09fe043191413447e9a01715f850d9a38625574`。

这两个标识固定本轮候选版本，**不是人工冻结记录**。20 项声明、7 项类型应用以及
未来证书命题的类型检查已经通过；三项旧节点继续保持已证。验证细节以链接的本轮记录为准。
用户审阅后，若批准这些完整契约，再追加冻结记录并交给独立证明阶段。
