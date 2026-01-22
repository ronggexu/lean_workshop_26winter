# 凸分析在Lean/mathlib中的形式化概况

2026/1/23

## 目录位置和核心文件

**目录位置**： `Mathlib.Analysis.Convex`

**核心文件**

- `Basic.lean` 凸集的定义及相关命题

- `Conbination.lean` 凸组合的定义及相关命题

- `Function.lean` 凸、凹函数的定义及相关命题

- `Hull.lean` 凸包的定义及相关命题

- `Topology.lean` 凸集的拓扑性质 

- `Segment.lean` 利用凸组合定义线段

## 主要定义

### `Convex` 凸集

用法为 `Convex 𝕜 s`，其中 `𝕜` 是凸组合系数所采取的（半环）标量（例如 ℝ，ℚ），`s` 是一个带偏序、加法交换，可以做标量乘法的集合.

定义采取 `starConvex 𝕜 x s` 间接定义，其中 `x` 是集合 `s` 中一点.   
星形集的定义是指从点 $x$ 到 $s$ 内任意一点的线段都包含于 `s` 内.

![](http://shuxueji.com/media/img/48315/thumb/220px-Star_domain.svg.png)

```lean
def StarConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
[AddCommMonoid E] [SMul 𝕜 E] (x : E) (s : Set E) : Prop :=
∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s

def Convex : Prop :=
∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s
```

### `convexHull` 取闭包
用法为 `convexHull 𝕜 s`，表示取 `s` 的闭包.
```lean
def convexHull : ClosureOperator (Set E) := .ofCompletePred (Convex 𝕜) fun _ ↦ convex_sInter
```
这个定义利用了 Lean 的取闭包算子 `ClosureOperator`，找到包含 $s$ 的最小的凸集，利用 `convex_sInter`（闭包的交依然是闭包）这一性质.

数学对应：$\text{convexHull}(s) = \bigcap \{ t \mid s \subseteq t, t \text{ 凸} \}$

### `ConvexOn` 凸函数

用法为 `ConvexOn 𝕜 s f`，表示函数 $f$ 在集合 $s$ 上是凸的. 定义包含两个方面：
- $s$ 是凸集 `Convex 𝕜 s`
- 凸组合处函数值小于等于端点函数值的对应凸组合

```lean
def ConvexOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y
```