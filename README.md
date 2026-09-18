# v4.tex 的 Lean 形式化工程

**当前状态：部分形式化。现有模块已通过 Lean 编译与公理依赖审计，但论文主定理尚未完成无条件的 Lean 验证。**

原稿为 `../3:2-tough-2K_2-free/论文/v4.tex`。`source/v4.tex` 保留了本次处理的副本；`source/metadata.json` 记录 SHA-256。原文件没有修改。

## 已验证的内容

- 图、独立集、最大独立集、邻域、删点后的连通分支、3/2-toughness、简单路径、简单圈与 Hamilton 性的定义。Hamilton 性已与 mathlib 的定义在至少三个顶点时证明等价。
- Fact 2.1 的三个结构性质，包括独立集邻域的可比性、邻域并由一个顶点实现，以及删点后含边的连通分支至多一个。
- Claim 2.1：最长的合格路径是支配路径；包含真实的路径延长构造。
- 阈值删除、交换、二换一的计数，以及有界严格增长序列的终止论证。
- 两次有限极大化的选择；给定前驱集合性质后的最大独立集交换论证。
- 第 4 节的邻域并集恒等式、两个集合计数上界、孤立点贡献的真实连通分支下界，以及最终韧性矛盾。
- 给定 `FinalConfiguration` 后的最终推导。**构造该配置仍是待证内容。**
- Chvátal 例子的具体图、split 性、2K₂-free 性、顶点数和阈值逼近；例子的韧性及非 Hamilton 性使用文献黑箱，随后证明了对每个实数 `t < 3/2` 的 sharpness 结论。

详细对应见 [STATUS.md](STATUS.md)。不要把这里的辅助定理数量解释为论文已形式化的比例。

## 尚未完成

论文中的前驱结构引理、路径/圈阶数界、受限圈族推论、近生成圈、两个遗漏顶点引理、结构引理的主要部分，以及旋转端点集合与三个计数 claim 的构造证明仍未全部形式化。

`Broersma/Manuscript.lean` 用 `def ...Statement : Prop` 保存已转写的待证命题。这些定义不宣称命题为真。受限圈族推论的阶段闭包条件及完整旋转过程尚未逐条转写。

`Broersma/MainReduction.lean` 中的

```lean
theorem main_of_configuration (G : SimpleGraph V)
    (construct : InternalConstruction G) : MainTheoremStatement G
```

明确带有尚未证明的内部假设 `construct`。当前工程没有无条件的 `Broersma.main`。`FinalConfiguration` 是足以推出矛盾的数据与性质记录；其字段中的三个 claim 是假设，并非在声明结构时就获得了证明。

## 文献黑箱

四项自定义公理集中在 `Broersma/External.lean`，各有出处：

1. Kratsch–Lehel–Müller：3/2-tough split 图的 Hamilton 性。
2. Ota–Sanka，Proposition 1.6：2-factor 的存在。
3. Ota–Sanka，Lemma 3.3 及其证明的近生成圈特例：后继集独立性与度上界。
4. Chvátal 已发表的 split 图例子的精确韧性、非 Hamilton 性和无 2-factor 性；仅用于 sharpness。

没有把本文内部的未证引理声明为公理，没有使用 `sorry`、`admit` 或 `native_decide`。证明允许 Lean/mathlib 通常使用的 `propext`、`Classical.choice` 和 `Quot.sound`。`Audit.lean` 自动拒绝任何额外的公理依赖。

## 运行验证

固定 Lean 与 mathlib 为 `v4.33.0-rc2`，mathlib commit 为 `51e6992efd06126df61a496bebf8f49482a4e129`。Lake 的依赖版本记录在 `lake-manifest.json`。本机已复制可用的依赖缓存，工程不依赖另一个项目的绝对导入路径。

在本机工程目录或克隆后的仓库根目录执行：

```sh
lake build
python3 verify.py
```

默认验证命令检查已完成模块，并同时报告主定理检查的结果。**退出码 0 仅表示部分证明库和公理审计通过。**

```sh
python3 verify.py --require-complete
```

此命令还会要求主定理仅从原文三个假设推出结论。当前预期退出码为 **2**，原因是主定理尚未证明。它不会接受带 `InternalConstruction` 附加假设的条件版本。

实际日志保存在 `verification/`：`build.log`、`axioms.log`、`complete-main.log` 和 `report.json`。

在未附带缓存的新机器上，先安装指定 Lean，然后运行 `lake update` 和 `lake exe cache get`；这些命令需要网络。

## 继续补全的位置

优先完成 `Manuscript.lean` 的前驱结构与圈/路径界，并实现真实旋转构造。最终需要证明 `InternalConstruction G`，再通过 `main_of_configuration` 定义无条件的 `Broersma.main`。完成后运行严格验证，并核对 `#print axioms Broersma.main` 仅包含上述允许的文献公理及 Lean 的基础公理。
