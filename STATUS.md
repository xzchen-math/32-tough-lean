# 验证状态与原稿对应

**总体：PARTIAL；主定理未完成 Lean 验证。**

本表中的“已证”只指相应 Lean 命题，包括其显式前提。尤其是条件推导通过编译，不表示其前提已经建立。

| 原稿标签/步骤 | Lean 位置 | 状态 |
| --- | --- | --- |
| 图、韧性、独立集、路径、圈 | `Definitions.lean`, `Basic.lean`, `Cycles.lean` | 已定义并验证主要连接性质 |
| `fact:2K2-property` (i)–(iii) | `TwoK2Free.lean` | 已证 |
| `lem:predecessor-structure` | `Manuscript.PathPredecessorStatement`, `CyclePredecessorStatement` | 命题已转写，证明开放 |
| `lem:path` (i) | `Manuscript.PathExistenceStatement` | 命题已转写，证明开放 |
| `claim:U-independent` | `longest_admissible_path_dominating` | 已证，包含实际延长路径 |
| `lem:path` (ii), (iii) | `Manuscript.PathBoundStatement`, `PathCoverBoundStatement` | 完整证明开放；部分计数在 `Descent.lean` 已证 |
| `lem:cycle` | `Manuscript.CycleBoundStatement` | 完整证明开放；部分计数与终止论证已证 |
| `claim:cycle-restricted` | — | 阶段闭包条件与推论尚未完整转写或证明 |
| `lem:n-1cycle` | `Manuscript.NearSpanningCycleStatement` | 完整证明开放；split completion 的构造、韧性保持及 KLM 应用已证 |
| 对 `(I,u)` 的两次极值选择 | `exists_extremalPair` | 给定每个最大独立集外存在 `D` 中顶点时已证 |
| `eq:s3-D-bound` | `ExtremalPair.degree_bound` | 已证 |
| `prop:s3-omitted-vertices` | `Manuscript.OmittedVerticesStatement` | 命题已转写，证明开放 |
| `lem:s3-structure` (i) | `Degree.lean` | 由两项 Ota–Sanka 黑箱推出 |
| `lem:s3-structure` (ii), (iii) | `Manuscript.CycleStructure`, `StructureStatement` | 命题已转写，证明开放 |
| `lem:secindependent` | `ExtremalPair.exchange` | 给定 `K₀` 的独立性、前驱覆盖等显式性质时，交换论证已证；这些性质的构造仍开放 |
| `W` 的独立性 | `TwoK2Free.independent_common_nonneighbors` | 给定与固定边两端反完全时已证；旋转端点性质仍开放 |
| `W \ I = K₀` 的极大性比较 | `endpoint_set_exchange` | 给定包含关系和反完全性质时已证 |
| `eq:s4-rotation-properties` | — | 路径旋转闭包与邻域等式未完成 |
| `claim:n`, `claim:h`, `claim:|W|+|V(H)setminus I|` | `FinalConfiguration.claim_n`, `.claim_h`, `.claim_WH` | 当前为配置字段中的假设，尚未构造证明 |
| 第一个 `|N(I₀)|` 上界 | `FinalConfiguration.first_bound` | 给定上述配置时已证 |
| `S = T ∪ T'` | `neighborhood_eq_union` | 从实际边与反完全性质已证 |
| 第二个 `|N(I₀)|` 上界 | `FinalConfiguration.second_bound` | 给定配置中的度界时已证 |
| `ω(G-S) ≥ k+1` | `components_neighborhood_ge` | 对真实连通分支计数已证 |
| 最终韧性矛盾 | `cut_contradiction`, `FinalConfiguration.impossible` | 已证 |
| `thm:main` | `MainTheoremStatement`, `main_of_configuration` | **仅有条件归约；无条件主定理未证明** |
| 最优性 | `Constructions.lean`, `Sharpness.lean` | 具体图和阈值算术已证；例子的韧性、非 Hamilton 性和无 2-factor 性引用 Chvátal 黑箱 |

## 严格验收条件

1. 实现未完成的内部证明，不增加本文内部黑箱。
2. 给出只有 `n ≥ 3`、`ToughThreeHalves G` 和 `TwoK2Free G` 三个数学假设的 `Broersma.main`。
3. `python3 verify.py --require-complete` 成功。
4. 公理审计通过，且主定理不依赖最优性用的 Chvátal 黑箱（该黑箱只与下界例子有关）。

`verification/report.json` 的 `complete_main_verified` 当前为 `false`。当前代码的编译成功不能用作“全文证明已通过 Lean”的声明。
