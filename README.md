# Theorem 9.9: Gaussian AFT in Lean

这是 Learning with Algebraic Rounding 论文中定理 9.9 的独立 Lean 证明快照。先打开根目录的 **[Theorem99.lean](Theorem99.lean)**，阅读 `theorem_9_9` 的完整声明与证明，即可核对主要量词和结论。

This repository formalizes Theorem 9.9 in an explicit counted binary-operation model. It contains the proof sources and locked dependencies, without the manuscript or generated build artifacts.

## 从哪里看

- **[`theorem_9_9`](Theorem99.lean)**：对每个固定精度阶，存在同一组不依赖安全参数的有限程序数据；汇总多项式公平随机带长度、每条随机带的最坏操作成本、整数仿射输出与模可逆性、实际执行的输出律、最终逆多项式精度及论文中的展开误差界。它还列出可忽略余项和变换后公开矩阵的精确均匀性与独立性。
- **[`evaluator_correct_and_polynomial`](Theorem99.lean)**：确定性仿射求值器的正确性与成本，适用于任意相应形状的整数矩阵、偏移和输入编码；成本多项式依赖安全参数及实际输入编码长度。
- [ActualConstructiveSampler.lean](CurrentAFT/ActualConstructiveSampler.lean)：原顶层构造、精度和定量误差定理。
- [ActualConstructiveProgram.lean](CurrentAFT/ActualConstructiveProgram.lean)：实际程序、校准表生产与源独立公开实验的连接。
- [ActualAffineEvaluator.lean](CurrentAFT/ActualAffineEvaluator.lean)：独立确定性求值器。

固定精度阶先于程序数据和多项式预算选定；同一公开参数族随后用于所有安全参数。结论不要求一个以精度阶为输入、同时对所有精度阶统一高效的算法。

## 记号对照

| 论文概念 | Lean 中的具体定义 |
| --- | --- |
| 安全参数、精度阶 | `security`、`accuracyOrder` |
| 校准阶数 (D=4a+267) | `CurrentAFT.Parameters.calibrationOrder accuracyOrder` |
| `base`、模数 (q)、总维度 | `Parameters.base`、`Parameters.modulus`、`Parameters.dimension` |
| 实际公平比特采样程序 | `ActualConstructiveSampler.run` |
| 整数矩阵与偏移 | `CurrentBinaryAffineEmitter.matrix`、`CurrentBinaryAffineEmitter.offset` |
| 采样器作用于独立 Gaussian 源后的律 | `ActualConstructiveSampler.law`，由 `law_eq` 连接实际程序 |
| 真实固定标签的均匀零纤维 | `CurrentZeroFiber.uniformFiber` |
| 数值实现误差 | `ActualConstructiveSampler.numericalError` |
| 分析中的可忽略余项 | `ActualGaussianRemainder.remainder` |

以上省略的命名空间前缀均为 `CurrentAFT`；根文件中的简写以其实际定义为准。

## 复现验证

安装 [elan](https://github.com/leanprover/elan) 后，在仓库根目录运行：

```sh
lake exe cache get
./check.sh
```

使用已提交的 `lean-toolchain` 和 `lake-manifest.json`，不要先运行 `lake update`。工具链固定为 Lean `v4.29.0-rc1`；mathlib 固定在 `33a7291a345d718bca41f8ae8a9bae365d8f2a3e`。验证入口和审计规则以 `check.sh` 及审计源码为准。

本快照的初次构建与审计见 [原始验证记录](provenance/verification.md)；精简后的源码清单和复验见 [清理验证记录](provenance/cleanup-2026-11-04.md)。

## 复杂度结论的边界

`work` 来自明确的 Boolean/list/counter 二进制操作计数，包含实际数组读写、随机带解码和中间整数的位长。根定理证明的是这个模型下的多项式最坏成本。**本快照没有另外形式化该模型到标准概率图灵机的通用模拟定理**，因此不声称标准图灵机层面的 PPT 模拟也已由 Lean 验证。

Lean 检查所编码命题的证明；论文与形式化规格的对应仍需阅读根定理及其引用定义。公理审计的允许项为 `propext`、`Classical.choice` 和 `Quot.sound`。

## 来源

上游论文仓库提交：`176d128e3361f975a3c7e2f889fdc5f2c96c1d29`。保留的原证明模块逐字节保持不变；根入口及独立验证文件用于本仓库导航与复现。当前只保留 `Theorem99.lean` 及审计所需的完整依赖闭包，共 1794 个 Lean 文件。仍被证明调用的旧命名模块继续保留，不能按文件名中的版本标记删除。

原模块文件快照见 [upstream-lean-snapshot.json](provenance/upstream-lean-snapshot.json)，论文对齐记录见 [upstream-manuscript-manifest.json](provenance/upstream-manuscript-manifest.json)。本仓库仅包含证明快照，不包含论文 LaTeX、PDF、`.lake` 缓存或历史 Git 记录；首次构建会在本地生成 `.lake`。

清理时删除了 13 个未被根定理使用的模块，具体路径及原始哈希见 [pruned-modules.json](provenance/pruned-modules.json)。`check.sh` 同时检查保留文件的原始哈希、删除清单和依赖可达性，缺失依赖或新增孤立模块都会使检查失败。
