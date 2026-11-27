# Uniqueness of the two-axis genus-one helicoid

本仓库提供双轴亏格一螺旋面唯一性论文及其配套的 Lean 4 形式化源码。
本文件所在的 `two-axis-helicoid-uniqueness/` 文件夹是 GitHub 仓库根目录。
整稿入口为 [`TwoAxisHelicoidManuscript.lean`](TwoAxisHelicoidManuscript.lean)，包含其完整的 **8,419 个项目模块**，约 **4.11 GiB** 源码。
其中大量 `TraceData*.lean` 文件是由 Lean 内核检查的计算证书，属于证明源码。

## 论文

*Uniqueness of the two-axis genus-one helicoid*

| 文件 | 内容 |
| --- | --- |
| [论文 PDF](paper/two-axis-helicoid-uniqueness.pdf) | 排版后的完整论文，22 页 |
| [论文 Markdown](paper/two-axis-helicoid-uniqueness.md) | 可阅读和修改的论文正文 |

论文放在仓库内的 `paper/` 目录，与形式化源码一起发布。§9 说明数学命题与 Lean 定义、验证结果及适用范围的对应，附录 A 给出计算证书和复现说明。当前版本为工作稿，作者与正式引用信息待补。

## 环境

| 组件 | 固定版本 |
| --- | --- |
| Lean | `4.35.0`，由 `lean-toolchain` 指定 |
| Lean 编译器提交 | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| mathlib 的间接依赖 | 由 `lake-manifest.json` 固定 |

已验证工程使用 Linux x86-64。需要 Git 和 [elan](https://github.com/leanprover/elan)，以及访问 GitHub 和 mathlib 缓存服务的网络。
Lean、mathlib、第三方源码和编译缓存由工具下载，不包含在本目录中。
完整构建还需要为依赖及编译产物预留磁盘和内存；4.11 GiB 仅指项目源码。

## 编译与审计

获取仓库并编译、审计：

```bash
git clone https://github.com/intern233/two-axis-helicoid-uniqueness.git
cd two-axis-helicoid-uniqueness
elan toolchain install leanprover/lean4:v4.35.0
lake exe cache get
lake build
lake env lean tools/StatementCheck.lean
lake env lean tools/Audit.lean
```

`lake exe cache get` 下载 mathlib 的预编译依赖；`lake build` 编译本项目。
默认构建同时包含 `TwoAxisHelicoid` 与 `TwoAxisHelicoidManuscript` 两个根模块及其递归依赖，无需重新生成数值证书。
复现时保留提交中的 `lake-manifest.json`，无需执行 `lake update`。
本目录不需要原工作区、VPN、服务器账户或任何绝对路径配置。

若 `cache get` 使用的 curl 提示 OpenSSL 证书文件路径错误，可用 `CURL_CA_BUNDLE` 指定系统已有的 CA 证书文件。例如，在存在该文件的 RHEL/CentOS 系统上：

```bash
CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt lake exe cache get
```

`StatementCheck.lean` 检查五个主要结论的完整类型，并打印其公理依赖。
`Audit.lean` 遍历整稿入口导入的全部 `TwoAxisHelicoid` 命名空间声明，检查其公理依赖仅为
`propext`、`Classical.choice`、`Quot.sound`，并检查 617 个原稿见证声明存在且不是公理或 unsafe 声明。
任何检查失败都会令 Lean 返回非零退出码。

## 主要入口与命题范围

| 源文件 | 内容 |
| --- | --- |
| [`TwoAxisHelicoidManuscript.lean`](TwoAxisHelicoidManuscript.lean) | 整稿证明、原路径区间证书及附录的统一入口 |
| [`TwoAxisHelicoid/ManuscriptGeometricTheoremOneOne.lean`](TwoAxisHelicoid/ManuscriptGeometricTheoremOneOne.lean) | 几何表述的主定理 `TwoAxisHelicoid.manuscript_geometric_theorem_one_one` |
| [`TwoAxisHelicoid/ManuscriptTheoremOneOne.lean`](TwoAxisHelicoid/ManuscriptTheoremOneOne.lean) | 归一化及物理坐标下的主唯一性定理 |
| [`tools/StatementCheck.lean`](tools/StatementCheck.lean) | 主命题类型、嵌入代表及同一封帽 Gauss 纤维的检查 |
| [`tools/Audit.lean`](tools/Audit.lean) | 全部导入声明的公理审计和原稿见证检查 |
| [`source_inventory.json`](source_inventory.json) | 8,419 个证明模块的路径、大小、SHA-256 和项目内依赖 |

主定理针对原稿 §1 与 §2.2 明确规定的曲面类：具有完整双轴、一次穿孔环面拓扑、光滑适当嵌入的极小曲面，且紧集外具有单层 C¹ 螺旋法向图。
类型与证明可直接在上述 Lean 文件中检查。
更宽曲面类的某些端结构归约，以及附录 B.3 的完整几何紧性定理，仍以明确的文献输入或前提出现；附录 B.3 的替代紧性路线不属于正文主唯一性定理的依赖。

## 源码快照

本目录按整稿入口的完整依赖图整理，模块和命名空间统一采用数学主题名称。逐文件检查完成一致的命名替换后，服务器全量重编发现一处加法化简未闭合；已在 `SpinGeneratorCoreRetraction.lean` 中显式补入 `add_assoc`，并通过该模块的重新编译。数学定义和定理陈述保持原样。
`source_inventory.json` 仅记录这 8,419 个证明模块，不含两个独立检查入口。
原工程的历史实验文件、未使用的旧证书模块、日志、编译产物及机器配置未收录。
构建输出和本机缓存已列入 `.gitignore`。

2026 年 11 月 27 日，发布命名下的全部 8,419 个项目模块已在 Linux 服务器上通过标准 Lake 从源码编译。构建从空的项目产物目录开始，续编时仅复用本次已经生成的项目产物；mathlib 使用固定版本的预编译依赖缓存。
随后五项主要结论检查、368,507 个项目声明的公理审计和 617 个原稿见证检查全部通过，仅使用上述三项标准公理。最后执行 `lake --no-build build`，确认所有目标均为最新。
独立复现请运行上面的编译和审计命令。并行量可通过 `LEAN_NUM_THREADS` 设置；本次后段构建使用 64 个工作线程。

## 发布前事项

本快照尚未指定开源许可证。正式发布前，请由权利人确定许可证、作者及引用信息。
第三方依赖遵循各自的许可证。
