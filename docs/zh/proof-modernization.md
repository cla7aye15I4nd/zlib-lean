# CRC32 证明现代化与 libc 分层试点

本试点从 `85cd20c` 开始，使用仓库固定的 Lean 4.36.0。选取 `loadWord_ok`，因为这一个定理就同时要求证明四次按序读取都在界内、返回的小端字正确、整个堆保持原样。公开的 `Goal.crc32_safety` 及 `Goal.crc32_z_safety` 通过现有的 CRC 证明使用这条路径。[CRC 证明](../../ZlibF/Proof/crc32.c.lean) · [公共入口](../../ZlibF/Proof/public-crc-updates.lean) · [注册表](../../ZlibF/Results.lean)

## 分层方案

| 层 | 职责与入口 |
| --- | --- |
| C 运行时 | `C.M` 描述带堆的计算、正常返回和 `Fault`。`Ptr` 检查单次指针运算及访问。[Monad](../../ZlibF/Runtime/Monad.lean) · [Ptr](../../ZlibF/Runtime/Ptr.lean) |
| libc 的可执行模型 | 三个模块分别放置数组复制与填充、字节及字块的分配与释放、C 字符串长度及字面量。各操作的求值引理随定义放置。旧导入入口 `ZlibF.Runtime.Libc` 和 `ZlibF.Runtime.Alloc` 可继续使用。模块与原有 `LibcTables` 平级，`make emit` 会收集这些文件。[内存操作](../../ZlibF/Runtime/LibcMemory.lean) · [分配释放](../../ZlibF/Runtime/LibcAllocation.lean) · [字符串](../../ZlibF/Runtime/LibcCString.lean) · [汇总入口](../../ZlibF/Runtime/Libc.lean) |
| 证明接口 | `open scoped C.HeapWP` 启用与 `StateT Heap (Except Fault)` 对应的最弱前置条件实例。`okOn_iff_triple` 将原来的 `OkOn` 与一个排除所有故障的三元组双向转换。`Ptr.index_spec` 把读前已经成立的堆谓词带过一次成功的读取。[HeapWP](../../ZlibF/Proof/HeapWP.lean) |
| 写操作的框架规则 | `memcpyB_frame` 给出目标块复制后的精确内容，并保留调用者对另一字节块的任意谓词。前提要求两个块视图可读、目标可写、区间在界内，且源与目标是不同块或同块的不重叠区间。被保留的块号必须区别于目标块号。[libc 内存三元组](../../ZlibF/Proof/LibcMemory.lean) |

## 试点结果

`loadWord_ok` 展开固定的四次迭代后，将读取规则交给 `vcgen`。每步的界限由 `off + 4 ≤ bs.size` 推出，所携带的堆谓词是“当前堆等于初始堆”。`bx_wob` 用一个 `Fin 4` 索引覆盖四个字节位置，`grind` 完成掩码和索引运算。原来的四个专用定理各自成为该引理的一个实例。[证明实现](../../ZlibF/Proof/crc32.c.lean)

按非空声明行计数，包含签名和新增的局部辅助引理，排除注释、导入和局部选项。

| CRC 声明 | 基线 | 试点 |
| --- | ---: | ---: |
| 四个字节位置及掩码引理 | 53 | 20 |
| 连续读取四字节 `loadWord_ok` | 17 | 9 |
| 32 → 64 → 32 位往返 `u32_roundtrip` | 3 | 2 |
| 合计 | 73 | 31 |

这组声明约缩短 2.35 倍。公共层另外新增 `HeapWP.lean` 53 行及 `Proof/LibcMemory.lean` 25 行，这两个整文件数字包含注释、导入和空行。估算后续迁移的收益时，应同时计算公共规则的复用次数。[公共证明接口](../../ZlibF/Proof/HeapWP.lean) · [写入规则](../../ZlibF/Proof/LibcMemory.lean)

Lean 4.36 已标记 `Std.Do` 的 `mvcgen` 为弃用，并提供 `Std.WP` 的 `vcgen`。本试点只在使用它的定理上启用实验选项。`bv_decide` 在 `u32_roundtrip` 的预处理阶段即可完成证明。直接用它证明 `and_xor64` 时，实测的公理列表多出 `_native.bv_decide.ax_…`。后续使用 SAT 路径的候选引理都需要检查公理依赖，仓库注册表只接受 `propext`、`Classical.choice`、`Quot.sound`。[固定版本的弃用声明](https://github.com/leanprover/lean4/blob/v4.36.0/src/lean/Std/Tactic/Do/Syntax.lean) · [原生求值机制](https://github.com/leanprover/lean4/blob/v4.36.0/src/lean/Lean/Meta/Native.lean) · [注册表检查器](../../ZlibF/ResultsCheck.lean)

## 安全结论的范围

对固定的 x86-64 Linux LP64 小端构建，公开 CRC 目标要求 `CrcGlobals`，并要求 `BufferBytes` 描述可读缓冲区或空指针查询。结论是正常返回且堆完全相同，因此同时排除 `Fault.ub` 与 `Fault.outOfFuel`。四字节定理本身只适用于活对象中满足长度条件的非空视图。模型逐字节拼字，C 源码按字读取时的严格别名条件仍由源码审查承担。[固定版本](../../pins.json) · [调用条件](../../ZlibF/Spec/Common/Checksums.lean) · [安全目标](../../ZlibF/Spec/Safety/Checksums.lean) · [读取模型](../../ZlibF/Zlib/crc32.c.lean) · [模型边界](../en/model-limits.md)

## 验证记录

`make proof` 成功退出。构建以警告为错误，注册表列出 305 个目标、243 个已有证明、62 个待证明，113 个必需目标全部有证明。`leanchecker --fresh ZlibF.Results` 在新的内核环境中完成回放。为让现有的 `stable_fast_inflate_fast` 在原心跳预算内完成，其证明只搜索外层函数实际调用的操作和循环体规则。[注册表](../../ZlibF/Results.lean) · [inflate 借用保持证明](../../ZlibF/Proof/inflate.c.borrow-stable-dispatch-fast.lean)

CRC 差分驱动在 macOS arm64 上对固定源码和编译后的 Lean 模型运行，6,534 个输入输出一致。`make test` 通过了 Lean 移位检查和 9 个 Python 测试。`make audit` 生成了本机的 Clang 比较报告，找到了全部 86 个公开 API。单独检查 `loadWord_ok`、`bx_wob`、`u32_roundtrip` 和两条内存访问规则的公理依赖，均在注册表许可范围内。[差分驱动](../../tools/differential.py) · [审计命令与目标平台](../../README.md#run-the-comparison)

本机的全套差分测试在 `gz` 的第一个输入出现差异。对打完补丁的 `zutil.h` 运行系统 Clang 的预处理器，得到 `OS_CODE = 19`，gzip 头中的对应字节为 `0x13`。固定 Linux 模型的 `C.OS_CODE = 3`，对应字节为 `0x03`。单独补跑余下的驱动时，`deflate` 在第 272 个输入遇到同一字节差异。其余八个驱动共 44,658 个输入全部匹配，其中包括 CRC 的 6,534 个输入。[平台常量](../../ZlibF/Runtime/Schema.lean) · [固定目标上的差分任务](../../.github/workflows/fidelity.yml)

## 后续迁移计划

1. 先将同一条 CRC 证明链中的 `body8_ok` 改写为三元组。记录新增规则行数、局部证明行数、公理和构建时间，用第二次复用的数据估算收益。
2. 在 inflate 的窗口复制调用处试用 `memcpyB_frame`。若调用方要保留目标块内部的另一区间，则补充区间级规则，并用相邻、重叠和零长度区间验证边界。
3. 再选用 `cwhile_ok` 的循环建立带不变量的三元组。保留剩余迭代数小于 fuel 的义务，在原有公开目标下回放注册表后再扩大范围。[CRC 候选](../../ZlibF/Proof/crc32.c.lean) · [窗口复制候选](../../ZlibF/Proof/inflate.c.copy-window-prefix.lean) · [循环规则](../../ZlibF/Runtime/Monad.lean)

## 复现

在工作区根目录运行以下命令。第一条构建试点，第二条构建注册表并在新内核环境中回放。最后两条初始化固定的 C 源码并用 CRC 驱动对比执行结果。[构建目标](../../Makefile) · [差分驱动](../../tools/differential.py)

```sh
lake build --wfail ZlibF.Proof.LibcMemory 'ZlibF.Proof.«crc32.c»'
make proof
git submodule update --init upstream
python3 tools/differential.py --only crc32
```
