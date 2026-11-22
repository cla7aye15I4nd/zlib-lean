# zlib 整库安全定理与 libc 证明现代化

固定目标是打完六个补丁的 x86-64 Linux LP64 静态库，使用默认分配器。整库定理 `ZlibF.Results.whole_library_safety` 覆盖 86 个文档化公开入口，以及 deflate、inflate、inflateBack 和 gzip 四种流式协议。各入口保留原合同的内存、分配、回调和返回条件。[覆盖清单](../../tests/public-api.json) · [定理陈述](../../ZlibF/Spec/Safety/WholeLibrary.lean) · [证明](../../ZlibF/Results.lean)

```lean
import ZlibF.Results

open ZlibF.Results ZlibF.Spec.Public

example : Goal.inflateCopy_safety := whole_library_safety.1 .inflateCopy
example : Goal.gz_sequence_safety := whole_library_safety.2 .gzip
```

流式定理从一个可达的流或句柄出发，按该协议允许的调用传递状态、写入边界和所有权。gzip 的六个读取入口在没有读取预算时排除 `Fault.ub`，还可能出现 `Fault.outOfFuel`。在可达句柄上，对一般读取调用保证返回，要满足合同的描述符及预算条件。空句柄的拒绝分支和已有缓冲输出的 `gzgetc` 宏分支都可以直接证明返回。回调解码的单次输入必须严格小于 `2^48` 字节。C 源码层面仍依赖手工翻译和运行时模型，两个已登记的指针算术例外也适用于整库结论。[流式合同](../../ZlibF/Spec/Safety/Sequences.lean) · [gzip 合同](../../ZlibF/Spec/Safety/GzSafety.lean) · [可信基础](../en/trusted-base.md) · [UB 例外](../en/model-limits.md)

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

## 首轮试点验证记录

`make proof` 成功退出。构建以警告为错误，注册表列出 305 个目标、243 个已有证明、62 个待证明，113 个必需目标全部有证明。`leanchecker --fresh ZlibF.Results` 在新的内核环境中完成回放。为让现有的 `stable_fast_inflate_fast` 在原心跳预算内完成，其证明只搜索外层函数实际调用的操作和循环体规则。[注册表](../../ZlibF/Results.lean) · [inflate 借用保持证明](../../ZlibF/Proof/inflate.c.borrow-stable-dispatch-fast.lean)

CRC 差分驱动在 macOS arm64 上对固定源码和编译后的 Lean 模型运行，6,534 个输入输出一致。`make test` 通过了 Lean 移位检查和 9 个 Python 测试。`make audit` 生成了本机的 Clang 比较报告，找到了全部 86 个公开 API。单独检查 `loadWord_ok`、`bx_wob`、`u32_roundtrip` 和两条内存访问规则的公理依赖，均在注册表许可范围内。[差分驱动](../../tools/differential.py) · [审计命令与目标平台](../../README.md#run-the-comparison)

macOS 上的全套差分测试在 `gz` 的第一个输入出现差异。对打完补丁的 `zutil.h` 运行系统 Clang 的预处理器，得到 `OS_CODE = 19`，gzip 头中的对应字节为 `0x13`。固定 Linux 模型的 `C.OS_CODE = 3`，对应字节为 `0x03`。单独补跑余下的驱动时，`deflate` 在第 272 个输入遇到同一字节差异。其余八个驱动共 44,658 个输入全部匹配，其中包括 CRC 的 6,534 个输入。[平台常量](../../ZlibF/Runtime/Schema.lean) · [固定目标上的差分任务](../../.github/workflows/fidelity.yml)

## 后续迁移实施

| 声明 | 原证明行数 | 新证明行数 | 共享规则 |
| --- | ---: | ---: | --- |
| `body1_ok` | 2 | 2 | `crcByte_spec` |
| `body8_ok` | 10 | 2 | `crcByte_spec` |
| `loop1_ok` | 36 | 16 | `cwhile_steps_spec` |
| `loop8_ok` | 41 | 18 | `cwhile_steps_spec` |

表中只统计 `:= by` 后的非空证明行。两个字节处理函数共用的规则含签名共 8 行。单字节和八字节循环共用的规则含签名共 17 行。循环必须证明迭代数严格小于 fuel，最后一次条件检查也消耗一步。按这四个调用点的证明体加上新增共享规则计算，89 行变为 63 行。[CRC 证明](../../ZlibF/Proof/crc32.c.lean) · [循环规则](../../ZlibF/Proof/CountedLoop.lean)

在 Apple M1 Pro 上，使用 Lean 4.36.0、三个线程、同一个已构建的 CRC 导入，分别预热一次，然后交错顺序、每种各运行六次全新的 Lean 进程。单独编译 `body8_ok` 的耗时中位数，手写证明为 0.402 秒，使用已编译规则为 0.466 秒，同时编译规则和调用点为 0.477 秒。这是包含进程启动和导入的局部测量。[CRC 证明](../../ZlibF/Proof/crc32.c.lean)

`memcpyB_range_frame` 同时保留另一块的谓词和目标写入区间之外的每个元素。在 `inflateCopy` 的动态表、固定表两条成功路径上，证明一直跟到整个函数返回，源窗口内容保持不变，新窗口中从 `whave` 到末尾的字节保持分配时的值。两条路径复用已有执行见证后，五个窗口证明文件合计净减少 433 行。边界测试覆盖首尾相接的复制、重叠故障、活块末尾的零长度复制、空指针零长度故障，以及刚好缺一次条件检查的 fuel。[区间规则](../../ZlibF/Proof/LibcMemory.lean) · [动态表](../../ZlibF/Proof/inflate.c.copy-dynamic-window.lean) · [固定表](../../ZlibF/Proof/inflate.c.copy-fixed-window.lean) · [测试](../../tests/SafetyRules.lean)

## 整库验证结果

`make library-safety` 成功退出。Lean 以警告为错误完成构建，`leanchecker --fresh ZlibF.Results` 在新内核环境回放整库，随后从固定头文件核对了全部 86 个公开入口。包括聚合定理在内，注册表现有 306 个目标，244 个已有证明，114 个必需目标全部通过。其余 62 个是功能目标。用 `#print axioms` 检查整库定理，依赖仅有 `propext`、`Classical.choice` 和 `Quot.sound`。[注册表](../../ZlibF/Results.lean) · [覆盖检查](../../tools/check_public_safety.py) · [构建目标](../../Makefile)

`make test` 通过两份 Lean 回归文件及 17 个 Python 测试，覆盖检查会拒绝遗漏入口、调换实现或协议、删去必需证明等情况。macOS 上的 `make audit` 在独立 C 源码和生成代码中定位到 86 个公开入口，同时报告 15 个翻译单元的 C AST 存在差异。[回归测试](../../tests/test_public_safety.py) · [AST 比较说明](../../README.md#run-the-comparison)

Ubuntu 24.04.5 x86-64 LP64 来宾使用 Clang 18.1.3 和 Lean 4.36.0 编译并执行原始 `make differential`。十个驱动的 49,459 个输入输出全部一致，包括 CRC 的 6,534 个、gzip 的 973 个和 deflate 的 3,828 个。对先前的两个差异样本，Linux C 和 Lean 的完整输出逐字节一致，gzip 头的 OS 字段均为 `0x03`。来宾使用快照 `53460cf`，已核对该快照的可执行模型、驱动、生成器、固定源码和补丁与最终证明版本相同。[差分测试实现](../../tools/differential.py) · [固定版本](../../pins.json)

## 复现

在工作区根目录运行。差分命令使用仓库固定的输入生成器；复现目标平台结果需要 Ubuntu 24.04 x86-64 和默认 LP64 配置。[构建目标](../../Makefile) · [差分驱动](../../tools/differential.py)

```sh
git submodule update --init upstream
make library-safety
make audit
make test
CC=/usr/bin/clang-18 make differential
```
