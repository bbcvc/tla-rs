<h1 align="center">tla-rs</h1>

<p align="center">
  <b>用 Rust 编写的高速 TLA+ 模型检查器，每个模型的状态数都与 TLC 完全相同。</b>
</p>

<p align="center">
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/license-MIT-blue"></a>
  <img alt="Rust" src="https://img.shields.io/badge/rust-1.85%2B-orange">
  <img alt="Conformance" src="https://img.shields.io/badge/TLC%20conformance-766%2F772%20match%2C%200%20mismatch-brightgreen">
</p>

<p align="center">
  <a href="README.md">English</a> | 简体中文
</p>

---

```console
$ tla-rs MCLamportMutex.tla -workers 4
Running breadth-first search Model-Checking with fp 0 and seed 0 with 4 workers on 11 cores ...
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2026-11-05 14:35:25.
Model checking completed. No error has been found.
2729079 states generated, 724274 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 61.
Finished in 04s at (2026-11-05 14:35:30)
```

## 亮点

- 🎯 **结果与 TLC 完全一致。** 结论、违反的属性名、生成状态数、不同状态数、搜索深度和反例长度都和 TLC 一样。我们用 823 条 TLC 运行记录做了验证，没有任何一个模型的结果与 TLC 不同；TLC 有结论的模型，除了超时的以外全部一致。
- ⚡ **不需要 JVM，启动即开跑。** 小规约几毫秒就能检查完。TLC 在这 823 个模型上的中位耗时约 1 秒，大部分花在启动 JVM 上。大模型单线程比 TLC 快 2 到 3 倍。
- 🧵 **并行且结果确定。** 用 `-workers N` 多线程运行时，每次的状态数都与单线程相同。即使 `SYMMETRY` 或 `VIEW` 让“保留哪个状态”会影响结果，也是如此。
- 🔁 **可直接替换 TLC 命令行。** 使用 TLC 的选项和配置文件，输出 TLC 的信息和反例轨迹，返回 TLC 的退出码，现有脚本和 CI 不用改。
- 🧩 **支持完整语言，而不是子集。** 支持 `INSTANCE`、递归、`ENABLED`、`CHOOSE`、活性与公平性、`SYMMETRY`、`VIEW` 和各类约束；也支持标准模块，以及 TLC、TLCExt、CommunityModules 中由 Java 实现的算子。
- 🪶 **小巧、独立。** 只有一个 8 MB 的可执行文件。不算队列，每个状态约占 30 字节。状态指纹是 128 位，是 TLC 的两倍宽。

## 性能

下表中的 TLC 耗时是 TLC 用 `-workers 1` 运行时记录下来的时间。tla-rs 的耗时在本地一台机器上测得，每个模型限时 60 秒，两者不是在同一台机器上测的。

| 模型规模（按 TLC 耗时） | 模型数 | 单线程中位加速比 |
| --- | ---: | ---: |
| < 2 秒 | 624 | 73× |
| 2 – 10 秒 | 91 | 17× |
| 10 – 60 秒 | 33 | 3.1× |
| > 60 秒 | 9 | 2.8× |

小模型的加速主要来自省掉了 JVM 启动，大模型的加速来自检查器本身。

部分大模型：

| 模型 | 不同状态数 | TLC | tla-rs 单线程 | tla-rs 4 线程 |
| --- | ---: | ---: | ---: | ---: |
| Detlefs | 952,912 | 82.3 秒 | 31.7 秒 | **9.4 秒** |
| Crossword_MC | 485,988 | 120.1 秒 | 50.8 秒 | **16.8 秒** |
| TLCSailfish1 | 109,604 | 77.2 秒 | 32.2 秒 | **10.0 秒** |
| MCLamportMutex | 724,274 | 33.1 秒 | 14.4 秒 | **4.7 秒** |
| MCbtree | 374,727 | 40.2 秒 | 20.7 秒 | **6.7 秒** |
| GameOfLife | 65,536 | 63.6 秒 | 12.9 秒 | **4.1 秒** |

单线程下与 TLC 一致的 757 个模型中，tla-rs 在 750 个上更快，总耗时 670 秒，TLC 是 2,441 秒。

## 与 TLC 对比

| | TLC | tla-rs |
| --- | :---: | :---: |
| 状态数 | 基准 | 772 个有结论的模型中 766 个完全一致，0 个不一致 |
| 运行环境 | JVM | 原生可执行文件，无需运行时 |
| 活性与公平性 | ✅ | ✅ |
| 并行搜索 | ✅ | ✅，状态数与单线程相同 |
| 命令行、输出信息、退出码 | ✅ | ✅ 与 TLC 兼容 |
| 指纹宽度 | 64 位 | 128 位 |

其他 Rust 写的 TLA+ 检查器，要么只支持语言的一个子集（`fabracht/tla-rs`），要么把规约编译成专用检查器（`ddalton/tla-mc`）。tla-rs 直接解释完整的 TLA+ 语言，目标是与 TLC 完全一致。

## 安装

| 渠道 | 包名 | 状态 |
| --- | --- | --- |
| crates.io | [`tla-tools`](https://crates.io/crates/tla-tools) | 计划中：`cargo install tla-tools` |
| npm | [`tla-rs`](https://www.npmjs.com/package/tla-rs) | 计划中：`npx tla-rs Spec.tla`，内含预编译二进制 |

两个渠道装出来的都是同一个 `tla-rs` 命令。正式发布前，请从源码编译（需要 Rust 1.85 或更高版本）：

```shell
git clone https://github.com/bbcvc/tla-rs.git && cd tla-rs
cargo build --release -p tla-tools
# 可执行文件在 target/release/tla-rs
```

## 使用

```shell
tla-rs Spec.tla                          # 用 Spec.cfg 检查 Spec.tla
tla-rs Spec.tla -config Other.cfg        # 使用其他模型配置
tla-rs Spec.tla -workers auto            # 每个 CPU 核心一个线程
tla-rs Spec.tla -deadlock                # 不检查死锁
tla-rs Spec.tla -library path/to/CommunityModules
```

退出码与 TLC 相同：

| 退出码 | 含义 |
| ---: | --- |
| `0` | 没有错误 |
| `10` | 假设（ASSUME）不成立 |
| `11` | 死锁 |
| `12` | 违反不变式或安全性属性 |
| `13` | 违反活性属性 |
| `75` | 求值出错 |
| `150` | 解析错误 |

完整的选项和退出码见 [crates/tla-tools/README.md](crates/tla-tools/README.md)。

## 架构

```
源码 ─► tla-tools-parser ─► tla-tools-resolve ─► tla-tools-eval ─► tla-tools-checker ─► tla-tools
                                                        ▲
                                                 tla-tools-value
```

| Crate | 作用 |
| --- | --- |
| `tla-tools-intern` | 全进程共用的字符串驻留表，按 TLC 的字符串顺序排序 |
| `tla-tools-ast` | TLA+ 模块的语法树 |
| `tla-tools-parser` | 解析 TLA+ 模块（基于 tree-sitter-tlaplus）和 TLC 配置文件 |
| `tla-tools-resolve` | 名字解析、`INSTANCE`、级别检查 |
| `tla-tools-value` | 值的表示，相等、排序、打印和指纹规则都与 TLC 相同 |
| `tla-tools-eval` | 表达式求值、初始状态与后继状态、`ENABLED`、标准模块 |
| `tla-tools-checker` | 规约处理、广度优先搜索（单线程与并行）、活性检查、对称性 |
| `tla-tools` | `tla-rs` 可执行文件（即发布到 crates.io 的包） |

要做到状态数与 TLC 完全一致，光把求值写对还不够。tla-rs 还复现了 TLC 的这些行为：
- 字符串和值的排序方式，它决定了 `CHOOSE` 返回哪个值；
- 变量的排列顺序；
- 后继状态的枚举方式；
- 32 位整数溢出；
- 活性检查遍历行为图的顺序。

这些设计取舍都记录在 [EVALUATION.md](EVALUATION.md) 中。

## 测试

```shell
cargo test --workspace

# 完整的一致性测试（需要把 tla-ts 仓库放在本仓库旁边）
C=../tla-ts/packages/tla-ts/tests/conformance
cargo run --release -p tla-tools-checker --example conformance -- $C/.corpora \
  --library $C/.corpora/tlapm/library --library $C/.corpora/community/modules \
  --expected $C/expected.json --timeout 60 --jobs 4 [--workers 4] [--filter NAME]
```

一致性测试会在独立进程里逐个检查模型，并与 TLC 的记录结果比对。823 个模型来自 16 个语料库，包括 TLC 自带的测试模型、tlaplus/Examples、Spectacle、CCF、MongoDB、CockroachDB 等。

## 路线图

**已完成**

- [x] 解析、名字解析、级别检查
- [x] 值的排序、相等和指纹与 TLC 一致
- [x] 求值器：初始状态与后继状态、`ENABLED`、标准模块、Java 实现的算子
- [x] 安全性检查：不变式、动作属性、死锁、约束、`VIEW`、`SYMMETRY`
- [x] 带公平性的活性检查，与 TLC 的 `-lncheck final` 相同
- [x] 结果确定的并行广度优先搜索
- [x] 与 TLC 兼容的命令行

**待办**

- [ ] 显示 `Print`、`PrintT` 打印的内容
- [ ] 反例轨迹支持 `ALIAS`
- [ ] 与 SANY 完全一致的解析信息和警告；求值出错时输出 TLC 那样的嵌套表达式调用栈
- [ ] 降低每次调用的求值开销：约有十个大模型（VR_*、S2C、MoveRange 等）仍比 TLC 慢 2 倍左右
- [ ] 让单线程下超过 60 秒的 15 个模型进入时限
- [ ] 并行活性检查（目前带时序属性的模型只用单线程）
- [ ] 并行查找反例（目前发现违反后会退回单线程，以给出 TLC 的最短反例）
- [ ] 常驻工作线程与无锁指纹表
- [ ] 支持磁盘存储状态队列和指纹表，以检查超出内存的状态空间
- [ ] 模拟模式（`-simulate`）、搜索过程中的活性检查（`-lncheck`）、`-dump`、`-continue`
- [ ] 把 `tla-tools` 发布到 crates.io，把带预编译二进制的 `tla-rs` 发布到 npm，并搭建 CI

## 文档

- [DESIGN.md](DESIGN.md)：最初的设计
- [EVALUATION.md](EVALUATION.md)：为了与 TLC 一致所做的设计修订，以及各阶段的结果
- [crates/tla-tools/README.md](crates/tla-tools/README.md)：命令行选项、输出格式，以及目前与 TLC 的差异

## 致谢

- [TLC](https://github.com/tlaplus/tlaplus)：tla-rs 对照的基准实现。
- [tla-ts](https://github.com/aidenybai/tla-ts)：提供了一致性测试集，以及 tla-rs 所移植的 TLC 算法实现。
- [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus)：语法解析器。

## 许可证

[MIT](LICENSE)
