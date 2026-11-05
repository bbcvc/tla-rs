# tla-rs

[English](README.md) | 简体中文

一个用 Rust 编写的 TLA+ 模型检查器，结果与 TLC 一致。

`tla-rs` 命令行工具使用 TLC 的选项，输出 TLC 的信息，返回 TLC 的退出码。它的目标是与 TLC 完全一致，而不是只支持 TLA+ 的一个子集。“一致”指的是：对 TLC 能检查的模型，结论、违反的属性名、生成状态数、不同状态数、搜索深度和反例长度都与 TLC 相同。这一点通过 823 条 TLC 运行记录来验证。

## 当前状态

验证使用 [tla-ts](https://github.com/aidenybai/tla-ts) 一致性测试集里的 823 个模型。它们来自 16 个语料库，包括 TLC 自带的测试模型、tlaplus/Examples、Spectacle、CCF、MongoDB、CockroachDB 等。每个模型限时 60 秒。

| 运行方式 | 与 TLC 一致 | 不一致 | TLC 无结论 | 超时 |
| --- | ---: | ---: | ---: | ---: |
| 1 线程 | 757 | 0 | 51 | 15 |
| 4 线程 | 766 | 0 | 51 | 6 |

- **TLC 无结论：** 这 51 个模型 TLC 自己跑了 20 秒以上后出错，没有结论可供比对。
- **超时：** 超时的都是 TLC 自己也要跑 60 秒以上的模型。
- **速度：** 单线程下，757 个一致的模型里有 750 个比 TLC 快，总耗时 670 秒，TLC 是 2,441 秒。

已支持：

- 安全性检查：不变式、动作属性、死锁、`ASSUME`、`CONSTRAINT`、`ACTION_CONSTRAINT`、`VIEW`、`SYMMETRY`。
- 活性检查：公平性和时序属性，检查方式与 TLC 的 `-lncheck final` 相同。
- `INSTANCE`、递归、`ENABLED`。
- 标准模块，以及 TLC、TLCExt、CommunityModules 中由 Java 重写的算子。
- 并行广度优先搜索（`-workers N`），统计结果与单线程完全相同。

## 快速开始

需要 Rust 1.85 或更高版本。

```shell
cargo build --release -p tla-cli
target/release/tla-rs Spec.tla                       # 用 Spec.cfg 检查 Spec.tla
target/release/tla-rs Spec.tla -config Other.cfg -workers 4
target/release/tla-rs Spec.tla -library path/to/CommunityModules
```

退出码与 TLC 相同，例如 `0` 表示没有错误，`11` 表示死锁，`12` 表示违反不变式，`13` 表示违反活性属性。完整的选项和退出码见 [crates/tla-cli/README.md](crates/tla-cli/README.md)。

## 工作区结构

| Crate | 作用 |
| --- | --- |
| `tla-intern` | 全进程共用的标识符与字符串驻留表，按 TLC 的字符串顺序排序 |
| `tla-ast` | TLA+ 模块的语法树 |
| `tla-parser` | 解析 TLA+ 模块（基于 tree-sitter-tlaplus）和 TLC 配置文件 |
| `tla-resolve` | 名字解析、`INSTANCE`、级别检查 |
| `tla-value` | 值的表示，相等、排序、打印和指纹规则都与 TLC 相同 |
| `tla-eval` | 求值器：表达式、初始状态与后继状态、`ENABLED`、标准模块 |
| `tla-checker` | 规约处理、广度优先搜索（单线程与并行）、活性检查、对称性 |
| `tla-cli` | `tla-rs` 可执行文件 |

处理流程如下：

```
源码 ─► tla-parser ─► tla-resolve ─► tla-eval ─► tla-checker ─► tla-cli
                                       ▲
                                   tla-value
```

## 一致性测试

```shell
cargo test --workspace

C=../tla-ts/packages/tla-ts/tests/conformance
cargo run --release -p tla-checker --example conformance -- $C/.corpora \
  --library $C/.corpora/tlapm/library --library $C/.corpora/community/modules \
  --expected $C/expected.json --timeout 60 --jobs 4 [--workers 4] [--filter NAME]
```

测试工具在独立进程里逐个检查模型，并与 TLC 的记录结果比对。加上 `--outcomes FILE` 会把每个模型的结果写成一行。

## 文档

- [DESIGN.md](DESIGN.md)：最初的设计。
- [EVALUATION.md](EVALUATION.md)：为了与 TLC 一致所做的设计修订，以及各阶段的结果。
- [crates/tla-cli/README.md](crates/tla-cli/README.md)：命令行选项、输出格式，以及目前与 TLC 的差异。

## 已知不足

- 不显示 `Print`、`PrintT` 打印的内容。
- SANY 的解析信息只是近似。
- 不支持 `ALIAS`。
- 约有十个大模型因为每次调用的求值开销，仍比 TLC 慢 2 倍左右。

## 许可证

MIT OR Apache-2.0。
