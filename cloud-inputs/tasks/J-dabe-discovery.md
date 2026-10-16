# 任务 J：DABEManager 发现阶段的实例爆炸与 Z3 异常（任务名 dabe-discovery）

先读 COMMON.md。基于分支 `cloud/inputs-dabe` 开工，它的代码等于冻结提交 caa01b1，Safe 和 ENS 已用这份代码拿到证书。

## 背景
fixture 是 `cloud-inputs/dabe/DABEManager.{json,hex}`，hex 由修复了 CALLDATALOAD 的编译器重新编译。合约有 960 个 IR 块、33 个循环 SCC；各循环的情况见 `tests/data/ext_contracts/README.md`。

服务器上用与证书相同的参数跑了两次：

```
python -m tools.verify_block_lockstep <stem> --gas-check full --timeout-ms 30000 --first-pass-node-seconds 300 \
  --node-seconds 1800 --max-depth 400 --max-instances N --max-parameter-values 32 --wall-seconds 21600 \
  --summaries --discover-first --constant-insensitive --node-workers 1 --pair-workers-per-node 3 --results-dir ... --output ...
```

1. `N=8192`：约 4 分钟后报 `ValueError: specialization instance budget exhausted`，attempted_instances 为 0。作为对照，CErc20（723 块）是 4708 个实例，Safe（742 块）是 3240 个实例。
2. `N=65536`：约 1.5 小时后报 `Z3Exception: At least two arguments expected.`，attempted_instances 仍为 0。报告里只有这一句，没有 traceback。

## 要做的
1. **复现并定位 Z3 异常**：拿到完整 traceback，找出是哪里构造了参数个数不足的 Z3 项（比如 `Distinct`/`Concat`/`Or` 只收到一个元素），修复它并补测试。修复必须保持健全性：不能因为参数不够就把检查跳过当作通过。如果完整跑一遍太慢，可以直接调用 discovery 的入口（参考 `verification/block_parallel.py` 的 `build_inputs` / `discover` / `proof_groups`），必要时打点定位。
2. **量化实例爆炸**：统计实例总数，以及按块、按维度（stack_depth、memory_size/fmp 参数值、stack_constants）的分布，找出贡献最多的块和维度，再与 CErc20/Safe 的分布对比（同样的统计方法）。
3. **给出通用的削减方案**，不得按合约特化，例如更激进的 constant-insensitive 合并、参数加宽阈值、深度类合并等。每个方案都要附健全性论证：合并后的实例必须覆盖原有的所有上下文（过近似），只能让证明更难，不能让证明不完整。给出估算的实例数。先不要改生产默认值，新行为用开关控制并补测试。
4. 跑全量快测（目标 0 失败）。交付到分支 `cloud/dabe-discovery`，报告写在 `cloud-inputs/reports/dabe-discovery.md`。
