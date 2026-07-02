# 外部合约 fixture

本目录收录了用于 EVM AOT 验证器的外部真实世界 Solidity 0.8.x 合约 fixture。

每个用例只保留面向验证器的产物,以及上游源码文件的一个精选子集:

- `<Contract>.json`:由运行时字节码生成的 go-hpc-evm IR。
- `<Contract>.hex`:由 go-hpc-evm 生成的 x86-64 AOT 机器码。
- `<Contract>.txt`:可选的 `<Contract>.hex` x86-64 反汇编;当文件会超过 3 MB
  时省略。
- `src/`:主源码文件,以及附近用于审阅上下文的核心源码文件。

`src/` 目录有意不是完整的上游项目检出。对于较大的项目,它们是经过挑选的源码
摘录,目的是让目标合约及其主要逻辑可读。

`*.json` 文件是 go-hpc-evm 的 EVM IR,而非 Solidity/Yul IR。

## 目标合约

| 用例 | 目标合约 | 主源码 | Pragma | 所用 solc | 运行时字节数 | IR 块数 | x86 字节数 | x64 反汇编 |
| --- | --- | --- | --- | --- | ---: | ---: | ---: | --- |
| `ens_registry` | `ENSRegistry` | `src/contracts/registry/ENSRegistry.sol` | `>=0.8.4` | `0.8.29` | 2390 | 127 | 149964 | 保留,32893 行 |
| `safe` | `Safe` | `src/contracts/Safe.sol` | `>=0.7.0 <0.9.0` | `0.8.29` | 11838 | 742 | 654030 | 省略,>3 MB |
| `compound_cerc20` | `CErc20` | `src/contracts/CErc20.sol` | `^0.8.10` | `0.8.29` | 14465 | 723 | 804046 | 省略,>3 MB |
| `aave_v3_pool` | `Pool` | `src/contracts/protocol/pool/Pool.sol` | `^0.8.10` | `0.8.29` | 17396 | 736 | 1090035 | 省略,>3 MB |
| `uniswap_permit2` | `Permit2` | `src/src/Permit2.sol` | `0.8.17` | `0.8.17` | 9152 | 397 | 432710 | 省略,>3 MB |
| `uniswap_v4_pool_manager` | `PoolManager` | `src/src/PoolManager.sol` | `0.8.26` | `0.8.26` | 24009 | 913 | 974350 | 省略,>3 MB |

## 循环情况

下表中的循环计数采用两种不同的统计口径:

- **源码循环**统计精选 `src/` 摘录中显式的 Solidity `for` / `while` / `do`
  结构,排除行注释。
- **EVM IR CFG 环路**统计编译后 go-hpc-evm IR 中的循环强连通分量,使用与
  `evm_ir.cfg_executor` 相同的块控制约定:第一个 `JUMP` / `JUMPI` / 终结操作
  是有效的控制转移,块中之后的操作被视为死代码。

| 用例 | 源码循环 | EVM IR CFG 环路 | 分类 | 验证处理方式 |
| --- | ---: | ---: | --- | --- |
| `ens_registry` | 0 | 0 | 在所检查的 IR 控制流模型下是无循环 fixture。 | 适合作为无环公开合约 fixture。诸如 `owner(bytes32)` 这类受选择器约束的检查不应需要循环定界。 |
| `compound_cerc20` | 0 | 3 | 编译器生成的动态 `string` 存储循环,并非 Compound 源码中的显式循环。这些环路是 `name` / `symbol` 存储字符串 getter 的复制循环,以及 `initialize(... name_, symbol_, ...)` 的存储字符串清除/写入循环。 | 避开 `name()`、`symbol()` 和字符串初始化的路径可以在不进入这些环路的情况下检查。触及它们的路径需要定界字符串长度,或一个存储字符串读/写摘要。 |
| `safe` | 5 | 3 | 用户可见的、对 owner、module、签名和存储区间的动态定界循环。 | 用诸如 owner 数量、签名数量、分页大小等界限来验证特定选择器路径。完整的无界验证需要循环摘要或不变式。 |
| `aave_v3_pool` | 9 | 6 | 用户可见的、对储备、资产和用户配置 bit 位的动态定界循环。 | 用储备数量、资产数组长度及相关 calldata/状态维度的显式界限来验证。完整的无界 pool 验证预期无法通过单纯的 CFG 展开终止。 |
| `uniswap_permit2` | 7 | 2 | 对 calldata 数组进行的批量 permit/签名哈希循环。 | 验证定界的批量大小,或对 ABI 数组遍历和 permit 哈希构造做摘要。 |
| `uniswap_v4_pool_manager` | 1 | 3 | swap/tick 遍历循环,外加编译后 IR 中编译器生成的循环形辅助逻辑。 | 验证定界的 swap/tick 跨越场景。完整的无界 swap 路径验证需要领域特定的循环不变式或摘要。 |

代表性的编译后 EVM IR 环路头:

- `compound_cerc20`:`0x739`、`0x36aa <-> 0x36b3`、
  `0x3731 <-> 0x373a`。
- `safe`:`0x7d2...`、`0xc3b <-> 0xc44`、`0x27f1 <-> 0x27fa`。
- `aave_v3_pool`:`0x175b`、`0x386f <-> 0x3878`、
  `0x3fb0 <-> 0x3fb9`、`0x3ff3 <-> 0x3ffc`、
  `0x4218 <-> 0x4221`、`0x4299 <-> 0x42a2`。
- `uniswap_permit2`:`0x1f71 <-> 0x1f7f`、
  `0x1f9a <-> 0x1fab`。
- `uniswap_v4_pool_manager`:`0x9b0 <-> 0x9c3`、
  `0xb62 <-> 0xb75`、`0x2635 <-> 0x2647`。

代表性的源码循环位置:

- `safe`:`Safe.sol:331`、`ModuleManager.sol:226`、
  `OwnerManager.sol:57`、`OwnerManager.sol:180`、
  `StorageAccessible.sol:20`。
- `aave_v3_pool`:`Pool.sol:521`、`GenericLogic.sol:84`、
  `FlashLoanLogic.sol:92`、`FlashLoanLogic.sol:115`、
  `PoolLogic.sol:55`、`PoolLogic.sol:88`、
  `ValidationLogic.sol:466`、`ValidationLogic.sol:685`、
  `UserConfiguration.sol:230`。
- `uniswap_permit2`:`AllowanceTransfer.sol:52`、
  `AllowanceTransfer.sol:67`、`AllowanceTransfer.sol:102`、
  `SignatureTransfer.sol:115`、`PermitHash.sol:46`、
  `PermitHash.sol:70`、`PermitHash.sol:107`。
- `uniswap_v4_pool_manager`:`Pool.sol:344`。

## 上游条目

- ENS Registry: https://github.com/ensdomains/ens-contracts/blob/master/contracts/registry/ENSRegistry.sol
- Safe: https://github.com/safe-global/safe-smart-account/blob/main/contracts/Safe.sol
- Compound CErc20: https://github.com/compound-finance/compound-protocol/blob/master/contracts/CErc20.sol
- Aave V3 Pool: https://github.com/aave/aave-v3-core/blob/master/contracts/protocol/pool/Pool.sol
- Uniswap Permit2: https://github.com/Uniswap/permit2/blob/main/src/Permit2.sol
- Uniswap v4 PoolManager: https://github.com/Uniswap/v4-core/blob/main/src/PoolManager.sol

## 构建来源

Solidity 字节码在编译时禁用了元数据哈希,之后临时的 `*.bin` 和
`*.bin-runtime` 文件已从本 fixture 集中移除。`*.hex` 中的 AOT 机器码由
go-hpc-evm amd64 后端在 `GOARCH=amd64` 下生成。

通用编译器标志:

```sh
--optimize --metadata-hash none
```

额外的编译器标志:

- ENS Registry、Safe、CErc20、Aave V3 Pool:`--evm-version cancun`。
- Uniswap Permit2:`--via-ir --optimize-runs 1000000`。
- Uniswap v4 PoolManager:`--evm-version cancun --via-ir --optimize-runs 44444444`。

Aave V3 `Pool` 链接时使用了确定性的本地基准地址:

```text
contracts/protocol/libraries/logic/BorrowLogic.sol:BorrowLogic:0x1000000000000000000000000000000000000001
contracts/protocol/libraries/logic/BridgeLogic.sol:BridgeLogic:0x1000000000000000000000000000000000000002
contracts/protocol/libraries/logic/EModeLogic.sol:EModeLogic:0x1000000000000000000000000000000000000003
contracts/protocol/libraries/logic/FlashLoanLogic.sol:FlashLoanLogic:0x1000000000000000000000000000000000000004
contracts/protocol/libraries/logic/LiquidationLogic.sol:LiquidationLogic:0x1000000000000000000000000000000000000005
contracts/protocol/libraries/logic/PoolLogic.sol:PoolLogic:0x1000000000000000000000000000000000000006
contracts/protocol/libraries/logic/SupplyLogic.sol:SupplyLogic:0x1000000000000000000000000000000000000007
```

## AOT 再生成

`*.hex` 文件可以借助 go-hpc-evm 仓库中的辅助测试,从已检入的 `*.json` IR
重新生成。请使用 `GOARCH=amd64`;否则后端会跟随宿主机架构。

```sh
VERIFIER_ROOT=$(pwd)
cd "$GOPATH/src/github.com/bcds/go-hpc-evm"
GOCACHE=/private/tmp/go-build-cache \
GOARCH=amd64 \
PUBLIC_CONTRACT_FIXTURE_ROOT="$VERIFIER_ROOT/tests/data/ext_contracts" \
go test ./evm/aot -run TestGenPublicContractFixtures -count=1 -v
```

## 注意事项

- `compound_cerc20` 的目标是 `CErc20`;在本源码树中,基础的 `CToken` 合约是
  抽象合约。
- `safe` 的目标是 `Safe`,而非 `SafeL2`。
- `uniswap_v4_pool_manager` 接近 EIP-170 部署字节码上限,但仍低于该上限,
  运行时为 24009 字节。
