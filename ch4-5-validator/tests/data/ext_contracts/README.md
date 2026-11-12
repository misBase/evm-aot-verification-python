# 外部合约 fixture

本目录收录了用于 EVM AOT 验证器的外部真实世界 Solidity 0.8.x 合约 fixture。

每个用例只保留面向验证器的产物,以及上游源码文件的一个精选子集:

- `<Contract>.json`:由运行时字节码生成的 AOT 编译器 IR。
- `<Contract>.hex`:由 AOT 编译器 生成的 x86-64 AOT 机器码。
- `<Contract>.txt`:可选的 `<Contract>.hex` x86-64 反汇编;当文件会超过 3 MB
  时省略。
- `src/`:主源码文件,以及附近用于审阅上下文的核心源码文件。

`src/` 目录有意不是完整的上游项目检出。对于较大的项目,它们是经过挑选的源码
摘录,目的是让目标合约及其主要逻辑可读。

`*.json` 文件是 AOT 编译器 的 EVM IR,而非 Solidity/Yul IR。

## 目标合约

| 用例 | 目标合约 | 主源码 | Pragma | 所用 solc | 运行时字节数 | IR 块数 | x86 字节数 | x64 反汇编 |
| --- | --- | --- | --- | --- | ---: | ---: | ---: | --- |
| `ens_registry` | `ENSRegistry` | `src/contracts/registry/ENSRegistry.sol` | `>=0.8.4` | `0.8.29` | 2390 | 127 | 149964 | 保留,32893 行 |
| `safe` | `Safe` | `src/contracts/Safe.sol` | `>=0.7.0 <0.9.0` | `0.8.29` | 11838 | 742 | 654030 | 省略,>3 MB |
| `compound_cerc20` | `CErc20` | `src/contracts/CErc20.sol` | `^0.8.10` | `0.8.29` | 14465 | 723 | 804046 | 省略,>3 MB |
| `aave_v3_pool` | `Pool` | `src/contracts/protocol/pool/Pool.sol` | `^0.8.10` | `0.8.29` | 17396 | 736 | 1090035 | 省略,>3 MB |
| `uniswap_permit2` | `Permit2` | `src/src/Permit2.sol` | `0.8.17` | `0.8.17` | 9152 | 397 | 432710 | 省略,>3 MB |
| `uniswap_v4_pool_manager` | `PoolManager` | `src/src/PoolManager.sol` | `0.8.26` | `0.8.26` | 24009 | 913 | 974350 | 省略,>3 MB |
| `dabe_manager` | `DABEManager` | `src/DABEManager.sol` | `^0.8.0` | `0.8.25`(原始字节码) | 17801 | 960 | 877727 | 省略,>3 MB |

## 循环情况

下表中的循环计数采用两种不同的统计口径:

- **源码循环**统计精选 `src/` 摘录中显式的 Solidity `for` / `while` / `do`
  结构,以及内联汇编中的 Yul `for` 循环,排除注释。它统计的是摘录文件,
  不代表这些循环都编进了目标合约的运行时字节码(见 `aave_v3_pool`)。
- **EVM IR CFG 环路**统计编译后 AOT 编译器 IR 中的循环强连通分量(SCC),使用与
  `evm_ir.cfg_executor` 相同的块控制约定:第一个 `JUMP` / `JUMPI` / 终结操作
  是有效的控制转移,块中之后的操作被视为死代码。建图时的边:
  - 静态跳转边(`is_static`)与 fallthrough 边;
  - **调用摘要边**:块内 `PUSH` 的常量若出现在某个动态 `JUMP` 的
    `immediate_set` 中(即内部函数的返回地址),就从该块直接连边到返回点,
    跳过被调用函数;
  - 动态返回边本身(`immediate_set`)不连。

  只用静态边会漏掉回边经过内部函数调用的循环。常见两种情况:`++i` 被编译成
  调用带溢出检查的自增 helper,或循环体调用了未内联的内部函数。例如 Safe 的
  `getOwners` 循环回边为 `0x1167 → helper 0x2b7a → 动态返回 0x119d → 0x1143`。
  反过来,直接连上下文不敏感的返回边又会把不同调用点串成假环:Safe 会塌成一个
  360 块的 SCC,无环的 ENS 也会出现假环。嵌套循环在 CFG 中属于同一个 SCC;
  被调用函数内部的循环单独计数,多个调用点共享时只计一次。

| 用例 | 源码循环 | EVM IR CFG 环路 | 构成 | 验证处理方式 |
| --- | ---: | ---: | --- | --- |
| `ens_registry` | 0 | 0 | 无循环。 | 适合作为无环公开合约 fixture。诸如 `owner(bytes32)` 这类受选择器约束的检查不应需要循环定界。 |
| `compound_cerc20` | 0 | 3 | 0 个源码循环 + 3 个编译器生成的动态 `string` 存储循环:`name` / `symbol` 存储字符串 getter 的复制循环,以及两个 `initialize(... name_, symbol_, ...)` 重载共用的存储字符串清除/写入循环。 | 避开 `name()`、`symbol()` 和字符串初始化的路径可以在不进入这些环路的情况下检查。触及它们的路径需要定界字符串长度,或一个存储字符串读/写摘要。 |
| `safe` | 5 | 7 | 5 个源码循环全部在 IR 中:对签名、owner 链表、module 链表和存储区间的动态定界循环。另有 2 个编译器生成的 ABI 编码循环:`getOwners` / `getModulesPaginated` 返回 `address[]` 的编码,以及 `setup()` 发出 `SafeSetup` 事件时对 `address[] owners` 的编码。 | 用诸如 owner 数量、签名数量、分页大小等界限来验证特定选择器路径。完整的无界验证需要循环摘要或不变式。 |
| `aave_v3_pool` | 9 | 8 | 9 个源码循环中只有 `Pool.sol:521`(`getReservesList`)编进了 Pool 字节码;其余 8 个位于通过 `DELEGATECALL` 调用的外部链接库(`PoolLogic`、`FlashLoanLogic`),或只被这些外部库调用的内部库函数(`GenericLogic`、`ValidationLogic`、`UserConfiguration`)中。另有 7 个编译器生成的循环:eMode 类别 `label` 字符串的存储读复制与存储清除/写入、`getReservesList` 返回 `address[]` 的编码,以及 `mintToTreasury` / `flashLoan` 把数组参数 ABI 编码进 `DELEGATECALL` calldata 的循环。 | 储备/资产遍历等业务循环的主体在外部库中,Pool 侧只表现为一次 `DELEGATECALL`。`getReservesList` 需要储备数量界限或循环摘要;其余环路按数组长度/字符串长度定界,或做复制摘要。 |
| `uniswap_permit2` | 7 | 11 | 7 个源码循环全部在 IR 中:批量 allowance `permit` / `transferFrom` / `lockdown`、批量签名转账,以及三种 permit 哈希循环。另有 4 个编译器生成的循环:`PermitDetails[]` 与 `TokenPermissions[]` 从 calldata 到内存的 ABI 解码、哈希数组的 `abi.encodePacked`,以及 witness 类型字符串的内存复制。 | 验证定界的批量大小,或对 ABI 数组遍历和 permit 哈希构造做摘要。 |
| `uniswap_v4_pool_manager` | 4 | 4 | 4 个源码循环全部在 IR 中,没有编译器生成的循环:`swap` 的 tick 遍历 `while` 循环(104 块,循环体含大量内部函数调用),以及 `Extsload` / `Exttload` 内联汇编中的 3 个 Yul `for` 循环。 | 验证定界的 swap/tick 跨越场景。完整的无界 swap 路径验证需要领域特定的循环不变式或摘要。`extsload` / `exttload` 的循环按 slot 数量定界即可。 |
| `dabe_manager` | 19 | 33 | 19 个源码循环中有 6 对是嵌套循环,内外层属于同一个 SCC,因此源码循环最多对应 13 个 SCC,其余至少 20 个是编译器生成的 `string` / `bytes` / 数组复制与 ABI 编解码循环。未逐个对照。 | **全合约与单 selector 验证均已知无法在合理时间内跑完**,对应的两个测试都标了 `@pytest.mark.skip`。诊断发现即使固定 4 字节 selector,当前 checker 的 reachability 剪枝也无法排除其他函数分支,符号执行会游荡进无关函数的 ABI 复制循环;这是 checker 本身的预存在限制,而非该合约独有的问题,只是在这个更大的 dispatcher(15+ 外部函数)上被放大到不可忽略。 |

源码循环与 EVM IR 环路头对照(环路头取 SCC 中的最小块 PC):

- `compound_cerc20`:
  - 编译器生成:`0x739`(`name` / `symbol`)、`0x36aa`、`0x3731`(`initialize`)。
- `safe`:
  - `Safe.sol:331`(`checkNSignatures`)→ `0x7d2`
  - `StorageAccessible.sol:20`(`getStorageAt`)→ `0xc3b`
  - `OwnerManager.sol:180`(`getOwners`)→ `0x1143`
  - `ModuleManager.sol:226`(`getModulesPaginated`)→ `0x1383`
  - `OwnerManager.sol:57`(`setupOwners`)→ `0x1f79`
  - 编译器生成:`0x27f1`(`address[]` 返回值编码)、`0x2cf8`(`SafeSetup` 事件编码)。
- `aave_v3_pool`:
  - `Pool.sol:521`(`getReservesList`)→ `0x23b2`
  - 不在 Pool 字节码中(外部链接库):`FlashLoanLogic.sol:92`、`FlashLoanLogic.sol:115`、
    `PoolLogic.sol:55`、`PoolLogic.sol:88`、`GenericLogic.sol:84`、
    `ValidationLogic.sol:466`、`ValidationLogic.sol:685`、`UserConfiguration.sol:230`。
  - 编译器生成:`0x175b`(`getEModeCategoryData`)、`0x4218`、`0x4299`
    (`configureEModeCategory`)、`0x386f`(`getReservesList`)、`0x3e7f`
    (`mintToTreasury`)、`0x3fb0`、`0x3ff3`(`flashLoan`)。
- `uniswap_permit2`:
  - `AllowanceTransfer.sol:52`(批量 `permit`)→ `0xf6d`
  - `AllowanceTransfer.sol:67`(批量 `transferFrom`)→ `0x12da`
  - `AllowanceTransfer.sol:102`(`lockdown`)→ `0x4f9`
  - `SignatureTransfer.sol:115`(批量 `permitTransferFrom` / `permitWitnessTransferFrom` 共用)→ `0x1b73`
  - `PermitHash.sol:46`(`PermitBatch` 哈希)→ `0xed9`
  - `PermitHash.sol:70`(`PermitBatchTransferFrom` 哈希)→ `0x3d7`
  - `PermitHash.sol:107`(带 witness 的批量哈希)→ `0x26e`
  - 编译器生成:`0xe7a`(`PermitDetails[]` 解码)、`0x16c6`(`TokenPermissions[]` 解码)、
    `0x1f71`(哈希数组 `abi.encodePacked`)、`0x1f9a`(witness 类型字符串复制)。
- `uniswap_v4_pool_manager`:
  - `libraries/Pool.sol:344`(`swap`)→ `0x4ad3`
  - `Extsload.sol:31`(`extsload(bytes32,uint256)`)→ `0x2635`
  - `Extsload.sol:55`(`extsload(bytes32[])`)→ `0x9b0`
  - `Exttload.sol:31`(`exttload(bytes32[])`)→ `0xb62`

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
AOT 编译器 amd64 后端在 `GOARCH=amd64` 下生成。

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

`*.hex` 文件可以借助 AOT 编译器 仓库中的辅助测试,从已检入的 `*.json` IR
重新生成。请使用 `GOARCH=amd64`;否则后端会跟随宿主机架构。

```sh
VERIFIER_ROOT=$(pwd)
cd "aot-compiler"
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
