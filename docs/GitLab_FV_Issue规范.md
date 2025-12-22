# 形式化验证 (FV) Issue 提交规范

## 1. Title（标题）

**格式**：`[FV][模块名] 简短描述`

### 格式说明

- **`[FV]`**: 固定前缀，方便全局搜索
- **`[模块名]`**: 发生问题的EVM AOT子模块名称
  - `EVM_IR` - EVM IR相关模块（解析、模型、程序等）
  - `X86_64` - x86-64相关模块（反汇编、执行状态、指令语义等）
  - `COMMON` - 公共模块（uint256、evm_stack等）
  - `STATE` - 状态管理模块（SMT状态等）

### 示例

- `[FV][EVM_IR] 解析过程中额外的PC值未被赋值`
- `[FV][X86_64] x86-64指令语义建模缺少溢出检查`
- `[FV][COMMON] Uint256加法语义实现错误`

## 2. Type（类型）

选择 **"Issue"**。

## 3. Description（描述）

使用以下模板：

```markdown
## 问题描述

[简要描述问题]

## 发现场景

- 验证场景：[具体验证的EVM IR和x86-64代码]
- 复现步骤：[如何复现问题]

## 影响范围

- [ ] 导致验证失败
- [ ] 影响验证准确性
- [ ] 影响形式化分析构建
- [ ] 影响性能

## 技术细节

### 相关代码
[代码位置和片段]

### 预期行为
[预期的正确行为]

### 实际行为
[实际观察到的行为]

## 修复建议

[如果有修复建议，请描述]
```

## 4. Labels（标签）

### 必需标签（必须各选一个）

**第一类：类别标签（必须选择一个）**

这些类别针对在形式化验证过程中发现的 **EVM AOT 代码/项目** 问题：

- `category:bug` - BUG：EVM AOT 逻辑违例（最重要）
  - AOT 生成的 x86 代码语义与 EVM 不等价
  - 编译器内部逻辑错误导致生成非预期结果
  - 形式化验证发现的实质性功能缺陷

- `category:setup` - SETUP：验证环境配置问题
  - 针对 AOT 代码的约束缺失（Under-constraint）导致伪反例
  - 验证环境过约束（Over-constraint）导致证明失败
  - 验证脚本或参数配置不当

- `category:perf` - PERF：验证 AOT 代码的性能/收敛问题
  - AOT 编译器的编译质量差，影响执行效率

- `category:model` - MODEL：建模与解析质量问题
  - 对 AOT 输出结果（如 PC 映射）解析异常
  - **PC 值未赋值/丢失**、解析字段不全等影响分析构建的问题
  - 建模不完整或辅助验证逻辑错误

- `category:doc` - DOC：规格文档不一致
  - 技术规格文档（Spec）与 AOT 代码实现不符
  - 文档描述的语义行为在代码中未被正确体现

**第二类：严重程度标签（必须选择一个）**

- `severity:critical` - 严重：AOT 代码逻辑错误导致验证失败（通常对应 `category:bug`）
- `severity:high` - 高：影响验证准确性、验证环境配置严重错误（通常对应 `category:setup`、`category:perf`）
- `severity:medium` - 中等：建模质量缺陷、解析异常（通常对应 `category:model`，如 PC 值未赋值）
- `severity:low` - 低：文档不一致、代码风格等非关键问题（通常对应 `category:doc`）

### 可选标签

**模块标签**（可选，用于进一步细化）：
- `module:evm-ir` - EVM IR相关
- `module:x86-64` - x86-64相关
- `module:common` - 公共模块
- `module:state` - 状态管理模块

**问题类型标签**（可选）：
- `type:bug` - Bug 修复
- `type:enhancement` - 功能增强
- `type:refactor` - 代码重构
- `type:documentation` - 文档相关

## 5. 其他字段

- **Assignee（负责人）**：可选，选择处理此 Issue 的人员
- **Due date（截止日期）**：可选，设置截止日期
- **Milestone（里程碑）**：可选，关联到项目里程碑

## 6. 标签组合示例

### PC值未赋值问题

**标题**：`[FV][EVM_IR] 解析过程中额外的PC值未被赋值`

**必需标签**：
- `category:model`（建模与解析质量问题）
- `severity:medium`

### AOT 语义违例（BUG）

**标题**：`[FV][X86_64] x86-64 指令语义建模缺少溢出检查`

**必需标签**：
- `category:bug`（EVM AOT 逻辑违例）
- `severity:critical`

### 验证环境配置错误

**标题**：`[FV][STATE] 约束缺失导致验证出现伪反例`

**必需标签**：
- `category:setup`（验证环境配置问题）
- `severity:high`
