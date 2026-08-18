# 测试说明

本目录包含EVM AOT验证系统的所有测试文件。

## 测试文件

### test_basic.py
基础功能测试，包括：
- 模块导入测试
- ADD语义测试（EVM和x86-64）
- 等价性检查器测试

运行方式：
```bash
python3 tests/test_basic.py
```

### test_ir_json.py
EVM IR JSON解析测试，包括：
- JSON文件解析
- IR数据模型构建
- 语义建模测试

运行方式：
```bash
python3 tests/test_ir_json.py
```

### test_verifier.py
主验证器测试，包括：
- 验证器导入测试
- 具体值ADD验证测试

运行方式：
```bash
python3 tests/test_verifier.py
```

## 运行所有测试

```bash
# 运行所有测试
python3 tests/test_basic.py
python3 tests/test_ir_json.py
python3 tests/test_verifier.py
```

## 测试数据

测试数据文件统一存放在 `data/` 目录下：

- `data/example_ir.json`: 示例EVM IR JSON文件，包含一个ADD操作的块

## 测试覆盖率

当前测试覆盖：
- ✅ 基础数据结构（Uint256, EVMStack）
- ✅ EVM IR JSON解析
- ✅ EVM ADD操作语义建模
- ✅ x86-64 ADD序列语义建模
- ✅ 等价性检查
- ✅ 主验证器功能

## 未来扩展

计划添加的测试：
- 更多EVM操作（MUL, SUB, DIV等）
- 控制流操作（JUMP, JUMPI）
- 块级验证
- 端到端验证流程

