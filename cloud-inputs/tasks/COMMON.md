# 云端任务通用约定

项目：Python + Z3 证明 EVM IR 与 go-hpc-evm 生成的 x86-64 AOT 代码块级 lockstep 等价。先读仓库根目录的 CLAUDE.md 和 cloud-inputs/README.md。全程用中文写报告。

## 环境
- 优先用 `pip install poetry && poetry config virtualenvs.in-project true && poetry install`。如果装不了，就 `pip install z3-solver capstone`，版本对齐 poetry.lock。
- 命令用 `poetry run python ...`（或 `.venv/bin/python`），模块路径设 `PYTHONPATH=.`。
- 不用 here-doc（<<EOF），不用管道给解释器喂代码；脚本先写成文件再运行。

## 纪律（必须遵守）
- 只做通用机制，不按合约或块号特化。每处改动都附健全性论证：UNSAT 必须来自可靠推理，抽象只能是过近似，"提议"类信息出错只能导致证不出，不能导致误证。
- 不改 go-hpc-evm。改动只限 Python 仓库。
- 先跑全量快测：`poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider -x`。已知例外：msize_absint 相关测试依赖被忽略的 tmp/prov_common.py，在云端会失败，可以忽略，但要在报告里列出。
- 新测试要按节点 ID 单独跑一遍，确认确实被收集到。同名类或函数会静默覆盖。

## 交付
- 在当前分支基础上新建分支 `cloud/<任务名>`，改动和 REPORT 都提交到这个分支，然后 push 到 origin。
- 报告写在 `cloud-inputs/reports/<任务名>.md`，内容包括：结论、改动位置（文件:行）、健全性论证、测试结果、离线验证数据、未解决的问题。
- 不要合并到 develop-cutpoint。本地会拉取你的分支，在服务器上做全量验证。
