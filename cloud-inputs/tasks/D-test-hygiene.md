# 任务 D：测试卫生两项（任务名 test-hygiene）

先读 COMMON.md。基于分支 `cloud/b3b-merged` 开工。

1. **msize_absint 测试依赖被忽略的文件。** `tools/msize_absint.py` 及其测试（约 35 条，在 tests/ 下搜 msize_absint）依赖仓库 .gitignore 掉的 `tmp/prov_common.py`，所以干净克隆后会失败。
   - 找出真正依赖的符号。如果它们是工具运行所必需的，就把它们正式迁到 `tools/` 或合适的模块，不能留在 tmp 下。
   - 迁移后测试在干净克隆中应全部通过。
   - 如果 `tmp/prov_common.py` 在仓库里根本不存在，无法恢复，就根据测试和调用点重建最小实现。重建的每个函数都要说明依据；实在无法可靠重建的，把对应测试标注为 skip 并写清原因，不能伪造行为。
2. **负载敏感的偶发失败。** `test_offset_view_step_lemma_proves...`（在 tests/unit 下搜索全名）在高负载时偶尔失败：它自己发出的 3s solver 查询会超时，单独运行时 3/3 通过。改为不依赖墙钟：例如改用 rlimit，或给足 timeout，同时断言答案为 unsat 而不是断言耗时。改法不能削弱测试原本要检查的东西。
3. 跑全量快测，确认 0 失败。
4. 交付到分支 `cloud/test-hygiene`，报告写在 `cloud-inputs/reports/test-hygiene.md`。
