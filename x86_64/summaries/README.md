# Summary 说明

`x86_64/summaries` 里的 Summary 是对一段已识别 x86 指令 slice 的语义折叠。开启
Summary 后，全局执行器会在命中点跳过原始指令并应用对应的抽象语义，因此 Summary
不能只依赖 matcher 或结构检查被静默信任。

## 证明要求

每一个开启 Summary 的命中点都必须单独证明。

这里的“单独证明”指：对具体命中的 x86 slice、入口位置、continuation、layout、
operand mapping、clobber/frame 条件和 Summary 抽象语义建立等价关系。只有证明产物明确
标记为已验证的 Summary，才允许进入全局 verifier 的信任链。

Summary matcher 只能说明“这段代码看起来可以实例化某个 Summary”，不能替代语义证明。
如果某个命中点没有对应的已验证 proof artifact，验证流程必须 fail closed，或者显式进入
离线证明流程。

## 单点证明清单

- [ ] CALLDATALOAD：对应calldataload.py
