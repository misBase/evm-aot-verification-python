"""缓存键里的对象身份标识。

单独成模块是为了避开 import 环：`verification/cutpoint_relation.py` 与
`verification/loop_certificates.py` 都需要它，而后者依赖前者所在的依赖链。
"""


def callable_identity(fn) -> str:
    """可调用对象在缓存键里的身份标识。

    **只用 `__qualname__` 会碰撞**，而碰撞意味着复用在**另一个**不变式下证出的
    定理（假绿）。三类都会撞：

    - lambda：同作用域内的两个 lambda qualname 完全相同；
    - 具名闭包：同一 factory 造出、捕获不同值的两个闭包 qualname 相同；
    - 绑定方法：同一方法绑到不同实例，qualname 也相同。

    因此只有**模块级具名函数**（qualname 不含 `<locals>` / `<lambda>`，且不是
    绑定方法）才用稳定的 `module.qualname`；其余一律回退 `repr()`——它含对象
    地址，同进程内可区分实例。代价是缓存命中率下降（每次重建都重证），方向安全。

    ⚠️ **`repr()` 回退的使用者必须锚定对象**。地址在对象被 GC 后可被 CPython
    立即复用，于是一个语义不同的新闭包可能拿到完全相同的 key 并复用旧定理
    （假绿）。所有把本函数结果放进缓存键的地方，都要在缓存的生命周期内持有
    该可调用对象——见 `LoopCertificateCache.anchor_callable()`。
    """
    if fn is None:
        return "none"
    qualname = getattr(fn, "__qualname__", None)
    is_bound_method = getattr(fn, "__self__", None) is not None
    if (
        qualname
        and not is_bound_method
        and "<lambda>" not in qualname
        and "<locals>" not in qualname
    ):
        return f"{getattr(fn, '__module__', '?')}.{qualname}"
    return repr(fn)


__all__ = ["callable_identity"]
