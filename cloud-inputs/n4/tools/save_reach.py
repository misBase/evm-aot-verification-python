# Diagnostics: run a tool (e.g. node_profile.py) with every x86 reachability query saved, conjuncts in push
# order, to the last argument before it is checked; --old-cap maps the memory cap back to memory_max_size
# (fix 23 v1) to reproduce its abort. Usage: save_reach.py [--old-cap] TOOL ARGS... OUT.smt2
import sys, runpy, z3
import x86_64.cfg_state as cs
real = cs.set_param
if "--old-cap" in sys.argv:
    sys.argv.remove("--old-cap")
    cs.set_param = lambda name, value: real("memory_max_size" if name == "memory_high_watermark_mb" else name, value)
out = sys.argv.pop()
orig = cs.X86Constraints.is_possible
n = [0]
def saving(self, *a, **k):
    n[0] += 1
    s = z3.Solver(); s.add(*(list(self._constraints) + list(self.flag_constraints.values())))
    open(out, "w").write(f"; check {n[0]}\n" + s.sexpr())
    return orig(self, *a, **k)
cs.X86Constraints.is_possible = saving
sys.argv = sys.argv[1:]
runpy.run_path(sys.argv[0], run_name="__main__")
