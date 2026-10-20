"""l2diff.py FILE.smt2 : closed sha3_slice apps (binders entered) by nesting level; minimal diffs between same-level args."""
import sys
from z3 import *

set_option(max_depth=12, max_args=16, max_width=220, max_lines=40)
F = And(*parse_smt2_file(sys.argv[1]))


def free(t):
    st, sn = [(t, 0)], set()
    while st:
        u, b = st.pop()
        if (u.get_id(), b) in sn:
            continue
        sn.add((u.get_id(), b))
        if is_var(u):
            if get_var_index(u) >= b:
                return True
        elif is_quantifier(u):
            st.append((u.body(), b + u.num_vars()))
        elif is_app(u):
            st.extend((c, b) for c in u.children())
    return False


apps, seen, work = {}, set(), [F]
while work:
    u = work.pop()
    if u.get_id() in seen:
        continue
    seen.add(u.get_id())
    if is_quantifier(u):
        work.append(u.body())
        continue
    if is_app(u):
        if u.decl().name() == "sha3_slice" and not free(u):
            apps[u.get_id()] = u
        work.extend(u.children())


def level(t):
    best, st, sn = 0, [(t, 0)], set()
    while st:
        u, d = st.pop()
        if (u.get_id(), d) in sn:
            continue
        sn.add((u.get_id(), d))
        if is_quantifier(u):
            st.append((u.body(), d))
        elif is_app(u):
            if u.decl().name() == "sha3_slice":
                d += 1
                best = max(best, d)
            st.extend((c, d) for c in u.children())
    return best


by = {}
for a in apps.values():
    by.setdefault(level(a), []).append(a)
for lv, xs in sorted(by.items()):
    print("level", lv, [len(a.sexpr()) for a in xs])
diffs = []


def walk(u, v, depth=0):
    if u.eq(v):
        return
    if is_quantifier(u) and is_quantifier(v) and u.num_vars() == v.num_vars():
        walk(u.body(), v.body(), depth)
        return
    if is_app(u) and is_app(v) and u.decl().eq(v.decl()) and u.num_args() == v.num_args() and u.num_args() > 0:
        for p, q in zip(u.children(), v.children()):
            walk(p, q, depth + 1)
        return
    diffs.append((u, v))


lv = int(sys.argv[2]) if len(sys.argv) > 2 else 2
xs = by[lv]
for i in range(len(xs)):
    for j in range(i + 1, len(xs)):
        diffs.clear()
        walk(xs[i].arg(0), xs[j].arg(0))
        print(f"== level {lv}: {len(xs[i].sexpr())} vs {len(xs[j].sexpr())}: {len(diffs)} differing leaves")
        for u, v in diffs[:4]:
            print("   A:", " ".join(str(u).split())[:600])
            print("   B:", " ".join(str(v).split())[:600])
