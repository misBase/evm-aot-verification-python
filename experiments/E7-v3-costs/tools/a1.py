"""A1 (read-only): workload, cost distribution, hidden (overwritten) attempts and block features
from the final1 certification JSONs.  a1.py OUT_JSON final1/*.json"""
import json
import statistics
import sys
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path

DATA = Path(__file__).resolve().parents[3] / "ch4-5-validator/data"  # artifact layout
FIX = DATA / "contracts"
TRACES = {n: DATA / "traces" / f"trace-{n}.json"
          for n in ("Pool", "PoolManager", "ENSRegistry", "CErc20", "Safe", "Permit2")}
KINDS = ("MSTORE", "MLOAD", "CALLDATACOPY", "CODECOPY", "RETURNDATACOPY", "MCOPY", "SHA3", "KECCAK256", "MUL", "DIV",
         "SDIV", "MOD", "EXP", "SSTORE", "SLOAD", "CALL", "STATICCALL", "DELEGATECALL", "LOG", "CALLDATALOAD")


def features(name):
    ir = json.loads((FIX / f"{name}.json").read_text())
    rows = json.loads(TRACES[name].read_text())["rows"]
    x86 = defaultdict(int)
    for r in rows:
        x86[r["block"]] += r["end"] - r["start"]
    out = {}
    for f in ir["control_frames"]:
        kinds = [o["kind"] for o in f["operations"]]
        row = dict(ops=len(kinds), x86_bytes=x86.get(f["pc"], 0))
        for k in KINDS:
            row[k] = sum(1 for x in kinds if x.startswith(k)) if k in ("LOG",) else kinds.count(k)
        out[f["pc"]] = row
    return out


def pct(xs, q):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(q * len(xs)))] if xs else None


def spearman(x, y):
    def rank(v):
        order = sorted(range(len(v)), key=v.__getitem__)
        r = [0] * len(v)
        for i, j in enumerate(order):
            r[j] = i
        return r
    rx, ry = rank(x), rank(y)
    n = len(x)
    return 1 - 6 * sum((a - b) ** 2 for a, b in zip(rx, ry)) / (n * (n * n - 1)) if n > 2 else None


def analyse(path):
    d = json.loads(Path(path).read_text())
    name = Path(d["stem"]).name
    cfg = d["configuration"]
    workers = cfg.get("node_workers") or cfg.get("workers")
    inst = [dict(i, pc=int(pc)) for pc, v in d["diagnostics"].items() for i in v["instances"]]
    final = [i for i in inst if i["status"] != "split"]
    secs = sorted((i["seconds"] for i in final), reverse=True)
    total = sum(secs)
    top = lambda f: sum(secs[:max(1, int(f * len(secs)))]) / total
    t = d["timings"]
    start = datetime.fromisoformat(d["started_at_utc"]).timestamp()
    proofs_start = start + t.get("analysis_and_setup", 0) + t["discovery"] + t["entry_H0"]
    proofs_end = proofs_start + t["proofs_and_H2"]
    by_pid = defaultdict(list)
    for i in inst:
        if i.get("started_at"):
            by_pid[i.get("pid")].append((i["started_at"], i["finished_at"]))
    gaps = lead = tail = 0.0
    for spans in by_pid.values():
        spans.sort()
        lead += max(0.0, spans[0][0] - proofs_start)
        tail += max(0.0, proofs_end - spans[-1][1])
        gaps += sum(max(0.0, b[0] - a[1]) for a, b in zip(spans, spans[1:]))
    kinds = Counter(i.get("proof_kind", "legacy") for i in final)
    chain = [i for i in final if i.get("proof_kind") == "instruction-chain/1"]
    chain_fail = [i for i in final if i.get("chain_attempt")]
    feats = features(name)
    legacy = [i for i in final if i.get("proof_kind") is None and i["status"] == "proved"]
    by_block = defaultdict(float)
    for i in final:
        by_block[i["pc"]] += i["seconds"]
    hot = sorted(by_block.items(), key=lambda kv: -kv[1])[:10]
    peaks = sorted((i.get("peak_rss_mb") or 0 for i in final), reverse=True)
    return dict(
        contract=name, status=d["status"], hints=bool(d.get("instruction_hints_sha256")), workers=workers,
        wall=round(d["process_wall_seconds"]), timings={k: round(v, 1) for k, v in t.items()},
        source_blocks=d.get("total_source_blocks"), blocks_with_instances=len(d["diagnostics"]),
        instances=len(final), contexts=sum(i.get("contexts", 1) for i in final), split_records=len(inst) - len(final),
        statuses=dict(Counter(i["status"] for i in final)), producers=dict(kinds),
        chain_after_legacy_fail=len(chain), legacy_after_chain_fail=len(chain_fail),
        chain_fail_seconds=round(sum(i["chain_attempt"]["seconds"] for i in chain_fail), 1),
        node_seconds=dict(sum=round(total), p50=round(pct(secs, .5), 1), p90=round(pct(secs, .9), 1),
                          p99=round(pct(secs, .99), 1), max=round(secs[0], 1),
                          top1pct_share=round(top(.01), 3), top10pct_share=round(top(.10), 3)),
        chain_node_seconds=dict(n=len(chain), sum=round(sum(i["seconds"] for i in chain)),
                                p50=round(pct([i["seconds"] for i in chain], .5) or 0, 1)),
        capacity=dict(worker_seconds=round(workers * t["proofs_and_H2"]), final_records=round(total),
                      hidden_gaps=round(gaps), lead_idle=round(lead), tail_idle=round(tail)),
        rss=dict(max=peaks[0] if peaks else None, p90=pct(peaks[::-1], .9)),
        hot_blocks=[dict(pc=pc, seconds=round(s), instances=sum(1 for i in final if i["pc"] == pc),
                         chain=sum(1 for i in chain if i["pc"] == pc), **feats.get(pc, {})) for pc, s in hot],
        length_vs_legacy_seconds=dict(
            n=len(legacy),
            spearman_ops=round(spearman([feats[i["pc"]]["ops"] for i in legacy], [i["seconds"] for i in legacy]), 3),
            spearman_x86=round(spearman([feats[i["pc"]]["x86_bytes"] for i in legacy],
                                        [i["seconds"] for i in legacy]), 3)),
        records=[dict(pc=i["pc"], s=round(i["seconds"], 2), kind=i.get("proof_kind", "legacy"), status=i["status"],
                      ctx=i.get("contexts", 1), rss=i.get("peak_rss_mb"), chain_fail=bool(i.get("chain_attempt")),
                      **feats.get(i["pc"], {})) for i in final])


if __name__ == "__main__":
    rows = [analyse(p) for p in sys.argv[2:]]
    Path(sys.argv[1]).write_text(json.dumps(rows, indent=1))
    for r in rows:
        print(json.dumps({k: v for k, v in r.items() if k not in ("records", "hot_blocks")}, ensure_ascii=False))
        for h in r["hot_blocks"][:5]:
            print("   hot", h)
