"""Freeze every number the V3 cost figures plot into figure-data.json (run once; render reads only that file).

  python3 build_figure_data.py   (from any cwd; paths are relative to this file)
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
RES = HERE.parent                                   # experiments/E7-v3-costs
RUNS = RES / "runs"                                 # raw replay events
load = lambda p: json.loads(Path(p).read_text())

CATS = {"H2": "H2", "局部:义务求解": "Local: obligation solving", "局部:建项/配对/摘要": "Local: construction",
        "局部:符号执行与summary": "Local: construction", "共享引理": "Shared lemmas", "指令链": "Instruction chain",
        "其他(任务框架)": "Other"}


def buckets(run):
    """Exclusive buckets of the run's longest task only (the synthetic block F), not the whole program."""
    import sys
    sys.path.insert(0, str(RES / "tools"))
    from analyze import bucket, load as load_spans
    spans = load_spans(RUNS / run)
    by_id = {(s["pid"], s["id"]): s for s in spans}
    task = max((s for s in spans if s["label"] == "task" and s["wall"]), key=lambda s: s["wall"])
    out = {}
    for s in spans:
        a = s
        while a is not None and a is not task:
            a = by_id.get((a["pid"], a["parent"]))
        if a is task and s["excl"] is not None:
            out.setdefault(bucket(s), {"s": 0.0})["s"] += s["excl"]
    return {k: {"s": round(v["s"], 1)} for k, v in out.items()}


def h2(b):
    return sum(v["s"] for k, v in b.items() if k.startswith(("h2.", "check@h2", "rel.goals")) or k == "check@other")


def f_instance(run, program):
    d = load(RES / "local" / run / f"{program}.json")
    return max(i["seconds"] for v in d["diagnostics"].values() for i in v["instances"])


def lemma_counts(run):
    enter, built, solved, seconds = {}, 0, 0, 0.0
    for f in (RUNS / run / "events").glob("pid-*.jsonl"):
        for line in f.open():
            d = json.loads(line)
            if d["event"] == "enter":
                enter[(d["pid"], d["id"])] = d
            elif d.get("label") == "lemma.prove" and not enter[(d["pid"], d["id"])]["metadata"].get("hit"):
                built += 1
                seconds += d["wall_inclusive_s"]
            elif d.get("label") == "lemma.cache_lookup" and not d["metadata"].get("hit"):
                solved += 1
    receipt = load(RES / "local" / run / "receipt.json")
    return dict(built=built, solved=solved, lemma_seconds=round(seconds, 1), wall=receipt["wall_s"],
                cpu=receipt["children_cpu_s"])


def where_rows(weighted):
    where = {}
    for contract, v in weighted.items():
        row = {}
        for k, x in v["categories"].items():
            row[CATS[k]] = row.get(CATS[k], 0) + x
        where[contract] = {k: round(x, 4) for k, x in row.items()}
    return where


def main():
    master = load(RES / "analysis/master.json")
    weighted = load(RES / "analysis/a2s-weighted.json")["weighted"]
    where = where_rows(weighted)
    # Safe's eight A2-S replays were added later (same seed, snapshot, tools and configuration).
    with_safe = load(RES / "analysis/a2s-weighted-with-safe.json")
    where_with_safe = where_rows(with_safe["weighted"])
    assert all(where_with_safe[c] == where[c] for c in where), "adding Safe changed another contract"
    ectx = []
    for k, run, prog in [(1, "ectx-same-k1", "ctx_same_k1"), (2, "ectx-same-k2", "ctx_same_k2"),
                         (4, "ectx-ctx_same_k4", "ctx_same_k4"), (8, "ectx-ctx_same_k8", "ctx_same_k8")]:
        b = buckets(run)
        ectx.append(dict(contexts=k, h2=round(h2(b), 1), local_solving=b["check@local.prove"]["s"],
                         instance=round(f_instance(run, prog), 1)))
    edepth = []
    for pad in (0, 8, 16, 32, 64):
        run, prog = f"edepth-depth_d{pad}", f"depth_d{pad}"
        b = buckets(run)
        edepth.append(dict(entry_depth=pad + 3, h2=round(h2(b), 1), instance=round(f_instance(run, prog), 1),
                           local_solving=b["check@local.prove"]["s"]))
    emsize = []
    for label, run, prog in [("known", "emsize-msize_const", "msize_const"), ("symbolic", "emsize-msize_sym", "msize_sym")]:
        b = buckets(run)
        close = sum(v["s"] for k, v in b.items() if k in ("h2.close_edge", "h2.prepare_shared") or k.startswith("check@h2"))
        emsize.append(dict(msize=label, instance=round(f_instance(run, prog), 1), h2_quick=b.get("h2.quick", {}).get("s", 0.0),
                           h2_close_edge=round(close, 1), local_solving=b["check@local.prove"]["s"]))
    lemma = [dict(workers=w, **lemma_counts(run)) for w, run in
             [(1, "b1a-w1"), (2, "b1a-w2"), (4, "mc2-on-1"), (4, "mc2-on-2"), (8, "b1a-w8")]]
    sim = [json.loads(l) for l in (RES / "analysis/sim.jsonl").read_text().splitlines() if l.strip()]
    data = dict(
        source="results/2026-11-12-v3 (c68c4df); built by figures/build_figure_data.py",
        concentration={c: dict(top10=m["top10"], top1=m["top1"], instances=m["instances"]) for c, m in master.items()},
        repetition={c: dict(same_block=m["same_block"], depth_only=m["depth_only"], msize_unknown=m["mnone"])
                    for c, m in master.items()},
        where=where,
        sample_sizes={c: sum(1 for r in load(RES / "analysis/a2s-weighted.json")["rows"] if r["contract"] == c)
                      for c in weighted},
        where_with_safe=where_with_safe,
        sample_sizes_with_safe={c: sum(1 for r in with_safe["rows"] if r["contract"] == c) for c in where_with_safe},
        ectx=ectx, edepth=edepth, emsize=emsize,
        cerc20_14263=dict(per_context_known=249, per_context_unknown=851, contexts_known=1.0, contexts_unknown=3.2),
        lemma=lemma,
        routing=[dict(obligation=r["name"], run=r["run"], production=r["production_wall"],
                      production_answer=r["production_answer"], best_route=r["best"][0], best=r["best"][1])
                 for r in load(RES / "analysis/b2.json")],
        schedule=[dict(contract=s["contract"].split(" ")[0], workers=s["workers"], production=s["production"],
                       lpt_block=s["lpt_block"], lower_bound=s["lower_bound"]) for s in sim
                  if not s["contract"].startswith("Safe")])
    # Data guards: what the captions claim.
    assert all(r["built"] >= 4 and r["solved"] >= 4 for r in data["lemma"]), "lemma events not found"
    assert len(data["routing"]) == 12 and len(data["ectx"]) == 4 and len(data["edepth"]) == 5
    assert all(abs(sum(v.values()) - 1) < 0.02 for v in where_with_safe.values())
    assert sorted(s["contract"] for s in data["schedule"]) == ["CErc20", "ENSRegistry", "Pool", "PoolManager"]
    OUT = Path(__import__("os").environ.get("E7_OUT", HERE))  # run.sh writes to results/
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "figure-data.json").write_text(json.dumps(data, indent=1, ensure_ascii=False))
    print(json.dumps(data, ensure_ascii=False)[:1500])


if __name__ == "__main__":
    main()
