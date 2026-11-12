"""Render the V3 cost-analysis figures from the frozen figure-data.json (paper style, as fig/evaluation).

  MPLCONFIGDIR=/tmp/evm-paper-mpl python3 render_v3_figures.py
Palette (validated, adjacent order, light surface): blue, gold, pink, green, violet; grey = neutral/other.
Gold is below 3:1 on white, so every gold mark carries a direct value label or sits beside a labelled line.
"""
import json
from collections import Counter
from pathlib import Path
from statistics import median

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Patch
from matplotlib.ticker import PercentFormatter

HERE = Path(__import__("os").environ.get("E7_OUT", Path(__file__).resolve().parent))  # run.sh: results/
D = json.loads((HERE / "figure-data.json").read_text())
BLUE, GOLD, PINK, GREEN, VIOLET, GREY = "#386CB0", "#BE9200", "#B55C8E", "#6B8A3A", "#5E4FA2", "#BDBDBD"
EDGE, MUTED = "#444444", "#555555"
CAT = [("H2", BLUE), ("Local: obligation solving", GOLD), ("Local: construction", PINK),
       ("Shared lemmas", GREEN), ("Instruction chain", VIOLET), ("Other", GREY)]
LIGHT_INK = {GOLD, GREY}  # dark text on these fills, white elsewhere
ORDER4 = ["ENSRegistry", "CErc20", "PoolManager", "Pool"]
ORDER5 = ["ENSRegistry", "CErc20", "Safe", "PoolManager", "Pool"]
plt.rcParams.update({"font.size": 8.5, "axes.titlesize": 9, "axes.labelsize": 8.5, "legend.fontsize": 8,
                     "pdf.fonttype": 42, "ps.fonttype": 42, "axes.spines.top": False,
                     "axes.spines.right": False, "axes.grid": False})


def save(fig, name):
    fig.savefig(HERE / f"{name}.pdf")
    fig.savefig(HERE / f"{name}.png", dpi=200)
    plt.close(fig)


def stacked_row(ax, y, parts, height=.55, label_min=.07):
    left = 0.0
    for value, color, hatch in parts:
        if value <= 0:
            continue
        ax.barh(y, value, left=left, color=color, edgecolor="white", linewidth=1.0, height=height, hatch=hatch)
        if value >= label_min:
            ax.text(left + value / 2, y, f"{100 * value:.0f}%", ha="center", va="center", fontsize=7.5,
                    color="black" if color in LIGHT_INK else "white")
        left += value
    return left


def patch(color, label, hatch=""):
    return Patch(facecolor=color, edgecolor=EDGE, linewidth=.4, hatch=hatch, label=label)


def where():
    fig, ax = plt.subplots(figsize=(5.5, 2.2))
    fig.subplots_adjust(left=.25, right=.97, bottom=.2, top=.72)
    for y, c in enumerate(ORDER4):
        row = D["where"][c]
        total = stacked_row(ax, y, [(row.get(name, 0), color, "") for name, color in CAT])
        assert abs(total - 1) < .02, (c, total)
    ax.set(yticks=range(4), yticklabels=[f"{c} (n={D['sample_sizes'][c]})" for c in ORDER4], xlim=(0, 1),
           xlabel="Share of node proof time (PPS-weighted replays)")
    ax.xaxis.set_major_formatter(PercentFormatter(1.0))
    ax.invert_yaxis()
    fig.legend(handles=[patch(c, n) for n, c in CAT], loc="upper center", ncol=3, frameon=False,
               bbox_to_anchor=(.55, 1), columnspacing=1)
    save(fig, "v3-cost-where")


def repetition():
    fig, (ax, ms) = plt.subplots(1, 2, figsize=(5.5, 2.4), sharey=True, gridspec_kw={"width_ratios": [1.55, 1]})
    fig.subplots_adjust(left=.17, right=.95, bottom=.2, top=.7, wspace=.22)
    for y, c in enumerate(ORDER5):
        r = D["repetition"][c]
        stacked_row(ax, y, [(1 - r["same_block"], GREY, ""), (r["depth_only"], BLUE, ""),
                            (r["same_block"] - r["depth_only"], GOLD, "")])
        v = r["msize_unknown"]
        ms.barh(y, v, color=PINK, edgecolor=EDGE, linewidth=.5, height=.55)
        ms.text(v + .03, y, f"{100 * v:.0f}%", va="center", fontsize=7.5)
    ax.set(yticks=range(5), yticklabels=ORDER5, xlim=(0, 1), xticks=[0, .5, 1], xlabel="Share of node proof time",
           title="(a) Repeated proofs of one block")
    ms.set(xlim=(0, 1.15), xticks=[0, .5, 1], xlabel="Share of node proof time", title="(b) Unknown msize")
    for a in (ax, ms):
        a.xaxis.set_major_formatter(PercentFormatter(1.0))
    ax.invert_yaxis()
    fig.legend(handles=[patch(GREY, "Costliest instance per block"), patch(BLUE, "Depth-only repeats"),
                        patch(GOLD, "Other repeats"), patch(PINK, "Instances with unknown msize")],
               loc="upper center", ncol=2, frameon=False, bbox_to_anchor=(.55, 1.01), columnspacing=1.2,
               handletextpad=.4, fontsize=7.5)
    save(fig, "v3-cost-repetition")


def mechanisms():
    fig, (a, b, c) = plt.subplots(1, 3, figsize=(5.5, 2.45), gridspec_kw={"width_ratios": [1, 1, .85]})
    fig.subplots_adjust(left=.09, right=.98, bottom=.2, top=.68, wspace=.45)
    k = [r["contexts"] for r in D["ectx"]]
    a.plot(k, [r["h2"] for r in D["ectx"]], color=BLUE, marker="o", ms=4, lw=1.5)
    a.plot(k, [r["local_solving"] for r in D["ectx"]], color=GOLD, marker="s", ms=4, lw=1.5)
    a.set(xscale="log", xticks=k, xticklabels=k, xlabel="Contexts per instance", ylabel="Seconds",
          ylim=(0, 140), title="(a) E-ctx")
    a.minorticks_off()
    d = [r["entry_depth"] for r in D["edepth"]]
    b.plot(d, [r["instance"] for r in D["edepth"]], color=PINK, marker="^", ms=4, lw=1.5)
    b.plot(d, [r["h2"] for r in D["edepth"]], color=BLUE, marker="o", ms=4, lw=1.5)
    b.plot(d, [r["local_solving"] for r in D["edepth"]], color=GOLD, marker="s", ms=4, lw=1.5)
    b.set(xlabel="Entry stack depth", ylim=(0, 220), title="(b) E-depth")
    for x, row in enumerate(D["emsize"]):
        parts = [(row["local_solving"], GOLD, ""), (row["h2_quick"], BLUE, ""), (row["h2_close_edge"], BLUE, "////")]
        parts.append((row["instance"] - sum(v for v, _, _ in parts), GREY, ""))
        assert parts[-1][0] >= 0
        bottom = 0
        for v, color, hatch in parts:
            c.bar(x, v, bottom=bottom, color=color, edgecolor="white", linewidth=1, hatch=hatch, width=.6)
            bottom += v
        c.text(x, bottom + 5, f"{row['instance']:.0f} s", ha="center", fontsize=7.5)
    c.set(xticks=[0, 1], xticklabels=["known", "symbolic"], xlabel="msize", ylim=(0, 250), title="(c) E-msize")
    fig.legend(handles=[Line2D([], [], color=BLUE, marker="o", ms=4, label="H2"),
                        patch(BLUE, "H2 per-conjunct (close_edge)", "////"),
                        Line2D([], [], color=GOLD, marker="s", ms=4, label="Local obligation solving"),
                        Line2D([], [], color=PINK, marker="^", ms=4, label="Block instance total"),
                        patch(GREY, "Rest of instance")],
               loc="upper center", ncol=3, frameon=False, bbox_to_anchor=(.5, 1.01), columnspacing=1,
               handletextpad=.4, fontsize=7.5)
    save(fig, "v3-cost-mechanisms")


def lemma():
    rows = D["lemma"]
    fig, (a, b) = plt.subplots(1, 2, figsize=(5.5, 2.2))
    fig.subplots_adjust(left=.1, right=.97, bottom=.22, top=.86, wspace=.38)
    ws = sorted({r["workers"] for r in rows})
    med = lambda w, key: median(r[key] for r in rows if r["workers"] == w)
    built, solved = [med(w, "built") for w in ws], [med(w, "solved") for w in ws]
    a.plot(ws, built, color=BLUE, marker="o", ms=4, lw=1.5)
    a.plot(ws, solved, color=GOLD, marker="s", ms=4, lw=1.5)
    a.text(8.6, built[-1], "constructed", va="center", fontsize=7.5)
    a.text(8.6, solved[-1], "solved", va="center", fontsize=7.5)
    a.axhline(4, color=MUTED, lw=1, ls="--")
    a.text(8, 2.4, "4 distinct lemmas", ha="right", fontsize=7.5, color=MUTED)
    a.set(xscale="log", xticks=ws, xticklabels=ws, xlim=(.85, 16), xlabel="Node workers", ylabel="Lemma proofs",
          ylim=(0, 17), title="(a) Shared-lemma proofs (ENS)")
    a.minorticks_off()
    walls = [(r["workers"], r["wall"]) for r in rows]
    b.scatter([w for w, _ in walls], [t for _, t in walls], color=BLUE, s=16, zorder=3)
    b.plot(ws, [med(w, "wall") for w in ws], color=BLUE, lw=1.5)
    base = med(1, "wall")
    b.plot(ws, [base / w for w in ws], color=MUTED, lw=1, ls="--")
    b.text(8.6, med(8, "wall"), "measured", va="center", fontsize=7.5)
    b.text(8.6, base / 8, "ideal 1/w", va="center", fontsize=7.5, color=MUTED)
    b.set(xscale="log", xticks=ws, xticklabels=ws, xlim=(.85, 16), xlabel="Node workers", ylabel="Wall seconds",
          ylim=(0, 1500), title="(b) Complete ENS wall time")
    b.minorticks_off()
    save(fig, "v3-cost-lemma")


def short(r):
    block = r["run"].split("-")[2].split("_")[0]
    contract = {"PoolManager": "PM", "CErc20": "CErc20"}[r["run"].split("-")[0]]
    n = r["obligation"]
    kind = ("H2 live stack" if "live_stack" in n else "H2 memory gas" if "memory_gas" in n else
            "H2 gas" if "_gas_" in n else "x86 coverage" if n == "x86_coverage" else
            "group trial" if "group" in n else "path pair" if n.startswith("pair") else n)
    return f"{contract} {block}: {kind}"


def routing():
    rows = sorted(D["routing"], key=lambda r: r["production"])
    labels = [short(r) for r in rows]
    seen, count = Counter(), Counter(labels)
    for i, l in enumerate(labels):  # same block and kind twice: number them
        if count[l] > 1:
            seen[l] += 1
            labels[i] = f"{l} #{seen[l]}"
    fig, ax = plt.subplots(figsize=(5.5, 3.2))
    fig.subplots_adjust(left=.36, right=.97, bottom=.13, top=.86)
    for y, r in enumerate(rows):
        ax.plot([r["best"], r["production"]], [y, y], color=GREY, lw=1.5, zorder=1)
        unknown = r["production_answer"] != "unsat"
        ax.scatter(r["production"], y, s=28, zorder=3, facecolor="white" if unknown else MUTED, edgecolor=MUTED)
        ax.scatter(r["best"], y, s=28, zorder=3, color=BLUE)
        right = r["best"] > .7 * r["production"]
        ax.text(r["best"] * (1.15 if right else 1 / 1.15), y, r["best_route"], ha="left" if right else "right",
                va="center", fontsize=7, color=MUTED)
    ax.set(xscale="log", xlim=(3, 1000), yticks=range(len(rows)), yticklabels=labels, xlabel="Seconds (log scale)")
    tot_p, tot_b = sum(r["production"] for r in rows), sum(r["best"] for r in rows)
    ax.set_title(f"Production cascade {tot_p:.0f} s vs fastest single route {tot_b:.0f} s", fontsize=8.5)
    fig.legend(handles=[Line2D([], [], color=MUTED, marker="o", lw=0, label="Production cascade"),
                        Line2D([], [], markerfacecolor="white", markeredgecolor=MUTED, marker="o", lw=0,
                               label="Cascade ended unknown"),
                        Line2D([], [], color=BLUE, marker="o", lw=0, label="Fastest single route")],
               loc="upper center", ncol=3, frameon=False, bbox_to_anchor=(.5, 1.0), handletextpad=.3, fontsize=7.5)
    save(fig, "v3-cost-routing")


def schedule():
    rows = {r["contract"]: r for r in D["schedule"]}
    fig, ax = plt.subplots(figsize=(5.5, 2.1))
    fig.subplots_adjust(left=.25, right=.95, bottom=.22, top=.8)
    for y, c in enumerate(ORDER4):
        r = rows[c]
        lpt, lb = r["lpt_block"] / r["production"], r["lower_bound"] / r["production"]
        ax.barh(y - .17, 1, height=.32, color=GREY, edgecolor=EDGE, linewidth=.5)
        ax.barh(y + .17, lpt, height=.32, color=BLUE, edgecolor=EDGE, linewidth=.5)
        ax.plot([lb, lb], [y - .35, y + .35], color="black", lw=1.2)
        ax.text(max(lpt, lb) + .015, y + .17, f"−{100 * (1 - lpt):.0f}%", va="center", fontsize=7.5)
    ax.set(yticks=range(4), yticklabels=[f"{c} ({rows[c]['workers']} w)" for c in ORDER4], xlim=(0, 1.1),
           xlabel="Proof-phase span relative to production")
    ax.xaxis.set_major_formatter(PercentFormatter(1.0))
    ax.invert_yaxis()
    fig.legend(handles=[patch(GREY, "Production order"), patch(BLUE, "Longest-first (block median)"),
                        Line2D([], [], color="black", lw=1.2, label="Lower bound")],
               loc="upper center", ncol=3, frameon=False, bbox_to_anchor=(.6, 1), columnspacing=1, handletextpad=.4)
    save(fig, "v3-cost-schedule")


def tail():
    fig, ax = plt.subplots(figsize=(5.5, 2.3))
    fig.subplots_adjust(left=.24, right=.95, bottom=.2, top=.82)
    for y, c in enumerate(ORDER5):
        r = D["concentration"][c]
        ax.barh(y + .17, r["top10"], height=.32, color=BLUE, edgecolor=EDGE, linewidth=.5)
        ax.barh(y - .17, r["top1"], height=.32, color=GOLD, edgecolor=EDGE, linewidth=.5)
        ax.text(r["top10"] + .01, y + .17, f"{100 * r['top10']:.0f}%", va="center", fontsize=7.5)
        ax.text(r["top1"] + .01, y - .17, f"{100 * r['top1']:.0f}%", va="center", fontsize=7.5)
    ax.set(yticks=range(5), yticklabels=[f"{c} ({D['concentration'][c]['instances']})" for c in ORDER5],
           xlim=(0, 1), xlabel="Share of node proof time (complete certification runs)")
    ax.xaxis.set_major_formatter(PercentFormatter(1.0))
    ax.invert_yaxis()
    fig.legend(handles=[patch(GOLD, "Most expensive 1% of instances"), patch(BLUE, "Most expensive 10% of instances")],
               loc="upper center", ncol=2, frameon=False, bbox_to_anchor=(.58, 1))
    save(fig, "v3-cost-tail")


if __name__ == "__main__":
    for f in (tail, where, repetition, mechanisms, lemma, routing, schedule):
        f()
    print("rendered", sorted(p.name for p in HERE.glob("v3-cost-*.pdf")))
