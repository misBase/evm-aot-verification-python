"""Plot completed timing costs and separate timeout outcomes, without imputation."""
from hashlib import sha256
import json
import os
from pathlib import Path
import statistics

os.environ.setdefault('MPLCONFIGDIR', '/tmp/evm-paper-v2-mpl')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

HERE = Path(__file__).resolve().parents[1]  # artifact layout: experiments/E6-shift
ROOT = HERE
SOURCE = HERE / 'expected/TIMING-ROOT-ANALYSIS.json'
OUT = HERE / 'figures'
OUT.mkdir(exist_ok=True)
data = json.loads(SOURCE.read_bytes())
assert data['executed'] == 36 and data['skipped'] == 12
assert data['outcomes'] == {'VERIFIED': 30, 'TO': 6}
for name, digest in data['guard_receipts_sha256'].items():
    # The per-run guard receipts live in the original run directory; check them only where present.
    if (ROOT / name).is_file():
        assert sha256((ROOT / name).read_bytes()).hexdigest() == digest
groups = {(g['k'], g['shift_summary']): g for g in data['groups']}
assert set(groups) == {(k, enabled) for k in range(1, 9) for enabled in (False, True)}

plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10})
fig = plt.figure(figsize=(11.3, 7.1))
grid = fig.add_gridspec(2, 1, height_ratios=(3.1, 1), left=.09, right=.97,
                      top=.84, bottom=.18, hspace=.28)
ax = fig.add_subplot(grid[0])
outcomes = fig.add_subplot(grid[1], sharex=ax)
plotted = []
for enabled, color, marker, style in ((False, '#bf7720', 's', '--'),
                                     (True, '#20678c', 'o', '-')):
    points = []
    for k in range(1, 9):
        group = groups[k, enabled]
        trials = group['trials']
        completed = all(t['result'] == 'VERIFIED' and not t['cpu_lower_bound'] for t in trials)
        if completed:
            assert len(trials) == group['required_repeats'] == 3
            values = [t['cpu_s'] for t in trials]
            middle = statistics.median(values)
            assert middle == group['completion_median_cpu_s']
            points.append((k, middle, middle - min(values), max(values) - middle))
            text, fill, edge, hatch = '3 / 3 P', '#e5f0f7', '#20678c', None
        else:
            assert len(trials) == group['required_repeats'] == 1 and trials[0]['result'] == 'TO'
            assert group['completion_median_cpu_s'] is None
            text, fill, edge, hatch = 'TO\n1 trial', '#fff1cf', '#ad7d1e', '//'
        row = 0 if enabled else 1
        outcomes.add_patch(Rectangle((k - .43, row - .31), .86, .62,
            facecolor=fill, edgecolor=edge, hatch=hatch, linewidth=.8))
        outcomes.text(k, row, text, ha='center', va='center', fontsize=9)
        plotted.append(dict(k=k, shift_summary=enabled, completed_cpu_point=completed,
            median_cpu_s=group['completion_median_cpu_s'], outcomes=[t['result'] for t in trials]))
    ax.errorbar([p[0] for p in points], [p[1] for p in points],
        yerr=[[p[2] for p in points], [p[3] for p in points]], color=color,
        marker=marker, linestyle=style, markersize=5, linewidth=1.5, capsize=3,
        label='Shift fallback' if enabled else 'Shift off (other summaries unchanged)')
ax.set_yscale('log')
ax.set_ylim(2, 100)
ax.set_ylabel('Completed verification CPU (seconds, log scale)')
ax.set_xticks(range(1, 9))
ax.tick_params(labelbottom=False)
ax.grid(axis='y', color='#dddddd', linewidth=.6)
ax.spines[['right', 'top']].set_visible(False)
ax.legend(loc='upper right', frameon=False)
ax.text(5.4, 35, 'Off, k = 3–8: external 600 s timeouts\nNo completed CPU-time coordinate',
        ha='center', va='center', fontsize=10, color='#795a1e')
outcomes.set_xlim(.5, 8.5)
outcomes.set_ylim(-.5, 1.5)
outcomes.set_yticks((1, 0), ('Shift off', 'Shift fallback'))
outcomes.set_xticks(range(1, 9))
outcomes.set_xlabel('Number of independent variable SHR operations (k)')
outcomes.spines[:].set_visible(False)
outcomes.tick_params(axis='y', length=0)
fig.suptitle('E2.2 | Shift summaries on a straight EVM family', x=.09, ha='left', fontsize=17, y=.975)
fig.text(.09, .915, 'Z6a d213 / 113 files · local M1 Pro · gas OFF · fixed 512-byte calldata · depth 400', fontsize=10)
fig.text(.09, .074, 'Completed points: median of 3 fresh processes; whiskers = min–max, not confidence intervals.', fontsize=9)
fig.text(.09, .046, 'TO cells show outcomes only. R1 wall > 300 s omits R2/R3: 36 actual trials + 12 protocol skips.', fontsize=9)
fig.text(.09, .018, 'P = VERIFIED. Main timing has no owned observer; separate diagnostics are excluded.', fontsize=9)
OUT.mkdir(exist_ok=True)
for suffix in ('png', 'pdf'):
    fig.savefig(OUT / f'E22_shift_summary.{suffix}', dpi=180)
plt.close(fig)
(OUT / 'E22_shift_summary.source.json').write_text(json.dumps(dict(
    source=str(SOURCE.relative_to(HERE)), source_sha256=sha256(SOURCE.read_bytes()).hexdigest(),
    generator_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), points=plotted,
    limits=['TO has no completed-proof time', 'Other7 summary modes fixed',
            'Only this declared synthetic512-byte input family; no general fitted growth rate']), indent=2) + '\n')
print(OUT / 'E22_shift_summary.png')
