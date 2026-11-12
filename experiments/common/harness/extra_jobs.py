"""V2 design has no hot-added V2L or lockstep-ablation jobs.

Repeats and long runs use explicit fresh output directories under root's schedule.
"""


def extra(fixtures, out_dir):
    return []
