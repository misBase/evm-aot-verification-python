from verification.block_parallel import LeaderFirstSchedule
from verification.block_specialization import BlockSpecialization as S

FIRST, FULL = 300, 3600
# Group (10, 64, 128): leader is `a` (fewest constants, then shallowest), siblings b, c.
a, b, c = S(10, 2, 64, 128), S(10, 1, 64, 128, ((0, 7),)), S(10, 3, 64, 128)
d = S(20, 1, 64, 128)  # lone group
e, f = S(10, 2, 96, 128), S(10, 4, 96, 128)  # same pc, other MSize: its own group


def drain(schedule):
    out = []
    while (item := schedule.pop())[0] is not None:
        out.append(item)
    return out


def test_leaders_first_then_siblings_after_their_leader():
    s = LeaderFirstSchedule([b, a, c, d, e, f], FIRST, FULL)
    assert drain(s) == [(a, FIRST), (d, FIRST), (e, FIRST)]
    assert sorted(map(repr, s.pending())) == sorted(map(repr, [b, c, f]))
    s.finish(e)
    assert drain(s) == [(f, FIRST)]
    s.finish(a)
    assert drain(s) == [(b, FIRST), (c, FIRST)]
    assert s.pending() == [] and not s.full_start


def test_retried_leader_blocks_siblings_then_releases_them_at_full_budget():
    s = LeaderFirstSchedule([a, b, c, d], FIRST, FULL)
    assert s.pop() == (a, FIRST)
    s.retry(a)  # first pass failed, not sat
    assert s.pop() == (a, FULL)  # the retry jumps ahead of other leaders
    assert s.pop() == (d, FIRST) and s.pop() == (None, None)
    s.finish(a)  # proved or not, siblings are released
    assert drain(s) == [(b, FULL), (c, FULL)]
    # Full-budget siblings are not retried again; first-pass siblings still are.
    assert {a, b, c} <= s.full_start and d not in s.full_start


def test_sibling_failing_first_pass_gets_one_full_retry():
    s = LeaderFirstSchedule([a, b], FIRST, FULL)
    s.pop()
    s.finish(a)
    assert s.pop() == (b, FIRST) and b not in s.full_start
    s.retry(b)
    assert s.pop() == (b, FULL) and b in s.full_start


def test_resume_picks_a_leader_among_the_remaining():
    s = LeaderFirstSchedule([b, c], FIRST, FULL)  # `a` proved in results_dir
    assert drain(s) == [(c, FIRST)]  # no constants beats one constant
    s.finish(c)
    assert drain(s) == [(b, FIRST)]


def test_split_contexts_are_released_at_the_given_budget():
    s = LeaderFirstSchedule([a], FIRST, FULL)
    assert s.pop() == (a, FIRST)
    s.finish(a)
    s.add([b, c], FULL)  # a proof instance failed at the full budget: its contexts
    assert drain(s) == [(b, FULL), (c, FULL)] and {b, c} <= s.full_start
