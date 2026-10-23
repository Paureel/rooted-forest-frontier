#!/usr/bin/env python3
"""One-shot fresh review instrument; not a general toolkit or census.
Uses explicit adjacency/BFS, never author Lean, Python, or stored results.
Known frozen fixtures are regressions. Run via ./bootloops-python this_file.
Exact set/count checks are valid only for the finite fixtures listed here.
Each case must pass its fixed expected value and reject its wrong-result twin.
"""
from collections import deque
from pathlib import Path
import hashlib, json, time

HERE = Path(__file__).resolve().parent

def graph(edges):
    g = {'': set()}
    for a, b in edges:
        g.setdefault(a, set()).add(b)
        g.setdefault(b, set()).add(a)
    return g

def path(g, start, end):
    q = deque([(start, [start])]); seen = {start}
    while q:
        v, p = q.popleft()
        if v == end: return set(p)
        for w in g[v] - seen:
            seen.add(w); q.append((w, p + [w]))
    raise ValueError('disconnected fixture')

def convex(g, s):
    return all(path(g, a, b) <= s for a in s for b in s)

def trim(g, labels, s):
    return set().union(*(path(g, '', a) for a in s & labels))

def shape(g, labels, s):
    c = trim(g, labels, s)
    return {'support': sorted(c), 'labels': sorted(c & labels),
            'convex': convex(g, c), 'subset': c <= s}

def family(g, labels, regions):
    sets = list(regions.values())
    assert all(s <= set(g) and convex(g, s) and bool(s & labels) for s in sets)
    assert all(not a & b for i, a in enumerate(sets) for b in sets[i+1:])
    assert set().union(*sets) & labels == labels
    owners = [k for k, s in regions.items() if '' in s]
    assert len(owners) <= 1
    return {'count': len(regions), 'closed': sum('' not in s for s in sets),
            'root_owners': owners, 'labels': {k: sorted(s & labels) for k, s in regions.items()}}

def checked(name, got, expected, wrong):
    clean = got == expected
    rejected = got != wrong
    if not clean or not rejected:
        raise AssertionError({'name': name, 'got': got, 'expected': expected, 'wrong': wrong})
    return {'name': name, 'got': got, 'expected': expected, 'wrong_result': wrong,
            'clean_pass': clean, 'wrong_rejected': rejected}

start = time.perf_counter(); rows = []
# Fixed graph edges explicitly authored from frozen specifications.
g = graph([('', '0'), ('', '1'), ('0', '00'), ('0', '01'), ('1', '10'), ('1', '11')])
leaves = {'00', '01', '10', '11'}
r0 = {'', '0', '00'}; r1 = r0 | {'1'}
expected = {'support': ['', '0', '00'], 'labels': ['00'], 'convex': True, 'subset': True}
for name, s in [('R0', r0), ('R1_leafless_child', r1)]:
    assert convex(g, s)
    rows.append(checked(name, shape(g, leaves, s), expected, {**expected, 'support': sorted(r1)} if s == r0 else {**expected, 'labels': ['00','10']}))
rows.append(checked('gapped_support', convex(g, {'', '00'}), False, True))
g2 = graph([('', '0'), ('', '1'), ('1', '10'), ('1', '11'), ('10', '100'), ('10', '101')])
l2 = {'0', '100', '101', '11'}
for name, s, labs in [('R2_opposite_label_kept', {'', '1', '10', '100', '11', '0'}, ['0', '100', '11']), ('R3_one_child_only', {'', '1', '10', '100', '11'}, ['100', '11'])]:
    e = {'support': sorted(s), 'labels': labs, 'convex': True, 'subset': True}
    rows.append(checked(name, shape(g2, l2, s), e, {**e, 'support': sorted(s - {'11'})}))
e = {'support': [], 'labels': [], 'convex': True, 'subset': True}
rows.append(checked('leafless_open_discard', shape(g, leaves, {'', '1'}), e, {**e, 'support': ['']}))
e = {'support': [''], 'labels': [''], 'convex': True, 'subset': True}
rows.append(checked('root_label_trim', shape({'': set()}, {''}, {''}), e, {**e, 'support': []}))
# Adjacent same-color blocks retain identity, and unused vertices need not be covered.
regions = {'A7': {'0', '00'}, 'B7': {'01'}, 'C8': {'10'}, 'D9': {'11'}}
e = {'count': 4, 'closed': 4, 'root_owners': [], 'labels': {'A7':['00'], 'B7':['01'], 'C8':['10'], 'D9':['11']}}
rows.append(checked('adjacent_same_color_unused_internal', family(g, leaves, regions), e, {**e, 'count': 3}))
# Explicit cherry child singleton families are lifted to disjoint vertex sets.
cherry = graph([('', '0'), ('', '1')]); cl = {'0', '1'}
for name, regions, closed, owner, toll in [
    ('close_both', {'L': {'0'}, 'R': {'1'}}, 2, [], 2),
    ('extend_left', {'L': {'', '0'}, 'R': {'1'}}, 1, ['L'], 1),
    ('extend_right', {'L': {'0'}, 'R': {'', '1'}}, 1, ['R'], 1)]:
    got = family(cherry, cl, regions)
    child_costs = family({'': set()}, {''}, {'child': {''}})['closed'] * 2
    got['toll'] = got['closed'] - child_costs
    e = {'count': 2, 'closed': closed, 'root_owners': owner,
         'labels': {'L':['0'], 'R':['1']}, 'toll': toll}
    rows.append(checked(name, got, e, {**e, 'count': 1}))
    rows.append(checked(name+'_toll', got['toll'], toll, toll+1))
e = {'count': 1, 'closed': 0, 'root_owners': ['M'], 'labels': {'M':['0','1']}}
rows.append(checked('manual_merge_fixture_only', family(cherry, cl, {'M':{'','0','1'}}), e, {**e, 'count':2}))
single = family({'': set()}, {''}, {'S': {''}})
rows.append(checked('singleton_closing_charge', single['closed'] + len(single['root_owners']), 1, 0))
assert len(rows) == 16
out = {'schema': 1, 'scope':'finite frozen regressions; no census or universal proof',
       'engine':'stdlib adjacency plus BFS; exact sets and integers',
       'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'rows':rows, 'clean_passed':sum(r['clean_pass'] for r in rows),
       'wrong_rejected':sum(r['wrong_rejected'] for r in rows),
       'elapsed_seconds':time.perf_counter()-start}
(HERE/'exact_graph_check.json').write_text(json.dumps(out, indent=2)+'\n')
print(f"PASS {len(rows)}/16 exact fixture clean twins; {out['wrong_rejected']}/16 wrong-result twins rejected")
