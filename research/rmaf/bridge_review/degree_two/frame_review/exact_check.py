#!/usr/bin/env python3
"""One-shot independent final-review checker, 2026-10-14.
Uses no project modules. Tests literal trees/partitions from FROZEN-CONTROLS.
Outputs exact fixtures and positive/negative controls; a failure raises with a
retained partial result. This is bounded semantic evidence, not a proof.
"""
import hashlib, json, time
from pathlib import Path
from itertools import combinations
BASE = Path(__file__).resolve().parent
started = time.perf_counter()
spec = json.loads((BASE / 'FROZEN-CONTROLS.json').read_text())
rows = []

def leaves(t, p=()):
    if isinstance(t, int):
        return [(t, p)]
    return leaves(t[0], p+(False,)) + leaves(t[1], p+(True,))

def eligible(t, labels):
    lab = [a for a, _ in leaves(t)]
    return len(set(lab)) == len(lab) and len(set(labels)) == len(labels) and set(labels) <= set(lab)

def support(t, labels):
    if not eligible(t, labels):
        raise ValueError('unique labels and actual occurrence required')
    points = [p for a, p in leaves(t) if a in labels]
    out = set(points)
    for p, q in combinations(points, 2):
        k = 0
        while k < min(len(p), len(q)) and p[k] == q[k]:
            k += 1
        out.update(p[:j] for j in range(k, len(p)+1))
        out.update(q[:j] for j in range(k, len(q)+1))
    return out

def degree(vertices, p):
    if p not in vertices:
        return 0
    return sum(q == p[:-1] and bool(p) or q in (p+(False,), p+(True,)) for q in vertices)

def shape(t, labels):
    if isinstance(t, int):
        return str(t) if t in labels else None
    a, b = shape(t[0], labels), shape(t[1], labels)
    if a is None: return b
    if b is None: return a
    return '(' + ','.join(sorted([a,b])) + ')'

def valid(t, u, blocks, universe, marks_t=(), marks_u=()):
    flat = [x for b in blocks for x in b]
    if len(set(flat)) != len(flat) or set(flat) != set(universe) or any(not b for b in blocks):
        return False
    if not eligible(t, flat) or not eligible(u, flat):
        return False
    previous_t, previous_u = set(), set()
    for b in blocks:
        a, c = support(t,b), support(u,b)
        if shape(t,b) != shape(u,b) or a & previous_t or c & previous_u or a & set(marks_t) or c & set(marks_u):
            return False
        previous_t |= a; previous_u |= c
    return True

def partitions(xs):
    if not xs:
        yield []
        return
    for p in partitions(xs[1:]):
        yield [[xs[0]]] + [b[:] for b in p]
        for i in range(len(p)):
            yield [([xs[0]]+b if i == j else b[:]) for j,b in enumerate(p)]

def check(name, actual, expected, kind='positive'):
    ok = actual == expected
    rows.append(dict(name=name, actual=actual, expected=expected, pass_check=ok, kind=kind))
    (BASE / 'independent-results.json').write_text(json.dumps(dict(status='in_progress', rows=rows),indent=2)+'\n')
    if not ok: raise AssertionError(name)

def rejects(name, actual, wrong):
    check(name, actual != wrong, True, 'planted_wrong_value_rejected')

for f in spec['fixtures'][:3]:
    t,u,b,v = f['t'], f['u'], f['B'], tuple(f['v'])
    st, su = support(t,b), support(u,b)
    check(f['id']+'.support', sorted(st), sorted(tuple(p) for p in f['support_t']))
    check(f['id']+'.degree', degree(st,v), f['degree'])
    check(f['id']+'.restriction_agrees', shape(t,b)==shape(u,b), True)
    check(f['id']+'.split', valid(t,u,f['split'],b,marks_t=[v]), True)
    check(f['id']+'.cost', len(f['split'])-1, f['cost'])
    check(f['id']+'.containment', all(support(t,c)<=st and support(u,c)<=su for c in f['split']), True)
    all_t = {p for _,p in leaves(t)} | {p[:i] for _,p in leaves(t) for i in range(len(p))}
    all_u = {p for _,p in leaves(u)} | {p[:i] for _,p in leaves(u) for i in range(len(p))}
    check(f['id']+'.all_old_marks', valid(t,u,f['split'],b,marks_t=all_t-st | {v},marks_u=all_u-su), True)
root,path,unequal,quart,three,joint=spec['fixtures']
rejects('wrong_degree',degree(support(root['t'],root['B']),()),1)
rejects('missing_path',support(path['t'],path['B']),{(),(False,False),(True,)})
check('leaf0_t',dict(leaves(path['t']))[0],tuple(path['leaf0_t']))
check('leaf0_u',dict(leaves(path['u']))[0],tuple(path['leaf0_u']))
rejects('cross_tree_address',dict(leaves(path['u']))[0],dict(leaves(path['t']))[0])
rejects('wrong_root',degree(support(root['t'],root['B']),(False,)),2)
check('overlap_clean_twin',valid(root['t'],root['u'],[[0],[1]],[0,1]),True)
check('overlap_corruption',valid(root['t'],root['u'],[[0],[0,1]],[0,1]),False,'planted_input_rejected')
check('unequal_outside',set(x for x,_ in leaves(unequal['t'])) != set(x for x,_ in leaves(unequal['u'])),True)
for key in ['partition','refined']:
    check('quartet.'+key,valid(quart['t'],quart['u'],quart[key],[0,1,2,3]),True)
check('quartet.before',len(quart['partition']),quart['before'])
check('quartet.after',len(quart['refined']),quart['after'])
check('quartet.cost',len(quart['refined'])-len(quart['partition']),1)
rejects('quartet.wrong_count',len(quart['refined']),3)
check('quartet.new_avoids',all(tuple(quart['v']) not in support(quart['t'],b) for b in quart['refined']),True)
check('degree_three.value',degree(support(three['t'],three['B']),tuple(three['v'])),3)
rejects('degree_three.wrong_degree',degree(support(three['t'],three['B']),tuple(three['v'])),2)
can=[p for p in partitions(three['B']) if valid(three['t'],three['u'],p,three['B'],marks_t=[tuple(three['v'])])]
check('degree_three.minimum',min(map(len,can)),3)
check('degree_three.no_two_piece',any(len(p)==2 for p in can),False,'planted_bound_rejected')
check('empty_degree',degree(support(root['t'],[]),()),0)
check('singleton_degree',degree(support(root['t'],[0]),(False,)),0)
for name,t,b in [('absent',root['t'],[3]),('duplicate',[0,0],[0])]:
    caught=False
    try: support(t,b)
    except ValueError: caught=True
    check(name+'.rejected',caught,True,'premise_rejected')
marks=[tuple(p) for p in joint['marks']]
costs=[]
for chosen in [[],marks[:1],marks[1:],marks]:
    choices=[p for p in partitions(joint['B']) if valid(joint['t'],joint['u'],p,joint['B'],marks_t=chosen)]
    costs.append(min(map(len,choices))-1)
check('joint_mark_costs',costs,joint['costs'])
rejects('joint_mark_nonadditive',costs[-1]-costs[0],sum(c-costs[0] for c in costs[1:3]))
receipt=dict(status='pass',scope='frozen finite exact controls only',seconds=time.perf_counter()-started,controls_sha256=hashlib.sha256((BASE/'FROZEN-CONTROLS.json').read_bytes()).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),count=len(rows),rows=rows)
(BASE/'independent-results.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['status','scope','seconds','count','controls_sha256']}))
