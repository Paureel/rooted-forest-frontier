#!/usr/bin/env python3
"""One-shot fresh transport fixture check, frozen before source-body reading.
Explicit graph/set implementation. No author source or computed outputs read.
The reviewer BFS method is copied locally so no earlier receipt is overwritten.
"""
from pathlib import Path
import hashlib, json, time
HERE = Path(__file__).resolve().parent
# Copy its pure finite primitives explicitly to avoid rerunning/overwriting old receipts.
from collections import deque

def path(g, a, b):
    q=deque([(a,[a])]); seen={a}
    while q:
        v,p=q.popleft()
        if v==b: return set(p)
        for w in g[v]-seen:
            seen.add(w);q.append((w,p+[w]))
    raise ValueError('fixture is disconnected')

def retained(g, labels, closed, raw_open):
    assert all(s & labels for s in closed)
    blocks=list(closed)
    if raw_open is not None and raw_open & labels:
        blocks.append(raw_open)
    assert all(path(g,a,b)<=s for s in blocks for a in s for b in s)
    assert all(not x&y for i,x in enumerate(blocks) for y in blocks[i+1:])
    assert set().union(*blocks)&labels==labels
    assert sum('' in s for s in blocks)<=1
    return {'count':len(blocks),'closed_cost':sum('' not in s for s in blocks),
            'root_owners':sum('' in s for s in blocks),
            'closing_increment':sum('' in s for s in blocks),
            'supports':[sorted(s) for s in blocks]}

def check(name, got, expected, wrong):
    assert got==expected,(name,got,expected)
    assert got!=wrong,(name,'wrong twin accepted')
    return {'name':name,'actual':got,'expected':expected,'wrong_twin':wrong,
            'clean_passed':True,'wrong_rejected':True}
start=time.perf_counter()
one={'count':1,'closed_cost':0,'root_owners':1,'closing_increment':1,'supports':[['']]}
two={'count':2,'closed_cost':2,'root_owners':0,'closing_increment':0,'supports':[['L'],['R']]}
rows=[check('retained_singleton',retained({'':set()},{''},[],{''}),one,{**one,'closed_cost':1}),
      check('raw_empty_open_discard_then_transport',retained({'':{'L','R'},'L':{''},'R':{''}}, {'L','R'}, [{'L'},{'R'}], {''}),two,{**two,'closed_cost':3})]
out={'scope':'two frozen exact regression fixtures; no universal transport claim',
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'rows':rows,'clean_passed':2,'wrong_rejected':2,'seconds':time.perf_counter()-start}
(HERE/'exact_transport_controls.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS 2/2 exact clean fixtures; 2/2 wrong cost twins rejected')
