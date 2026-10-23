#!/usr/bin/env python3
"""One-shot post-run receipt analysis; no new scientific search.
This reuses exact_x0 Graph for literal cut replay, so it is NOT a second
independent implementation or a second certification route.
"""
import collections
import hashlib
import importlib.util
import json
import pathlib

P=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('fresh_x0',P/'exact_x0.py')
x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x)
c=json.loads((P/'COVERAGE-v2.json').read_text())
reps=[];stable_singletons=0;stable_minima=0;global_min_replays=[]
for n in (2,3,4,5):
    groups=collections.defaultdict(list)
    for line in (P/f'bank-n{n}-v2.jsonl').read_text().splitlines():
        r=json.loads(line);groups[r['case_index']].append(r)
    for index,rows in groups.items():
        seen={tuple(r['reps']) for r in rows};first=rows[0]
        expected=set(__import__('itertools').product(first['X'],first['Y']))
        assert seen==expected and len(rows)==len(seen),'incomplete representative denominator'
        topologies={tuple(x.canonical(x.tree(t)) for t in r['marked_trees']) for r in rows}
        assert len(topologies)==1,'representative marked-topology invariance failure'
        reps.append({'n':n,'case_index':index,'expected_representatives':len(expected),'executed':len(rows),'canonical_marked_tree_tuples':len(topologies)})
        for r in rows:
            for side in (0,1):
                if r['flags'][side]==0:
                    stable_minima+=r['marked_minimum_counts'][side]
                    stable_singletons+=r['marker_singleton_minimum_counts'][side]
assert stable_singletons==0
for bucket,r in c['bucket_witnesses'].items():
    gt=x.graph(x.tree(r['T']));gs=x.graph(x.tree(r['S']))
    witnesses=[]
    for p in r['global_minima']:
        assert x.agrees(gt,gs,p)
        witnesses.append({'partition':p,'T':gt.cut_witness(p),'S':gs.cut_witness(p)})
    r['original_graphs']=[gt.literal(),gs.literal()];r['cut_realizations']=witnesses
    global_min_replays.append({'bucket':bucket,'global_minimum_families':len(witnesses)})
summary={'representative_groups':len(reps),'representative_denominator':sum(r['expected_representatives'] for r in reps),'marked_tree_topology_invariance_groups':len(reps),'stable_marked_minimum_families_checked':stable_minima,'stable_marker_singleton_violations':stable_singletons,'observed_flag_orientation_buckets':len(c['bucket_witnesses']),'global_minimum_cut_replay_per_bucket':global_min_replays,'scope':'receipt analysis of executed bank only; Graph and agrees reused; not independent replication'}
(P/'REPRESENTATIVE-REPLAY-v2.json').write_text(json.dumps({'summary':summary,'groups':reps},indent=2)+'\n')
(P/'BUCKET-WITNESSES-v2.json').write_text(json.dumps(c['bucket_witnesses'],indent=2,sort_keys=True)+'\n')
print(json.dumps(summary,sort_keys=True))
