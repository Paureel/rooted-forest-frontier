#!/usr/bin/env python3
"""One-shot fixed original-generator output controls; no candidate imports."""
import importlib.util,sys,json,time,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('own_frozen_rank',HERE/'frozen-controls-v1/independent_rank_restriction.py')
m=importlib.util.module_from_spec(sp);sys.modules[sp.name]=m;sp.loader.exec_module(m)
p=HERE/'ACTUAL-CLEARING-PIN-v1.json';spec=json.loads(p.read_text());checks=m.Checks();rows=[]
for f in spec['cases']:
    start=time.monotonic();S,T=m.g.Original(f['S']),m.g.Original(f['T']);colors=dict(f['colors']);requested=f['requested_vertices']
    assert all(v in T.graph and v not in T.leaf_at for v in requested)
    signatures={x:tuple(T.path(v,a)[1] for v in requested) for a,x in T.leaf_at.items()}
    assert all((colors[x]==colors[y])==(signatures[x]==signatures[y]) for x in T.labels for y in T.labels)
    receipt=m.generate(f['S'],colors,f['budget']);outputs=receipt['outputs']
    checks.equal(f['id']+'_raw_costs',[len(x['cuts']) for x in outputs],f['expected_raw_costs'])
    assert not receipt['refusals'] and len(outputs)==2
    expected={m.g.canon_partition(f['expected_bad_Q']),m.g.canon_partition(f['expected_good_Q'])}
    checks.equal(f['id']+'_literal_partitions',sorted(m.g.canon_partition(x['partition']) for x in outputs),sorted(expected))
    every_clear=True;bad_output=None
    for o in outputs:
        q=o['partition'];assert m.g.partition_check(S.labels,q) and S.embedding_disjoint(q)
        assert m.cut_components(S,o['cuts'])==m.g.canon_partition(q)
        assert len(o['cuts'])==len(q)-1
        every_clear &= all(not(T.hull(frozenset(U))&set(requested)) for U in q)
        if m.g.canon_partition(q)==m.g.canon_partition(f['expected_bad_Q']):bad_output=o
    checks.equal(f['id']+'_every_actual_output_clears',every_clear,True)
    assert bad_output is not None;q=bad_output['partition']
    checks.equal(f['id']+'_bad_Q_source_disjoint',S.embedding_disjoint(q),True)
    checks.equal(f['id']+'_bad_Q_target_disjoint',T.embedding_disjoint(q),False)
    checks.equal(f['id']+'_bad_Q_whole_local_agreement',m.local_guard(S,T,q,[[U] for U in q]),True)
    checks.equal(f['id']+'_bad_Q_global_agreement',bool(m.g.agrees(S,T,q)),False)
    rows.append({'id':f['id'],'receipt':receipt,'target_joint_region_signatures':signatures,'bad_output':bad_output,
                 'requested_vertices':requested,'local_cost':0,'actual_source_precut_cost':len(bad_output['cuts']),
                 'bad_Q_original_target_hulls':[sorted(T.hull(frozenset(U))) for U in q],'seconds':time.monotonic()-start})
    assert rows[-1]['seconds']<2
out={'phase':'PRERELEASE','verdict':'ACTUAL-OUTPUT-CLEARING-CONTROLS-PASSED','case_denominator':2,'literal_checks':len(checks.rows),
     'checks':checks.rows,'cases':rows,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'spec_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'Bell_partitions_enumerated':0,
     'scope':'Actual original CoreProgram interpretation, finite controls only. Candidate consumers uninspected; all main milestones OPEN.'}
path=m.ROOT/'research/rmaf/results/algorithm-rank-restriction-fresh-actual-clearing-v1.json';path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'verdict':out['verdict'],'cases':2,'literal_checks':len(checks.rows),'raw_occurrences':sum(len(x['receipt']['outputs']) for x in rows)}))
