#!/usr/bin/env python3
"""Compare actual frozen Lean definitions with own pre-candidate graph code."""
import importlib.util,json,hashlib,itertools,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
def module(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
m=module('own_frozen',HERE/'frozen-readiness-v1/independent_paircase.py')
r=module('own_replay',HERE/'review_replay.py')
r.OUT=r.RMAF/'results/algorithm-pair-case-fresh-review-actual-v2.json'
r.state={'scope':'Actual frozen definitions versus independent pre-candidate graph instruments; universal claims require formal proof','runs':[],'audits':{},'fixtures':[]}
folder=r.BUILD/'joint'
shutil.copyfile(HERE/'ActualReadout.lean',folder/'ActualReadout.lean')
spec=json.loads((HERE/'frozen-readiness-v1/preregistration.json').read_text())

def lean(x):
    if isinstance(x,(list,tuple)):return '['+','.join(map(lean,x))+']'
    return str(x)
def tree(x):
    if isinstance(x,(list,tuple)):return '(.node '+tree(x[0])+' '+tree(x[1])+')'
    return '(.leaf '+str(x)+')'
def verify_tree(actual,t):
    labels=sorted(t.labels);wanted={tuple(x for x,b in zip(labels,bits) if b) for bits in itertools.product((0,1),repeat=len(labels))}
    seen=set();degrees=0
    for row in actual['hulls']:
        a=tuple(row['selection']);assert a not in seen;seen.add(a)
        h=t.hull(frozenset(a));assert set(row['hull'])==h and len(row['hull'])==len(h)
        for v,regions,degree in row['regions_degree']:
            assert regions==degree==len(t.occupied(v,a));degrees+=1
    assert seen==wanted
    seen=set();eligible=0
    for row in actual['choices']:
        a,b=tuple(row['A']),tuple(row['B']);key=(a,b);assert key not in seen;seen.add(key)
        actual_guard=m.g_guard(t,a,b);c=row['choice']
        assert bool(c)==actual_guard,(a,b,c,actual_guard)
        if not c:continue
        eligible+=1
        h=t.hull(frozenset(a))&t.hull(frozenset(b))
        if c['kind']=='vertex':assert c['v'] in h and (len(t.occupied(c['v'],a))==3 or len(t.occupied(c['v'],b))==3)
        else:assert m.clear_edge(t,a,b,(c['u'],c['v']))['eligible']
    assert len(seen)==3**len(labels)
    return {'selections':len(wanted),'regions_degree':degrees,'color_assignments':len(seen),'eligible_choices':eligible}

try:
    r.compile_one(folder,'ActualReadout')
    for i,name in enumerate(['binary_tiny','T1','root_promoted','three_region_probe']):
        f=spec['fixtures'][name];s,t=m.Original(f['S']),m.Original(f['T']);ps=list(m.partitions(sorted(s.labels)))
        source='import ActualReadout\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\nopen FreshActualReadout\n'
        source+='def suppliedPartitions : List (List (List Nat)) := '+lean(ps)+'\n'
        source+='#eval IO.println ("FRESH_READOUT|" ++ (fixtureRows '+json.dumps(name)+' '+tree(f['S'])+' '+tree(f['T'])+' '+lean(sorted(s.labels))+' '+lean(f['A'])+' '+lean(f['B'])+' '+lean(f['P'])+' suppliedPartitions).compress)\n'
        module_name='Fixture'+str(i);(folder/(module_name+'.lean')).write_text(source)
        log=r.compile_one(folder,module_name)
        lines=[line.split('|',1)[1] for line in log.splitlines() if line.startswith('FRESH_READOUT|')]
        assert len(lines)==1;actual=json.loads(lines[0]);assert actual['fixture']==name
        (folder/(module_name+'-actual.json')).write_text(json.dumps(actual,indent=2)+'\n')
        tree_counts={'S':verify_tree(actual['S'],s),'T':verify_tree(actual['T'],t)}
        seen=set()
        for row in actual['partitions']:
            p=m.canon_partition(row['F']);assert p not in seen;seen.add(p);assert row['agreement']==bool(m.agrees(s,t,p))
        assert seen==set(ps) and len(seen)==f['partition_denominator']
        wanted={(e,p) for e in t.edges if m.clear_edge(t,f['A'],f['B'],e)['eligible'] for p in ps if m.refines(p,f['P']) and m.agrees(s,t,p)}
        seen=set()
        for row in actual['exchanges']:
            e=tuple(row['edge']);p=m.canon_partition(row['F']);key=(e,p);assert key not in seen;seen.add(key)
            assert set(row['D'])==set(t.descendants(e[1]))
            expected=m.exchange(f['A'],f['B'],row['D'],p)
            assert m.canon_partition(row['Fprime'])==expected
            assert row['A_count']==1 and all(row[n] for n in ('actual_agreement','refines_P','nonincreasing','outside_equal','B_mono'))
        assert seen==wanted
        r.state['fixtures'].append({'fixture':name,'partition_denominator':len(ps),'exchange_denominator':len(wanted),'tree_counts':tree_counts,'verdict':'ACTUAL-DEFINITION-COMPARISONS-PASSED','readout_source_sha256':hashlib.sha256(source.encode()).hexdigest()});r.save()
    r.state['verdict']='ALL-ACTUAL-DEFINITION-COMPARISONS-PASSED';r.save()
except Exception as ex:
    r.state['verdict']='OPEN-ACTUAL-DEFINITION-FAILURE';r.state['error']=repr(ex);r.save();raise
