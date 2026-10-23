"""One-shot review controls and freeze. Expected answers are literal prior plants."""
import hashlib, json, platform, random, sys, time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
from independent_graph import Graph, exact, predicate, priority, valid, thaw

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = ROOT / 'results'
rows = []
def check(name, expected, observed):
    row = {'name': name, 'expected': expected, 'observed': observed, 'pass': observed == expected}
    rows.append(row)
    if not row['pass']:
        (OUT/'algorithm-review-control-failure.json').write_text(json.dumps(row, indent=2)+'\n')
        raise AssertionError(row)
def write(name, data):
    (OUT / name).write_text(json.dumps(data, indent=2)+'\n')

started = time.perf_counter()
a, b = [0,[1,2]], [[0,1],2]
quartet = [[0,1],[2,3]]
check('wrong topology', False, valid(a,b,[[0,1,2]])[0])
check('wrong topology clean twin', True, valid(a,a,[[0,1,2]])[0])
check('vertex overlap', False, valid(quartet,quartet,[[0,2],[1,3]])[0])
check('vertex overlap clean twin', True, valid(quartet,quartet,[[0,1],[2,3]])[0])
check('duplicate labels', False, valid(a,a,[[0],[0,1,2]])[0])
check('duplicate clean twin', True, valid(a,a,[[0],[1,2]])[0])
check('missing labels', False, valid(a,a,[[0],[1]])[0])
check('missing clean twin', True, valid(a,a,[[0],[1],[2]])[0])
check('tree universe mismatch', False, valid(a,[0,[1,3]],[[0],[1],[2]])[0])
check('tree universe clean twin', True, valid(a,a,[[0],[1],[2]])[0])
check('duplicate tree labels', False, valid([0,[1,1]],a,[[0],[1],[2]])[0])
check('duplicate tree labels clean twin', True, valid(a,a,[[0],[1],[2]])[0])
check('empty', 0, exact(None,None)['components'])
check('singleton', 1, exact(0,0)['components'])
check('identical', 1, exact(quartet,quartet)['components'])
triplet = exact(a,b)
check('conflicting_rooted_triple', 2, triplet['components'])
check('suppression', [0,2], thaw(Graph([[[0,1],2],3]).restrict([0,2])))
g = Graph(quartet)
check('component count vs paid cuts', 2, len(g.cut_partition([(g.address['0'],g.address['00'])])))
base = Fraction(231,100)
mass = lambda v: sum((base**(-q) for q in v), Fraction())
badmass, goodmass = mass([1,1,3,4,4]), mass([1,1,4,4,4])
check('published_bottleneck', '2896278200/2847396321', str(badmass))
check('conditional_macro_a', '921759400/949132107', str(goodmass))
check('false recurrence caught', False, badmass <= 1)
check('false recurrence clean twin', True, goodmass <= 1)
check('false optimum comparator caught', False, triplet['components'] == 1)
check('false optimum comparator clean twin', True, triplet['components'] == 2)
assert len(rows) == 24
write('algorithm-review-original24-controls.json', {'scope':'independent reproduction of original 24 planted controls; expected literals are development data', 'total':24, 'passed':sum(x['pass'] for x in rows), 'rows':rows, 'elapsed_seconds':time.perf_counter()-started})

additional = []
additional.append({'name':'crossed quartets', 'expected':3, 'observed':exact(quartet,[[0,2],[1,3]])['components']})
additional.append({'name':'shared root rejected', 'expected':False, 'observed':valid(quartet,quartet,[[0,2],[1,3]])[0]})
additional.append({'name':'unary root suppression', 'expected':True, 'observed':Graph([[[0,1]]]).topology([0,1]) == Graph([0,1]).topology([0,1])})
literal = json.loads((ROOT/'algorithm/x0/frozen-controls-v1.json').read_text())
fixture_rows = []
for nkey in ['branching-search-n6.json', 'branching-search-n7.json']:
    src = literal['sources'][nkey]
    for key in ['forced_cherry_counterexample','forced_cherry_hard_counterexample','forced_cherry_baseline_hard_counterexample']:
        case = src[key]
        t0 = time.perf_counter()
        original = exact(case['T'],case['Tprime'])
        retained = exact(case['T'],case['Tprime'],containing=case['cherry'])
        row = {'source':nkey, 'case':key, 'observed':original, 'retained':retained, 'seconds':time.perf_counter()-t0,
               'pass':original['components']==case['optimum_components'] and retained['components']==case['optimum_if_cherry_retained'] and original['optimal']==sorted([sorted(p) for p in case['optimal_forests']])}
        fixture_rows.append(row)
        write('algorithm-review-fixtures-progress.json',fixture_rows)
        assert row['pass'], row
    for key in ['endpoint_lookahead_counterexample','endpoint_lookahead_baseline_hard_counterexample']:
        if not src[key]: continue
        case = src[key]
        endpoint = case['isolated_endpoint']
        chosen = sorted(set(Graph(case['T']).labels)-{endpoint})
        children = [thaw(Graph(case[which]).restrict(chosen)) for which in ['T','Tprime']]
        expected_children = [case['child_T'],case['child_Tprime']]
        same = all(Graph(x).topology(chosen)==Graph(y).topology(chosen) for x,y in zip(children,expected_children))
        fixture_rows.append({'source':nkey, 'case':key,'pass':same, 'child_priority':priority(*children)})
        assert same
case = literal['sources']['branching-search-n6.json']['forced_cherry_baseline_hard_counterexample']
gg = Graph(case['Tprime']); leaf4,leaf5=gg.labels[4],gg.labels[5]
path = set(gg.path(leaf4,leaf5))
pendants = [e for e in gg.edges if e[0] in path and e[1] not in path]
branch_cuts = [[(gg.parent[leaf4],leaf4)],[(gg.parent[leaf5],leaf5)],pendants]
children = [gg.cut_partition(cuts) for cuts in branch_cuts]
child_opts = [exact(case['T'],case['Tprime'],required_refinement=p) for p in children]
bad_total = min(x['cuts'] for x in [child_opts[0],child_opts[2]])
good_total = min(x['cuts'] for x in child_opts)
additional.append({'name':'nonempty omitted isolate5 loses optimum','expected':[3,2], 'observed':[bad_total,good_total], 'original_optimum':case['optimal_forests'],'children':thaw(children),'child_optima':child_opts})
for row in additional:
    row['pass']=row['expected']==row['observed']; assert row['pass'],row
write('algorithm-review-additional-controls.json',{'rows':additional,'fixture_rows':fixture_rows})
supp = json.loads((ROOT/'algorithm/x0/source-control-spec-v1.json').read_text())
source_rows=[]
for case in supp['cases']:
    got = predicate(case['T'],case['Tprime'],case['cherry'])
    ok = all(got[k]==v for k,v in case['expected'].items())
    source_rows.append({'name':case['name'],'expected':case['expected'],'observed':got,'pass':ok})
    assert ok
write('algorithm-review-supplementary5-controls.json',{'scope':supp['registration_scope'],'total':5,'passed':5,'rows':source_rows})

rng = random.Random(40871)
def generate():
    active = list(range(8))
    while len(active)>1:
        i,j=sorted(rng.sample(range(len(active)),2),reverse=True)
        a,b=active.pop(i),active.pop(j)
        active.append([a,b])
    return active[0]
sample = {'version':1,'frozen_at_utc':datetime.now(timezone.utc).isoformat(),'seed':40871,'n':8,'count':16,'generator':'uniform two-active-subtree join', 'classification':'reserved finite supplementary validation, values never fed candidate construction', 'pairs':[{'id':i,'T':generate(),'Tprime':generate()} for i in range(16)]}
(HERE/'RESERVED-n8-seed40871.json').write_text(json.dumps(sample,indent=2)+'\n')
lineage={'frozen_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_code_read':False,'source_reuse':False,'imports':['itertools','functools','hashlib','json','platform','random','sys','time','datetime','fractions','pathlib'], 'shared':['mathematical original source definition','literal frozen control JSON values','Python runtime'],'python':sys.version,'platform':platform.platform(),'files_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [HERE/'independent_graph.py',HERE/'run_controls.py',HERE/'CONTROL-PIN.json',HERE/'RESERVED-n8-seed40871.json']}}
(HERE/'PRE-CANDIDATE-FREEZE.json').write_text(json.dumps(lineage,indent=2)+'\n')
print(json.dumps({'original24':24,'supplementary5':5,'extra':len(additional),'fixture_checks':len(fixture_rows),'seconds':time.perf_counter()-started,'reserved':16,'code_read':False}))
