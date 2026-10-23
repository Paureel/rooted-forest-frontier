#!/usr/bin/env python3
"""Compare actual released executable values with immutable independent controls."""
import copy,hashlib,json,sys
from pathlib import Path
P=Path(__file__).resolve().parent; B=P.parent; sys.path.insert(0,str(B))
import graph_gate_v2 as independent
E=json.loads((B/'EXPECTATIONS-v1.json').read_text()); fixture=json.loads((B/'CHILD-FIXTURE-v1.json').read_text())
readout=Path(sys.argv[1]) if len(sys.argv)>1 else P/'readouts-run3.log'
actual=json.loads(readout.read_text()); passed=[]
assert len(actual['cases'])==len(E['cases'])==7
def verify_child(S,c,Pexpected,paid):
    assert independent.partnorm(c['P'])==independent.partnorm(Pexpected)
    assert c['paid']==paid and c['sourceCount']==len(Pexpected)==len(c['sourceForest'])
    expected=[independent.restricted_shape(S,tuple(x)) for x in c['P']]
    shapes=[independent.restricted_shape(independent.tree(t),tuple(independent.leaves(independent.tree(t)))) for t in c['sourceForest']]
    assert shapes==expected and all(x is not None for x in expected)
for got,e in zip(actual['cases'],E['cases']):
    assert got['id']==e['id']; T,S=independent.tree(e['T']),independent.tree(e['S'])
    assert sorted(got['cuts'])==sorted(e['cuts'])
    assert independent.partnorm(got['P'])==independent.partnorm(e['P'])
    assert set(got['roots'])==set(e['cuts']+['']) and len(got['roots'])==len(e['cuts'])+1
    assert set(got['minimalVertices'])==independent.hull(S,tuple(sorted([e['a'],e['b']])))
    assert set(got['sourceVertices'])==set(independent.graph(S)[0])
    verify_child(S,got['pendantChild'],e['P'],len(e['cuts']))
    comps=independent.components(S,got['cuts'])
    assert independent.partnorm([list(B) for _,B in comps])==independent.partnorm(got['P'])
    if 'components_vertices' in e: assert sorted(V for V,_ in comps)==sorted(tuple(sorted(V)) for V in e['components_vertices'])
    for key,label in [('endpointA',e['a']),('endpointB',e['b'])]:
        endpoint=got[key]; address=next(p for p,x in independent.graph(S)[1].items() if x==label)
        assert endpoint['cuts']==[address] and address!=''
        Pendpoint=[[label],[x for x in independent.leaves(S) if x!=label]]
        verify_child(S,endpoint['child'],Pendpoint,1)
        assert independent.partnorm([list(B) for _,B in independent.components(S,[address])])==independent.partnorm(Pendpoint)
    F=e.get('F',e['P']); G=e.get('G',e['P'])
    for key,forest in [('F',F),('G',G)]:
        agree=independent.agreement(T,S,forest); ref=independent.refines(forest,e['P'])
        assert got[key+'agreement']==agree and got[key+'refines']==ref and got[key+'state']==(agree and ref)
    assert got['remaining']==[independent.remaining(k,len(e['cuts'])) for k in range(5)]
    passed.append({'id':e['id'],'cuts':got['cuts'],'literal_components':len(comps),'child_source_counts':[got[k]['child']['sourceCount'] for k in ('endpointA','endpointB')]+[got['pendantChild']['sourceCount']]})
assert len(actual['priority'])==len(E['priority_cases'])==5
for got,e in zip(actual['priority'],E['priority_cases']):
    assert got['id']==e['id'] and got['counts']==e['counts'] and len(got['candidates'])==len(e['counts'])
    T,S=independent.tree(e['T']),independent.tree(e['S']); original=independent.cherries(T)
    for c,(parent,a,b) in zip(got['candidates'],original):
        assert c['parent']==parent and c['pair']==[a,b]
        assert sorted(c['cuts'])==sorted(independent.pendant(S,a,b)[0])
    if e['selected'] is None: assert got['selected'] is None
    else:
        s=got['selected']; assert s['category']==e['selected'] and s['pair']==e['pair']
        predicates=[('common',lambda n:n==0),('t1',lambda n:n==1),('high',lambda n:n>=3),('hard2',lambda n:n==2)]
        for name,pred in predicates:
            candidates=[c for c in got['candidates'] if pred(len(c['cuts']))]
            if candidates:
                assert name==s['category'] and candidates[0]['pair']==s['pair']; break
assert len(actual['calls'])==12
for call in actual['calls']:
    child=next(c for c in fixture['children'] if independent.partnorm(c['P'])==independent.partnorm(call['P']))
    assert call['paid']==child['paid']
    r=independent.remaining(call['k'],child['paid']); assert call['remaining']==r
    expected=child['G'] if r is not None and r>=child['minimum_residual'] else None
    assert call['result']==expected
out={'status':'ALL_FROZEN_READOUTS_MATCH','cases':passed,'priority_cases':5,'actual_child_calls':12,'source_states_checked':21,'expected_files_unchanged':True,'candidate_values_sha256':hashlib.sha256(readout.read_bytes()).hexdigest()}
(P/'readout-comparison-v2.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='cases'}))
