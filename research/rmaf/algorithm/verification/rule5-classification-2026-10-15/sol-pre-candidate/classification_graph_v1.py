#!/usr/bin/env python3
"""One-shot new Rule5 guard/prefix comparator extending pinned own BFS code.

No candidate implementation or reference-generator code is imported. Complete
AF expectations are immutable JSON from the separate edge/union-find route.
"""
from copy import deepcopy
from fractions import Fraction
from itertools import product
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

HERE=Path(__file__).resolve().parent
module_spec=importlib.util.spec_from_file_location('own_pinned_BFS',HERE/'reused/graph_partition_v2.py')
old=importlib.util.module_from_spec(module_spec);module_spec.loader.exec_module(old)
Graph,State,partitions=old.Graph,old.State,old.partitions
INPUT=json.loads((HERE/'FIXTURE-INPUTS-v1.json').read_text())
CONTROL=json.loads((HERE/'GRAPH-CONTROL-EXPECTATIONS-v1.json').read_text())
MODE=sys.argv[1]
RESULT={'candidate_contact':False,'mode':MODE,'lineage':'pinned own forest BFS/partition/clade instrument; new public Rule5 guard layer','extra_replication_credit':0,'cases':[],'false_twins':[],'metamorphisms':[]}
OUT=HERE/('graph-'+MODE+'-v1.json')
DEADLINE=time.perf_counter()+30


def forest_key(F):return tuple(sorted(tuple(sorted(B)) for B in F))
def family_key(Fs):return {forest_key(F) for F in Fs}
def refines(F,P):return all(any(set(B)<=set(C) for C in P) for B in F)
def subtree(t,address):
    for side in address:
        assert type(t) is list and side in (0,1)
        t=t[side]
    return t
def leaf_order(g,address):return [x for v,x in g.at.items() if v[:len(address)]==tuple(address)]
def cherries(g):
    return [(v,g.at[v+(0,)],g.at[v+(1,)]) for v in g.adj if v+(0,) in g.at and v+(1,) in g.at]
def cuts(g,a,b):
    hull=g.hull([a,b])
    return [list(v) for v in g.adj if v and v[:-1] in hull and v not in hull]
def has_cherry(g,a,b):return any({x,y}=={a,b} and a!=b for _,x,y in cherries(g))
def pendant_partition(g,a,b):
    cs=cuts(g,a,b);removed={x for c in cs for x in leaf_order(g,c)}
    return cs,[leaf_order(g,c) for c in cs]+[[x for x in g.taxa if x not in removed]]
def earlier(g,h):return all(len(cuts(h,a,b))==2 for _,a,b in cherries(g))
def rule4(g,h):
    for _,a,b in cherries(g):
        cs=cuts(h,a,b)
        if len(cs)!=2:continue
        for c in cs:
            B=leaf_order(h,c)
            if len(B)==1 and (has_cherry(h,a,B[0]) or has_cherry(h,b,B[0])):return True
    return False


def inspect(T,S,a,b):
    t,s=Graph(T),Graph(S)
    proper=len(t.taxa)==len(set(t.taxa)) and len(s.taxa)==len(set(s.taxa)) and set(t.taxa)==set(s.taxa)
    assert all(type(x) is int and x>=0 for x in t.taxa+s.taxa)
    cs,P=pendant_partition(s,a,b)
    good=[t.topology(B) is not None and t.topology(B)==s.topology(B) for B in P]
    flags={'proper':proper,'has_cherry':has_cherry(t,a,b),'earlier_target':earlier(t,s),'earlier_source':earlier(s,t),
       'rule4_target':rule4(t,s),'rule4_source':rule4(s,t),'two_cuts':len(cs)==2,
       'target_embeddings':t.disjoint(P),'source_embeddings':s.disjoint(P),'exact_two_good':sum(good)==2}
    admitted=all(flags[k] for k in ['proper','has_cherry','earlier_target','earlier_source','two_cuts','target_embeddings','source_embeddings','exact_two_good']) and not flags['rule4_target'] and not flags['rule4_source']
    category='remaining';pair=None;selected=None
    for wanted,name in [(lambda B:len(B)>=3,'large'),(lambda B:len(B)==2,'sizeTwo')]:
        if selected is None:
            for i,(c,B) in enumerate(zip(cs,P)):
                if good[i] and wanted(B):
                    selected=c;category=name
                    inner=Graph(subtree(S,c));cc=cherries(inner)
                    assert len(cc)==1,'positive good pendant is not one-cherry'
                    pair=cc[0][1:];break
    outside_attempts=[]
    if selected is None and P and good[-1]:
        core=Graph(s.restriction(P[-1]))
        for _,p,q in cherries(core):
            outside_attempts.append({'p':p,'q':q,'disjoint_selected':p not in (a,b) and q not in (a,b)})
            if p not in (a,b) and q not in (a,b):
                assert has_cherry(s,p,q),'restricted second cherry is not an original source cherry'
                category='outside';pair=(p,q);break
    return {'flags':flags,'admitted':admitted,'cuts':cs,'partition':P,'good':good,'category':category,
      'selected_pendant':selected,'pair':list(pair) if pair else None,'outside_attempts':outside_attempts},t,s


def check_cuts(g,cs,P=None):
    arcs=[tuple(c) for c in cs]
    assert all(c and c in g.adj for c in arcs),'nonoriginal/root arc'
    assert len(arcs)==len(set(arcs)),'duplicate original edge'
    blocks,leafless=g.cut_components(cs)
    assert leafless==0,'leafless original component'
    assert len(blocks)==len(cs)+1,'component/cut offset'
    if P is not None:assert forest_key(blocks)==forest_key(P),'original cut partition mismatch'
    return blocks


def build_children(observation,t,s,a,b):
    assert observation['admitted'] and observation['category']!='remaining'
    specs=[('hard-two',observation['cuts'],observation['partition'])]
    if observation['category']!='large':
        p,q=observation['pair']
        for x,y,name in [(p,a,'p+a'),(p,b,'p+b'),(q,a,'q+a'),(q,b,'q+b')]:
            vx=next(v for v,z in s.at.items() if z==x);vy=next(v for v,z in s.at.items() if z==y)
            assert vx and vy and vx!=vy
            P=[[x],[y],[z for z in s.taxa if z not in (x,y)]]
            specs.append((name,[list(vx),list(vy)],P))
    rows=[]
    for name,cs,P in specs:
        check_cuts(s,cs,P)
        ss=[s.restriction(B) for B in P]
        assert all(x is not None for x in ss) and len(ss)==len(P)==3
        assert State(t.tree,ss).proper
        rows.append({'id':name,'sourceCuts':cs,'partition':P,'sourceForest':ss,'paid':len(cs),'sourceCount':len(ss)})
    return rows


def refinements(P):
    banks=[list(partitions(B)) for B in P]
    for parts in product(*banks):yield [B for part in parts for B in part]


def exact_family(actual,expected):
    assert len(actual)==len({forest_key(F) for F in actual}),'duplicate forest'
    assert family_key(actual)==family_key(expected),'complete original AF family mismatch'


def caught(name,call):
    try:call()
    except (AssertionError,ValueError,StopIteration) as exc:
        RESULT['false_twins'].append({'name':name,'caught':True,'message':str(exc)});return
    raise AssertionError('SURVIVING FALSE PLANT '+name)


def equal(a,b):assert a==b,(a,b)


def check_case(case):
    start=time.perf_counter();obs,t,s=inspect(case['target'],case['source'],case['a'],case['b'])
    assert obs['admitted']==case['expected_admitted']
    assert obs['category']==case['expected_prefix'] and obs['cuts']==case['original_cuts']
    assert obs['partition']==case['partition'] and obs['good']==case['good_flags']
    assert obs['pair']==[case['p'],case['q']]
    assert cuts(t,case['p'],case['q'])==case['target_attachments']
    tparts=check_cuts(t,case['target_attachments'])
    assert forest_key(tparts)==forest_key(case['partition'])
    for name,address in case['terminal_arcs'].items():assert s.at[tuple(address)]==case[name]
    reference=json.loads((HERE/('REFERENCE-'+case['id']+'-full-v1.json')).read_text())
    af=list(State(t.tree,[s.tree]).forests())
    assert time.perf_counter()<=DEADLINE,'bounded BFS run exceeded30s'
    exact_family(af,[r['F'] for r in reference['originalAF']])
    for cert in reference['originalAF']:
        check_cuts(t,cert['targetCuts'],cert['F']);check_cuts(s,cert['sourceCuts'],cert['F'])
    minimum=min(len(F)-1 for F in af)
    assert minimum==reference['minimumOriginalCost']
    children=build_children(obs,t,s,case['a'],case['b'])
    assert [r['paid'] for r in children]==case['raw_costs']
    assert children[0]['sourceForest']==case['hard_source_forest']
    for actual,expected in zip(children,reference['children'],strict=True):
        for k in ['id','sourceCuts','partition','sourceForest','paid','sourceCount']:assert actual[k]==expected[k],(case['id'],k)
        state=State(t.tree,actual['sourceForest'])
        valid=[F for F in refinements(actual['partition']) if state.agrees(F)]
        exact_family(valid,expected['compatibleAF'])
        child_min=min(len(F)-3 for F in valid)
        assert child_min==expected['minimumAdditionalCost']
        for F in valid:
            assert State(t.tree,[s.tree]).agrees(F)
            assert len(F)>=3
            assert actual['paid']+(len(F)-3)==len(F)-1
        actual['minimumAdditionalCost']=child_min
        actual['compatibleAFCount']=len(valid)
    if case['expected_prefix']=='large':
        assert all(any(refines(G,obs['partition']) and len(G)<=len(F) for G in af) for F in af),'large exchange failed'
        X=set(obs['partition'][0])
        assert all(all(len(set(B)&X)<=1 for B in F if set(B)-X) for F in af),'large crossing contains two X taxa'
    for budget in reference['budgetControls']:
        q=budget['q'];calls=[{'child':r['id'],'remaining':q-2,'succeeds':r['minimumAdditionalCost']<=q-2} for r in children] if q>=2 else []
        assert calls==budget['paidCalls']
        assert any(r['succeeds'] for r in calls)==(minimum<=q)==budget['originalSuccess']
    row={'id':case['id'],'admitted':obs,'originalAF':len(af),'minimumOriginalCost':minimum,
      'children':children,'raw_costs':[r['paid'] for r in children],
      'raw_mass_at_2':str(sum((Fraction(2)**(-r['paid']) for r in children),Fraction())),
      'budgetControls':reference['budgetControls'],'seconds':time.perf_counter()-start}
    expected_mass=CONTROL['raw_mass']['one_cost2_at_c2' if len(children)==1 else 'five_cost2_at_c2']
    assert row['raw_mass_at_2']==expected_mass
    RESULT['cases'].append(row)
    return obs,t,s,af,children


def mutated_tree(t,at=()):
    root=deepcopy(t)
    if not at:return [root[1],root[0]]
    parent=root
    for side in at[:-1]:parent=parent[side]
    v=parent[at[-1]];parent[at[-1]]=[v[1],v[0]]
    return root


def mirrored(t):return t if type(t) is int else [mirrored(t[1]),mirrored(t[0])]
def relabel(t,f):return f(t) if type(t) is int else [relabel(t[0],f),relabel(t[1],f)]


def plants():
    # Known original AF plants traverse the reused BFS comparator first.
    for name,plant in INPUT['reference_plants'].items():
        af=list(State(plant['target'],[plant['source']]).forests())
        exact_family(af,plant['AF'])
    case=next(c for c in INPUT['cases'] if c['id']=='sizeTwo7')
    obs,t,s=inspect(case['target'],case['source'],0,1)
    assert obs['admitted']
    boundary={}
    for name in ['four_leaf_rule4','five_leaf_all_good']:
        e=CONTROL['guard_boundaries'][name];o,_,_=inspect(e['target'],e['source'],e['a'],e['b'])
        assert o['admitted']==e['admitted']
        assert (o['flags']['earlier_target'] and o['flags']['earlier_source'])==e['earlier_both']
        assert (o['flags']['rule4_target'] and o['flags']['rule4_source'])==e['rule4_both']
        if 'good_count' in e:assert sum(o['good'])==e['good_count']
        boundary[name]=o
    common,_,_=inspect(case['target'],case['target'],0,1)
    assert not common['admitted'] and not common['flags']['earlier_target']
    for name,bad in [('duplicate_label',relabel(case['source'],lambda x:0 if x==1 else x)),('foreign_label',relabel(case['source'],lambda x:9001 if x==1 else x))]:
        o,_,_=inspect(case['target'],bad,0,1)
        assert not o['flags']['proper'] and not o['admitted'];boundary[name]=o
    no,_,_=inspect(case['target'],case['source'],0,2)
    assert not no['flags']['has_cherry'] and not no['admitted']
    RESULT['guard_boundaries']=boundary


try:
    for pin_name in ['REUSE-PINS-v1.json','REFERENCE-EXPECTATIONS-PIN-v1.json']:
        pin=json.loads((HERE/pin_name).read_text())
        for row in pin.get('entries',pin.get('items',[])):
            path=HERE/row.get('copy',row.get('path'))
            assert hashlib.sha256(path.read_bytes()).hexdigest()==row['sha256']
    plants()
    cases=[c for c in INPUT['cases'] if c['id']=='sizeTwo7'] if MODE=='pilot' else INPUT['cases']
    assert MODE in ('pilot','full')
    cache={c['id']:check_case(c) for c in cases}
    if MODE=='full':
        for case in cases:
            obs,t,s,af,children=cache[case['id']]
            # All 16 root/selected-cherry sibling orders. These are original-
            # vertex permutations; no additional partition census is needed.
            for tr,sr,tc,sc in product([False,True],repeat=4):
                assert time.perf_counter()<=DEADLINE,'bounded metamorphism run exceeded30s'
                T=deepcopy(case['target']);S=deepcopy(case['source'])
                if tc:
                    address=next(v for v,a,b in cherries(Graph(T)) if {a,b}=={case['a'],case['b']})
                    T=mutated_tree(T,address)
                if sc:S=mutated_tree(S,case['source_cherry_parent'])
                if tr:T=mutated_tree(T)
                if sr:S=mutated_tree(S)
                o,_,ss=inspect(T,S,case['a'],case['b'])
                assert o['admitted'] and o['category']==case['expected_prefix']
                assert all(State(T,[S]).agrees(F) for F in af)
                got=build_children(o,Graph(T),ss,case['a'],case['b'])
                assert [r['paid'] for r in got]==case['raw_costs']
                RESULT['metamorphisms'].append({'id':case['id'],'root/cherry_swaps':[tr,sr,tc,sc],'passed':True})
            reverse,_,_=inspect(case['source'],case['target'],case['p'],case['q'])
            assert reverse['admitted'] and reverse['category']==CONTROL['role_exchanges'][case['id']]
            RESULT['metamorphisms'].append({'id':case['id'],'kind':'roles','category':reverse['category'],'passed':True})
            for name,T,S,f in [('mirror',mirrored(t.tree),mirrored(s.tree),lambda x:x),
                               ('arbitrary_Nat',relabel(t.tree,lambda x:1000003+37*x),relabel(s.tree,lambda x:1000003+37*x),lambda x:1000003+37*x)]:
                o,_,_=inspect(T,S,f(case['a']),f(case['b']))
                assert o['admitted'] and o['category']==case['expected_prefix']
                assert all(State(T,[S]).agrees([[f(x) for x in B] for B in F]) for F in af)
                RESULT['metamorphisms'].append({'id':case['id'],'kind':name,'passed':True})
        case=next(c for c in cases if c['id']=='sizeTwo7');o,t,s,af,children=cache[case['id']]
        caught('missing_original_AF',lambda:exact_family(af[1:],af))
        caught('duplicated_original_AF',lambda:exact_family(af+[af[0]],af))
        caught('root_cut',lambda:check_cuts(s,[[]]))
        caught('duplicate_cut',lambda:check_cuts(s,[case['original_cuts'][0]]*2))
        caught('nonexistent_local_address',lambda:check_cuts(s,[[1,1,1]]))
        cq=case['source_cherry_parent']
        caught('leafless_internal_component',lambda:check_cuts(s,[cq,cq+[0],cq+[1]]))
        c=INPUT['controls']
        caught('wrong_original_topology',lambda:equal(State(t.tree,[s.tree]).agrees(c['false_topology']['F']),True))
        caught('wrong_embedding',lambda:equal(t.disjoint(c['false_embedding']['F']),True))
        F=c['false_child_ownership']['F'];assert State(t.tree,[s.tree]).agrees(F)
        caught('foreign_child_owner',lambda:equal(State(t.tree,children[0]['sourceForest']).agrees(F),True))
        large=next(z for z in cases if z['id']=='large8');lo,lt,ls,laf,lchildren=cache['large8']
        for name in ['large_crossing','large_no_crossing','false_strict_exchange']:
            e=c[name];assert State(lt.tree,[ls.tree]).agrees(e['F']) and State(lt.tree,[ls.tree]).agrees(e['G'])
            assert refines(e['G'],lo['partition']) and len(e['G'])<=len(e['F'])
            if name=='large_crossing':
                assert len(e['split'])-len(e['F'])==e['split_added']==2
                assert len(e['split'])-len(e['G'])==e['regroup_saved']==2
        e=c['false_strict_exchange'];best=min(len(G) for G in laf if refines(G,e['F']) and refines(G,lo['partition']))
        assert best==e['common_refinement_minimum_blocks']==8
        caught('strict_refinement_exchange',lambda:equal(best<=len(e['F']),True))
        costs=[r['paid'] for r in children]
        caught('missing_occurrence',lambda:equal(costs[:-1],case['raw_costs']))
        caught('deduplicated_costs',lambda:equal(sorted(set(costs)),case['raw_costs']))
        caught('failed_child_dropped',lambda:equal([r['paid'] for r in children if r['minimumAdditionalCost']<=1],case['raw_costs']))
        caught('unpaid_pair',lambda:equal([2,1,2,2,2],case['raw_costs']))
        F=af[0];caught('wrong_component_offset',lambda:equal(2+(len(F)-1),len(F)-1))
        budget=CONTROL['paid_budget'];caught('own_minimum_discount',lambda:equal(budget['false_own_minimum_discount'],budget['remaining']))
        materialized=[s.restriction(B) for B in [[],s.taxa]];materialized=[x for x in materialized if x is not None]
        caught('empty_restriction_drop',lambda:equal(len(materialized),2))
        assert {r['name'] for r in RESULT['false_twins']}==set(CONTROL['false_detector_names'])
        assert len(RESULT['metamorphisms'])==57
    RESULT['passed']=True
except Exception as exc:
    RESULT['passed']=False;RESULT['failure']=repr(exc)
    raise
finally:
    RESULT['elapsed_seconds']=30-(DEADLINE-time.perf_counter())
    OUT.write_text(json.dumps(RESULT,indent=2)+'\n')
print(json.dumps({'passed':True,'mode':MODE,'cases':len(RESULT['cases']),'false_twins':len(RESULT['false_twins']),'metamorphisms':len(RESULT['metamorphisms']),'seconds':RESULT['elapsed_seconds']}))
