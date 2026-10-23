#!/usr/bin/env python3
"""One-shot prerelease controls, reusing only own frozen original-graph code.
New direct interpreter of permitted original CoreProgram; no candidate imports.
"""
from __future__ import annotations
import argparse,collections,hashlib,importlib.util,itertools,json,time,traceback
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=next(p for p in (HERE,*HERE.parents) if (p/'bootloops-python').is_file() and (p/'research/rmaf/lean/RMAF.lean').is_file())
BASE=ROOT/'research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-readiness-v1/independent_paircase.py'
assert hashlib.sha256(BASE.read_bytes()).hexdigest()=='9f9d9d33ddcfe867a9d82113478a07807f1ad73b32cf50c3180aa54a6770eab4'
ms=importlib.util.spec_from_file_location('own_frozen_original_graph',BASE)
g=importlib.util.module_from_spec(ms);ms.loader.exec_module(g)

@dataclass(frozen=True)
class Group:
    origin:str
    labels:tuple
    color:int
@dataclass(frozen=True)
class Node:
    origin:str
    left:object
    right:object

def from_tree(t,colors,p=''):
    if isinstance(t,int):return Group(p,(t,),colors[t])
    return Node(p,from_tree(t[0],colors,p+'0'),from_tree(t[1],colors,p+'1'))
def groups(t):
    return [t] if isinstance(t,Group) else groups(t.left)+groups(t.right)
def normalize(t):
    if isinstance(t,Group):return t
    a,b=normalize(t.left),normalize(t.right)
    if isinstance(a,Group) and isinstance(b,Group) and a.color==b.color:
        return Group(t.origin,a.labels+b.labels,a.color)
    return Node(t.origin,a,b)
def erase(t,p):
    if t.origin==p:return None
    if isinstance(t,Group):return t
    a,b=erase(t.left,p),erase(t.right,p)
    return b if a is None else a if b is None else Node(t.origin,a,b)
def mixed_cherry(t):
    if isinstance(t,Group):return None
    if isinstance(t.left,Group) and isinstance(t.right,Group):return (t.left,t.right)
    return mixed_cherry(t.left) or mixed_cherry(t.right)
def choose(t):
    gs=groups(t)
    if not gs:return ('refuse','empty current source')
    if all(x.color==gs[0].color for x in gs):return ('finish',)
    for x in gs:
        if sum(y.color==x.color for y in gs)==1:return ('one',x)
    pair=mixed_cherry(t)
    if not pair:return ('refuse','no mixed cherry in multicolor source')
    return ('refuse','unnormalized homogeneous cherry') if pair[0].color==pair[1].color else ('two',*pair)
def run(t,detached,cuts,q):
    t=normalize(t);decision=choose(t)
    if decision[0]=='finish':return {'outputs':[{'partition':[list(x.labels) for x in detached]+[[z for x in groups(t) for z in x.labels]],'cuts':list(cuts)}],'refusals':[],'visited':1,'attempts':0,'pruned':0}
    if decision[0]=='refuse':return {'outputs':[],'refusals':[decision[1]],'visited':1,'attempts':0,'pruned':0}
    answer={'outputs':[],'refusals':[],'visited':1,'attempts':0,'pruned':0}
    for part in decision[1:]:
        answer['attempts']+=1
        if not part.origin:answer['refusals'].append('attempt to cut original root');continue
        if part.origin in cuts:answer['refusals'].append('duplicate original source cut');continue
        remaining=erase(t,part.origin)
        if remaining is None:answer['refusals'].append('attempt removed entire current source');continue
        if q==0:answer['pruned']+=1;continue
        child=run(remaining,[part]+detached,[part.origin]+cuts,q-1)
        for key in ('outputs','refusals'):answer[key]+=child[key]
        for key in ('visited','attempts','pruned'):answer[key]+=child[key]
    return answer
def generate(t,colors,budget):
    if budget<0:raise ValueError('Nat budget required')
    model=g.Original(t)
    if not model.proper:return {'outputs':[],'refusals':['duplicate original label'],'visited':0,'attempts':0,'pruned':0}
    return run(from_tree(t,colors),[],[],min(budget,len(model.labels)-1))

class Checks:
    def __init__(self):self.rows=[]
    def equal(self,name,actual,expected):
        passed=actual==expected
        corrupted={'deliberately_other_expected_value':expected}
        reject=actual!=corrupted
        self.rows.append({'id':name,'actual':actual,'expected':expected,'passed':passed,'mismatched_expectation_rejected':reject})
        assert passed and reject,name

def mass(costs,c):return sum((c**(-x) for x in costs),Fraction())
def cut_components(model,cuts):
    assert len(set(cuts))==len(cuts) and all(cuts)
    assert all((p[:-1],p) in model.edges for p in cuts)
    removed={frozenset((p[:-1],p)) for p in cuts};seen=set();blocks=[]
    for v in model.graph:
        if v in seen:continue
        queue=[v];seen.add(v);labels=[]
        while queue:
            w=queue.pop()
            if w in model.leaf_at:labels.append(model.leaf_at[w])
            for x in model.graph[w]-seen:
                if frozenset((w,x)) not in removed:seen.add(x);queue.append(x)
        if labels:blocks.append(labels)
    return g.canon_partition(blocks)
def raw_key(o):return (g.canon_partition(o['partition']),tuple(o['cuts']))
def rank_case(f,checks,bases):
    start=time.monotonic();model=g.Original(f['tree']);colors=dict(f['colors']);n=len(model.labels)
    if f.get('proper') is False:
        receipt=generate(f['tree'],colors,n-1)
        checks.equal(f['id']+'_proper',model.proper,False)
        checks.equal(f['id']+'_empty_outputs',receipt['outputs'],[])
        checks.equal(f['id']+'_refusal',receipt['refusals'],f['refusals'])
        return {'id':f['id'],'proper':False,'receipt':receipt,'seconds':time.monotonic()-start}
    ps=list(g.partitions(sorted(model.labels)));r=len({colors[x] for x in model.labels})
    witnesses=[p for p in ps if len(p)==r and g.partition_check(model.labels,p) and model.embedding_disjoint(p)
               and all(len({colors[x] for x in b})==1 for b in p)]
    checks.equal(f['id']+'_partition_denominator',len(ps),f['partition_denominator'])
    checks.equal(f['id']+'_rank',r,f['rank']);checks.equal(f['id']+'_feasibility',bool(witnesses),f['feasible'])
    class_partition=g.canon_partition([[x for x in model.labels if colors[x]==c] for c in sorted(set(colors.values()))])
    outputs=[];previous=collections.Counter();mass_rows=[]
    for q in range(n+3):
        receipt=generate(f['tree'],colors,q);raw=receipt['outputs'];costs=[len(o['cuts']) for o in raw]
        assert not receipt['refusals'],receipt
        assert receipt['visited']<=(2**(min(q,n-1)+1)-1)
        assert receipt['attempts']<=2*receipt['visited']
        assert all(x<=min(q,n-1) for x in costs)
        for o in raw:
            p=o['partition'];assert g.partition_check(model.labels,p) and model.embedding_disjoint(p)
            assert all(len({colors[x] for x in b})==1 for b in p)
            assert cut_components(model,o['cuts'])==g.canon_partition(p)
            assert len(o['cuts'])==len(p)-1
        current=collections.Counter(map(raw_key,raw));assert not (previous-current);previous=current
        if f['feasible']:
            checks.equal(f['id']+'_raw_costs_q'+str(q),costs,[] if q<r-1 else [r-1])
            if q>=r-1:assert len(raw)==1 and g.canon_partition(raw[0]['partition'])==class_partition
        else:assert all(x>=r for x in costs)
        for L in range(r-1,n+2):
            if not all(x>=L for x in costs):continue
            for c in bases:
                value=mass(costs,c);bound=Fraction(2)**(L-(r-1))*c**(-L)
                assert value<=bound
                mass_rows.append({'budget':q,'L':L,'c':str(c),'raw_mass':str(value),'bound':str(bound),'occurrences':len(costs)})
        outputs.append({'budget':q,'effective_cap':min(q,n-1),'raw_costs':costs,'receipt':receipt})
        if time.monotonic()-start>5:raise TimeoutError(f['id'])
    checks.equal(f['id']+'_full_raw_costs',outputs[n-1]['raw_costs'],f['full_raw_costs'])
    for name,q in [('budget_zero_raw_costs',0),('budget_one_raw_costs',1),('budget_two_raw_costs',2)]:
        if name in f:checks.equal(f['id']+'_'+name,outputs[q]['raw_costs'],f[name])
    if 'mass_at_two' in f:checks.equal(f['id']+'_raw_mass_at_two',str(mass(outputs[n-1]['raw_costs'],Fraction(2))),f['mass_at_two'])
    return {'id':f['id'],'partition_denominator':len(ps),'rank':r,'feasibility_witnesses':witnesses,'budgets':outputs,'mass_checks':mass_rows,'seconds':time.monotonic()-start}

def prune_map(t,selection,p=''):
    if isinstance(t,int):return None if t not in selection else (p,t)
    a,b=prune_map(t[0],selection,p+'0'),prune_map(t[1],selection,p+'1')
    return b if a is None else a if b is None else (p,(a,b))
def unpack_pruned(node):
    mapping={}
    def walk(node,local=''):
        p,body=node;mapping[local]=p
        return body if isinstance(body,int) else (walk(body[0],local+'0'),walk(body[1],local+'1'))
    return walk(node),mapping
def transport(model,U,C):
    node=prune_map(model.tree,set(U));assert node is not None
    restricted,mapping=unpack_pruned(node)
    assert restricted==g.raw_restrict(model.tree,U)
    local=g.Original(restricted);h=local.hull(frozenset(C));expanded={mapping[v] for v in h}
    for a,b in local.edges:
        if a in h and b in h:expanded.update(model.path(mapping[a],mapping[b]))
    assert expanded==set(model.hull(frozenset(C)))
    return {'selection':list(U),'block':list(C),'local_hull':sorted(h),'local_to_original':mapping,'expanded_original_hull':sorted(expanded)}
def local_guard(S,T,Q,families):
    if not S.proper or not T.proper or set(S.labels)!=set(T.labels):return False
    if not g.partition_check(S.labels,Q) or not g.partition_check(T.labels,Q) or len(Q)!=len(families):return False
    for U,family in zip(Q,families):
        a,b=g.raw_restrict(S.tree,U),g.raw_restrict(T.tree,U)
        if a is None or b is None or not g.agrees(g.Original(a),g.Original(b),family):return False
    return True
def restriction_case(f,checks):
    start=time.monotonic();S,T=g.Original(f['S']),g.Original(f['T']);Q,F=f['Q'],f['F']
    forward=bool(S.proper and T.proper and g.partition_check(S.labels,Q) and g.partition_check(T.labels,Q) and g.agrees(S,T,F) and g.refines(F,Q))
    checks.equal(f['id']+'_forward_guard',forward,f['forward_guard'])
    families=[[C for C in F if set(C)<=set(U)] for U in Q]
    checks.equal(f['id']+'_local_lengths',list(map(len,families)),f['local_family_lengths'])
    assert all(families) and local_guard(S,T,Q,families)
    total=sum(len(x)-1 for x in families)
    checks.equal(f['id']+'_local_cost_sum',total,f['local_cost_sum'])
    checks.equal(f['id']+'_F_minus_Q',len(F)-len(Q),f['F_minus_Q'])
    checks.equal(f['id']+'_global_cut_cost',len(F)-1,f['global_F_cut_cost'])
    assert total==len(F)-len(Q) and len(F)-1==(len(Q)-1)+total
    ds,dt=S.embedding_disjoint(Q),T.embedding_disjoint(Q)
    checks.equal(f['id']+'_reverse_disjoint_guards',ds and dt,f['reverse_Q_embeddings'])
    for key,val in [('source_Q_disjoint',ds),('target_Q_disjoint',dt)]:
        if key in f:checks.equal(f['id']+'_'+key,val,f[key])
    if ds and dt:
        flat=[C for family in families for C in family];assert g.agrees(S,T,flat)
        assert len(flat)-1==(len(Q)-1)+total
    if 'whole_Q_local_agreements' in f:
        wholes=[[U] for U in Q]
        checks.equal(f['id']+'_whole_Q_locals',local_guard(S,T,Q,wholes),f['whole_Q_local_agreements'])
        checks.equal(f['id']+'_whole_Q_global',bool(g.agrees(S,T,Q)),f['whole_Q_global_agreement'])
    transports=[]
    for side,model in [('S',S),('T',T)]:
        for U in Q:
            for bits in itertools.product((0,1),repeat=len(U)):
                C=[x for x,b in zip(U,bits) if b]
                transports.append({'side':side,**transport(model,U,C)})
    return {'id':f['id'],'forward_guard':forward,'families':families,'local_cost_sum':total,'global_cut_cost':len(F)-1,'source_Q_disjoint':ds,'target_Q_disjoint':dt,'transports':transports,'seconds':time.monotonic()-start}

def remaining_controls(spec,c):
    raw=spec['mass_controls'];costs=raw['raw_cost_list'];base=Fraction(raw['base'])
    c.equal('raw_mass',str(mass(costs,base)),raw['expected_mass'])
    bound=Fraction(2)**(raw['L']-(raw['rank']-1))*base**(-raw['L'])
    c.equal('dyadic_bound',str(bound),raw['expected_dyadic_bound'])
    c.equal('omitted_occurrence_mass',str(mass(costs[:-1],base)),raw['omit_one_expected_mass'])
    c.equal('duplicate_occurrence_mass',str(mass(costs+[costs[0]],base)),raw['duplicate_one_expected_mass'])
    c.equal('forged_zero_cost_mass',str(mass([0,2],base)),raw['forged_zero_expected_mass'])
    for name,forged in [('omitted',[2]),('duplicated',[2,2,2]),('forged_cost',[0,2])]:
        c.equal(name+'_raw_list_comparator_rejects',forged!=costs,True)
        c.equal(name+'_exact_mass_comparator_rejects',mass(forged,base)!=mass(costs,base),True)
    c.equal('upper_bound_alone_does_not_catch_omission',mass([2],base)<=bound,True)
    a=spec['address_controls'];S=g.Original(a['tree']);restricted,mapping=unpack_pruned(prune_map(S.tree,set(a['root_selection'])))
    c.equal('root_original_hull',sorted(S.hull(frozenset(a['root_selection']))),a['root_original_hull'])
    c.equal('root_mapping',mapping,a['root_local_to_original'])
    h=g.Original(restricted).hull(frozenset(a['root_selection']))
    c.equal('mapped_vertices_insufficient',{mapping[v] for v in h}==set(S.hull(frozenset(a['root_selection']))),False)
    transport(S,a['root_selection'],a['root_selection'])
    c.equal('displayed_edge_not_original',tuple(a['displayed_edge']) in S.edges,False)
    for name,U,expected in [('below_root',a['below_root_selection'],a['local_root_original_address']),('singleton',a['singleton_selection'],a['singleton_local_root_original_address'])]:
        _,mp=unpack_pruned(prune_map(S.tree,set(U)));c.equal(name+'_local_root',mp[''],expected)
    bad=spec['false_controls'];S=g.Original([[0,1],[2,3]]);T=g.Original([[0,2],[1,3]]);Q=[[0,1],[2,3]]
    c.equal('wrong_refinement',g.refines(bad['wrong_refinement']['F'],Q),False)
    c.equal('reverse_refinement_different',g.refines(Q,bad['wrong_refinement']['F']),True)
    for i,q in enumerate(bad['invalid_Qs']):c.equal('malformed_Q_'+str(i),g.partition_check(S.labels,q),False)
    for i,f in enumerate(bad['invalid_Fs']):c.equal('malformed_F_'+str(i),bool(g.agrees(S,S,f)),False)
    for name in ['empty_local_family','duplicate_local_block','missing_local_family']:
        fam=bad[name]['families'];c.equal(name+'_local_guard',local_guard(S,S,Q,fam),False)
    fam=bad['empty_local_family']['families'];flat=[x for family in fam for x in family]
    c.equal('empty_local_Nat_cost_trap',sum(max(len(x)-1,0) for x in fam)==max(len(flat)-len(Q),0),True)
    c.equal('empty_local_label_coverage',g.partition_check(S.labels,flat),False)
    wrong=bad['wrong_rooted_topology'];c.equal('wrong_local_rooted_topology',local_guard(g.Original(wrong['S']),g.Original(wrong['T']),wrong['Q'],wrong['families']),False)
    c.equal('reverse_clean_twin',local_guard(S,S,Q,[[U] for U in Q]) and bool(g.agrees(S,S,Q)),True)
    c.equal('omit_target_disjointness_false_extension',local_guard(S,T,Q,[[U] for U in Q]) and not bool(g.agrees(S,T,Q)),True)
    c.equal('omit_source_disjointness_false_extension',local_guard(T,S,Q,[[U] for U in Q]) and not bool(g.agrees(T,S,Q)),True)
    for name in ['requested_root_clearing_does_not_imply_Q_disjoint','requested_two_clears_do_not_imply_Q_disjoint']:
        f=bad[name];s,t=g.Original(f['S']),g.Original(f['T']);q=f['Q']
        assert g.partition_check(s.labels,q) and g.partition_check(t.labels,q)
        c.equal(name+'_actual_Q_clears',all(not(t.hull(frozenset(U))&set(f['requested_vertices'])) for U in q),True)
        c.equal(name+'_source_disjoint',s.embedding_disjoint(q),True)
        c.equal(name+'_target_disjoint',t.embedding_disjoint(q),False)
    return {'mass_original_occurrences':len(costs),'rank_negative_mutations':3,'source_target_reverse_omission_controls':2,'requested_clearing_counterexamples':2}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--spec',required=True);ap.add_argument('--mode',choices=['pilot','battery'],required=True);ap.add_argument('--output',required=True);args=ap.parse_args()
    p=Path(args.spec);spec=json.loads(p.read_text());c=Checks();started=time.monotonic();status=0
    result={'phase':'PRERELEASE','lineage':spec['lineage'],'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'spec_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'reused_graph_sha256':hashlib.sha256(BASE.read_bytes()).hexdigest(),'mode':args.mode,'rank_cases':[],'restriction_cases':[],'all_main_milestones':'OPEN'}
    try:
        c.equal('literal_comparator_clean_twin',0,0)
        cases=[spec['rank_cases'][1]] if args.mode=='pilot' else spec['rank_cases']
        for f in cases:result['rank_cases'].append(rank_case(f,c,list(map(Fraction,spec['rational_bases']))))
        if args.mode=='battery':
            for f in spec['restriction_cases']:result['restriction_cases'].append(restriction_case(f,c))
            result['negative_controls']=remaining_controls(spec,c)
            assert len(result['rank_cases'])==8 and len(result['restriction_cases'])==7
        assert time.monotonic()-started<20
        result['verdict']='FROZEN-PRERELEASE-CONTROLS-PASSED'
    except Exception as ex:
        result['verdict']='OPEN-CONTROL-OR-PIN-FAILURE';result['error']=repr(ex);result['traceback']=traceback.format_exc();status=1
    result['checks']=c.rows;result['literal_check_denominator']=len(c.rows);result['mismatches_rejected']=sum(x['mismatched_expectation_rejected'] for x in c.rows);result['seconds']=time.monotonic()-started
    out=Path(args.output);out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'verdict':result['verdict'],'literal_checks':len(c.rows),'seconds':result['seconds'],'output':str(out)}))
    try:
        from telemetry import gate,artifact,metric
        artifact(str(out));metric('frozen literal controls',sum(x['passed'] for x in c.rows),total=len(c.rows),unit='checks')
        gate('known_truth','passed' if not status else 'failed',detail='Prerelease finite controls only; '+str(out))
    except ImportError:pass
    return status
if __name__=='__main__':raise SystemExit(main())
