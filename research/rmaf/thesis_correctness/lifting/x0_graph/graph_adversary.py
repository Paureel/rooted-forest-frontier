#!/usr/bin/env python3
"""One-shot X0 evaluator, fresh stdlib lineage; no external or prior graph code.
2026-10-14. See PREEXECUTION.md and README.md for scope and controls.
"""
import argparse
import hashlib
import itertools
import json
import os
from pathlib import Path
import time
from collections import Counter
from functools import lru_cache

ROOT = Path('/Users/paurel/Documents/ChatGPT/bootscience')
HERE = ROOT / 'research/rmaf/thesis_correctness/lifting/x0_graph'
PREFIX = ROOT / 'research/rmaf/results/thesis-correctness-lifting-x0-graph-'
CARD = ROOT / 'research/rmaf/progress/thesis-correctness-lifting-x0-graph.json'
PIN = HERE.parent / 'controls.json'


def atomic(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_name(path.name + '.tmp')
    temp.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
    os.replace(temp, path)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def record_card(status, summary, metrics, artifacts):
    atomic(CARD, dict(id='thesis-correctness-lifting-x0-graph',
        title='X0 graph adversary: original-edge lifting', status=status,
        summary=summary, metrics=metrics,
        claims=[dict(id=k, label=v, status='tested' if status=='tested' else 'open',
                     detail='Finite exact adversarial checks only; no universal proof.')
                for k,v in [('L1','Actual residual paths'),('L2','Every origin choice'),('L3','Projection')]],
        lemmas=[], artifacts=[str(Path(x).resolve()) for x in artifacts]))


def freeze(x):
    if isinstance(x, list): return tuple(map(freeze,x))
    if isinstance(x, dict): return tuple(sorted((k,freeze(v)) for k,v in x.items()))
    return x


class Alarm(Exception):
    def __init__(self, site, actual, expected, witness=None):
        self.record=dict(site=site, actual=actual, expected=expected, witness=witness)
        super().__init__(site)


def eq(site, actual, expected, witness=None):
    if freeze(actual) != freeze(expected):
        raise Alarm(site, actual, expected, witness)


def require(site, condition, witness=None):
    eq(site, bool(condition), True, witness)


def powerset(values):
    values=tuple(values)
    for mask in range(1<<len(values)):
        yield frozenset(values[i] for i in range(len(values)) if mask>>i&1)


def valid(F, reduced=False):
    V=set(F['vertices']); L=F['labels']; E=F['edges']
    require('unique vertex IDs',len(V)==len(F['vertices']))
    require('unique labels',len(set(L.values()))==len(L))
    require('labels have vertices',set(L)<=V)
    require('unique edge IDs',len({e[0] for e in E})==len(E))
    parents={}; children={v:[] for v in V}
    for eid,u,v in E:
        require('edge endpoints',u in V and v in V)
        require('indegree at most one',v not in parents)
        parents[v]=u; children[u].append(v)
    for v in V:
        seen=set(); x=v
        while x in parents:
            require('acyclic',x not in seen)
            seen.add(x); x=parents[x]
        if v in L:
            if L[v]=='rho':
                require('rho component root',v not in parents)
                require('rho has zero or one child in tested regime',len(children[v])<=1)
            else: require('ordinary label is leaf',not children[v])
        elif reduced: require('unlabelled input binary',len(children[v])==2)
    return True


def signature(F, with_ids=False):
    children={v:[] for v in F['vertices']}; nonroots=set()
    for _,u,v in F['edges']: children[u].append(v); nonroots.add(v)
    def node(v):
        lab=F['labels'].get(v,'')
        return ((v,lab) if with_ids else lab,
                tuple(sorted((node(w) for w in children[v]), key=repr)))
    return tuple(sorted((node(v) for v in F['vertices'] if v not in nonroots),key=repr))


def component_labels(F):
    def labels(t):
        return ([t[0]] if t[0] else [])+sum((labels(c) for c in t[1]),[])
    return sorted([sorted(labels(t)) for t in signature(F)])


def yield_graph(F, cuts=()):
    # Actual deletion; every listed vertex initially remains, including isolated ones.
    cuts=set(cuts); V=set(F['vertices']); L=dict(F['labels'])
    require('actual current cuts',cuts<={e[0] for e in F['edges']})
    E={(u,v):(eid,) for eid,u,v in F['edges'] if eid not in cuts}
    trace=[]
    while True:
        changed=False
        for v in sorted(V):
            if v in L: continue
            out=[w for u,w in E if u==v]
            if len(out)>1: continue
            inc=[u for u,w in E if w==v]
            if not out:
                if inc: del E[(inc[0],v)]
                V.remove(v); trace.append(['delete_unlabelled_leaf',v]); changed=True; break
            w=out[0]; tail=E.pop((v,w))
            if inc:
                u=inc[0]; head=E.pop((u,v)); E[(u,w)]=head+tail
                trace.append(['suppress_unlabelled_unary',v,u,w])
            else: trace.append(['delete_unlabelled_root_stem',v,w])
            V.remove(v); changed=True; break
        if not changed: break
    paths={u+'-'+v:list(p) for (u,v),p in sorted(E.items())}
    G=dict(vertices=sorted(V),labels=L,
           edges=[[u+'-'+v,u,v] for u,v in sorted(E)])
    return G, paths, trace


def oracle(F, cuts=()):
    # Different algorithm: recursively trim child trees, returning unary child's root.
    cuts=set(cuts); ch={v:[] for v in F['vertices']}; nonroots=set()
    for eid,u,v in F['edges']:
        if eid not in cuts: ch[u].append(v); nonroots.add(v)
    V=[]; E=[]
    def visit(v):
        roots=[r for w in ch[v] if (r:=visit(w)) is not None]
        if v not in F['labels']:
            if len(roots)==0:return None
            if len(roots)==1:return roots[0]
        V.append(v)
        for w in roots:E.append([v+'-'+w,v,w])
        return v
    for v in F['vertices']:
        if v not in nonroots:visit(v)
    return dict(vertices=sorted(V),labels=dict(F['labels']),edges=sorted(E))


def path_checks(F,C,G,paths,trace):
    original={eid:(u,v) for eid,u,v in F['edges']}; used=set()
    suppressed={x[1] for x in trace if x[0]=='suppress_unlabelled_unary'}
    for g,u,v in G['edges']:
        p=paths[g]
        require('L1 nonempty path',bool(p))
        require('L1 original edges avoid C',all(e in original and e not in C for e in p))
        require('L1 start endpoint',original[p[0]][0]==u)
        require('L1 end endpoint',original[p[-1]][1]==v)
        for a,b in zip(p,p[1:]):
            eq('L1 directed incidence',original[a][1],original[b][0])
            require('L1 internal vertex suppressed',original[a][1] in suppressed)
        require('L1 paths edge-disjoint',not used.intersection(p));used.update(p)
    return used


def same_yield(site,left,right,witness=None):
    eq(site+' full labelled topology',signature(left),signature(right),witness)
    eq(site+' original surviving IDs',signature(left,True),signature(right,True),witness)


def controls():
    start=time.perf_counter(); pin=json.loads(PIN.read_text()); F=pin['base_graph'];valid(F,True)
    rows=[]; catches=[]
    # Full topology expected by hand before execution, beyond component-only pin.
    leaf=lambda s:(s,())
    singleton=tuple(sorted([leaf('rho'),leaf('a'),leaf('b'),leaf('c')],key=repr))
    rho_a_b=(('rho',(('',(leaf('a'),leaf('b'))),)),leaf('c'))
    rho_a=(('rho',(leaf('a'),)),leaf('b'),leaf('c'))
    expected_top={
        'identity':(('rho',(('',(('',(leaf('b'),leaf('c'))),leaf('a'))),)),),
        'suppressed-path-choice':tuple(sorted(rho_a,key=repr)),
        'absent-parent':singleton,
        'empty-component-and-redundant-cost':singleton,
        'sequential-choice':singleton,
        'two-protected-origins-one-residual-edge':tuple(sorted(rho_a,key=repr))}
    for c in pin['graph_controls']:
        cid=c['id']; C=frozenset(c['C']); G,P,T=yield_graph(F,C)
        path_checks(F,C,G,P,T);same_yield(cid+' oracle',G,oracle(F,C))
        if 'expected_residual_paths' in c:eq(cid+' paths',P,c['expected_residual_paths'])
        row=dict(id=cid,C=sorted(C),residual=G,paths=P,trace=T,outcomes=[])
        if cid=='sequential-choice':
            g=c['first_R'][0]; s=c['first_origin'];require(cid+' first choice',s in P[g])
            K=C|{s};H,Q,U=yield_graph(F,K)
            eq(cid+' second path',Q[c['second_R'][0]],c['expected_second_path_origins'])
            observed=[]
            for t in Q[c['second_R'][0]]:
                J=K|{t}; Y,_,_=yield_graph(F,J); observed.append(sorted(J))
                eq(cid+' count',len(J),c['expected_lift_count'])
                eq(cid+' topology',signature(Y),expected_top[cid])
                eq(cid+' components',component_labels(Y),sorted(map(sorted,c['expected_components'])))
                row['outcomes'].append(dict(K=sorted(J),yielded=Y,topology=signature(Y)))
            eq(cid+' cutsets',sorted(observed),sorted(map(sorted,c['all_final_cutsets'])))
            require(cid+' raw sets differ',observed[0]!=observed[1])
        else:
            R=c.get('R',[])
            choices=list(itertools.product(*(P[g] for g in R)))
            if 'all_expected_origin_choices' in c:
                eq(cid+' every choice',[x[0] for x in choices],c['all_expected_origin_choices'])
            for ss in choices:
                K=C|set(ss); Y,_,_=yield_graph(F,K); Z,_,_=yield_graph(G,R)
                same_yield(cid+' L2',Y,Z)
                eq(cid+' topology',signature(Y),expected_top[cid])
                if 'expected_lift_count' in c:eq(cid+' count',len(K),c['expected_lift_count'])
                if 'expected_components' in c:
                    eq(cid+' components',component_labels(Y),sorted(map(sorted,c['expected_components'])))
                row['outcomes'].append(dict(origins=ss,K=sorted(K),yielded=Y,topology=signature(Y)))
            if cid=='two-protected-origins-one-residual-edge':
                eq(cid+' individual selectability',all(p in P[R[0]] for p in c['protected_origins']),c['expected_each_individually_selectable'])
                both=C|set(c['protected_origins']); Y,_,_=yield_graph(F,both)
                eq(cid+' both count',len(both),c['expected_select_both_lift_count'])
                require(cid+' false additive count rejected',len(both)!=c['rejection_twins']['claimed_both_origins_with_additive_count'])
                row['both_origins']=dict(K=sorted(both),yielded=Y,topology=signature(Y))
            if 'expected_discarded_component_vertices' in c:
                # Independently get actual connected components of F-C.
                adj={v:set() for v in F['vertices']}
                for eid,u,v in F['edges']:
                    if eid not in C:adj[u].add(v);adj[v].add(u)
                seen=set();discarded=[]
                for v in F['vertices']:
                    if v in seen:continue
                    comp={v}; stack=[v];seen.add(v)
                    while stack:
                        for w in adj[stack.pop()]-seen:seen.add(w);comp.add(w);stack.append(w)
                    if not comp.intersection(F['labels']):discarded+=list(comp)
                eq(cid+' discarded component',sorted(discarded),sorted(c['expected_discarded_component_vertices']))
                require(cid+' component count rejection',len(signature(G))!=c['rejection_twins']['claimed_component_count_equals_cut_count_plus_one'])
        rows.append(row)
    # Plants exercise comparison, shape preservation and rejection logic directly.
    def catch(name, fn):
        try:fn()
        except Alarm as err:catches.append(dict(id=name,caught=True,alarm=err.record));return
        raise Alarm('uncaught planted corruption',name,'must throw Alarm')
    for name,a,b in [('count',2,3),('components',[['a','b']],[['a'],['b']]),
                      ('path',['es','eb'],['ea']),('topology',(('',(('a',()),('',(('b',()),('c',()))))),),
                         (('',(('',(('a',()),('b',()))),('c',()))),)),
                      ('surviving_ids',['r','a'],['s','a'])]:
        eq('clean '+name,a,a);catch(name,lambda a=a,b=b:eq(name,a,b))
    G,P,T=yield_graph(F,['ec'])
    catch('wrong_origin',lambda:require('origin belongs to path','ea' in P['r-b']))
    bad=dict(P);bad['r-b']=['ea'];catch('forged_path',lambda:path_checks(F,{'ec'},G,bad,T))
    H,Q,U=yield_graph(F,['er','ec'])
    catch('fictitious_parent',lambda:require('no fictitious incoming edge','er' in set(sum(Q.values(),[]))))
    catch('suppressed_edge',lambda:require('actual edge','r-s' in P))
    broken=json.loads(json.dumps(F));broken['labels']['b']='a'
    catch('duplicate_label',lambda:valid(broken,True))
    broken2=json.loads(json.dumps(F));broken2['edges'].append(['bad','a','b'])
    catch('indegree',lambda:valid(broken2,True))
    empty=dict(vertices=[],labels={},edges=[]);Y,P,T=yield_graph(empty)
    eq('empty null',Y,empty);eq('empty null path',P,{})
    return dict(status='CONTROLS-PASS',controls_count=len(rows),controls=rows,
                planted_catches=len(catches),catches=catches,null_count=1,
                elapsed_seconds=time.perf_counter()-start,pin_sha256=sha(PIN),script_sha256=sha(__file__))


@lru_cache(None)
def trees(labels):
    if len(labels)==1:return (labels[0],)
    out=[]; rest=labels[1:]
    for k in range(len(rest)):
        for extra in itertools.combinations(rest,k):
            a=(labels[0],)+extra; b=tuple(x for x in rest if x not in extra)
            for x in trees(a):
                for y in trees(b):out.append((x,y))
    return tuple(out)


@lru_cache(None)
def forests(labels):
    if not labels:return ((),)
    out=[];rest=labels[1:]
    for k in range(len(rest)+1):
        for extra in itertools.combinations(rest,k):
            block=(labels[0],)+extra; remainder=tuple(x for x in rest if x not in extra)
            for t in trees(block):
                for f in forests(remainder):out.append((t,)+f)
    return tuple(out)


def build(forest,mode):
    V=[];E=[];L={};i=0
    def walk(t):
        nonlocal i
        if isinstance(t,str):V.append(t);L[t]=t;return t
        v='u'+str(i);i+=1;V.append(v)
        for x in t:
            w=walk(x);E.append(['e'+str(len(E)),v,w])
        return v
    roots=[walk(t) for t in forest]
    if mode!='none':
        V.append('rho');L['rho']='rho'
        if mode!='singleton':E.append(['e'+str(len(E)),'rho',roots[mode]])
    return dict(vertices=V,labels=L,edges=E)


def all_graphs(n):
    labels=tuple(chr(97+i) for i in range(n));out=[]
    for f in forests(labels):
        for mode in ['none','singleton']+list(range(len(f))):
            out.append((f,mode,build(f,mode)))
    return out


def search(n,selection,cap,seq_mode,runname):
    start=time.perf_counter(); M=Counter();examples={};windows=[]
    population=all_graphs(n)
    indices=list(range(len(population)))
    if selection:
        # Stratified deterministic sample spreads across component counts and shapes.
        step=max(1,len(indices)//selection)
        indices=indices[::step][:selection]
    completed=[];interrupted=False
    result_path=Path(str(PREFIX)+runname+'.json')
    def witness(F,C,**kw):
        return dict(graph=F,C=sorted(C),**kw)
    def example(category,F,C,G,P,**kw):
        if category not in examples:
            examples[category]=dict(graph=F,C=sorted(C),residual=G,paths=P,
                                    residual_topology=signature(G),**kw)
    for idx in indices:
        if time.perf_counter()-start>cap:interrupted=True;break
        graph_start=time.perf_counter();f,mode,F=population[idx];valid(F,True)
        edgeids=tuple(e[0] for e in F['edges']);Ys={};Ps={};Ts={}
        for C in powerset(edgeids):
            G,P,T=yield_graph(F,C);same_yield('recursive oracle',G,oracle(F,C))
            Ys[C]=G;Ps[C]=P;Ts[C]=T;M['yield_oracle_checks']+=1
        for C,G in Ys.items():
            P=Ps[C];T=Ts[C];used=path_checks(F,C,G,P,T);M['C_cases']+=1
            M['L1_residual_edges']+=len(P)
            if mode!='none':M['rho_C_cases']+=1
            if any(t[0]=='delete_unlabelled_root_stem' for t in T):
                M['root_stem_C_cases']+=1;example('root_absent',F,C,G,P)
            remaining=set(edgeids)-set(C)
            if remaining-used:
                M['unrepresented_edges_C_cases']+=1
                example('discarded_or_root_stem_edges',F,C,G,P,unrepresented=sorted(remaining-used))
            if any(len(p)>1 for p in P.values()):
                M['multi_origin_path_C_cases']+=1;example('multiple_origins',F,C,G,P)
            for R in powerset(P):
                H,Q,U=yield_graph(G,R);M['R_cases']+=1
                for ss in itertools.product(*(P[g] for g in sorted(R))):
                    K=C|set(ss);M['L2_origin_choices']+=1
                    W=witness(F,C,R=sorted(R),origins=ss,K=sorted(K),paths=P)
                    eq('L2 additive count',len(K),len(C)+len(R),W)
                    same_yield('L2',Ys[frozenset(K)],H,W)
                    # Sequential checks: every second residual subset and origin choice.
                    do_seq=(seq_mode=='all' or (seq_mode=='single' and len(R)==1))
                    if do_seq:
                        direct=Ys[frozenset(K)];DP=Ps[frozenset(K)]
                        eq('sequential intermediate paths',
                           {g:[e for h in path for e in P[h]] for g,path in Q.items()},DP,W)
                        M['sequential_first_choices']+=1
                        for S in powerset(Q):
                            J,_,_=yield_graph(H,S);M['sequential_second_subsets']+=1
                            for tt in itertools.product(*(DP[g] for g in sorted(S))):
                                final=frozenset(K|set(tt));M['sequential_origin_choices']+=1
                                eq('sequential additive count',len(final),len(C)+len(R)+len(S),W)
                                same_yield('sequential',Ys[final],J,W)
            for extra in powerset(remaining):
                K=C|extra;R=frozenset(g for g,p in P.items() if extra.intersection(p))
                H,_,_=yield_graph(G,R);M['L3_K_extensions']+=1
                W=witness(F,C,K=sorted(K),projected_R=sorted(R),paths=P)
                require('L3 count inequality',len(R)<=len(extra),W)
                same_yield('L3 projection',Ys[K],H,W)
                if len(R)<len(extra):
                    M['strict_redundant_K_extensions']+=1
                    example('redundant_cut',F,C,G,P,K=sorted(K),projected_R=sorted(R),yielded=Ys[K],yielded_topology=signature(Ys[K]))
                if any(len(extra.intersection(p))>1 for p in P.values()):
                    M['multiple_cuts_one_path_K_extensions']+=1
        M['graphs']+=1;completed.append(idx)
        if len(f)>1:M['multicomponent_graphs']+=1
        if mode=='none':M['no_rho_graphs']+=1
        elif mode=='singleton':M['singleton_rho_graphs']+=1
        else:M['unary_rho_graphs']+=1
        windows.append(dict(graph_index=idx,seconds=time.perf_counter()-graph_start,edges=len(edgeids)))
        if M['graphs']%5==0:
            partial=dict(status='RUNNING',n=n,metrics=dict(M),elapsed_seconds=time.perf_counter()-start,
                         graphs_completed=completed,graphs_planned=indices)
            atomic(result_path,partial)
            record_card('running','Exact graph X0 enumeration underway; universal claims remain open.',dict(M),[__file__,result_path])
    elapsed=time.perf_counter()-start
    result=dict(status='BOUNDED-NO-FIRE',n=n,exhaustive_planned=not interrupted,
        full_graph_population=len(population),planned_indices=indices,completed_indices=completed,
        scope=dict(ordinary_labels=[chr(97+i) for i in range(n)],
                   rho_modes=['absent','singleton component','unary above each component'],
                   sequential_first=seq_mode,
                   all_C=True,all_R=True,all_origin_choices=True,all_K_containing_C=True,
                   original_ID_equality_also_checked=True),
        metrics=dict(M),elapsed_seconds=elapsed,per_graph_timing=windows,examples=examples,
        script_sha256=sha(__file__),pin_sha256=sha(PIN),
        lineage='Fresh stdlib code; no prior evaluator or author/repair proof read. Recursive oracle is same-author internal check.')
    atomic(result_path,result)
    record_card('tested','Bounded X0 NO-FIRE; exact scope in receipts; L1–L3 remain unproved.',dict(M),[__file__,result_path,HERE/'WORKFILE.md',HERE/'SOURCES.md'])
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--controls-only',action='store_true')
    parser.add_argument('--n',type=int,default=3);parser.add_argument('--sample',type=int,default=0)
    parser.add_argument('--cap-seconds',type=float,default=45)
    parser.add_argument('--sequential',choices=['all','single','none'],default='all')
    parser.add_argument('--name',default='controls');args=parser.parse_args()
    record_card('running','Frozen controls executing before any graph search.',{},[__file__,PIN])
    try:
        control=controls();cp=Path(str(PREFIX)+args.name+'-controls.json');atomic(cp,control)
        print(json.dumps({k:control[k] for k in ['status','controls_count','planted_catches','null_count','elapsed_seconds']},sort_keys=True),flush=True)
        if not args.controls_only:
            result=search(args.n,args.sample,args.cap_seconds,args.sequential,args.name)
            print(json.dumps({k:result[k] for k in ['status','n','exhaustive_planned','full_graph_population','metrics','elapsed_seconds']},sort_keys=True),flush=True)
    except Alarm as err:
        failure=dict(status='STOP-AND-REPORT',failure=err.record,script_sha256=sha(__file__),pin_sha256=sha(PIN))
        fp=Path(str(PREFIX)+args.name+'-failure.json');atomic(fp,failure)
        record_card('open','Control/search alarm; stopped without repair. See exact witness.',{},[fp,__file__])
        print(json.dumps(failure,sort_keys=True));raise SystemExit(2)

if __name__=='__main__':main()
