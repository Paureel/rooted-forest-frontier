#!/usr/bin/env python3
"""One-shot blind cherry review instrument; not a toolkit or recursive solver.
Graph path/hull/component construction is independent of the uncontacted source.
Output is exact finite diagnostic evidence; never a universal theorem certificate.
"""
import argparse
import ast
from collections import Counter, deque
from fractions import Fraction
from functools import lru_cache
import hashlib
import inspect
import itertools
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
EXPECT = json.loads((HERE / 'EXPECTATIONS-v1.json').read_text())

def tree(x):
    if type(x) is int:
        if x < 0: raise ValueError('negative label')
        return x
    if not isinstance(x, (list,tuple)) or len(x) != 2: raise ValueError('not binary')
    return (tree(x[0]),tree(x[1]))

def leaves(t):
    return [t] if type(t) is int else leaves(t[0])+leaves(t[1])

@lru_cache(None)
def graph(t):
    nodes, labels, children, adj = [], {}, {}, {}
    def visit(x,p):
        nodes.append(p); adj[p] = []
        if type(x) is int: labels[p] = x
        else:
            children[p] = (p+'0',p+'1')
            visit(x[0],p+'0'); visit(x[1],p+'1')
            for c in children[p]: adj[p].append(c); adj[c].append(p)
    visit(t,'')
    return nodes,labels,children,adj

def valid_pair(T,S):
    a,b=leaves(T),leaves(S)
    if len(a)!=len(set(a)) or len(b)!=len(set(b)): raise ValueError('duplicate labels')
    if set(a)!=set(b): raise ValueError('unequal labels')

def graph_path(t,start,end):
    adj=graph(t)[3]; prev={start:None}; queue=deque([start])
    while queue:
        p=queue.popleft()
        if p==end: break
        for q in adj[p]:
            if q not in prev: prev[q]=p; queue.append(q)
    out=[]; p=end
    while p is not None: out.append(p); p=prev[p]
    return list(reversed(out))

@lru_cache(None)
def hull(t,B):
    loc={x:p for p,x in graph(t)[1].items()}
    if not B or any(x not in loc for x in B): raise ValueError('empty or absent hull labels')
    points=[loc[x] for x in B]; out={points[0]}
    for p in points[1:]: out.update(graph_path(t,points[0],p))
    return frozenset(out)

def pair_path(S,a,b):
    if a==b: raise ValueError('equal endpoints')
    loc={x:p for p,x in graph(S)[1].items()}
    if a not in loc or b not in loc: raise ValueError('absent endpoint')
    return graph_path(S,loc[a],loc[b])

def partnorm(P):
    return tuple(sorted(tuple(sorted(B)) for B in P))

def checked_partition(labels,P):
    if any(not B for B in P): raise ValueError('empty block')
    if Counter(itertools.chain.from_iterable(P)) != Counter(labels): raise ValueError('not a partition')
    return True

def components(S,cuts):
    nodes,labels,_,adj=graph(S)
    if '' in cuts: raise ValueError('root cut')
    if len(cuts)!=len(set(cuts)): raise ValueError('duplicate cut')
    if any(c not in adj for c in cuts): raise ValueError('invalid cut')
    removed={frozenset((c[:-1],c)) for c in cuts}
    seen=set(); out=[]
    for p in nodes:
        if p in seen: continue
        group={p}; seen.add(p); queue=[p]
        while queue:
            q=queue.pop()
            for r in adj[q]:
                if r not in seen and frozenset((q,r)) not in removed:
                    group.add(r); seen.add(r); queue.append(r)
        B=sorted(labels[x] for x in group if x in labels)
        if not B: raise ValueError('leafless region')
        out.append((tuple(sorted(group)),tuple(B)))
    return out

def pendant(S,a,b):
    H=set(pair_path(S,a,b)); nodes,_,children,_=graph(S)
    cuts=[c for p in nodes if p in H for c in children.get(p,()) if c not in H]
    comps=components(S,cuts)
    return cuts,[list(B) for _,B in comps]

@lru_cache(None)
def restricted_shape(t,B):
    selected=set(B)
    def run(x):
        if type(x) is int: return ('leaf',x) if x in selected else None
        a,b=run(x[0]),run(x[1])
        if a is None: return b
        if b is None: return a
        return ('node',)+tuple(sorted((a,b),key=repr))
    return run(t)

def agreement(T,S,P):
    try:
        valid_pair(T,S); checked_partition(leaves(T),P)
        H={}
        for t in (T,S):
            hs=[hull(t,tuple(sorted(B))) for B in P]
            if any(hs[i]&hs[j] for i in range(len(hs)) for j in range(i)): return False
            H[t]=hs
        return all(restricted_shape(T,tuple(B))==restricted_shape(S,tuple(B)) for B in P)
    except ValueError: return False

def refines(F,P):
    return all(any(set(B)<=set(C) for C in P) for B in F)

@lru_cache(None)
def partitions(labels):
    if not labels: return ((),)
    out=[]
    def go(i,blocks):
        if i==len(labels): out.append(tuple(tuple(B) for B in blocks)); return
        x=labels[i]
        for j in range(len(blocks)):
            blocks[j].append(x); go(i+1,blocks); blocks[j].pop()
        blocks.append([x]); go(i+1,blocks); blocks.pop()
    go(0,[])
    return tuple(out)

def all_agreements(T,S):
    return [P for P in partitions(tuple(sorted(leaves(T)))) if agreement(T,S,P)]

def cherries(T,p=''):
    if type(T) is int: return []
    if type(T[0]) is int and type(T[1]) is int: return [(p,T[0],T[1])]
    return cherries(T[0],p+'0')+cherries(T[1],p+'1')

def candidates(T,S):
    valid_pair(T,S)
    return [(p,a,b,pendant(S,a,b)[0]) for p,a,b in cherries(T)]

def select(T,S):
    cs=candidates(T,S)
    for name,pred in [('common',lambda n:n==0),('t1',lambda n:n==1),('high',lambda n:n>=3),('hard2',lambda n:n==2)]:
        for c in cs:
            if pred(len(c[3])): return name,c,cs
    return None,None,cs

def validate_selection(name,chosen,cs,reported_counts=None):
    predicates=[('common',lambda n:n==0),('t1',lambda n:n==1),('high',lambda n:n>=3),('hard2',lambda n:n==2)]
    counts=[len(c[3]) for c in cs]
    if reported_counts is not None and counts!=reported_counts: raise ValueError('omitted candidate/rejection')
    for category,pred in predicates:
        hits=[c for c in cs if pred(len(c[3]))]
        if hits:
            if name!=category or chosen!=hits[0]: raise ValueError('wrong priority')
            return True
    if chosen is not None or name is not None: raise ValueError('nonempty selection')
    return True

def make_child(S,P,paid):
    return {'P':P,'paid':paid,'sourceForest':[restricted_shape(S,tuple(B)) for B in P if restricted_shape(S,tuple(B)) is not None]}

def validate_child(S,c):
    checked_partition(leaves(S),c['P'])
    if c['paid']+1!=len(c['P']): raise ValueError('wrong component offset')
    if len(c['sourceForest'])!=len(c['P']): raise ValueError('filter drop')
    hs=[hull(S,tuple(sorted(B))) for B in c['P']]
    if any(hs[i]&hs[j] for i in range(len(hs)) for j in range(i)): raise ValueError('source embeddings overlap')
    return True

def remaining(k,paid):
    return k-paid if paid<=k else None

def endpoint_child(S,a):
    loc={x:p for p,x in graph(S)[1].items()}
    if a not in loc or not loc[a]: raise ValueError('invalid terminal cut')
    cut=loc[a]; P=[list(B) for _,B in components(S,[cut])]
    c=make_child(S,P,1); c['cuts']=[cut]; validate_child(S,c); return c

def child_minimum(T,S,c,AF):
    subset=[F for F in AF if refines(F,c['P'])]
    return min(subset,key=len)

def check_original_case(c):
    T,S=tree(c['T']),tree(c['S']); valid_pair(T,S)
    cuts,P=pendant(S,c['a'],c['b']); path=pair_path(S,c['a'],c['b'])
    assert sorted(cuts)==sorted(c['cuts']), (c['id'],'cuts',cuts,c['cuts'])
    assert partnorm(P)==partnorm(c['P']), (c['id'],'partition',P,c['P'])
    comps=components(S,cuts); assert len(comps)==len(cuts)+1
    if 'path' in c: assert path==c['path'], (c['id'],'path',path)
    if 'components_vertices' in c:
        assert sorted(V for V,_ in comps)==sorted(tuple(sorted(V)) for V in c['components_vertices'])
    if 'forbidden_above_lca' in c: assert c['forbidden_above_lca'] not in cuts
    AF=all_agreements(T,S); assert min(map(len,AF))==c['opt']
    for key in ('F','G'):
        if key in c:
            assert agreement(T,S,c[key]),(c['id'],key,'agreement')
            if key+'_refines' in c: assert refines(c[key],P)==c[key+'_refines']
    child=make_child(S,P,len(cuts)); validate_child(S,child)
    for F in AF:
        if refines(F,P): assert len(cuts)+(len(F)-len(P))==len(F)-1
    out={'id':c['id'],'cuts':cuts,'partition':P,'path':path,'components':[{'vertices':V,'labels':B} for V,B in comps],'opt':min(map(len,AF)),'agreements':len(AF)}
    if 'branch_min_blocks' in c:
        cs=[endpoint_child(S,c['a']),endpoint_child(S,c['b']),child]
        mins=[len(child_minimum(T,S,x,AF)) for x in cs]
        assert mins==c['branch_min_blocks'],(c['id'],'branch minima',mins)
        assert [x['paid'] for x in cs]==c['branch_paid']
        assert [m-len(x['P']) for m,x in zip(mins,cs)]==c['branch_min_residual']
        out['branch_min_blocks']=mins
        out['child_budget_calls']=[{'k':k,'eligible':[remaining(k,x['paid']) for x in cs], 'success':[remaining(k,x['paid']) is not None and m-len(x['P'])<=remaining(k,x['paid']) for m,x in zip(mins,cs)]} for k in range(4)]
    return out

def validate_literal(S,a,b,cuts,P):
    expected,E=pendant(S,a,b)
    if sorted(cuts)!=sorted(expected): raise ValueError('literal pendant cover/address')
    if partnorm(P)!=partnorm(E): raise ValueError('literal components')
    return True

def runtime_dependency_gate(source):
    bad={'all_agreements','partitions','child_minimum','optimum','known_minimum'}
    module=ast.parse(source)
    calls={x.func.id for x in ast.walk(module) if isinstance(x,ast.Call) and isinstance(x.func,ast.Name)}
    if calls&bad: raise ValueError('injected optimum/enumeration dependency')
    return True

def planted_controls():
    results=[check_original_case(c) for c in EXPECT['cases']]
    priorities=[]
    for c in EXPECT['priority_cases']:
        name,chosen,cs=select(tree(c['T']),tree(c['S'])); counts=[len(x[3]) for x in cs]
        assert counts==c['counts'],(c['id'],counts)
        assert name==c['selected'] and (list(chosen[1:3]) if chosen else None)==c['pair']
        validate_selection(name,chosen,cs,counts); priorities.append({'id':c['id'],'counts':counts,'selected':name,'pair':None if chosen is None else chosen[1:3]})
    cases={c['id']:c for c in EXPECT['cases']}; c=cases['t1-public']; T,S=tree(c['T']),tree(c['S']); P=c['P']
    rb=cases['root-boundary']; R=tree(rb['S']); t3=cases['t3-new']; H=tree(t3['S']); HT=tree(t3['T'])
    highAF=all_agreements(HT,H); ca=endpoint_child(H,0); cb=endpoint_child(H,1)
    def compare(x,y):
        if x!=y: raise ValueError('frozen mismatch')
    def budget_success(child,k,F):
        r=remaining(k,child['paid'])
        if r is None or len(F)-len(child['P'])>r or not refines(F,child['P']) or not agreement(HT,H,F): raise ValueError('child/budget/refusal')
        return True
    n,ch,cs=select(tree(EXPECT['priority_cases'][0]['T']),tree(EXPECT['priority_cases'][0]['S']))
    mutants={
      'incomplete-endpoint-cover':lambda: checked_partition(leaves(S),[[1,2]]),
      'incomplete-pendant-cover':lambda:validate_literal(S,0,1,[],P),
      'skip-suppressed-vertex':lambda:compare(set(pair_path(H,0,1))-{ '000' },set(t3['path'])),
      'edge-above-lca':lambda:validate_literal(R,0,1,['0','001'],rb['P']),
      'root-cut':lambda:components(S,['']),
      'leafless-region':lambda:components(S,['0','00','01']),
      'invalid-cut':lambda:components(S,['111111']),
      'duplicate-cut':lambda:components(S,['01','01']),
      'component-offset':lambda:validate_child(S,make_child(S,P,2)),
      'nat-truncation':lambda:compare(max(0,0-1),remaining(0,1)),
      'filter-drop':lambda:validate_child(S,make_child(S,[[0],[99],[1,2]],2)),
      'display-address-as-original':lambda:validate_literal(R,0,1,['01'],rb['P']),
      'free-known-minimum':lambda:compare(0,len(cb['P'])-1),
      'unpaid-parent':lambda:budget_success(cb,0,child_minimum(HT,H,cb,highAF)),
      'double-proof-split':lambda:validate_child(S,make_child(S,P,2)),
      'wrong-priority':lambda:validate_selection('t1',cs[0],cs),
      'omitted-earlier-rejection':lambda:validate_selection(n,ch,cs,[len(ch[3])]),
      'forged-agreement':lambda:compare(agreement(T,S,[[0,1,2]]),True),
      'wrong-child':lambda:budget_success(ca,2,child_minimum(HT,H,cb,highAF)),
      'wrong-budget':lambda:budget_success(ca,1,child_minimum(HT,H,ca,highAF)),
      'missing-failure':lambda:budget_success(ca,0,child_minimum(HT,H,ca,highAF)),
      'injected-optimum-oracle':lambda:runtime_dependency_gate('def choose(T,S):\n return optimum(T,S)\n')
    }
    assert set(mutants)==set(EXPECT['mutations_required'])
    caught=[]
    for name,run in mutants.items():
        try: run()
        except (ValueError,AssertionError) as ex: caught.append({'mutation':name,'caught':True,'reason':str(ex)})
        else: raise AssertionError(('mutation survived',name))
    invalid=[lambda:valid_pair(tree([0,0]),tree([0,1])),lambda:valid_pair(tree([0,1]),tree([0,2])),lambda:pair_path(S,0,99),lambda:pair_path(S,0,0),lambda:tree(-1),lambda:checked_partition([0,1],[[],[0,1]])]
    for fn in invalid:
        try: fn()
        except ValueError: pass
        else: raise AssertionError('invalid input accepted')
    for f in (select,candidates,pendant,make_child,remaining,endpoint_child): runtime_dependency_gate(inspect.getsource(f))
    assert remaining(0,0)==0 and remaining(0,1) is None and remaining(3,1)==2
    masses={'q2_t3':2/Fraction(2)+1/Fraction(2)**3,'q233over100_t3':2/Fraction(233,100)+1/Fraction(233,100)**3,'q3_t3':2/Fraction(3)+1/Fraction(3)**3,'q233over100_t2':2/Fraction(233,100)+1/Fraction(233,100)**2}
    assert {k:str(v) for k,v in masses.items()}==EXPECT['mass_literals']
    assert all(2/Fraction(233,100)+1/Fraction(233,100)**t<1 for t in range(3,20))
    return {'plants':results,'priority':priorities,'mutations':caught,'caught':len(caught),'required':len(mutants),'invalid_rejections':len(invalid),'masses':{k:str(v) for k,v in masses.items()},'runtime_dependency_gate':'clean own runtime functions; no candidate conclusion'}

@lru_cache(None)
def trees(labels):
    if len(labels)==1: return (labels[0],)
    first=labels[0]; rest=labels[1:]; out=[]
    for mask in range(1<<len(rest)):
        A=(first,)+tuple(x for j,x in enumerate(rest) if mask>>j&1)
        B=tuple(x for j,x in enumerate(rest) if not mask>>j&1)
        if not B: continue
        out.extend((a,b) for a in trees(A) for b in trees(B))
    return tuple(out)

def finite_pairs(mode):
    if mode=='pilot':
        ts=trees((0,1,2)); pairs=list(itertools.product(ts,repeat=2)); c=EXPECT['cases'][3]; pairs.append((tree(c['T']),tree(c['S'])))
        return pairs
    out=[]
    for n in range(1,5): out.extend(itertools.product(trees(tuple(range(n))),repeat=2))
    fixed=tree(EXPECT['cases'][3]['T']); out.extend((fixed,S) for S in trees(tuple(range(5))))
    return out

def bank(mode):
    pairs=finite_pairs(mode); started=time.perf_counter(); counts=Counter(); timings=[]; failures=[]
    for index,(T,S) in enumerate(pairs):
        at=time.perf_counter(); AF=all_agreements(T,S); counts['tree_pairs']+=1; counts['agreements']+=len(AF)
        for _,a,b in cherries(T):
            cuts,P=pendant(S,a,b); t=len(cuts); counts['cherry_pairs']+=1; counts['t'+str(t)]+=1
            validate_child(S,make_child(S,P,t))
            for F in AF:
                if t>=3:
                    counts['high_checks']+=1
                    if not ([a] in [list(B) for B in F] or [b] in [list(B) for B in F] or refines(F,P)):
                        failures.append({'claim':'high','T':T,'S':S,'F':F,'P':P})
                if t==1:
                    counts['t1_checks']+=1
                    if not any(len(G)<=len(F) and refines(G,P) for G in AF): failures.append({'claim':'t1exchange','T':T,'S':S,'F':F,'P':P})
        timings.append(time.perf_counter()-at)
        if time.perf_counter()-started>EXPECT['finite_bank']['limit_seconds']: raise TimeoutError('frozen finite bound exceeded')
    assert counts['tree_pairs']==len(pairs) and not failures,failures
    return {'mode':mode,'counts':dict(counts),'denominator_pairs':len(pairs),'pair_seconds':timings,'seconds':time.perf_counter()-started,'failures':failures,'scope':'finite diagnostic only'}

def main():
    p=argparse.ArgumentParser(); p.add_argument('mode',choices=['controls','pilot','bounded']); p.add_argument('--out',required=True); a=p.parse_args()
    started=time.perf_counter(); out=planted_controls() if a.mode=='controls' else bank(a.mode)
    out.update({'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'mode':a.mode,'total_seconds':time.perf_counter()-started,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'expectations_sha256':hashlib.sha256((HERE/'EXPECTATIONS-v1.json').read_bytes()).hexdigest(),'candidate_contact':False})
    Path(a.out).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k in ('mode','counts','caught','required','total_seconds','denominator_pairs')}))
if __name__=='__main__': main()
