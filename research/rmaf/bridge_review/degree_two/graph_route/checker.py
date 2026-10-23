#!/usr/bin/env python3
"""One-shot independent actual-tree audit. No project/checker imports.

Uses pairwise address paths for minimal support and restricted cluster hierarchies
for rooted isomorphism, rather than the source's recursive extractor/sameShape.
Run via ./bootloops-python; exact values only. Fixtures are frozen hand literals.
"""
from __future__ import annotations
import hashlib, itertools, json, pathlib, time
from functools import lru_cache

HERE = pathlib.Path(__file__).resolve().parent

def tree(x):
    return tuple(tree(y) for y in x) if isinstance(x, list) else x

def address_json(vs):
    return [list(v) for v in sorted(vs)]

@lru_cache(None)
def occurrence_items(t):
    if isinstance(t, int):
        return (((), t),)
    return tuple(((False,) + p, x) for p, x in occurrence_items(t[0])) + tuple(((True,) + p, x) for p, x in occurrence_items(t[1]))

@lru_cache(None)
def vertices(t):
    return frozenset(p[:i] for p, _ in occurrence_items(t) for i in range(len(p)+1))

def adjacent(p, q):
    return (len(p)+1 == len(q) and q[:-1] == p) or (len(q)+1 == len(p) and p[:-1] == q)

def path(p, q):
    k = 0
    while k < min(len(p),len(q)) and p[k] == q[k]:
        k += 1
    return {p[:j] for j in range(k,len(p)+1)} | {q[:j] for j in range(k,len(q)+1)}

@lru_cache(None)
def support(t, B):
    terminals = [p for p,x in occurrence_items(t) if x in B]
    result = set(terminals)
    for p,q in itertools.combinations(terminals,2):
        result.update(path(p,q))
    return frozenset(result)

@lru_cache(None)
def shape(t, B):
    # Labelled rooted clade hierarchy after removing absent labels and suppressing
    # unary nodes. For unique labels it completely specifies rooted isomorphism.
    occ = occurrence_items(t)
    return frozenset(frozenset(x for p,x in occ if p[:len(v)] == v and x in B)
                     for v in vertices(t)) - {frozenset()}

def agrees(t,u,B):
    return bool(support(t,B)) and bool(support(u,B)) and shape(t,B) == shape(u,B)

def degree(v,S):
    return sum(adjacent(v,w) for w in S) if v in S else 0

def unique(t):
    ls = [x for _,x in occurrence_items(t)]
    return len(ls) == len(set(ls))

def premises(t,u,B,v):
    labels_t = {x for _,x in occurrence_items(t)}
    labels_u = {x for _,x in occurrence_items(u)}
    return (unique(t) and unique(u) and bool(B) and len(B)==len(set(B))
            and set(B) <= labels_t & labels_u and agrees(t,u,tuple(B))
            and v in support(t,tuple(B)) and degree(v,support(t,tuple(B)))==2)

def splits(B):
    B = tuple(sorted(B))
    if len(B)<2: return
    for mask in range(1 << (len(B)-1)):
        A = (B[0],)+tuple(x for i,x in enumerate(B[1:]) if mask >> i & 1)
        C = tuple(x for x in B if x not in A)
        if C: yield A,C

def full_conclusion(t,u,B,v,A,C):
    if not (A and C and len(A)==len(set(A)) and len(C)==len(set(C)) and set(A).isdisjoint(C) and set(A)|set(C)==set(B)):
        return False
    if not agrees(t,u,A) or not agrees(t,u,C): return False
    for T in (t,u):
        original,a,c = support(T,tuple(B)),support(T,A),support(T,C)
        if not (a <= original and c <= original and a.isdisjoint(c)): return False
        # Every previously avoided mark is retained, within that tree.
        for mark in vertices(T)-original:
            if mark in a or mark in c: return False
    return v not in support(t,A) and v not in support(t,C)

def witnesses(t,u,B,v):
    return [(A,C) for A,C in splits(B) if full_conclusion(t,u,B,v,A,C)]

def partitions(B):
    if not B:
        yield ()
        return
    x,*rest = B
    for P in partitions(rest):
        yield ((x,),)+P
        for i,block in enumerate(P):
            yield P[:i]+((x,)+block,)+P[i+1:]

def partition_check(labels,P):
    flat = [x for b in P for x in b]
    return all(P) and all(flat.count(x)==1 for x in labels) and all(x in labels for x in flat)

def agreement(t,u,P):
    if not all(partition_check([x for _,x in occurrence_items(T)],P) for T in (t,u)): return False
    if not all(agrees(t,u,b) for b in P): return False
    return all(support(T,a).isdisjoint(support(T,b)) for T in (t,u) for a,b in itertools.combinations(P,2))

def local_partition(t,u,B,P,marks=()):
    return (partition_check(B,P) and all(agrees(t,u,b) for b in P)
            and all(support(T,a).isdisjoint(support(T,b)) for T in (t,u) for a,b in itertools.combinations(P,2))
            and all(v not in support(t,b) for b in P for v in marks))

def min_blocks(t,u,B,marks=()):
    return min(len(P) for P in partitions(B) if local_partition(t,u,B,P,marks))

def components(S):
    remaining=set(S); result=[]
    while remaining:
        todo=[min(remaining)]; found=set()
        while todo:
            p=todo.pop()
            if p in found: continue
            found.add(p); remaining.discard(p)
            todo.extend(q for q in remaining if adjacent(p,q))
        result.append(frozenset(found))
    return result

def check_controls(F):
    rows=[]
    def check(name,actual,expected):
        if actual != expected: raise AssertionError((name,actual,expected))
        rows.append({'id':name,'actual':actual,'expected':expected,'pass':True})
    for name in ('root','suppressed'):
        f=F[name]; t,u=tree(f['t']),tree(f['u']); B=tuple(f['B']); v=tuple(f['v']); A,C=map(tuple,f['blocks'])
        check(name+'.premises',premises(t,u,B,v),True)
        check(name+'.degree',degree(v,support(t,B)),f['degree'])
        check(name+'.support_t',address_json(support(t,B)),sorted(f['t_support']))
        if 'u_support' in f: check(name+'.support_u',address_json(support(u,B)),sorted(f['u_support']))
        for T,side in ((t,'t'),(u,'u')):
            check(name+'.blocks_'+side,[address_json(support(T,b)) for b in (A,C)],f[side+'_block_supports'])
        check(name+'.full_conclusion',full_conclusion(t,u,B,v,A,C),True)
        check(name+'.cost',2-1,f['cost'])
    f=F['consumer']; t,u=tree(f['t']),tree(f['u']); P=tuple(map(tuple,f['blocks'])); Q=tuple(map(tuple,f['after_blocks']))
    check('consumer.before',agreement(t,u,P),f['agreement_before'])
    check('consumer.after',agreement(t,u,Q),f['agreement_after'])
    check('consumer.counts',[len(P),len(Q)],[f['before'],f['after']])
    f=F['degree_three']; t,u=tree(f['t']),tree(f['u']); B=tuple(f['B']); v=tuple(f['v'])
    check('degree_three.degree',degree(v,support(t,B)),f['degree'])
    check('degree_three.no_two_blocks',len(witnesses(t,u,B,v)),f['two_block_refinements'])
    check('degree_three.minimum',min_blocks(t,u,B,(v,)),f['min_avoiding_blocks'])
    f=F['wrong_root']; t=tree(f['t']); B=tuple(f['B']); v=tuple(f['v'])
    check('wrong_root.support',address_json(support(t,B)),sorted(f['t_support']))
    check('wrong_root.absent',v in support(t,B),f['v_in_support'])
    f=F['joint_marks']; t,u=tree(f['t']),tree(f['u']); B=tuple(f['B']); a,b=map(tuple,f['marks'])
    check('joint_marks.costs',[min_blocks(t,u,B,M)-1 for M in ((),(a,),(b,),(a,b))],f['costs_empty_first_second_both'])
    for f in F['invalid_premises']:
        t,u=tree(f['t']),tree(f['u']); B=tuple(f['B']); v=tuple(f['v'])
        check(f['id']+'.degree',degree(v,support(t,B)),f['degree'])
        check(f['id']+'.premises',premises(t,u,B,v),f['local'])
    # Mutations are falsity detectors, not contradictory reference regeneration.
    for m in F['mutations']:
        f=F[m['case']]; t=tree(f['t']); B=tuple(f.get('B',()))
        if m['id']=='wrong_degree': false_claim=degree(tuple(f['v']),support(t,B))==2
        elif m['id'] in ('missing_path','wrong_root'): false_claim=support(t,B)==frozenset(map(tuple,m['false_support']))
        elif m['id']=='cross_tree_address': false_claim=support(t,(0,))==support(tree(f['u']),(0,))
        elif m['id']=='overlapping_blocks': false_claim=full_conclusion(t,tree(f['u']),B,tuple(f['v']),*map(tuple,m['false_blocks']))
        elif m['id']=='wrong_cost': false_claim=len(f['after_blocks'])==m['false_after']
        else: raise ValueError(m)
        check('mutation.'+m['id']+'.caught',not false_claim,True)
    return rows

@lru_cache(None)
def shapes(n):
    if n==1: return (None,)
    return tuple((a,b) for k in range(1,n) for a in shapes(k) for b in shapes(n-k))

def relabel(s, labels):
    it=iter(labels)
    def walk(x): return next(it) if x is None else (walk(x[0]),walk(x[1]))
    return walk(s)

def mirror(t): return t if isinstance(t,int) else (mirror(t[1]),mirror(t[0]))

def pilot(deadline):
    start=time.perf_counter(); counts=dict(pairs=0,selections=0,in_regime=0,full_witnesses=0,agreement_partitions=0,consumer_refinements=0,degree_propagation=0,deletion_splits=0,root_vertices=0,suppressed_nonroot=0,unequal_outside_B=0)
    timing=[]
    for n in range(1,5):
        ts=sorted(set(relabel(s,p) for s in shapes(n) for p in itertools.permutations(range(n))),key=repr) if n<=3 else list(dict.fromkeys(T for s in shapes(n) for T in (relabel(s,range(n)),mirror(relabel(s,range(n))))))
        lap=time.perf_counter()
        for t,u in itertools.product(ts,repeat=2):
            counts['pairs']+=1
            for mask in range(1<<n):
                B=tuple(x for x in range(n) if mask>>x&1); counts['selections']+=1
                if not B or not agrees(t,u,B): continue
                S=support(t,B)
                for v in S:
                    if degree(v,S)!=2: continue
                    assert premises(t,u,B,v)
                    counts['in_regime']+=1
                    counts['root_vertices' if not v else 'suppressed_nonroot']+=1
                    W=witnesses(t,u,B,v)
                    assert W, ('IN_REGIME_FIRE',t,u,B,v)
                    counts['full_witnesses']+=len(W)
                    comps=components(S-{v})
                    assert len(comps)==2, ('DELETE_COMPONENTS',t,B,v)
                    blocks=tuple(tuple(sorted(x for p,x in occurrence_items(t) if p in c and x in B)) for c in comps)
                    assert full_conclusion(t,u,B,v,*blocks), ('DELETE_TRANSPORT',t,u,B,v,blocks)
                    counts['deletion_splits']+=1
                for mask2 in range(1<<len(B)):
                    C=tuple(x for i,x in enumerate(B) if mask2>>i&1); Csupport=support(t,C)
                    for v in Csupport:
                        if degree(v,S)==2 and v not in {p for p,x in occurrence_items(t) if x in C}:
                            assert degree(v,Csupport)==2, ('DEGREE_PROPAGATION',t,B,C,v)
                            counts['degree_propagation']+=1
            for P in partitions(tuple(range(n))):
                if not agreement(t,u,P): continue
                counts['agreement_partitions']+=1
                for i,B in enumerate(P):
                    for v in support(t,B):
                        if degree(v,support(t,B))!=2: continue
                        W=witnesses(t,u,B,v)
                        assert W
                        for A,C in W:
                            Q=P[:i]+(A,C)+P[i+1:]
                            assert agreement(t,u,Q) and len(Q)==len(P)+1, ('CONSUMER_FIRE',t,u,P,v,Q)
                            counts['consumer_refinements']+=1
            if time.perf_counter()-start > deadline:
                raise TimeoutError({'completed':counts,'deadline':deadline})
        timing.append(dict(n=n,trees=len(ts),seconds=time.perf_counter()-lap,cumulative=counts.copy()))
    # Same restricted pair, deliberately different full taxon sets and root paths.
    t=((0,4),2); u=(2,(5,0)); B=(0,2)
    for v in support(t,B):
        if premises(t,u,B,v):
            assert witnesses(t,u,B,v)
            counts['unequal_outside_B']+=1
    return {'counts':counts,'timing':timing,'seconds':time.perf_counter()-start,'verdict':'NO_FIRE_WITHIN_BOUNDED_PILOT','scope':'frozen pilot only; no universal theorem and no G3/G4 closure'}

def main():
    started=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
    F=json.loads((HERE/'fixtures.json').read_text())
    controls=check_controls(F)
    (HERE/'controls-result.json').write_text(json.dumps({'started_utc':started,'checks':controls,'count':len(controls),'verdict':'ALL_FROZEN_CONTROLS_PASS'},indent=2)+'\n')
    result=pilot(F['pilot']['deadline_seconds'])
    result['started_utc']=started
    result['hashes']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (HERE/'fixtures.json',pathlib.Path(__file__),HERE/'controls-result.json')}
    (HERE/'pilot-result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'controls':len(controls),'pilot':result},sort_keys=True))
if __name__=='__main__': main()
