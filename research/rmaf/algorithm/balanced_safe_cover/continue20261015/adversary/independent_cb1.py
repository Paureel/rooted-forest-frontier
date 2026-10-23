#!/usr/bin/env python3
"""One-shot independent CB1 falsifier, frozen design DESIGN-v1.md; no code reuse."""
import argparse, itertools, json, time, hashlib
from pathlib import Path
from fractions import Fraction

class Tree:
    def __init__(self, raw):
        self.raw=raw; self.adj={}; self.parent={}; self.depth={}; self.leaf={}; self.edges=[]
        def rec(x,p=None):
            v=len(self.adj); self.adj[v]=[]; self.parent[v]=p; self.depth[v]=0 if p is None else self.depth[p]+1
            if p is not None:
                i=len(self.edges); self.edges.append((p,v)); self.adj[p].append((v,i)); self.adj[v].append((p,i))
            if isinstance(x,str):
                if x in self.leaf: raise ValueError('duplicate label')
                self.leaf[x]=v
            else:
                if not isinstance(x,list) or len(x)!=2: raise ValueError('not binary')
                rec(x[0],v); rec(x[1],v)
            return v
        if raw is not None: rec(raw)
        self.labels=tuple(sorted(self.leaf))
    def path(self,a,b):
        x,y=self.leaf[a],self.leaf[b]; todo=[(x,frozenset([x]),0)]; seen=set()
        while todo:
            v,vs,es=todo.pop()
            if v==y:return vs,es
            seen.add(v)
            for w,e in self.adj[v]:
                if w not in seen:todo.append((w,vs|{w},es|(1<<e)))
        raise ValueError('missing path')
    def support(self,B):
        B=tuple(sorted(B))
        if not B:return frozenset()
        if len(B)==1:return frozenset([self.leaf[B[0]]])
        out=frozenset()
        for z in B[1:]:out |= self.path(B[0],z)[0]
        return out
    def triple(self,B):
        def lca(a,b):
            a,b=self.leaf[a],self.leaf[b]
            while self.depth[a]>self.depth[b]:a=self.parent[a]
            while self.depth[b]>self.depth[a]:b=self.parent[b]
            while a!=b:a,b=self.parent[a],self.parent[b]
            return a
        pairs=list(itertools.combinations(B,2)); return tuple(sorted(max(pairs,key=lambda p:self.depth[lca(*p)])))
    def cut_partition(self,C):
        done=set(); parts=[]; empty=0
        for start in self.adj:
            if start in done:continue
            q=[start]; done.add(start); vs=set()
            while q:
                v=q.pop(); vs.add(v)
                for w,e in self.adj[v]:
                    if not (C>>e)&1 and w not in done:done.add(w);q.append(w)
            B=frozenset(x for x,v in self.leaf.items() if v in vs)
            if B:parts.append(B)
            else:empty+=1
        return tuple(sorted(parts,key=lambda b:tuple(sorted(b)))),empty

def restriction(raw,B):
    if raw is None:return None
    if isinstance(raw,str):return raw if raw in B else None
    a,b=(restriction(x,B) for x in raw)
    if a is None:return b
    if b is None:return a
    return tuple(sorted((a,b),key=repr))

def agreement(S,T,P):
    flat=[x for B in P for x in B]
    if len(flat)!=len(set(flat)) or set(flat)!=set(S.labels) or S.labels!=T.labels:return False
    usedS=set();usedT=set()
    for B in P:
        if not B or restriction(S.raw,B)!=restriction(T.raw,B):return False
        U,V=S.support(B),T.support(B)
        if usedS&U or usedT&V:return False
        usedS|=U;usedT|=V
    return True

def partitions(L):
    if not L:yield ();return
    x=L[0]
    for P in partitions(L[1:]):
        yield (frozenset([x]),)+P
        for i in range(len(P)):yield P[:i]+(P[i]|{x},)+P[i+1:]

def partition_opt(S,T):
    best=len(S.labels)+1; win=None
    for P in partitions(S.labels):
        if len(P)<best and agreement(S,T,P):best=len(P);win=P
    return max(0,best-1),win

def minimal(H):
    U=sorted(set(H),key=lambda h:(h.bit_count(),h));out=[]
    for h in U:
        if not h:raise ValueError('empty conflict')
        if not any((a&h)==a for a in out):out.append(h)
    return tuple(sorted(out))

def conflicts(S,T):
    if S.labels!=T.labels:raise ValueError('label mismatch')
    H=[]
    for B in itertools.combinations(S.labels,3):
        if S.triple(B)!=T.triple(B):
            H.append(S.path(B[0],B[1])[1]|S.path(B[0],B[2])[1])
    for Q in itertools.combinations(S.labels,4):
        a=Q[0]
        for b in Q[1:]:
            c,d=[x for x in Q if x not in (a,b)]
            vs,es=S.path(a,b);ws,fs=S.path(c,d)
            if not vs&ws and T.path(a,b)[0]&T.path(c,d)[0]:H.append(es|fs)
    return minimal(H)

def factors(H):
    todo=set(H);out=[]
    while todo:
        h=todo.pop();rows=[h];univ=h
        while True:
            add={q for q in todo if q&univ}
            if not add:break
            todo-=add;rows.extend(add)
            for q in add:univ|=q
        out.append(tuple(sorted(rows)))
    return tuple(sorted(out,key=lambda f:(min(f),f)))

def quotient(H):
    H=minimal(H)
    cols={}
    U=0
    for h in H:U|=h
    for e in range(U.bit_length()):
        I=sum(1<<i for i,h in enumerate(H) if (h>>e)&1)
        if I:cols.setdefault(I,e)
    keep=[e for I,e in cols.items() if not any(I!=J and (I&J)==I for J in cols)]
    K=sum(1<<e for e in keep)
    return minimal(tuple(h&K for h in H))

def search(H,t,stats):
    stats['nodes']+=1
    if not H:return 0
    if t==0:return None
    R=quotient(H);h=min(R,key=lambda z:(z.bit_count(),z));stats['max_rank']=max(stats['max_rank'],h.bit_count())
    stats['rank_counts'][str(h.bit_count())]=stats['rank_counts'].get(str(h.bit_count()),0)+1
    for e in range(h.bit_length()):
        if (h>>e)&1:
            W=search(tuple(q for q in R if not (q>>e)&1),t-1,stats)
            if W is not None:return W|(1<<e)
    return None

def solve(H,b):
    F=factors(minimal(H)); unspent=b;C=0;rec=[]; total={'nodes':0,'max_rank':0,'rank_counts':{}}
    for f in F:
        trials=[];W=None
        for t in range(unspent+1):
            s={'nodes':0,'max_rank':0,'rank_counts':{}};W=search(f,t,s);trials.append({'budget':t,**s,'success':W is not None})
            total['nodes']+=s['nodes'];total['max_rank']=max(total['max_rank'],s['max_rank'])
            for k,v in s['rank_counts'].items():total['rank_counts'][k]=total['rank_counts'].get(k,0)+v
            if W is not None:break
        rec.append({'rows':len(f),'universe':(lambda z:z.bit_count())(sum([])) if False else len(set(e for h in f for e in range(h.bit_length()) if (h>>e)&1)),'trials':trials})
        if W is None:return {'success':False,'cuts':None,'factors':rec,**total}
        C|=W;unspent-=W.bit_count()
    return {'success':True,'cuts':C,'cost':C.bit_count(),'factors':rec,**total}

def brute_hit(H,m):
    for t in range(m+1):
        for C in itertools.combinations(range(m),t):
            mask=sum(1<<e for e in C)
            if all(mask&h for h in H):return t,mask
    raise AssertionError()

def certificate(S,T,C):
    P,E=S.cut_partition(C)
    return {'cuts':C,'cost':C.bit_count(),'partition':[sorted(B) for B in P], 'target_supports':[sorted(T.support(B)) for B in P]}

def check_cert(S,T,K):
    try:
        C=K['cuts'];P,E=S.cut_partition(C);P2=tuple(frozenset(B) for B in K['partition'])
        return (isinstance(C,int) and C>=0 and C<(1<<len(S.edges)) and E==0 and K['cost']==C.bit_count()==max(0,len(P)-1)
                and P==P2 and agreement(S,T,P) and K['target_supports']==[sorted(T.support(B)) for B in P])
    except (KeyError,TypeError,ValueError):return False

def controls(path):
    controls=json.loads(Path(path).read_text());A=[];O=[];start=time.perf_counter()
    for f in controls['abstract']:
        H=f['rows'];v,w=brute_hit(H,f['m']);assert v==f['optimum'];assert len(factors(minimal(H)))==f['factors']
        Z=solve(H,v);assert Z['success'] and Z['cost']==v and all(Z['cuts']&h for h in H)
        if v:assert not solve(H,v-1)['success']
        A.append({'id':f['id'],'optimum':v,'factors':f['factors'],'execution':Z})
    catches=0
    for f in controls['ordinary']:
        t0=time.perf_counter();S,T=Tree(f['source']),Tree(f['target']);v,P=partition_opt(S,T);assert v==f['optimum'],(f['id'],v)
        H=conflicts(S,T);Z=solve(H,v);assert Z['success'] and Z['cost']==v
        K=certificate(S,T,Z['cuts']);assert check_cert(S,T,K)
        if v:assert not solve(H,v-1)['success']
        for C in range(1<<len(S.edges)):
            PP,_=S.cut_partition(C);assert agreement(S,T,PP)==all(C&h for h in H),(f['id'],C)
        if S.labels:
            for mutation in ['cost','label','support']:
                M=json.loads(json.dumps(K))
                if mutation=='cost':M['cost']+=1
                if mutation=='label':M['partition'][0][0]='__WRONG_LABEL__'
                if mutation=='support':M['target_supports'][0]=[-1]
                assert not check_cert(S,T,M);catches+=1
        O.append({'id':f['id'],'optimum':v,'minimal_conflicts':len(H),'rows':H,'certificate':K,'execution':Z,'seconds':time.perf_counter()-t0})
    assert not Fraction(3,2)>=2;catches+=1
    assert next(x['optimum'] for x in O if x['id']=='crossed-quartet')!=1;catches+=1
    assert len(A)==6 and len(O)==9 and catches==26
    return {'status':'CONTROLS_PASS','abstract_count':len(A),'ordinary_count':len(O),'corruptions_caught':catches,'abstract':A,'ordinary':O,'seconds':time.perf_counter()-start}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--controls',required=True);ap.add_argument('--output',required=True);a=ap.parse_args()
    out=controls(a.controls);out['instrument_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','abstract_count','ordinary_count','corruptions_caught','seconds','instrument_sha256']}))
if __name__=='__main__':main()
