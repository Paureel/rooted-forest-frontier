#!/usr/bin/env python3
"""One-task independent exact oracle for rho transfer; no prior solver imports.

Representation: explicitly numbered vertices and undirected BFS paths. Restrictions
are induced-span rooted trees with unlabeled unary vertices suppressed. Enumerates
set partitions, not edge cut sets or candidate DP states. It is deliberately small.
Read README.md for scope and acceptance controls.
"""
from __future__ import annotations
import argparse
from collections import deque
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
RHO = '@rho'

class Tree:
    def __init__(self, spec, augmented=False):
        self.children, self.labels, self.depth, self.parent = {}, {}, {}, {}
        self.leaves = {}
        def visit(s, par=None, depth=0):
            v = len(self.children)
            self.children[v] = []
            self.parent[v] = par
            self.depth[v] = depth
            if isinstance(s, str):
                if s == RHO or s in self.leaves:
                    raise ValueError('duplicate or reserved label')
                self.labels[v] = s
                self.leaves[s] = v
            else:
                if not isinstance(s, (list, tuple)) or len(s) != 2:
                    raise ValueError('source must be binary')
                self.children[v] = [visit(x, v, depth+1) for x in s]
            return v
        self.root = visit(spec)
        if augmented:
            v = len(self.children)
            self.children[v] = [self.root]
            self.parent[self.root] = v
            self.parent[v] = None
            self.labels[v] = RHO
            self.leaves[RHO] = v
            self.depth = {u:d+1 for u,d in self.depth.items()}
            self.depth[v] = 0
            self.root = v
        self.adj = {v:list(ch) for v,ch in self.children.items()}
        for v,p in self.parent.items():
            if p is not None:
                self.adj[v].append(p)
        self.labelset = frozenset(self.leaves)

    def path(self, a, b):
        pending = deque([(a, (a,))])
        seen = {a}
        while pending:
            v, seq = pending.popleft()
            if v == b:
                return set(seq)
            for u in self.adj[v]:
                if u not in seen:
                    seen.add(u)
                    pending.append((u, seq+(u,)))
        raise AssertionError('disconnected tree')

    def block(self, block):
        terminals = [self.leaves[x] for x in block]
        span = {terminals[0]}
        for v in terminals[1:]:
            span |= self.path(terminals[0], v)
        top = min(span, key=self.depth.__getitem__)
        def shape(v):
            ch = [shape(u) for u in self.children[v] if u in span]
            ch.sort(key=repr)
            lab = self.labels.get(v) if self.labels.get(v) in block else None
            if lab is None and len(ch) == 1:
                return ch[0]
            return (lab, tuple(ch))
        return frozenset(span), shape(top)

    def partition_signature(self, part, unsafe_disjoint=False):
        flat = [x for b in part for x in b]
        if any(not b for b in part) or len(set(flat)) != len(flat) or set(flat) != self.labelset:
            raise ValueError('not a partition of input labels')
        used, answer = set(), []
        for b in part:
            span, sig = self.block(b)
            if not unsafe_disjoint and used & span:
                return None
            used |= span
            answer.append(sig)
        return tuple(answer)


def normal(part):
    return tuple(sorted((tuple(sorted(b)) for b in part)))

@lru_cache(None)
def partitions(labels):
    if not labels:
        return ((),)
    x, *tail = labels
    answer = []
    for p in partitions(tuple(tail)):
        answer.append(normal(((x,),)+p))
        for j in range(len(p)):
            answer.append(normal(p[:j]+((x,)+p[j],)+p[j+1:]))
    return tuple(answer)


def agrees(a, b, part, unsafe_disjoint=False):
    if a.labelset != b.labelset:
        raise ValueError('unequal labels')
    p = normal(part)
    x = a.partition_signature(p, unsafe_disjoint)
    y = b.partition_signature(p, unsafe_disjoint)
    return x is not None and x == y


def profiles(tree):
    return {p:s for p in partitions(tuple(sorted(tree.labelset)))
            if (s := tree.partition_signature(p)) is not None}


def common(pa, pb):
    return tuple(p for p,s in pa.items() if pb.get(p) == s)


def exact(a, b, augmented=False):
    ta, tb = Tree(a, augmented), Tree(b, augmented)
    if ta.labelset != tb.labelset:
        raise ValueError('unequal labels')
    afs = common(profiles(ta), profiles(tb))
    return min(map(len, afs)), afs


def delete_rho(part):
    return normal(tuple(tuple(x for x in b if x != RHO) for b in part
                        if b != (RHO,)))


def controls(path):
    spec = json.loads(Path(path).read_text())
    rows = []
    for c in spec['cases']:
        k, fs = exact(c['a'], c['b'])
        kr, fr = exact(c['a'], c['b'], True)
        assert k == c['k'], (c['name'], 'k', k, c['k'])
        assert kr == c['krho'], (c['name'], 'krho', kr, c['krho'])
        if 'ordinary_witness' in c:
            assert agrees(Tree(c['a']), Tree(c['b']), c['ordinary_witness'])
        if 'invalid_witness' in c:
            assert not agrees(Tree(c['a']), Tree(c['b']), c['invalid_witness'])
            assert agrees(Tree(c['a']), Tree(c['b']), c['invalid_witness'], True)
        rows.append({'name':c['name'],'k':k,'krho':kr})
    bad = [lambda:Tree(['a','a']), lambda:Tree(['a']),
           lambda:exact('a','b'), lambda:Tree(RHO),
           lambda:agrees(Tree(['a','b']),Tree(['a','b']),[[],['a','b']]),
           lambda:agrees(Tree(['a','b']),Tree(['a','b']),[['a'],['a','b']]),
           lambda:agrees(Tree(['a','b']),Tree(['a','b']),[['a']])]
    for i,f in enumerate(bad):
        try: f()
        except ValueError: pass
        else: raise AssertionError(('missed malformed', i))
    return {'positive':rows,'malformed_rejected':len(bad),'vertex_disjoint_mutation_caught':True}

@lru_cache(None)
def trees(labels):
    if len(labels)==1: return (labels[0],)
    first, *rest = labels
    ans=[]
    for m in range(1 << len(rest)):
        left=(first,)+tuple(x for i,x in enumerate(rest) if m>>i&1)
        right=tuple(x for i,x in enumerate(rest) if not m>>i&1)
        if not right: continue
        for a in trees(left):
            for b in trees(right): ans.append((a,b))
    return tuple(ans)


def scan(n):
    start=time.perf_counter()
    ts=trees(tuple('abcdefghi'[:n]))
    ps=[profiles(Tree(t)) for t in ts]
    rs=[profiles(Tree(t,True)) for t in ts]
    prep=time.perf_counter()-start
    rows=[]; gaps={0:0,1:0}; afcount=0; rc=0
    pair_start=time.perf_counter()
    for i,a in enumerate(ts):
        for j in range(i,len(ts)):
            fs=common(ps[i],ps[j]); fr=common(rs[i],rs[j])
            k=min(map(len,fs)); kr=min(map(len,fr))
            forced=min(len(p) for p in fr if (RHO,) in p)
            assert k <= kr <= k+1, (a,ts[j],k,kr)
            assert forced == k+1, (a,ts[j],k,forced)
            sf=set(fs); sr=set(fr)
            for p in fs:
                assert normal(p+((RHO,),)) in sr
            for p in fr:
                assert delete_rho(p) in sf
            afcount += len(fs); rc += len(fr); gaps[kr-k]+=1
            if kr>k and len(rows)<3:
                rows.append({'a':a,'b':ts[j],'k':k,'krho':kr,
                             'ordinary_optimum':next(p for p in fs if len(p)==k)})
    elapsed=time.perf_counter()-pair_start
    return {'n':n,'trees':len(ts),'unordered_pairs':len(ts)*(len(ts)+1)//2,
            'ordinary_forests_checked':afcount,'augmented_forests_checked':rc,
            'gap_counts':gaps,'gap_examples':rows,
            'profile_seconds':prep,'pair_seconds':elapsed,'seconds':time.perf_counter()-start}


def write_json(path, data):
    p=Path(path); tmp=p.with_suffix(p.suffix+'.tmp')
    tmp.write_text(json.dumps(data,indent=2)+'\n'); tmp.replace(p)

if __name__ == '__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--controls',default=str(HERE/'controls.json'))
    ap.add_argument('--n',type=int,nargs='*',default=[]); ap.add_argument('--out',required=True)
    args=ap.parse_args()
    result={'created':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
            'scope':'finite exact controls; not a universal proof',
            'controls_sha256':hashlib.sha256(Path(args.controls).read_bytes()).hexdigest(),
            'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'controls':controls(args.controls),'scans':[]}
    write_json(args.out,result)
    for n in args.n:
        result['scans'].append(scan(n)); write_json(args.out,result)
        print(json.dumps(result['scans'][-1]),flush=True)
    print(json.dumps({'positive_controls':len(result['controls']['positive']),
                      'malformed_rejected':result['controls']['malformed_rejected']}),flush=True)
