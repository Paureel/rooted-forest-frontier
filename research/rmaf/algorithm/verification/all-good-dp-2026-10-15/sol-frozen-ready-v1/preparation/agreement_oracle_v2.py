"""One-shot own reused partition/agreement checker, corrected global-function extraction.
No runtime DP import; raw integer offset retained.
"""
import collections
from original_graph_v1 import Graph,canonical
def labels(t): return Graph(t).labels()
def partition(X,F):
    flat = [x for B in F for x in B]
    return all(B for B in F) and collections.Counter(flat) == collections.Counter(X)
def proper(T,ss):
    X=labels(T)
    return len(X)==len(set(X)) and partition(X,[labels(s) for s in ss])
def disjoint(T,F):
    hs=[Graph(T).hull(B) for B in F]
    return all(not hs[i] & hs[j] for i in range(len(hs)) for j in range(i))
def agrees(T,ss,F):
    if not proper(T,ss) or not partition(labels(T),F): return False
    sets=[set(labels(s)) for s in ss]
    if not all(any(set(B)<=S for S in sets) for B in F): return False
    if not disjoint(T,F): return False
    for s,S in zip(ss,sets):
        G=[B for B in F if set(B)<=S]
        if not partition(labels(s),G) or not disjoint(s,G): return False
        for B in G:
            if canonical(Graph(T).restriction(B)) != canonical(Graph(s).restriction(B)): return False
    return True

def partitions(X):
    if not X: yield []; return
    head,*tail=X
    for F in partitions(tail):
        yield [[head]]+[list(B) for B in F]
        for j in range(len(F)):
            G=[list(B) for B in F]; G[j]=[head]+G[j]; yield G

def forests(T,ss):
    if not proper(T,ss): return []
    return [F for F in partitions(labels(T)) if agrees(T,ss,F)]
def normalize_forest(F): return sorted(sorted(B) for B in F)
def raw_cost(ss,F): return len(F)-len(ss)
def summarize(T,ss):
    Ps=list(partitions(labels(T)))
    records=[{'F':F,'valid':agrees(T,ss,F),'rawCost':raw_cost(ss,F)} for F in Ps]
    valid=[r for r in records if r['valid']]
    assert all(r['rawCost']>=0 for r in valid), 'valid source-refining agreement had truncated offset'
    minimum=min((r['rawCost'] for r in valid),default=None)
    minima=sorted({tuple(tuple(B) for B in normalize_forest(r['F'])) for r in valid if r['rawCost']==minimum})
    return {'partitionCount':len(Ps),'records':records,'minimum':minimum,'minima':[[list(B) for B in F] for F in minima]}
