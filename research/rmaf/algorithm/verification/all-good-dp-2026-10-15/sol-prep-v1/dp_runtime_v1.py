"""One-shot independent owner-color runtime toy, no agreement/minimum enumerator.
Graph/canonical core is disclosed own reuse. No candidate implementation contact.
"""
import collections
from original_graph_v1 import Graph,canonical

POISON_CALLS={'unknown_minimum':0,'partition_oracle':0}
class ForbiddenOracleAccess(RuntimeError): pass
def unknown_minimum(*args,**kwargs):
    POISON_CALLS['unknown_minimum']+=1
    raise ForbiddenOracleAccess('unknown_minimum access poisoned')
def partition_oracle(*args,**kwargs):
    POISON_CALLS['partition_oracle']+=1
    raise ForbiddenOracleAccess('partition_oracle access poisoned')
def _labels(t): return Graph(t).labels()
def _tree(t):
    return (isinstance(t,int) and not isinstance(t,bool) and t>=0) or (isinstance(t,list) and len(t)==2 and all(_tree(x) for x in t))
def proper(T,ss):
    if (T is not None and not _tree(T)) or not all(_tree(s) for s in ss):return False
    X=_labels(T); return len(X)==len(set(X)) and collections.Counter(X)==collections.Counter(x for s in ss for x in _labels(s))
def all_good(T,ss):
    if not proper(T,ss): return False
    G=Graph(T)
    return all(canonical(G.restriction(_labels(s)))==canonical(s) for s in ss)
def owners(T,ss):
    if not proper(T,ss): raise ValueError('proper state required for unique owner map')
    return {x:c for c,s in enumerate(ss) for x in _labels(s)}
def addr(v):return ''.join(map(str,v))
def regions(G,assignment):
    assert set(assignment)==set(G.child), 'original vertices missing or added'
    unseen=set(G.child); result=[]
    while unseen:
        start=min(unseen); color=assignment[start]; todo=[start]; component=set()
        while todo:
            v=todo.pop()
            if v in component:continue
            component.add(v);unseen.discard(v)
            ns=list(G.child[v])+([G.parent[v]] if v in G.parent else [])
            todo.extend(w for w in ns if assignment[w]==color and w not in component)
        result.append({'color':color,'vertices':sorted(addr(v) for v in component),'leaves':sorted(G.taxon[v] for v in component if v in G.taxon)})
    return sorted(result,key=lambda r:r['vertices'])
def run(T,ss):
    if not all_good(T,ss):return {'accepted':False,'F':None,'minimum':None,'visits':0,'rows':0,'evaluations':0}
    if T is None:return {'accepted':True,'F':[],'minimum':0,'changes':0,'regions':[],'assignment':{},'ownerMap':{},'internalRows':{},'visits':0,'rows':0,'evaluations':0}
    G=Graph(T);owner=owners(T,ss);k=len(ss);stats={'visits':0,'rows':0,'evaluations':0};rowcosts={}
    def walk(v):
        stats['visits']+=1
        if v in G.taxon:
            c=owner[G.taxon[v]];table={c:(0,{v:c})}
        else:
            childrows=[walk(w) for w in G.child[v]];table={}
            for c in range(k):
                total=0;assignment={v:c}
                for child in childrows:
                    stats['evaluations']+=len(child)
                    cc,(value,colors)=min(child.items(),key=lambda item:(item[1][0]+(item[0]!=c),item[0]))
                    total+=value+(cc!=c);assignment.update(colors)
                table[c]=(total,assignment)
            rowcosts[addr(v)]={str(c):value for c,(value,_) in table.items()}
        stats['rows']+=len(table)
        return table
    table=walk(());color,(changes,assignment)=min(table.items(),key=lambda item:(item[1][0],item[0]))
    actual_changes=sum(assignment[v]!=assignment[w] for v,cs in G.child.items() for w in cs)
    assert changes==actual_changes
    raw=regions(G,assignment);assert len(raw)==changes+1
    if any(not r['leaves'] for r in raw):raise AssertionError('leafless region in final minimum coloring')
    F=sorted(r['leaves'] for r in raw)
    additional=len(raw)-k
    assert additional>=0, 'source offset would require Nat truncation'
    return {'accepted':True,'F':F,'minimum':additional,'changes':changes,'regions':raw,'assignment':{addr(v):c for v,c in assignment.items()},'ownerMap':{str(x):c for x,c in owner.items()},'internalRows':rowcosts,**stats}
