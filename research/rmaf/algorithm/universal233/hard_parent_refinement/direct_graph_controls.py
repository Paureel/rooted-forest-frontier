#!/usr/bin/env python3
"""One-shot supplemental exact original-graph controls, not universal proof.

Expected leaf components were pinned in CONTROLS-PIN.md before theorem work.
This direct BFS was executed after theorem development and is therefore a
supplemental check, not the pre-proof X0 run or independent certification.
"""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent

def component_control(tree,expected_cuts,expected_leaves):
    adjacency={}; leaves={}
    def build(t,v=''):
        adjacency.setdefault(v,set())
        if isinstance(t,int): leaves[v]=t
        else:
            for side,child in enumerate(t):
                w=v+str(side)
                adjacency.setdefault(w,set()).add(v)
                adjacency[v].add(w)
                build(child,w)
    build(tree)
    aa=next(v for v,x in leaves.items() if x==0)
    bb=next(v for v,x in leaves.items() if x==1)
    def path(u,v):
        todo=[(u,[u])]; seen={u}
        while todo:
            w,p=todo.pop()
            if w==v:return p
            for x in adjacency[w]-seen:seen.add(x);todo.append((x,p+[x]))
        raise AssertionError('missing actual source path')
    p=set(path(aa,bb))
    cuts=sorted(v for v in adjacency if v and v[:-1] in p and v not in p)
    assert cuts==expected_cuts,(cuts,expected_cuts)
    for v in cuts:adjacency[v].remove(v[:-1]);adjacency[v[:-1]].remove(v)
    remaining=set(adjacency);components=[]
    while remaining:
        root=min(remaining);todo=[root];found={root}
        while todo:
            v=todo.pop()
            for w in adjacency[v]-found:found.add(w);todo.append(w)
        remaining-=found
        lab=sorted(leaves[v] for v in found if v in leaves)
        assert lab,('leafless original component',sorted(found))
        components.append({'vertices':sorted(found),'labels':lab})
    got=sorted(c['labels'] for c in components)
    assert got==sorted(expected_leaves),(got,expected_leaves)
    assert len(components)==3
    return {'cuts':cuts,'components':components,'no_leafless':True}

result={
 'chronology':'SUPPLEMENTAL POST-DEVELOPMENT DIRECT BFS; not pre-proof X0 or independent certification',
 'root_lca_singleton_pendants':component_control(((0,2),(1,3)),['01','11'],[[2],[3],[0,1]]),
 'upward_region_permitted':component_control((((0,2),(1,3)),4),['001','011'],[[2],[3],[0,1,4]])}
# A deliberate false expected component must be caught by the same comparator.
try:component_control(((0,2),(1,3)),['01','11'],[[2],[3],[]])
except AssertionError:result['wrong_root_leafset_plant']='CAUGHT'
else:raise RuntimeError('wrong-root corruption survived')
result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
result['verdict']='PASS'
(H/'DIRECT-GRAPH-CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: two original-source BFS controls; three nonleafless components each; false root-leafset plant caught')
