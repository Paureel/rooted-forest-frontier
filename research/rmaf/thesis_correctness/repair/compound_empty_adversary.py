"""One-shot main-arm exact original-edge check; reuses the existing controlled
raw-deletion evaluator. This is not an independent-author certification.
"""
import json,sys
from pathlib import Path
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R.parent))
from algorithm import Forest
from local_obligations import info,component_data,controls,all_optimal_cuts
controls()  # earlier fixed raw-deletion controls before the new candidate

def cluster_nodes(f):
    def lab(v):
        z=set(f.label.get(v,()))
        for c in f.child[v]:z.update(lab(c))
        return frozenset(z)
    return {lab(v):v for v in f.child}

def is_af(f1,f2,E):
    used=set();out=[];ok=True
    for block in component_data(f2,E):
        s1,v1=info(f1,block);s2,v2=info(f2,block)
        equal=s1==s2 and s1 is not None;overlap=sorted(used & (v1 or set()))
        ok=ok and equal and not overlap
        if v1:used |= v1
        out.append({'labels':sorted(x for atom in block for x in atom),'equal_restrictions':equal,'overlap_vertices':overlap,'T1_restriction':s1,'F2_restriction':s2})
    return ok,out
z=json.loads((R/'compound-empty-hypothesis.json').read_text())
f1,f2=Forest.tree(z['T1']),Forest.tree(z['T2']);nodes=cluster_nodes(f2)
E={nodes[frozenset(c)] for c in z['E_clusters']};E0={nodes[frozenset(c)] for c in z['E0_clusters']}
a=nodes[frozenset(z['a_subtree'])];c=nodes[frozenset(z['c_subtree'])]
p={v:u for u,cs in f2.child.items() for v in cs}
assert p[a]==p[c]
assert f1.match(f2,a) is not None and f1.match(f2,c) is not None
p1=f1.parent();assert p1[f1.match(f2,a)]==p1[f1.match(f2,c)]
good,oldparts=is_af(f1,f2,E);newgood,newparts=is_af(f1,f2,E0)
assert good is True and newgood is False
opt,opts=all_optimal_cuts(f1,f2)
report={'status':'REFUTED-active-containment-alone-with-compound-endpoints','T1':z['T1'],'T2':z['T2'],'F1_equals_T1':True,'F2_equals_T2':True,'active_component_containment':True,'sibling_subtrees':['a','(c1,c2)'],'E_edge_bottoms':sorted(E),'E0_edge_bottoms':sorted(E0),'E_clusters':z['E_clusters'],'E0_clusters':z['E0_clusters'],'E_is_AF':good,'E0_is_AF':newgood,'E_components':oldparts,'E0_components':newparts,'minimum_cuts':opt,'E_size':len(E),'E_is_minimum':len(E)==opt,'source_scope':'Literal Lemma6.5 permits arbitrary AF edge set E and compound sibling roots. This does not refute atom-only or minimum-E normalization, nor the algorithm.'}
path=R.parent.parent/'results'/'thesis-correctness-repair-compound-empty.json';path.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['E_components','E0_components']},indent=2))
