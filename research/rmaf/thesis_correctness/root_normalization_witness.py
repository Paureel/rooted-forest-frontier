"""One-shot exact domain witness for the parent-edge formula in Lemma 6.5."""
import json
from pathlib import Path
from algorithm import Forest
from local_obligations import component_data, info

f1=Forest.tree([['a','c'],'b'])
f2=Forest({0:[],1:[2,5],2:[3,4],3:[],4:[],5:[]},
          {0:frozenset(['rho']),3:frozenset(['a']),4:frozenset(['b']),5:frozenset(['c'])},set())
E={3,4,5};E2={4};E1={3,5};u=1
parent={c:v for v,cs in f2.child.items() for c in cs}
seen=set()
for b in component_data(f2,E):
    s1,v1=info(f1,b);s2,_=info(f2,b)
    assert s1==s2 and not(seen&v1)
    seen|=v1
# After cutting b's edge, component {a,c} suppresses the unlabelled unary node 2.
ac=frozenset([frozenset(['a']),frozenset(['c'])])
s1,_=info(f1,ac);s2,_=info(f2,ac)
assert s1==s2
seen=set()
for b in component_data(f2,E-E1):
    s1,v1=info(f1,b);s2,_=info(f2,b)
    assert s1==s2 and not(seen&v1)
    seen|=v1
assert E2<=E and E1<=E and len(E1)==2 and u not in parent
out={'source':'Whidden2013 Lemma 6.5 pp.101–103','F1':'rho->((a,c),b)',
     'F2':['rho','((a,b),c)'],'a':'a','c':'c','E':['ea','eb','ec'],'E2':['eb'],'E1':['ea','ec'],
     'F2_cut_E_is_AF':True,'a_c_common_siblings_after_E2':True,'lca_is_unlabelled_component_root':True,
     'lca_parent_edge_exists':False,'root_safe_repair_is_AF':True,'verdict':'formula for E0 refers to undefined eu on this allowed forest; deleting all path cuts without inserting eu gives the expected root-safe repair',
     'algorithm_verdict':'not a decision counterexample; this is a source-lemma domain obligation'}
p=Path(__file__).resolve().parent.parent/'results'/'thesis-correctness-root-normalization-witness.json'
p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
