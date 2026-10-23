"""Literal Lemma 6.5 domain adversary; deliberately outside active containment.
It is not an algorithm execution and must never be reported as one.
"""
import json
from pathlib import Path
from independent import Graph,valid
T1=Graph([(('a','b'),('c','d'))],True)
F1=Graph([('a','c'),'b','d','rho'])
T2=Graph([(('a','c'),('b','d'))],True)
F2=T2
E={F2.bylabel['a'],F2.bylabel['c']}
u=F2.parent[F2.bylabel['a']]
E0={u}
original=T1.allcuts()
F1_is_forest=F1.cut([]) in original
E_AF=F2.cut(E) in original
E0_AF=F2.cut(E0) in original
assert F1_is_forest and E_AF and not E0_AF and u in F2.parent
# Passing twin: T1=T2 has the cherry in the original tree.
twin_E_AF=F2.cut(E) in T2.allcuts();twin_E0_AF=F2.cut(E0) in T2.allcuts()
assert twin_E_AF and twin_E0_AF
blocks=(frozenset('ac'),frozenset(['rho','b','d']))
assert not valid(T1,T2,blocks)
spans=[T1.span(b) for b in blocks]
receipt={'claim':'root-safe normalization with ONLY literal Lemma6.5 hypotheses','verdict':'FALSE on stated standalone domain','algorithm_counterexample':False,'T1':[['a','b'],['c','d']],'T2':[['a','c'],['b','d']],'rho':'labelled unary root','F1_components':[['a','c'],['b'],['d'],['rho']],'F1_is_forest_of_T1':F1_is_forest,'F2_is_forest_of_T2':True,'E':['parent(a)','parent(c)'],'E2':[],'a_c_siblings_in_F1_and_F2_minus_E2':True,'E_yields_AF':E_AF,'path_cuts':2,'u_parent_exists':True,'normalized_E0':['parent(LCA(a,c))'],'E0_yields_AF':E0_AF,'E_forest':F2.cut(E),'E0_forest':F2.cut(E0),'T1_embedding_intersection':sorted(spans[0]&spans[1]),'violated_active_invariant':'F2 component labels do not refine F1 component labels; no valid active-state claim is refuted','passing_twin':{'T1_equals_T2':True,'E_AF':twin_E_AF,'E0_AF':twin_E0_AF}}
p=Path(__file__).parent/'normalization-domain.json';p.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
