"""One-shot finite consumer checks; fresh review lineage only."""
from fresh_exact import *
from hunt import shapes,fragment,normal
from additional_checks import replace
import time
start=time.perf_counter();rows=[];counts={'ordinary_swapped_exchange':0,'two_stage_minimum_cases':0,'two_stage_missing_second_parent':0,'compound_two_stage':0}
# Ordinary and endpoint-swapped 2-pendant exchanges on all n4 pairs.
for s1 in shapes(tuple('abcd')):
 a=Tree(s1)
 for s2 in shapes(tuple('abcd')):
  b=Tree(s2);op,opts=optimum(a,b)
  for kids in a.children.values():
   if len(kids)!=2:continue
   clusters=[a.cluster[v] for v in kids]
   if not all(c in b.edge_for and a.restriction(c)==b.restriction(c) for c in clusters):continue
   x,y=[b.edge_for[c] for c in clusters];P=b.pendant_edges(x,y)
   if len(P)!=2:continue
   u=b.lca([x,y]);path=b.path_edges(x,y)
   for e in opts:
    for endpoint in [x,y]:
     if endpoint not in e or not(P&e):continue
     counts['ordinary_swapped_exchange']+=1
     new=normal(b,e|P,path,u,set())
     assert P<=new and af(a,b,new) and len(new)==op
# Exhaustive five atomic-label common-uncle geometries; each tested intact and compound.
family=shapes(('a','b1','b2','c','x'))
for s1 in family:
 a0=Tree(s1);ac=a0.lca([a0.at['a'],a0.at['c']])
 if a0.cluster[ac]!=frozenset(['a','c']):continue
 p=a0.parent[ac]
 if a0.children[p]!=[ac,a0.at['x']] and set(a0.children[p])!={ac,a0.at['x']}:continue
 for s2 in family:
  b0=Tree(s2);u0=b0.lca([b0.at['a'],b0.at['c']]);p0=b0.parent[u0]
  if set(b0.children[p0])!={u0,b0.at['x']}:continue
  if len(b0.pendant_edges('a','c'))!=2:continue
  for compound in [False,True]:
   mapping={v:[v+'1',v+'2'] for v in ['a','c','x']} if compound else {}
   a,b=Tree(replace(s1,mapping)),Tree(replace(s2,mapping));node=lambda v:b.edge_for[frozenset(mapping.get(v,[v]))]
   u=b.lca([node('a'),node('c')]);p=b.parent[u];P=b.pendant_edges(node('a'),node('c'));path1=b.path_edges(node('a'),node('c'))
   for detached in [False,True]:
    initial={1} if detached else set();op,opts=optimum(a,b,initial)
    for e in opts:
     if not(e&{node('a'),node('c')}):continue
     c1=normal(b,e|P,path1,u,initial);path2=b.path_edges(node('x'),u);c2=normal(b,c1,path2,p,initial)
     counts['two_stage_minimum_cases']+=1
     counts['compound_two_stage']+=compound
     counts['two_stage_missing_second_parent']+=p in initial
     assert af(a,b,initial|c1) and af(a,b,initial|c2) and P<=c2 and len(c2)<=op
     assert not(path1&c1) and path2=={node('x'),u}
     assert fragment(b,u,initial|c1) and fragment(b,node('x'),initial|c1)
     # The only cuts removed by projection to yielded F2~P are the fixed P.
     assert (c1-P).isdisjoint(path1|P)
receipt={'status':'passed','counts':counts,'elapsed_seconds':time.perf_counter()-start,'scope':'All n4 whole-tree 2-pendant minimum exchanges and all 5-atomic-label common-uncle geometries, expanded uniformly at a,c,x, whole/rho-detached. No arbitrary active-forest or protected-origin lift proof.'}
(ROOT/'results/thesis-correctness-repair-review-consumer-census.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
