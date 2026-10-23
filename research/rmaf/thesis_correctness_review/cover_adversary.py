"""Post-unblinding concrete audit of the actual universal Cover interface."""
import json
from pathlib import Path
from independent import Graph,trees,optimum_partition
out=[]; premises=0
for t in trees(list('abcd')):
 g=Graph([t],True); gm=g.allcuts()
 for s in trees(list('abcd')):
  h=Graph([s],True); hm=h.allcuts(); common=set(gm)&set(hm)
  q=min(len(F)-1 for F in common)
  opts=[E for F in common if hm[F][0]==q for E in hm[F][1]]
  for cs in g.child.values():
   if len(cs)!=2 or not all(v in g.label for v in cs): continue
   a,c=(h.bylabel[g.label[v]] for v in cs)
   path=h.path(a,c); ps=set(path)
   bs=[w for v in path for w in h.child[v] if w not in ps]
   if len(bs)!=2: continue
   for E in opts:
    premises+=1
    if a not in E and c not in E and not set(bs)<=E:
     def descendants(v):
      return ([h.label[v]] if v in h.label else []) + [x for w in h.child[v] for x in descendants(w)]
     out.append({'T1':t,'T2':s,'q':q,'partition_optimum_components':optimum_partition(g,h),'a':g.label[cs[0]],'c':g.label[cs[1]],'pendants':[descendants(v) for v in bs],'cut_edge_bottoms':sorted(E),'cut_edge_clusters':[descendants(v) for v in sorted(E)],'cut_forest':h.cut(E),'F2_child':h.child,'F2_labels':h.label})
     break
p=Path(__file__).parent/'cover-adversary.json'
p.write_text(json.dumps({'status':'REFUTED-as-all-raw-optima-Cover','premises':premises,'counterexamples':len(out),'witnesses':out[:4]},indent=2)+'\n')
print(json.dumps({'premises':premises,'counterexamples':len(out),'first':out[:1]}))
