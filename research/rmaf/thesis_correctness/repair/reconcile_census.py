"""Reconcile author/reviewer premise counters; explicitly reuses review evaluator.
Not an independent scientific verifier and does not alter either frozen run.
"""
import hashlib,json,pathlib,sys,time
BASE=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf');HERE=BASE/'thesis_correctness/repair'
sys.path.insert(0,str(HERE/'review'))
from fresh_exact import Tree,af
from hunt import shapes,fragment,component_labels

def main():
    start=time.perf_counter();counts={'anchor_general_E2':0,'anchor_direct_pendant_edges':0,'both_general_E2':0,'both_direct_pendant_edges':0};witness=None
    for s1 in shapes(tuple('abcd')):
      a=Tree(s1)
      for s2 in shapes(tuple('abcd')):
        b=Tree(s2)
        common={v:b.edge_for[c] for v,c in a.cluster.items() if c in b.edge_for and a.restriction(c)==b.restriction(c)}
        pairs=[(common[x],common[y]) for kids in a.children.values() if len(kids)==2 for x,y in [kids] if x in common and y in common]
        for detached1,detached2 in [(False,False),(False,True),(True,True)]:
          ia={1} if detached1 else set();ib={1} if detached2 else set();available=sorted(set(b.parent)-ib)
          for mask in range(1<<len(available)):
            e={v for i,v in enumerate(available) if mask>>i&1}
            if not af(a,b,ib|e):continue
            for x,y in pairs:
              path=b.path_edges(x,y);u=b.lca([x,y])
              if path&ib:continue
              inside={v for v,c in b.cluster.items() if c<b.cluster[x] or c<b.cluster[y]}
              e2=e-path-inside;sides=set(b.pendant_edges(x,y))
              if any(child not in e2 and fragment(b,child,ib|e2) for child in sides):continue
              sx=fragment(b,x,ib|e);sy=fragment(b,y,ib|e);d=e&path;uc=component_labels(b,u,ib|e)
              outside=uc-(set(b.cluster[x])|set(b.cluster[y]));separated=sx if not b.path_edges(x,u).isdisjoint(e) else sy
              anchor=not(len(d)==1 and outside and separated) or bool(uc&(set(b.cluster[x])|set(b.cluster[y])))
              if not anchor:continue
              strict=sides<=e;both=bool(sx and sy)
              counts['anchor_general_E2']+=1;counts['anchor_direct_pendant_edges']+=int(strict)
              counts['both_general_E2']+=int(both);counts['both_direct_pendant_edges']+=int(both and strict)
              if not strict and witness is None:witness={'T1':s1,'T2':s2,'initial1':sorted(ia),'initial2':sorted(ib),'pair_clusters':[sorted(b.cluster[x]),sorted(b.cluster[y])],'E_clusters':[sorted(b.cluster[v]) for v in sorted(e)],'pendant_clusters':[sorted(b.cluster[v]) for v in sorted(sides)],'E2_clusters':[sorted(b.cluster[v]) for v in sorted(e2)],'explanation':'A pendant root is retained but every label below it is disconnected, so yielding removes the label-free side branch. The source E2 sibling premise holds although the pendant incoming edge itself is not cut.'}
    assert counts=={'anchor_general_E2':44862,'anchor_direct_pendant_edges':43710,'both_general_E2':42204,'both_direct_pendant_edges':41052},counts
    out={'status':'counter_denominators_reconciled','counts':counts,'extra_general_premises':counts['anchor_general_E2']-counts['anchor_direct_pendant_edges'],'witness':witness,'scope':'Reviewer permits general E2 that empties a pendant branch; author census requires cutting the pendant incoming edge. This explains all count differences in anchor/both counters. Neither receipt changed.','provenance':'Reuses reviewer fresh_exact and hunt helpers after independent construction; this is a diagnostic, not a fresh verifier.','seconds':time.perf_counter()-start}
    target=BASE/'results/thesis-correctness-repair-census-reconciliation.json';target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'counts':counts,'extra':out['extra_general_premises'],'seconds':out['seconds'],'receipt':str(target)}))
if __name__=='__main__':main()
