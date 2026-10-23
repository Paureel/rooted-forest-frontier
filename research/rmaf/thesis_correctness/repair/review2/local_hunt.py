#!/usr/bin/env python3
"""One-shot post-proof-read hostile audit, using only this review's fresh checker."""
from fresh_graph import *

def trees(labels):
    if len(labels)==1: return [labels[0]]
    out=[]; head=labels[0]
    for n in range(1,len(labels)):
        for rest in combinations(labels[1:],n-1):
            left=(head,)+rest; right=tuple(x for x in labels if x not in left)
            for a in trees(left):
                for b in trees(right): out.append([a,b])
    return out

def subtree(F,v):
    vs=F.desc(v)
    return Graph(vs,{w:l for w,l in F.labels.items() if w in vs},{e:t for e,t in F.arcs.items() if t[0] in vs and t[1] in vs})

def blocks(F):
    return [F.labs(v) for v in F.vertices if F.parent(v) is None]

def run(limit=0):
    t0=time.perf_counter(); count={'tree_pairs':0,'active_pairs':0,'AF_cutsets':0,'anchor':0,'both_survive':0,'anchor_compound':0,'anchor_nonminimum':0,'minimum_fragments':0,'empty_repairs':0,'absent_parent_multicut':0,'ordinary_swapped_exchange':0}
    ts=trees(('a','b','c','d')); assert len(ts)==15
    cached={}
    def cache(F):
        key=F.signature()
        if key not in cached: cached[key]=yields(F)
        return cached[key]
    for t1 in ts:
      for t2 in ts:
        count['tree_pairs']+=1
        for detach1,detach2 in product([False,True],repeat=2):
          F1,F2=tree(t1),tree(t2)
          if detach1:F1=F1.cut(['e:n'])
          if detach2:F2=F2.cut(['e:n'])
          if not all(any(B<=A for A in blocks(F1)) for B in blocks(F2)):continue
          count['active_pairs']+=1; accepted=cache(F1)
          af=[E for E in subsets(F2.arcs) if F2.cut(E).signature() in accepted]
          mincost=min(map(len,af)); count['AF_cutsets']+=len(af)
          common=[]; pairs=[]
          for w in F1.vertices:
            if F1.parent(w) is None:continue
            lab=F1.labs(w)
            candidates=[v for v in F2.vertices if F2.labs(v)==lab and F2.parent(v) is not None]
            for v in candidates:
                if subtree(F1,w).signature()==subtree(F2,v).signature():common.append((w,v,lab))
          mapping={w:v for w,v,_ in common}
          for p in F1.vertices:
            ch=F1.children(p)
            if len(ch)==2 and all(w in mapping for _,w in ch):
              a,c=[mapping[w] for _,w in ch]
              if any({a,c}<=F2.desc(r) for r in F2.vertices if F2.parent(r) is None):pairs.append((a,c))
          for E in af:
            raw=F2.cut(E)
            for w,v,L in common:
              alive=raw.labs(v)
              if len(E)==mincost:
                assert alive,('minimum-empty',t1,t2,E,v)
                count['minimum_fragments']+=1
              if not alive:
                inside={e for e,(p,ch,_) in F2.arcs.items() if p in F2.desc(v)}
                I=E&inside; ep=F2.parent(v)[0]; repaired=(E-I)|{ep}
                assert len(I)>=2 and len(repaired)<len(E)
                assert F2.cut(repaired).signature() in accepted,('repair',t1,t2,E,v)
                count['empty_repairs']+=1
            for a,c in pairs:
              P,u=F2.path(a,c); D=E&P
              forbidden=P|{e for e,(p,ch,_) in F2.arcs.items() if p in F2.desc(a)|F2.desc(c)}
              E2=E-forbidden; G=reduce_graph(F2.cut(E2))
              if a not in G.vertices or c not in G.vertices:continue
              if G.parent(a) is None or G.parent(c) is None or G.parent(a)[1]!=G.parent(c)[1]:continue
              sa,sc=raw.labs(a),raw.labs(c); AC=F2.labs(a)|F2.labs(c)
              anchor=True
              if len(D)==1:
                e=next(iter(D)); child=F2.arcs[e][1]
                detached=a if a in F2.desc(child) else c
                ulabels=raw.component_labs(u)
                anchor=not((ulabels-AC) and raw.labs(detached)) or bool(ulabels&AC)
              if anchor:
                result=norm(F2,E,a,c)
                assert len(result)<=len(E)
                assert F2.cut(result).signature() in accepted,('N-anchor',t1,t2,E,a,c)
                count['anchor']+=1
                count['anchor_nonminimum']+=len(E)>mincost
                count['anchor_compound']+=len(AC)>2
                count['both_survive']+=bool(sa and sc)
                count['absent_parent_multicut']+=len(D)>=2 and F2.parent(u) is None
              if len(E)==mincost:
                pv={a,c}|{z for e in P for z in F2.arcs[e][:2]}
                B={e for e,(p,ch,_) in F2.arcs.items() if p in pv-{a,c} and ch not in pv}
                if len(B)==2 and E&B:
                  for v in [a,c]:
                    if F2.parent(v)[0] in E:
                      result=norm(F2,E|B,a,c)
                      assert B<=result and len(result)==len(E) and F2.cut(result).signature() in accepted
                      count['ordinary_swapped_exchange']+=1
        if limit and count['tree_pairs']>=limit:
          return {**count,'limited':True,'elapsed_seconds':time.perf_counter()-t0,'failures':[]}
    return {**count,'limited':False,'elapsed_seconds':time.perf_counter()-t0,'failures':[]}

def pendant_internals():
    t0=time.perf_counter(); cases=0; internal_cuts=0
    # Enough additional internal B edges to challenge cut/yield composition independently of AF.
    T=[[[[['a1','a2'],['b1','b1x']],['b2','b2x']],['c1','c2']],['x1','x2']]
    for mode in ['rho','rho_singleton','no_rho_component']:
      F=tree(T,rho=mode!='no_rho_component')
      if mode=='rho_singleton': F=F.cut(['e:n'])
      a,c,x=F.node(['a1','a2']),F.node(['c1','c2']),F.node(['x1','x2'])
      P,u=F.path(a,c); B={F.edge(['b1','b1x']),F.edge(['b2','b2x'])}
      internal={F.edge([s]) for s in ['b1','b1x','b2','b2x']}
      for R in subsets(F.arcs.keys()-B-P):
        transport(F,a,c,x,B|R); cases+=1; internal_cuts+=bool(R&internal)
    return {'cases':cases,'internal_pendant_cut_cases':internal_cuts,'elapsed_seconds':time.perf_counter()-t0,'failures':[]}

if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='pendants':d=pendant_internals(); name='pendant-internals'
    else:
      lim=int(sys.argv[1]) if len(sys.argv)>1 else 0
      d=run(lim); name='local-hunt'+('-pilot' if lim else '')
    print(json.dumps(d,sort_keys=True));write(name+'.json',d)
