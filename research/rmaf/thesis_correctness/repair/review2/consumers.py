#!/usr/bin/env python3
"""One-shot review2 exact five-label consumer check; local-hunt's four-leaf denominator was zero."""
from local_hunt import trees
from fresh_graph import *

def expand(t):
    if t=='ac':return ['a','c']
    return t if isinstance(t,str) else [expand(s) for s in t]

def run(limit=0):
    t0=time.perf_counter();pairs=0;ordinary=0;swapped=0;stages=0;first=None;counts={}
    for t1small in trees(('ac','b1','b2','x')):
      F1=tree(expand(t1small))
      for shape in [0,1,2]:
       U=[[['a','b1'],'b2'],'c'] if shape==0 else ([['a','b1'],['c','b2']] if shape==1 else ['a',[['c','b1'],'b2']])
       for detach in [False,True]:
        F2=tree([U,'x']);A=F1
        if detach:A=A.cut(['e:n']);F2=F2.cut(['e:n'])
        accepted=yields(A); optimum_=None; minima=[]
        for E in subsets(F2.arcs):
          if optimum_ is not None and len(E)>optimum_:break
          if F2.cut(E).signature() in accepted:
            optimum_=len(E);minima.append(E)
        pairs+=1
        a,c,x=[F2.node([s]) for s in ['a','c','x']];B={F2.edge(['b1']),F2.edge(['b2'])}
        P,u=F2.path(a,c);Q={F2.parent(x)[0],F2.parent(u)[0]}
        ac1=A.node(['a','c']); x1=A.node(['x'])
        uncle=A.parent(ac1) and A.parent(x1) and A.parent(ac1)[1]==A.parent(x1)[1]
        for E in minima:
          for label,v in [('ordinary_c',c),('swapped_a',a)]:
            if F2.parent(v)[0] in E and E&B:
              result=norm(F2,E|B,a,c)
              assert B<=result and len(result)==optimum_ and F2.cut(result).signature() in accepted
              if label=='ordinary_c':ordinary+=1
              else:swapped+=1
              if first is None:first={'t1':expand(t1small),'t2':[U,'x'],'detached_rho':detach,'cutset':sorted(E),'endpoint':label,'normalized':sorted(result),'optimum':optimum_,'edges':F2.manifest()}
          if uncle and len(E&P)>=1 and len(E&(P|Q|B))>=2:
            K=norm(F2,E|B,a,c);out=transport(F2,a,c,x,K);Kp=set(out['Kprime'])
            assert F2.cut(K).signature() in accepted and F2.cut(Kp).signature() in accepted and len(Kp)==optimum_
            p,s,q=len(E&B),len(E&P),len(E&Q);delta=len(K-(E|B));r=len(K&Q);eps=len(Kp-K)
            assert r==q+delta
            assert len(Kp)-len(E)==2-p-s+delta-r+eps<=0
            stages+=1;key=str([len(E),len(K),len(Kp)]);counts[key]=counts.get(key,0)+1
        if limit and pairs>=limit:return {'pairs':pairs,'ordinary_c':ordinary,'swapped_a':swapped,'two_stage_minimum_cases':stages,'two_stage_counts':counts,'first_exchange':first,'elapsed_seconds':time.perf_counter()-t0,'limited':True,'failures':[]}
    assert ordinary>0 and swapped>0 and stages>0
    return {'pairs':pairs,'ordinary_c':ordinary,'swapped_a':swapped,'two_stage_minimum_cases':stages,'two_stage_counts':counts,'first_exchange':first,'elapsed_seconds':time.perf_counter()-t0,'limited':False,'failures':[]}
if __name__=='__main__':
    lim=int(sys.argv[1]) if len(sys.argv)>1 else 0;d=run(lim)
    write('consumers'+('-pilot' if lim else '')+'.json',d);print(json.dumps(d,sort_keys=True))
