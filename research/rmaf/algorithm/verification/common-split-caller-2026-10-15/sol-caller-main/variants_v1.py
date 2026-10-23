#!/usr/bin/env python3
"""Five already-pinned construction variants; same own graph lineage, no new replication."""
import copy,json,time
from pathlib import Path
import scoped_graph_v1 as s
P=Path(__file__).resolve().parent; base=s.E['cases'][0]
def mirror(t): return t if isinstance(t,int) else [mirror(t[1]),mirror(t[0])]
def maplabels(x,m): return m.get(x,x) if isinstance(x,int) else [maplabels(a,m) for a in x]
def addr_flip(p): return ''.join('1' if c=='0' else '0' for c in p)
variants=[]
v=copy.deepcopy(base); v['id']='root-child-swap-T'; v['T']=[v['T'][1],v['T'][0]]; v['cutT']='0'; v['trees']['TMX']=[10,0]; v['trees']['TMY']=[[[1,2],3],11]; v['hulls']['T']=[['' if not p else ('1' if p[0]=='0' else '0')+p[1:] for p in h] for h in v['hulls']['T']]; variants.append(v)
v=copy.deepcopy(base); v['id']='opposite-cut-sides'; v['cutS']='0'; variants.append(v)
v=copy.deepcopy(base); v['id']='reverse-roles-refusal'; v['X'],v['Y']=v['Y'],v['X']; v['repX'],v['repY']=v['repY'],v['repX']; old=copy.deepcopy(v['trees']); v['trees']={'TX':old['TY'],'SX':old['SY'],'TY':old['TX'],'SY':old['SX'],'TMX':maplabels(old['TMY'],{11:10}),'SMX':maplabels(old['SMY'],{11:10}),'TMY':maplabels(old['TMX'],{10:11}),'SMY':maplabels(old['SMX'],{10:11})}; fs=copy.deepcopy(v['minimum_families']); v['minimum_families']={'X':fs['Y'],'Y':fs['X'],'MX':maplabels(fs['MY'],{11:10}),'MY':maplabels(fs['MX'],{10:11}),'global':fs['global']}; v['costs']={'X':1,'Y':0,'MX':1,'MY':0,'global':1}; v['guard']='REFUSAL'; v.pop('marked_outside_depth01'); v['answers']={k:'REFUSAL' for k in v['answers']}; variants.append(v)
v=copy.deepcopy(base); v['id']='arbitrary-Nat'; m={0:17,1:101,2:5,3:999,10:10000,11:10001}
for k in ['T','S','X','Y','repX','repY','rho','gamma']: v[k]=maplabels(v[k],m)
v['trees']={k:maplabels(t,m) for k,t in v['trees'].items()}; v['minimum_families']={k:maplabels(Fs,m) for k,Fs in v['minimum_families'].items()}; v['hulls']['forest']=maplabels(v['hulls']['forest'],m); variants.append(v)
v=copy.deepcopy(base); v['id']='all-child-swaps'; v['T']=mirror(v['T']); v['S']=mirror(v['S']); v['cutT']=v['cutS']='0'; v['trees']={k:mirror(t) for k,t in v['trees'].items()}
for k in ['T','S']: v['hulls'][k]=[[addr_flip(p) for p in H] for H in v['hulls'][k]]
variants.append(v)
at=time.perf_counter(); out=[s.check_case(v) for v in variants]; (P/'graph-variants-run1.json').write_text(json.dumps({'variants':out,'count':len(out),'seconds':time.perf_counter()-at,'candidate_contact':False,'replication_credit':0},indent=2)+'\n'); print(json.dumps({'variants':len(out),'seconds':time.perf_counter()-at}))
