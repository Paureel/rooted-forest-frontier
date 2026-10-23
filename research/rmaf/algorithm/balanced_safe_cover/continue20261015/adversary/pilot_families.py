#!/usr/bin/env python3
"""One-shot fixed small pilots, run only after independent_cb1 controls pass."""
import time,json,hashlib
from pathlib import Path
import independent_cb1 as X
OUT=Path('results/algorithm-balanced-cover-continue-adversary-pilots-v1.json')
def cat(L):
    if len(L)==1:return L[0]
    return [L[0],cat(L[1:])]
def rename(Q,prefix):
    if isinstance(Q,str):return prefix+Q
    return [rename(q,prefix) for q in Q]
def mixed(Q):
    if isinstance(Q,str):return ['a'+Q,'b'+Q]
    return [mixed(q) for q in Q]
def record(id,Sraw,Traw,b,oracle):
    t0=time.perf_counter();S,T=X.Tree(Sraw),X.Tree(Traw);H=X.conflicts(S,T);F=X.factors(H);R=X.quotient(H)
    Z=X.solve(H,b);assert Z['success'];K=X.certificate(S,T,Z['cuts']);assert X.check_cert(S,T,K)
    if oracle:
        v,_=X.partition_opt(S,T);assert v==Z['cost']
    else:v=None
    row={'id':id,'source':Sraw,'target':Traw,'budget':b,'partition_optimum':v,'cost':Z['cost'],'minimal_rows':len(H),'factor_count':len(F),'factor_sizes':[len(f) for f in F],'initial_min_rank':min((h.bit_count() for h in R),default=0),'initial_max_rank':max((h.bit_count() for h in R),default=0),'execution':Z,'certificate':K,'seconds':time.perf_counter()-t0}
    return row
A=[]
for m in range(2,8):
    Q=cat([str(i) for i in range(1,m+1)]);r=record('matched-cat-'+str(m),[rename(Q,'a'),rename(Q,'b')],mixed(Q),m,m<=4);A.append(r);OUT.write_text(json.dumps(A,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['id','cost','factor_count','initial_min_rank','seconds']}|{k:r['execution'][k] for k in ['nodes','max_rank']}),flush=True)
    if r['seconds']>10:break
for n in range(3,11):
    L=[str(i) for i in range(n)];r=record('reverse-cat-'+str(n),cat(L),cat(L[::-1]),n-1,n<=7);A.append(r);OUT.write_text(json.dumps(A,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['id','cost','factor_count','initial_min_rank','seconds']}|{k:r['execution'][k] for k in ['nodes','max_rank']}),flush=True)
    if r['seconds']>10:break
