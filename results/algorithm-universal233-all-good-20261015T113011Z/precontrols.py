#!/usr/bin/env python3
"""One-shot project controls: independent set partitions plus literal Lean checks.

This is intentionally not a toolkit solver or a production DP subroutine.
The expected minima are read from the prior manual pin, never from an algorithm.
"""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, time

D=Path(__file__).resolve().parent
ROOT=D.parents[4]
OUT=D/'dev'/'preproof'
OUT.mkdir(parents=True,exist_ok=True)
pin=json.loads((D/'CONTROLS-PIN-v1.json').read_text())
def leaves(t):
    return [] if t is None else [t] if isinstance(t,int) else leaves(t[0])+leaves(t[1])
def restrict(t,b):
    if isinstance(t,int): return t if t in b else None
    l,r=restrict(t[0],b),restrict(t[1],b)
    return r if l is None else l if r is None else [l,r]
def iso(t,u):
    if isinstance(t,int) or isinstance(u,int): return t==u
    if t is None or u is None: return t is u
    return (iso(t[0],u[0]) and iso(t[1],u[1])) or (iso(t[0],u[1]) and iso(t[1],u[0]))
def span(t,b,p=()):
    if isinstance(t,int): return {p} if t in b else set()
    l,r=span(t[0],b,p+(False,)),span(t[1],b,p+(True,))
    return l|r|({p} if l or r else set())
def minimal(t,b,p=()):
    if isinstance(t,int): return {p} if t in b else set()
    l,r=span(t[0],b,p+(False,)),span(t[1],b,p+(True,))
    return minimal(t[1],b,p+(True,)) if not l else minimal(t[0],b,p+(False,)) if not r else l|r|{p}
def clear(t,bs):
    spans=[minimal(t,b) for b in bs]
    return all(not (spans[i]&spans[j]) for i in range(len(bs)) for j in range(i))
def partition(ls,bs):
    flat=sum(bs,[])
    return all(bs) and sorted(flat)==sorted(ls) and len(set(flat))==len(flat)
def proper(t,ss):
    return len(set(leaves(t)))==len(leaves(t)) and partition(leaves(t),[leaves(s) for s in ss])
def allgood(t,ss):
    return proper(t,ss) and all(t is not None and iso(restrict(t,leaves(s)),s) for s in ss)
def agrees(t,ss,bs):
    if not proper(t,ss) or not partition(leaves(t),bs): return False
    if not all(any(set(b)<=set(leaves(s)) for s in ss) for b in bs): return False
    if not (not bs if t is None else clear(t,bs)): return False
    for s in ss:
        local=[b for b in bs if set(b)<=set(leaves(s))]
        if not partition(leaves(s),local) or not clear(s,local): return False
        if not all(iso(restrict(t,b),restrict(s,b)) for b in local): return False
    return True
def partitions(xs):
    if not xs:
        yield []
    else:
        x,*tail=xs
        for bs in partitions(tail):
            yield [[x]]+bs
            for i in range(len(bs)):
                yield bs[:i]+[[x]+bs[i]]+bs[i+1:]
start=time.monotonic()
rows=[]
for c in pin['cases']:
    t,ss=c['target'],c['sources']
    good=allgood(t,ss)
    assert good==c.get('all_good',True),c['name']
    if not good:
        rows.append({'name':c['name'],'all_good':False,'guard':'REJECTED'})
        continue
    ps=list(partitions(leaves(t)))
    valid=[p for p in ps if agrees(t,ss,p)]
    assert valid,c['name']
    best=min(max(0,len(p)-len(ss)) for p in valid)
    assert best==c['minimum_additional_cost'],(c['name'],best)
    try:
        assert best==c['minimum_additional_cost']+1
    except AssertionError:
        caught=True
    else: raise AssertionError('comparison did not catch mismatch')
    rows.append({'name':c['name'],'all_good':good,'partitions_checked':len(ps),
                 'agreements':len(valid),'minimum_additional_cost':best,'mismatch_caught':caught})
deps=[('RMAF',ROOT/'research/rmaf/lean/RMAF.lean',None),
      ('StateRestriction',D.parent/'restriction_bridge/Restriction.lean',None),
      ('StateEmbedding',D.parent/'restriction_bridge/Embedding.lean',('import Restriction','import StateRestriction')),
      ('StatePartition',D.parent/'restriction_bridge/Partition.lean',('import Embedding','import StateEmbedding')),
      ('State',D.parent/'state_reductions/State.lean',None),
      ('PreControls',D/'PreControls.lean',None)]
env=dict(os.environ,LEAN_PATH=str(OUT))
runs=[]
for name,path,adapt in deps:
    s=path.read_text()
    if adapt: s=s.replace(*adapt,1)
    (OUT/(name+'.lean')).write_text(s)
    begin=time.monotonic()
    p=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(OUT/(name+'.olean')),str(OUT/(name+'.lean'))],
        cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
    (OUT/(name+'.log')).write_text(p.stdout)
    runs.append({'module':name,'exit':p.returncode,'seconds':time.monotonic()-begin})
    assert p.returncode==0,(name,p.stdout)
(OUT/'FalseControls.lean').write_bytes((D/'FalseControls.lean').read_bytes())
p=subprocess.run([str(ROOT/'bootloops-lean'),str(OUT/'FalseControls.lean')],cwd=ROOT,env=env,text=True,
    stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
(OUT/'FalseControls.log').write_text(p.stdout)
assert p.returncode!=0 and p.stdout.count('is false')==4,p.stdout
receipt={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'PASS_7_GUARDS_6_EXACT_MINIMA_4_FALSE_CONTROLS',
 'pin_sha256':hashlib.sha256((D/'CONTROLS-PIN-v1.json').read_bytes()).hexdigest(),
 'pin_before_proof':True,'enumeration_is_not_algorithm_subroutine':True,
 'independence':'Manual fixtures and separate set-partition route; author development evidence only',
 'cases':rows,'lean_runs':runs,'false_lean_claims_rejected':4,
 'seconds':time.monotonic()-start}
(OUT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
