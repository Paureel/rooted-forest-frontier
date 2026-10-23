#!/usr/bin/env python3
"""Bounded original Case1 development controls, not a large census."""
from pathlib import Path
import sys,importlib.util,json,datetime,time,itertools,hashlib
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;R=D.parents[4];V=D.parent/'rule5_local'
s=importlib.util.spec_from_file_location('frozen_rule5',V/'local.py');L=importlib.util.module_from_spec(s);s.loader.exec_module(L)
T,S,_=L.fixture_family()['large'];case=L.classify(T,S);X=set(case['P'][case['j']]);outside=set(L.labels(S))-X
assert all(L.admitted(T,S).values()) and len(X)==3
start=time.monotonic();rows=[]
for x,y in itertools.product(sorted(X),sorted(outside)):
 F=[[x,y]]+[[z] for z in L.labels(S) if z not in {x,y}]
 assert L.O.validate(T,S,F)['valid']
 assert not all(any(set(B)<=set(C) for C in case['P']) for B in F)
 G=[sorted(X)]+[[z] for z in L.labels(S) if z not in X]
 assert L.O.validate(T,S,G)['valid'] and len(G)<=len(F)
 assert all(any(set(B)<=set(C) for C in case['P']) for B in G)
 rows.append(dict(F=F,G=G,source_cuts=L.cuts(S,'a','b')))
# A source-pendant X does not alone justify the mixed-block exclusion.
bad=((('p','q'),'r'),'z');B=['p','q','z'];F=[B,['r']]
assert L.O.validate(bad,bad,F)['valid'] and len(set(B)&{'p','q','r'})==2
assert not L.earlier(bad,bad)
O=R/'results'/('algorithm-universal233-rule5-classification-large-controls-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir()
rec=dict(status='PASS_BOUNDED_CASE1_DEVELOPMENT_CONTROLS',target=T,source=S,X=sorted(X),
 rows=rows,control_count=len(rows),false_missing_attachment=dict(T=bad,S=bad,F=F),
 seconds=time.monotonic()-start,provenance='Frozen original evaluator reused DEVELOPMENT only; no exhaustive large census',
 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],len(rows),round(rec['seconds'],3),str(O.relative_to(R)))
