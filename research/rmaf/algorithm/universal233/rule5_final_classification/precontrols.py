#!/usr/bin/env python3
"""Pinned finite original-graph controls; reused evaluator is DEVELOPMENT."""
from pathlib import Path
import sys,importlib.util,json,hashlib,time,datetime
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent; R=D.parents[4]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def tuplefy(t): return t if isinstance(t,str) else tuple(tuplefy(x) for x in t)
pins={};mode_observations=[]
for dr,mn in [('rule5_local','RULE5-LOCAL-MANIFEST-v1.json'),('rule5_classification','CLASSIFICATION-MANIFEST-v1.json')]:
 p=D.parent/dr/mn; m=json.loads(p.read_text());pins[str(p.relative_to(R))]=sha(p)
 for e in m['immutable_files']:
  f=R/e['path']; assert sha(f)==e['sha256'],f
  if f.stat().st_mode & 0o222:mode_observations.append(str(f.relative_to(R)))
spec=importlib.util.spec_from_file_location('frozen_rule5_local',D.parent/'rule5_local/local.py')
L=importlib.util.module_from_spec(spec);spec.loader.exec_module(L)
def flip(t,p):
 if not p:return t[::-1]
 d=int(p[0]);z=list(t);z[d]=flip(z[d],p[1:]);return tuple(z)
def mirror(t):return t if L.leaf(t) else tuple(mirror(v) for v in t[::-1])
def rename(t):return {'a':'b','b':'a'}.get(t,t) if L.leaf(t) else tuple(rename(x) for x in t)
def fork(t,a,b):return t==(a,b) or t==(b,a)
def geometry(t,s):
 g=L.admitted(t,s); assert all(g.values()),('ADMITTED_FAILURE',t,s,g)
 P=L.part(s,'a','b');good=[L.agrees(t,s,B) for B in P]
 assert not any(good[i] and len(P[i])>=2 for i in [0,1]),('NOT_REMAINING',P,good)
 j=next(i for i in [0,1] if not good[i]); assert len(P[1-j])==1 and good[2]
 X=P[j];c=P[1-j][0]; C=P[2]
 assert all({'a','b'} & {p,q} for _,p,q in L.cherries(L.O.restriction(s,frozenset(C))))
 e=L.cuts(s,'a','b')[j];U=L.index(s)[e];spines=[]
 for p,V in L.vertices(s):
  for a,b in [('a','b'),('b','a')]:
   for ax in [(a,U),(U,a)]:
    for ac in [(ax,c),(c,ax)]:
     if fork(V,ac,b):
      anc=[];ok=True
      for k,d in enumerate(p):
       q=p[:k]+str(1-int(d));W=L.index(s)[q]
       if not L.leaf(W):ok=False
       anc.append(dict(arc=q,label=W))
      if ok:spines.append(dict(base=p,near_endpoint=a,far_endpoint=b,ancestor_siblings=anc))
 assert spines,('SOURCE_SPINE_FAILURE',t,s,P,e)
 V=L.span(t,set(X));arcs=[]
 for q in L.incident(t,X):
  desc=set(L.labels(L.index(t)[q]));out=q[:-1] in V
  arcs.append(dict(arc=q,direction='outgoing' if out else 'incoming',outside=sorted(desc if out else set(L.labels(t))-desc)))
 assert len(arcs) in [1,2],('INCIDENT_FAILURE',t,s,arcs)
 if len(arcs)==1:panel='common';witness=L.split_witness(t,s,X)
 else:
  witness=None;roles=[]
  for z in arcs:
   z['role']='c' if set(z['outside'])=={c} else 'C' if set(z['outside'])==set(C) else 'BAD'
   roles.append((z['direction'],z['role']))
  assert sorted(z['role'] for z in arcs)==['C','c'],('ATTACHMENT_FAILURE',t,s,arcs)
  if ('outgoing','c') in roles and ('outgoing','C') in roles:panel='322'
  elif ('outgoing','c') in roles:panel='321'
  else:
   panel='323';assert not L.leaf(t) and c in t,('ROOT_C_FAILURE',t,c,arcs)
 return dict(target=t,source=s,guards=g,P=P,good=good,bad_source_arc=e,spines=spines,incident=arcs,panel=panel,witness=witness)
def run():
 root=R/'results/algorithm-universal233-rule5-local-root-control-20261015T125808Z/certificate.json'
 raw=json.loads(root.read_text())
 # The root fixture is retained by its exact original certificate fields.
 rt=tuplefy(raw['target']);rs=tuplefy(raw['source'])
 base=[(n,*L.fixture_family()[n][:2]) for n in ['six','first','third','common']]+[('root',rt,rs)]
 start=time.monotonic();pilot=[geometry(t,s) for _,t,s in base[:4]];pt=time.monotonic()-start
 assert pt<1,('PILOT_TOO_SLOW',pt)
 rows=[]
 for n,t,s in base:
  variants=[('original',t,s),('mirror',mirror(t),mirror(s)),('ab_swap',rename(t),rename(s))]
  variants += [('target_flip_'+p,flip(t,p),s) for p,u in L.vertices(t) if not L.leaf(u)]
  variants += [('source_flip_'+p,t,flip(s,p)) for p,u in L.vertices(s) if not L.leaf(u)]
  for v,T,S in variants:
   assert len(rows)<128 and time.monotonic()-start<30,('TIMING_LIMIT',len(rows))
   z=geometry(T,S);z.update(fixture=n,variant=v);rows.append(z)
 V,W=L.fixture_family()['common'][0][0],L.fixture_family()['common'][1][0][0][1]
 T=(('a','b'),('c',V));S=(('a','c'),('b',W));g=L.admitted(T,S)
 assert g['proper'] and g['cherry'] and g['earlier_both'] and g['hard2'] and g['target_disjoint'] and g['source_disjoint'] and g['exactly_two_good'] and not g['no_rule4_both'],g
 T=(('x',('a','b')),('y',('s',('z','c'))));S=(((('a',(('x','y'),'z')),'c'),'b'),'s')
 cg=L.admitted(T,S);ix=L.incident(T,['x','y','z'])
 assert len(ix)==3 and not cg['target_disjoint']
 caught=False
 try:
  assert pilot[0]['panel']=='321','PANEL_COMPARATOR'
 except AssertionError as e:
  assert str(e)=='PANEL_COMPARATOR';caught=True
 assert caught and all(z['arc'] for x in rows for z in x['incident'])
 return dict(status='PASS_FINITE_DEVELOPMENT_CONTROLS',pilot_seconds=pt,seconds=time.monotonic()-start,rows=rows,
  missing_noRule4=dict(target=(('a','b'),('c',V)),source=(('a','c'),('b',W)),guards=g),
  missing_clearance=dict(target=T,source=S,guards=cg,incident=ix),wrong_panel_caught=caught,old_manifest_pins=pins,
  old_writable_mode_observations=mode_observations)
if __name__=='__main__':
 out=R/'results'/('algorithm-universal233-rule5-final-classification-pre-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));out.mkdir()
 try:r=run()
 except Exception as e:
  (out/'failure.txt').write_text(repr(e)+'\n');raise
 r['input_pins']={str(p.relative_to(R)):sha(p) for p in [Path(__file__),D/'TARGET-v1.md',D/'CONTROLS-PIN-v1.md']}
 (out/'certificate.json').write_text(json.dumps(r,indent=2)+'\n')
 (D/'PREPROOF-RECEIPT-v1.json').write_text(json.dumps(dict(receipt=str(out.relative_to(R)),sha256=sha(out/'certificate.json')),indent=2)+'\n')
 print(r['status'],len(r['rows']),out)
