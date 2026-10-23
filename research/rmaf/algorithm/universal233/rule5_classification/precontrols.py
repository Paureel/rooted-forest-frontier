#!/usr/bin/env python3
"""One-shot classification controls wrapping the completed original evaluator.

BootLoops index/guides and frozen Rule5 v1 source instruments were consulted.
No existing instrument proves this classification; reuse the actual graph
instrument for controls rather than copy or modify the frozen source.
"""
from pathlib import Path
import importlib.util,json,hashlib,datetime,sys
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;R=D.parents[4]
V=D.parent/'rule5_local';m=json.loads((V/'RULE5-LOCAL-MANIFEST-v1.json').read_text())
for e in m['immutable_files']:assert hashlib.sha256((R/e['path']).read_bytes()).hexdigest()==e['sha256']
spec=importlib.util.spec_from_file_location('rule5_frozen_local',V/'local.py')
L=importlib.util.module_from_spec(spec);spec.loader.exec_module(L)

def attachment(T,X,Y,Z,p,q):
 E=L.cuts(T,p,q);I=L.index(T);sets=[set(L.labels(I[e])) for e in E]
 core=set(L.labels(T))-set().union(*sets)
 return len(E)==2 and ((sets==[set(Y),set(Z)]) or (sets==[set(Z),set(Y)])) and core==set(X)
def mirror(T):return T if L.leaf(T) else tuple(mirror(v) for v in T[::-1])
def run(corrupt=False):
 rows=[]
 for name in ['large','two','outside']:
  T,S,_=L.fixture_family()[name];C=L.classify(T,S);P=C['P']
  if name=='outside':j=2;p,q=C['second_cherry']
  else:j=C['j'];p,q='p','q'
  X=P[j];Y,Z=[P[i] for i in range(3) if i!=j]
  result=attachment(T,X,Y,Z,p,q)
  want=not (corrupt and name=='large')
  assert result==want,('ATTACHMENT_COMPARATOR',name,result,want)
  assert all(L.admitted(T,S).values())
  assert attachment(mirror(T),X,Y,Z,p,q)
  rows.append(dict(name=name,X=X,Y=Y,Z=Z,cuts=L.cuts(T,p,q),target=T,source=S,p=p,q=q))
 T=((('p','y'),('q','z')),'w');X=['p','q','w'];Y=['y'];Z=['z']
 assert attachment(T,X,Y,Z,'p','q') and attachment(mirror(T),X,Y,Z,'p','q')
 assert all(e for e in L.cuts(T,'p','q')) and len(L.cuts(T,'p','q'))==2
 badT=('p',('y',('q','z')));badX={'p','q','y'}
 assert any(badX&set(L.labels(L.index(badT)[e])) for e in L.cuts(badT,'p','q'))
 assert not L.disjoint(T,[['p','q'],['y','z'],['w']])
 assert not attachment(T,['p','q'],['y','z'],['w'],'p','q')
 PX=(('p','q'),('r','s'));PT=(('p',('q','y')),('r',('s','z')));PS=(PX,('y','z'))
 assert L.agrees(PT,PS,['p','q','r','s']) and L.disjoint(PT,[['p','q','r','s'],['y'],['z']])
 assert len(L.cherries(PX))==2 and len(L.cuts(PT,'p','q'))==1 and len(L.cuts(PT,'r','s'))==1
 assert not L.earlier(PS,PT)
 return dict(status='PASS_CLASSIFICATION_PREPROOF_DEVELOPMENT',positive_attachment_fixtures=rows,
  root_positive=dict(T=T,X=X,Y=Y,Z=Z,cuts=L.cuts(T,'p','q')),
  negative_controls=['missing_pruned_cherry','outside_overlap','missing_no_t1','unpaid_root_count'],
  root_control_count=len(L.cuts(T,'p','q')),old_manifest_sha256=hashlib.sha256((V/'RULE5-LOCAL-MANIFEST-v1.json').read_bytes()).hexdigest())

if __name__=='__main__':
 O=R/'results'/('algorithm-universal233-rule5-classification-pre-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir()
 result=run();caught=False
 try:run(True)
 except AssertionError as e:
  assert 'ATTACHMENT_COMPARATOR' in str(e);caught=True;(O/'corruption.log').write_text(str(e)+'\n')
 assert caught
 result['corruption_caught']=True
 result['input_pins']={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),D/'TARGET-v1.md',D/'CONTROLS-PIN-v1.md']}
 (O/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
 (D/'PREPROOF-RECEIPT-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),sha256=hashlib.sha256((O/'certificate.json').read_bytes()).hexdigest()),indent=2)+'\n')
 print(result['status'],O)
