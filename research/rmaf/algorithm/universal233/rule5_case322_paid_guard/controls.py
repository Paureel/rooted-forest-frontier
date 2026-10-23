#!/usr/bin/env python3
"""Paid-guard controls; completed author instruments, no independent credit."""
from pathlib import Path
import importlib.util,json,hashlib,datetime,time,sys
D=Path(__file__).resolve().parent;R=D.parents[4]
sp=importlib.util.spec_from_file_location('completed_extraction_controls',D.parent/'rule5_case322_extraction/controls.py')
A=importlib.util.module_from_spec(sp);sp.loader.exec_module(A);L=A.L
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(corrupt=False):
 O=R/'results'/('algorithm-universal233-rule5-case322-paid-guard-controls-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
 rec=dict(status='RUNNING',rows=[],controls={},input_pins={},independence='AUTHOR DEVELOPMENT');start=time.monotonic()
 def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
 for name,h in [('rule5_case322/RULE5-CASE322-MANIFEST-v1.json','2d5f9c672e7d2a2dc23e7a7c5434200ccd46bcb053188ff51c4954623d164763'),('rule5_case322_extraction/RULE5-CASE322-EXTRACTION-MANIFEST-v1.json','d99afd406d82e857f4d5035d9ee7a052883c0732769960709a99f171f73029b4')]:
  p=D.parent/name;assert sha(p)==h
  for e in json.loads(p.read_text())['immutable_files']:assert sha(R/e['path'])==e['sha256'],e['path']
  rec['input_pins'][str(p.relative_to(R))]=h
 for p in [D/'TARGET-v1.md',D/'CONTROLS-PIN-v1.md',Path(__file__)]:rec['input_pins'][str(p.relative_to(R))]=sha(p)
 save()
 fixtures=A.A.fixtures();fixtures['core']=((((('x',(('a','b'),'s')),'y'),'c'),'z'),(((('a',('x',('y','z'))),'c'),'b'),'s'),[2,1,4])
 for name,(t,u,want) in fixtures.items():
  X=L.index(u)['0001'] if name=='core' else L.index(u)['001']
  for bits in range(8):
   ss=A.source('a','b','c',X,['s'] if name=='core' else [],bits)
   for mirrored,tt in [(False,t),(True,A.A.mirror(t))]:
    cls=L.classify(tt,ss);assert cls['kind']=='322',cls
    bs=L.branches(tt,ss,cls);got=[z['paid'] for z in bs]
    expected=[2,1,2] if corrupt and name=='core' else want
    assert got==expected,('CORRUPT_COST_EXPECTATION',name,expected,got)
    hull=L.span(tt,set(L.labels(X)));edges=L.incident(tt,L.labels(X));I=L.index(tt)
    core=set(L.labels(tt))-set(L.labels(X))-{'c'}
    assert len(edges)==2 and all(e[:-1] in hull and e not in hull for e in edges)
    assert sorted([set(L.labels(I[e]))==core for e in edges])==[False,True]
    assert any(L.labels(I[e])==['c'] for e in edges)
    for z in bs:
     current=ss if z['role']=='source' else tt
     assert z['partition']==L.cut_partition(current,z['cuts'])
     assert len(z['partition'])==len(z['cuts'])+1
    rec['rows'].append(dict(family=name,bits=bits,mirror=mirrored,costs=got,exact_outgoing=True))
 t=(('a','b'),('c',('x',('y','z'))));s=((('a',('y',('x','z'))),'c'),'b');X=['x','y','z']
 edges=L.incident(t,X);V=L.span(t,set(X));assert len(edges)==1
 b=L.singleton_arc(t,'b');c=L.singleton_arc(t,'c');top=min(L.span(t,{'b','c'}),key=len);assert top==''
 assert len(L.path_outgoing(t,'b','c','c'))<2
 assert not [q for q in L.path_outgoing(t,'b','c','b') if L.index(t)[q]!='a']
 try:L.cut_partition(t,[L.singleton_arc(t,'a'),top])
 except AssertionError:rec['controls']['weaker_root']='REJECTED_OUTSIDE_EXACT_FRONTIER'
 else:raise AssertionError('ROOT_PLANT_SURVIVED')
 t,s,_=A.A.fixtures()['i'];qb=L.singleton_arc(s,'b');qc=L.singleton_arc(s,'c')
 assert L.cut_partition(s,[qb])!=L.cut_partition(s,[qc]);rec['controls']['wrong_terminal_binding']='CAUGHT'
 rec['seconds']=time.monotonic()-start;assert rec['seconds']<30
 rec['status']='PASS_PRECONSTRUCTION_DEVELOPMENT';save();print(rec['status'],len(rec['rows']),rec['seconds'],O)
if __name__=='__main__':run('--corrupt' in sys.argv)
