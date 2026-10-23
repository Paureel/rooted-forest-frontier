#!/usr/bin/env python3
"""One-shot Case322 development controls. Consulted completed local.py/oracle.
No toolkit engine supplies rooted AF path claims; this wraps completed literal
original-cut materialization. Already contacted code/fixtures are DEVELOPMENT.
"""
from pathlib import Path
import importlib.util,json,hashlib,datetime,time,sys
D=Path(__file__).resolve().parent;R=D.parents[4]
spec=importlib.util.spec_from_file_location('completed_rule5_local',D.parent/'rule5_local/local.py')
L=importlib.util.module_from_spec(spec);spec.loader.exec_module(L)
def mirror(t):return t if L.leaf(t) else (mirror(t[1]),mirror(t[0]))
def split(F,X):return [C for B in F for C in ([x for x in B if x in X],[x for x in B if x not in X]) if C]
def fixtures():
 return {
 'i':(('t',(('a','b'),('p',('x',('q',('w','c')))))),((('a',('w',('t',('x',('p','q'))))),'c'),'b'),[2,1,2,2]),
 'ii':((((('x',('a','b')),'y'),'c'),'z'),((('a',('x',('y','z'))),'c'),'b'),[2,1,3]),
 'iii':(('p',('x',('q',(('a','b'),('w','c'))))),((('a',('w',('x',('p','q')))),'c'),'b'),[2,1,2])}
def run(corrupt=False):
 O=R/'results'/('algorithm-universal233-rule5-case322-controls-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
 rec=dict(status='RUNNING',independence='AUTHOR DEVELOPMENT; completed rule5 local + oracle contacted',fixtures={},controls={},pins={})
 for p in [D/'CONTROLS-PIN-v1.md',Path(__file__),D.parent/'rule5_local/local.py',R/'research/rmaf/oracle/oracle.py']:
  rec['pins'][str(p.relative_to(R))]=hashlib.sha256(p.read_bytes()).hexdigest()
 def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
 save()
 for name,(t,u,cost) in fixtures().items():
  for suffix,tt,uu in [('',t,u),('-mirror',mirror(t),mirror(u))]:
   k=name+suffix;C=L.classify(tt,uu);assert C['kind']=='322',(k,C)
   bs=L.branches(tt,uu,C);got=[b['paid'] for b in bs]
   want=[2,1,2] if corrupt and k=='ii' else cost
   if got!=want:raise AssertionError(('EXPECTED_LITERAL_COST',k,want,got))
   assert all(L.admitted(tt,uu).values())
   rec['fixtures'][k]=dict(target=tt,source=uu,classification=C,branches=bs,guards=L.admitted(tt,uu))
 t,u,_=fixtures()['i'];F=[['a'],['b','c','w'],['t'],['x'],['p'],['q']]
 assert L.O.validate(t,u,F)['valid'],'WRONG_SAVING_PLANT_NOT_AF'
 X=L.part(u,'a','b')[0];H=split(split(F,set(X)),{'c'})
 assert len(H)==len(F)+2 and ['a'] in F and ['b'] not in F
 rec['controls']['wrong_saving']=dict(F=F,valid=True,components=len(F),split_components=len(H),conditional_guard=False)
 malformed=((('a','b'),'c'),('w',('t',('x',('p','q')))))
 mg=L.admitted(malformed,u);assert not all(mg.values());rec['controls']['malformed_geometry']=mg
 rec['status']='PASS_PRECONSTRUCTION_DEVELOPMENT';save();print(rec['status'],len(rec['fixtures']),'literal fixtures;',O)
 return O
if __name__=='__main__':run('--corrupt' in sys.argv)
