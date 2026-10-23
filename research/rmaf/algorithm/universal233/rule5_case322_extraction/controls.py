#!/usr/bin/env python3
"""One-shot extraction controls wrapping the completed literal instrument.
Consulted frozen Case322 v1 and its Rule5 local/oracle inputs; no independent
credit. New capability is source-orientation/role and actual core-rung controls.
"""
from pathlib import Path
import importlib.util,json,hashlib,datetime,time,sys
D=Path(__file__).resolve().parent;R=D.parents[4]
sp=importlib.util.spec_from_file_location('old_case322_controls',D.parent/'rule5_case322/controls.py');A=importlib.util.module_from_spec(sp);sp.loader.exec_module(A);L=A.L

def oriented(a,b,bit):return (b,a) if bit else (a,b)
def source(a,b,c,X,S,bits):
 t=oriented(oriented(oriented(a,X,bits&1),c,bits&2),b,bits&4)
 for x in S:t=(t,x)
 return t

def run(corrupt=False):
 O=R/'results'/('algorithm-universal233-rule5-case322-extraction-controls-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
 t0=time.monotonic();rec=dict(status='RUNNING',controls={},rows={},independence='AUTHOR DEVELOPMENT',pins={})
 for p in [D/'CONTROLS-PIN-v1.md',Path(__file__),D.parent/'rule5_case322/RULE5-CASE322-MANIFEST-v1.json']:
  rec['pins'][str(p.relative_to(R))]=hashlib.sha256(p.read_bytes()).hexdigest()
 def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
 save()
 for name,(t,u,costs) in A.fixtures().items():
  X=L.index(u)['001']
  for bits in range(8):
   uu=source('a','b','c',X,[],bits)
   for mir,tt in [(False,t),(True,A.mirror(t))]:
    got=L.classify(tt,uu);assert got['kind']=='322',(name,bits,mir,got)
    bs=L.branches(tt,uu,got);assert [b['paid'] for b in bs]==costs
    for branch in bs:
     current=uu if branch['role']=='source' else tt
     swapped_role='target' if branch['role']=='source' else 'source'
     swapped_current=tt if swapped_role=='source' else uu
     assert current==swapped_current
     assert L.cut_partition(swapped_current,branch['cuts'])==branch['partition']
    rec['rows'][name+'-'+str(bits)+'-'+str(mir)]=dict(guards=L.admitted(tt,uu),costs=[b['paid'] for b in bs],source=uu,target=tt)
 t=(((('x',(('a','b'),'s')),'y'),'c'),'z');u=(((('a',('x',('y','z'))),'c'),'b'),'s')
 got=L.classify(t,u);assert got['kind']=='322',got
 bs=L.branches(t,u,got);costs=[b['paid'] for b in bs];want=[2,1,2] if corrupt else [2,1,4]
 assert costs==want,('EXPECTED_LITERAL_CORE_COST',want,costs)
 X=set(got['P'][got['j']]);s_arc=L.singleton_arc(t,'s');assert s_arc in bs[2]['cuts'] and 's' not in X
 rec['controls']['core_rung']=dict(target=t,source=u,classification=got,branches=bs,costs=costs,s_arc=s_arc,v1_all_bside_X=False)
 rec['status']='PASS_PRECONSTRUCTION_DEVELOPMENT';rec['seconds']=time.monotonic()-t0;save();print(rec['status'],len(rec['rows']),'orientation/role rows; core costs',costs,'seconds',rec['seconds']);print(O)
if __name__=='__main__':run('--corrupt' in sys.argv)
