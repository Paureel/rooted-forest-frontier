"""One-shot G controls; reuses the dedicated completed X0 checker as DEVELOPMENT.
No profile author/referee X0 import and no production optimum oracle.
"""
from pathlib import Path
import sys,hashlib,json,time
from itertools import combinations
ROOT=Path(__file__).resolve().parents[5];BASE=Path(__file__).resolve().parent
OUT=ROOT/'research/rmaf/results/algorithm-pair-case-geometry-controls-v1.json'
if OUT.exists():raise FileExistsError(OUT)
freeze={}
for name in ('PRE-CONSTRUCTION-FREEZE.sha256','PRE-RUN-CODE-FREEZE.sha256'):
 for line in (BASE.parent/'x0'/name).read_text().splitlines():
  expected,path=line.split(None,1);p=ROOT/path.strip();actual=hashlib.sha256(p.read_bytes()).hexdigest()
  assert actual==expected,(path,'frozen dependency changed');freeze[path]=actual
sys.path.insert(0,str(BASE.parent/'x0'));import engine as X
start=time.perf_counter()
def clean(x):
 if isinstance(x,dict):return {str(k):clean(v) for k,v in x.items()}
 if isinstance(x,(tuple,list)):return [clean(v) for v in x]
 if isinstance(x,(set,frozenset)):return sorted([clean(v) for v in x],key=str)
 return x
def cut_blocks(g,cuts):
 adj={v:set() for v in g.ch};cuts=set(map(tuple,cuts))
 for u,v in g.original_edges:
  if (u,v) not in cuts:adj[u].add(v);adj[v].add(u)
 todo=set(adj);out=[];empty=[]
 while todo:
  found={min(todo)};pending=list(found)
  while pending:
   u=pending.pop()
   for v in adj[u]-found:found.add(v);pending.append(v)
  todo-=found;labs=frozenset().union(*(g.group.get(v,frozenset()) for v in found))
  if labs:out.append(tuple(sorted(labs)))
  else:empty.append(found)
 return tuple(sorted(out)),empty
# Plants before T1 case evaluation.
ident=X.original(((0,1),2));wrong=X.original((0,(1,2)))
assert X.partition_af(ident,ident,((0,1,2),))
assert not X.partition_af(ident,wrong,((0,1,2),))
q=X.original(((0,1),(2,3)))
assert not X.partition_af(q,q,((0,2),(1,3)))
assert len(tuple(X.partitions({0,1,2})))==5
cross=X.original(((3,5),(4,6)));colors=[{3,4},{5,6}]
one=[]
for e in cross.original_edges:
 p,empty=cut_blocks(cross,[e]);pure=not empty and all(any(set(b)<=c for c in colors) for b in p)
 one.append({'edge':e,'partition':p,'pure':pure})
assert len(one)==6 and not any(x['pure'] for x in one)
two=[]
for cuts in combinations(cross.original_edges,2):
 p,empty=cut_blocks(cross,cuts)
 if not empty and all(any(set(b)<=c for c in colors) for b in p):two.append({'cuts':cuts,'partition':p})
assert two
T=(((1,(3,4)),(2,(5,6))),7);S=(((1,2),((3,5),(4,6))),7);A=[1,2];B=[3,4,5,6];P=((1,2),(3,4,5,6),(7,))
rows=[]
for name,t,a,b,expected in [('T1',T,A,B,'mutually_clear_original_edge'),('root',T[0],A,B,'mutually_clear_original_edge'),('three',((0,3),(1,(2,4))),[0,1,2],[3,4],'three_occupied_regions')]:
 g=X.G(t,a,b);assert g['G']=='FINITE-NOFIRE' and g['choice']['kind']==expected
 assert g['region_degree_correspondence'];rows.append({'name':name,'geometry':g})
assert rows[0]['geometry']['shared_vertices']==['0','00','01']
assert [x['original_address_edge'] for x in rows[0]['geometry']['shared_edges']]==[('0','00'),('0','01')]
for a,b,expected in [([],B,'REFUSED'),([1,99],B,'REFUSED'),([1,1,2],B,'REFUSED'),([1],B,'OUTSIDE_DISJOINT')]:
 assert X.G(T,a,b)['G']==expected
s,t=X.original(S),X.original(T);parts=tuple(X.partitions({1,2,3,4,5,6,7}));ref=[F for F in parts if X.refines(F,P)];valid=[F for F in ref if X.partition_af(t,s,F)]
assert len(parts)==877 and len(ref)==30 and len(valid)==10
m=min(map(len,valid));ma=min(len(F) for F in valid if tuple(A) in F);assert m==ma==5
assert m!=4 # deliberate corrupted optimum rejected
F=((1,),(2,),(3,5),(4,),(6,),(7,));Fp=((1,2),(3,),(5,),(4,),(6,),(7,))
assert X.partition_af(t,s,F) and X.partition_af(t,s,Fp)
result={'scope':'DEVELOPMENT replay of fixed G/T1 controls using dedicated completed X0 dependency lineage; no new independence or universal E claim','frozen_input_dependency_code_hashes':freeze,'controls':{'identical':True,'wrong_rooted_topology_caught':True,'false_forest_validity_caught':True,'false_optimum_caught':True,'whole_original_B_one_cut_false_caught':True},'one_cut_B_trials':one,'two_cut_B_witness':two[0],'rows':rows,'T1':{'all_partitions':877,'under_P':30,'valid_under_P':valid,'minimum_under_P':m,'minimum_under_P_with_A_retained':ma,'literal_F':F,'literal_Fprime':Fp},'seconds':time.perf_counter()-start,'wrapper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
OUT.write_text(json.dumps(clean(result),indent=2)+'\n');print(json.dumps({'controls':result['controls'],'G_cases':len(rows),'T1_counts':[877,30,10],'minima':[m,ma],'seconds':result['seconds']}))
