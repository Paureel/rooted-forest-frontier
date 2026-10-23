"""One-shot actual original-vertex/source-target restriction readout adapter."""
from pathlib import Path
import json,sys,os,subprocess,time,shutil,copy
H=Path(__file__).resolve().parent;ROOT=H.parents[5];B=H/'isolated';P=H.parent/'sol-frozen-ready-v1/preparation';sys.path.insert(0,str(P));import agreement_oracle_v2 as oracle;from original_graph_v1 import Graph,canonical
sys.path.insert(0,str(H));from native_values_v2 import tr,opt,ls,ss
def addresses(t,block):return sorted(''.join(map(str,a)) for a in Graph(t).hull(block))
def compare(f,F,row):
 assert row['F']==F
 assert row['targetEmbeddings']==(not F if f['T'] is None else oracle.disjoint(f['T'],F))
 assert row['refines']==all(any(set(b)<=set(oracle.labels(s)) for s in f['ss']) for b in F)
 topology=all(any(set(b)<=set(oracle.labels(s)) and canonical(Graph(f['T']).restriction(b))==canonical(Graph(s).restriction(b)) for s in f['ss']) for b in F) if f['T'] is not None else not F
 assert row['componentTopology']==topology
 def geometry(t,blocks,rows):
  assert len(blocks)==len(rows)
  for b,r in zip(blocks,rows):assert r['B']==b and r['hull']==addresses(t,b) and canonical(r['restriction'])==canonical(Graph(t).restriction(b))
 if f['T'] is None:assert row['target']==[]
 else:geometry(f['T'],F,row['target'])
 assert len(row['sources'])==len(f['ss'])
 for s,r in zip(f['ss'],row['sources']):
  fam=[b for b in F if set(b)<=set(oracle.labels(s))];assert r['family']==fam and r['labels']==oracle.labels(s) and r['embeddings']==oracle.disjoint(s,fam);geometry(s,fam,r['geometry'])
start=time.perf_counter();spec=json.loads((P/'EXPECTATIONS-v1.json').read_text());fixed=json.loads((P/'fixed-timed-v2.json').read_text());byid={f['id']:f for f in spec['fixtures']};jobs=[]
for r in fixed['rows']:
 for i,v in enumerate(r['oracle']['records']):jobs.append((r['id']+':'+str(i),byid[r['id']],v['F']))
for i,e in enumerate(spec['explicitForests']):jobs.append(('explicit:'+str(i),byid[e['fixture']],e['F']))
commands=['import NativeGeometry','open SolNative SolGeometry']
for tag,f,F in jobs:commands.append(f'#eval emit "GEOM" (record {json.dumps(tag)} {opt(f["T"])} {ss(f["ss"])} {ls(F)})')
shutil.copyfile(H/'NativeGeometry-v1.lean',B/'NativeGeometry.lean');(B/'ProbeNativeGeometry.lean').write_text('\n'.join(commands)+'\n');records=[];lean=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
for label,args in [('compile-native-geometry',['-o','NativeGeometry.olean','NativeGeometry.lean']),('native-geometry',['ProbeNativeGeometry.lean'])]:
 t=time.perf_counter();r=subprocess.run([str(lean),*args],cwd=B,env={**os.environ,'LEAN_PATH':str(B)},text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60);(H/(label+'-v1.log')).write_text(r.stdout);records.append({'label':label,'exit':r.returncode,'seconds':time.perf_counter()-t});assert r.returncode==0,(label,r.stdout[:1000])
rows=[json.loads(l[5:]) for l in (H/'native-geometry-v1.log').read_text().splitlines() if l.startswith('GEOM\t')];assert len(rows)==len(jobs)
for (tag,f,F),r in zip(jobs,rows):assert r['id']==tag;compare(f,F,r)
for e,r in zip(spec['explicitForests'],rows[-7:]):
 if 'targetHullsDisjoint' in e:assert r['targetEmbeddings']==e['targetHullsDisjoint']
 if 'componentTopologyChecks' in e:assert r['componentTopology']==e['componentTopologyChecks']
 if 'refines' in e:assert r['refines']==e['refines']
target=next(i for i,j in enumerate(jobs) if j[0]=='explicit:0');tag,f,F=jobs[target];base=rows[target];catches=[]
for m in ['drop-original-unary-target-vertex','drop-original-source-vertex','wrong-restricted-source-topology']:
 c=copy.deepcopy(base)
 if m=='drop-original-unary-target-vertex':c['target'][0]['hull'].remove('0')
 elif m=='drop-original-source-vertex':c['sources'][0]['geometry'][0]['hull'].pop()
 else:c['sources'][0]['geometry'][0]['restriction']=999
 try:compare(f,F,c)
 except AssertionError:catches.append(m)
 else:raise AssertionError(('geometry corruption accepted',m))
out={'status':'NATIVE-ORIGINAL-GEOMETRY-PASS','forestRecords':len(jobs),'rows':rows,'catches':catches,'processes':records,'seconds':time.perf_counter()-start,'independentReplicaIncrement':0};(H/'native-geometry-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
