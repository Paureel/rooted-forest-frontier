"""Completed-import COPY-only assembly for actual binary callback dispatch."""
from pathlib import Path
import hashlib,json,os,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[4];B=D/'build';B.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=R/'results/algorithm-universal233-output-state-20261015T105826Z'
meta=json.loads((base/'certificate.json').read_text())
frozen=[R/'research/rmaf/algorithm/universal233/output_state/OUTPUT-STATE-MANIFEST-v1.json',R/'research/rmaf/algorithm/universal233/maf_scheduler/MAF-SCHEDULER-MANIFEST-v1.json']
for p in frozen:
 for e in json.loads(p.read_text())['immutable_files']:assert sha(R/e['path'])==e['sha256'],e['path']
entries=[{'module':n,'source':str((base/(n+'.lean')).relative_to(R)),'original_sha256':sha(base/(n+'.lean')),'compiled_sha256':sha(base/(n+'.lean')),'import_adapter':None} for n in meta['positive_order']]
mf=R/'results/algorithm-universal233-maf-scheduler-20261015T103458Z'
new=['QueryCaller','QuerySpecification','QueryBudgets','QueryMass','QueryWork','MafCaller','LocalSlots','Regional','Indexing','OriginalReconstruction','OriginalCaller','OriginalPaid']
runs=[]
for n in new:
 p=mf/(n+'.lean');data=p.read_text();adapt=None
 if n=='MafCaller':
  assert '\nimport Reconstruction\n' in data
  data=data.replace('\nimport Reconstruction\n','\nimport GroupReconstruction\n',1);adapt=['Reconstruction','GroupReconstruction']
 q=B/(n+'.lean');q.write_text(data)
 entries.append({'module':n,'source':str(p.relative_to(R)),'original_sha256':sha(p),'compiled_sha256':sha(q),'import_adapter':adapt})
 st=time.monotonic();proc=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(q)],cwd=R,env=dict(os.environ,LEAN_PATH=str(B)+':'+str(base)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (B/(n+'.log')).write_text(proc.stdout);runs.append({'module':n,'exit':proc.returncode,'seconds':time.monotonic()-st})
 assert proc.returncode==0,(n,proc.stdout)
(D/'DISPATCH-SOURCE-PINS-v1.json').write_text(json.dumps({'base_completed_manifests':[{'path':str(p.relative_to(R)),'sha256':sha(p)} for p in frozen],'entries':entries,'runs':runs,'scope':'source filename/import copies only; no proof body edits. Development build reuses exact frozen output-state binaries; final source replay must rebuild all.'},indent=2)+'\n')
print('PASS dispatch source assembly',len(entries),'completed modules')
