from pathlib import Path
import os,json,hashlib,subprocess,time
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent;iso=b/'isolated';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pin=json.loads((b/'CANDIDATE-PIN.json').read_text());gates=json.loads((b/'KERNEL-GATES.json').read_text())
plant_names=['WholeReviewClean','WholeReviewFalse','WholeReviewUsed','WholeReviewUnused','WholeReviewBrokenImport']
for n,g in zip(plant_names,gates['plants']):(iso/(n+'.lean')).write_text(g['source'])
env=os.environ.copy();env['LEAN_PATH']=str(iso);rows=[]
def execute(n,success,false=False):
 t=time.monotonic();p=subprocess.run([str(root/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 log=b/(n+'-rebuild.log');log.write_text(p.stdout)
 explicit='Tactic `decide` proved that the proposition' in p.stdout and 'is false' in p.stdout
 row={'module':n,'returncode':p.returncode,'seconds':time.monotonic()-t,'source_sha256':h(iso/(n+'.lean')),'log_sha256':h(log),'expected_success':success,'explicit_false_diagnostic':explicit}
 rows.append(row);(b/'REBUILD-PROGRESS.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True)
 assert (p.returncode==0)==success,(n,p.stdout)
 if false:assert explicit,(n,p.stdout)
for n in plant_names:execute(n,n in ['WholeReviewClean','WholeReviewUsed','WholeReviewUnused'],n=='WholeReviewFalse')
for n in pin['topological_rebuild_order']:execute(n,True)
for n in ['FalseControl','FalseColorCount','FalsePruned','FalseAppend']:execute(n,False,True)
(b/'REBUILD.json').write_text(json.dumps({'status':'PASS-ISOLATED-SOURCE-REPLAY','positive_candidate_modules':len(pin['positive_modules']),'builds':rows},indent=2)+'\n')
