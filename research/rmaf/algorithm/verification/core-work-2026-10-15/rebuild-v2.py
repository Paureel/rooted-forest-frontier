from pathlib import Path
import json,hashlib,subprocess,time,os,sys
root=Path(__file__).resolve().parents[5];base=Path(__file__).resolve().parent;iso=base/'isolated'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
order=['RMAF','Geometry','Bridge','Composition','CoreGraph','CherryCoarsening','CoreProgram','CoreInvariants','SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','Work','Primitive','Payload','Controls']
gates=json.loads((base/'KERNEL-GATES.json').read_text())
names=['ReviewClean','ReviewPrivatePlant','ReviewFalse','ReviewBrokenImport']
for n,g in zip(names,gates['plants']): (iso/(n+'.lean')).write_text(g['source'])
env=os.environ.copy();env['LEAN_PATH']=str(iso)
rows=[]
def run(n,positive,diagnostic=None):
 t=time.monotonic();p=subprocess.run([str(root/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 log=base/(n+'-rebuild-v2.log');log.write_text(p.stdout)
 row={'module':n,'returncode':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(iso/(n+'.lean')),'log_sha256':sha(log),'expected_positive':positive}
 if diagnostic: row['explicit_false_diagnostic']=('evaluated to `false`' in p.stdout or ('Tactic `decide` proved that the proposition' in p.stdout and 'is false' in p.stdout));assert row['explicit_false_diagnostic'],p.stdout
 assert (p.returncode==0)==positive,(n,p.stdout)
 rows.append(row);(base/'REBUILD-PROGRESS-v2.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True)
run('ReviewClean',True)
run('ReviewPrivatePlant',True)
run('ReviewFalse',False,'false')
run('ReviewBrokenImport',False)
for n in order: run(n,True)
for n in ['FalseControl','FalseAppend','FalsePruned','FalseOracle']: run(n,False,'false')
(base/'REBUILD.json').write_text(json.dumps({'status':'PASS-ISOLATED-SOURCE-REPLAY','positive_candidate_modules':len(order),'builds':rows,'scope':'Compiler outcomes only; source-cost and complete axiom audit separate'},indent=2)+'\n')
