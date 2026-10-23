from pathlib import Path
import json,subprocess,os,hashlib,time
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent;iso=b/'isolated';env=os.environ.copy();env['LEAN_PATH']=str(iso);rows=[]
for e in json.loads((b/'SUPPLEMENTAL-CONTROL-PIN.json').read_text())['controls']:
 n=e['module'];p=iso/(n+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256'];t=time.monotonic();r=subprocess.run([str(root/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=20);log=b/(n+'.log');log.write_text(r.stdout);positive=e['expectation']=='success';false='Tactic `decide` proved that the proposition' in r.stdout and 'is false' in r.stdout;assert (r.returncode==0)==positive and (positive or false),r.stdout
 rows.append({'module':n,'returncode':r.returncode,'explicit_false_diagnostic':false,'source_sha256':e['sha256'],'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'seconds':time.monotonic()-t})
(b/'SUPPLEMENTAL-CONTROLS.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows))
