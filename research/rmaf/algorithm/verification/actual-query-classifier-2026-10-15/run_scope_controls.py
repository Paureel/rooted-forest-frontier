from pathlib import Path
import os,json,subprocess,time,hashlib
b=Path(__file__).resolve().parent;root=b.parents[4];h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=[('query','ReviewScope',True),('rank','ReviewScope',True),('rank','ReviewFalseScope',False)]
pin={'phase':'POST-CANDIDATE explicit interface witnesses; not preregistered35/111 evidence','expectations':['wrong solver results are accepted absent IH','missing completeness can reject feasible planted minima','independent conservative source sheet72n+96 <=128(n+1)','known-four literal list theorem fails at one leaf/rank1 without rank4 premise','false universal one-leaf list equality rejected by explicit decide diagnostic'],'sources':{label+'/'+n:h(b/('isolated-'+label)/(n+'.lean')) for label,n,_ in plan}}
(b/'POST-CANDIDATE-SCOPE-PIN.json').write_text(json.dumps(pin,indent=2)+'\n');rows=[]
for label,n,positive in plan:
 iso=b/('isolated-'+label);env=os.environ.copy();env['LEAN_PATH']=str(iso);t=time.monotonic();r=subprocess.run([str(root/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);log=b/('logs-'+label)/(n+'.log');log.write_text(r.stdout);assert (r.returncode==0)==positive,r.stdout
 false='Tactic `decide` proved that the proposition' in r.stdout and 'is false' in r.stdout
 if not positive:assert false,r.stdout
 rows.append({'label':label,'module':n,'exit':r.returncode,'explicit_false_diagnostic':false,'seconds':time.monotonic()-t,'source_sha256':h(iso/(n+'.lean')),'log_sha256':h(log)})
(b/'POST-CANDIDATE-SCOPE-RECEIPT.json').write_text(json.dumps({'status':'PASS-SCOPED-INTERFACE-WITNESSES','runs':rows},indent=2)+'\n');print(json.dumps(rows))
