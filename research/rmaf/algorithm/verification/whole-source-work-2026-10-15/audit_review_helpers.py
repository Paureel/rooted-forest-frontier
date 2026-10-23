from pathlib import Path
import json,subprocess,os,hashlib,time
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent;iso=b/'isolated'
names=json.loads((b/'CANDIDATE-PIN.json').read_text())['positive_modules'];extra=['WholeReviewSourceBounds','WholeReviewSupplementClean']
s=(iso/'WholeReviewInventory.lean').read_text().replace('import WorkControls','import WholeReviewSupplementClean').replace(json.dumps(names),json.dumps(names+extra));p=iso/'WholeReviewHelperInventory.lean';p.write_text(s)
env=os.environ.copy();env['LEAN_PATH']=str(iso);t=time.monotonic();r=subprocess.run([str(root/'bootloops-lean'),p.name],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);log=b/'WholeReviewHelperInventory.log';log.write_text(r.stdout);assert r.returncode==0,r.stdout
rows=[json.loads(x.split('WHOLE_ORIGIN_ROW ',1)[1]) for x in r.stdout.splitlines() if 'WHOLE_ORIGIN_ROW ' in x];extra_rows=[x for x in rows if x['origin'] in extra];orig=[x for x in rows if x['origin'] not in extra]
assert len(orig)==2565 and {x['name'] for x in orig}=={x['name'] for x in json.loads((b/'ORIGIN-INVENTORY.json').read_text())['all_rows']}
assert extra_rows and all(x['kind']!='axiom' and set(x['axioms'])<={'Classical.choice','Quot.sound','propext'} for x in extra_rows)
x={'status':'PASS-ACCEPTED-REVIEW-HELPER-ORIGIN-AUDIT','candidate_origin_rows':len(orig),'review_origin_rows':len(extra_rows),'all_review_rows':extra_rows,'seconds':time.monotonic()-t,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'failed_value_adapter_not_imported':True}
(b/'REVIEW-HELPER-INVENTORY.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:v for k,v in x.items() if k!='all_review_rows'}))
