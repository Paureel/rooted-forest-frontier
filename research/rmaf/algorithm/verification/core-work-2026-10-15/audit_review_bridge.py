from pathlib import Path
import json,hashlib,subprocess,os,time
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent;iso=b/'isolated'
s=(iso/'ReviewInventory.lean').read_text().replace('import Controls','import ReviewCostClean').replace('let wanted := ["RMAF"','let wanted := ["ReviewCostBridgeV4","ReviewCostClean","RMAF"')
(iso/'ReviewBridgeInventory.lean').write_text(s)
env=os.environ.copy();env['LEAN_PATH']=str(iso);t=time.monotonic();p=subprocess.run([str(root/'bootloops-lean'),'ReviewBridgeInventory.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=20)
log=b/'ReviewBridgeInventory.log';log.write_text(p.stdout);assert p.returncode==0,p.stdout
rows=[json.loads(x.split('WORK_REVIEW_ROW ',1)[1]) for x in p.stdout.splitlines() if 'WORK_REVIEW_ROW ' in x]
review=[r for r in rows if r['origin'] in ['ReviewCostBridgeV4','ReviewCostClean']]
assert review and all(r['kind']!='axiom' and set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in review)
orig=json.loads((b/'ORIGIN-INVENTORY.json').read_text())['all_rows'];assert {r['name'] for r in rows if r not in review}=={r['name'] for r in orig}
result={'status':'PASS-ACCEPTED-REVIEW-BRIDGE-ORIGIN-AUDIT','candidate_origin_rows_unchanged':len(orig),'review_origin_rows':len(review),'all_review_rows':review,'seconds':time.monotonic()-t,'audit_source_sha256':hashlib.sha256((iso/'ReviewBridgeInventory.lean').read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'failed_V1_V3_sources_not_imported':True}
(b/'REVIEW-BRIDGE-INVENTORY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='all_review_rows'}))
