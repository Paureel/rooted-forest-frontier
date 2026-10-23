from pathlib import Path
import os,subprocess,json,time,copy,hashlib
b=Path(__file__).resolve().parent;root=b.parents[4]
allowed={'Classical.choice','Quot.sound','propext'};results={}
def gate(rows,expected):
 names=[x['name'] for x in rows]
 if len(names)!=len(set(names)):return 'REJECT duplicate originating record'
 if {(x['name'],x['origin']) for x in rows}!=expected:return 'REJECT missing/wrong originating record'
 for x in rows:
  if x['kind']=='axiom':return 'REJECT originating custom axiom '+x['name']
  if not set(x['axioms'])<=allowed:return 'REJECT custom axiom closure '+x['name']
 return 'ACCEPT complete origin inventory'
for label in ['query','rank']:
 iso=b/('isolated-'+label);logs=b/('logs-'+label);env=os.environ.copy();env['LEAN_PATH']=str(iso)
 for a,z in [('ToyUsed','ReviewPlantUsed'),('ToyUnused','ReviewPlantUnused')]:
  (iso/(z+'.lean')).write_text((b/'std-toys'/(a+'.lean')).read_text())
 audit=(b/'std-toys/ToyAudit.lean').read_text().replace('import ToyClean\nimport ToyUsed\nimport ToyUnused','import ReviewPlantUsed\nimport ReviewPlantUnused').replace('["ToyClean","ToyUsed","ToyUnused"]','["ReviewPlantUsed","ReviewPlantUnused"]').replace('TOY_ORIGIN ','REVIEW_ORIGIN ')
 (iso/'ReviewAuditPlants.lean').write_text(audit);builds=[]
 for n in ['ReviewPlantUsed','ReviewPlantUnused','ReviewAuditPlants']:
  t=time.monotonic();r=subprocess.run([str(root/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);(logs/(n+'.log')).write_text(r.stdout);assert r.returncode==0,r.stdout;builds.append({'module':n,'exit':r.returncode,'seconds':time.monotonic()-t})
 plants=[json.loads(l.split('REVIEW_ORIGIN ',1)[1]) for l in r.stdout.splitlines() if 'REVIEW_ORIGIN ' in l]
 clean=json.loads((b/('REPLAY-'+label.upper()+'.json')).read_text())['origins'];expected={(x['name'],x['origin']) for x in clean};statuses={}
 statuses['clean']=gate(clean,expected);assert statuses['clean'].startswith('ACCEPT')
 statuses['missing']=gate(clean[1:],expected)
 statuses['duplicate']=gate(clean+[clean[0]],expected)
 wrong=copy.deepcopy(clean);wrong[0]['origin']='Foreign';statuses['wrong_origin']=gate(wrong,expected)
 for mod in ['ReviewPlantUsed','ReviewPlantUnused']:
  rs=[x for x in plants if x['origin']==mod];statuses[mod]=gate(rs,{(x['name'],x['origin']) for x in rs});assert statuses[mod].startswith('REJECT')
  assert any(x['kind']=='axiom' and '_private.' in x['name'] for x in rs)
  if mod=='ReviewPlantUnused':assert any(x['kind']=='theorem' and not x['axioms'] for x in rs)
 pin=json.loads((b/'CANDIDATE-PIN.json').read_text())['packages'][label]['copied_sources'][0];data=(iso/(pin['module']+'.lean')).read_bytes()
 assert hashlib.sha256(data).hexdigest()==pin['sha256'];assert hashlib.sha256(data+b'\n-- planted mismatch\n').hexdigest()!=pin['sha256'];statuses['byte_corruption']='REJECT source SHA mismatch'
 wrongpin='0'*64;assert hashlib.sha256(data).hexdigest()!=wrongpin;statuses['source_pin_mismatch']='REJECT source SHA mismatch'
 assert all(x.startswith('REJECT') for k,x in statuses.items() if k!='clean')
 results[label]={'status':'PASS COMPLETE-ORIGIN GATES','clean_count':len(clean),'plant_origins':plants,'diagnostics':statuses,'builds':builds,'scope':'Used and UNUSED private custom axioms are compiled deliberately only in isolated detector plants; excluded from accepted scientific inventory.'}
(b/'ORIGIN-DETECTOR-RECEIPT.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps({k:v['diagnostics'] for k,v in results.items()}))
