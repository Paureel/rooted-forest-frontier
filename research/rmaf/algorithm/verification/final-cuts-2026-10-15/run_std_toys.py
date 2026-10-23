"""One-shot Std-only audit controls; no scientific candidate imports."""
from pathlib import Path
import os,sys,json,subprocess,time,hashlib
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent;iso=b/'std-toys';env=os.environ.copy();env['LEAN_PATH']=str(iso)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pilot='--pilot' in sys.argv
names=['CutClean'] if pilot else ['CutClean','CutUsed','CutUnused','CutFalseCost','CutFalseVertices','CutBrokenImport','CutAudit'];rows=[]
for n in names:
 t=time.monotonic();r=subprocess.run([str(root/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=iso,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30);log=b/(n+('-pilot' if pilot else '')+'.log');log.write_text(r.stdout);positive=n not in ['CutFalseCost','CutFalseVertices','CutBrokenImport'];false='Tactic `decide` proved that the proposition' in r.stdout and 'is false' in r.stdout
 assert (r.returncode==0)==positive,(n,r.stdout)
 if n in ['CutFalseCost','CutFalseVertices']:assert false,r.stdout
 rows.append({'module':n,'returncode':r.returncode,'seconds':time.monotonic()-t,'explicit_false_diagnostic':false,'source_sha256':h(iso/(n+'.lean')),'log_sha256':h(log)})
 if n=='CutAudit':audit=[json.loads(l.split('CUT_ORIGIN ',1)[1]) for l in r.stdout.splitlines() if 'CUT_ORIGIN ' in l]
if not pilot:
 allowed={'Classical.choice','Quot.sound','propext'}
 def gate(rs,names):return len(rs)==len({x['name'] for x in rs}) and {(x['name'],x['origin']) for x in rs}==names and all(x['kind']!='axiom' and set(x['axioms'])<=allowed for x in rs)
 clean=[x for x in audit if x['origin']=='CutClean'];used=[x for x in audit if x['origin']=='CutUsed'];unused=[x for x in audit if x['origin']=='CutUnused'];ns={(x['name'],x['origin']) for x in clean};assert gate(clean,ns)
 assert any('_private.' in x['name'] for x in clean) and any(x['kind']=='constructor' for x in clean) and any(x['kind']=='recursor' for x in clean)
 assert not gate(clean[1:],ns) and not gate(clean+[clean[0]],ns)
 wrong=[dict(x) for x in clean];wrong[0]['origin']='Foreign';assert not gate(wrong,ns)
 assert not gate(used,{(x['name'],x['origin']) for x in used}) and not gate(unused,{(x['name'],x['origin']) for x in unused})
 assert any(x['kind']=='axiom' and '_private.' in x['name'] for x in unused) and any(x['kind']=='theorem' and not x['axioms'] for x in unused)
 source=(iso/'CutClean.lean').read_bytes();assert hashlib.sha256(source+b'\n-- corrupt\n').hexdigest()!=h(iso/'CutClean.lean');assert h(iso/'CutClean.lean')!='0'*64
 result={'status':'PASS-STD-ONLY-PRERELEASE-AUDIT-TOYS','builds':rows,'all_origin_rows':audit,'origin_counts':{m:sum(x['origin']==m for x in audit) for m in ['CutClean','CutUsed','CutUnused']},'controls':{'clean':'ACCEPT','private_used':'REJECT','private_unused':'REJECT','missing_record':'REJECT','duplicate_record':'REJECT','wrong_origin':'REJECT','changed_bytes':'REJECT','wrong_pin':'REJECT','two_explicit_false':'REJECT','broken_import':'EXCLUDE-falsity'},'candidate_source_contact':False,'scientific_candidate_compilations':0,'additional_replications':0}
else:result={'status':'PASS-STD-ONLY-BUILD-PILOT','builds':rows,'candidate_source_contact':False,'scientific_candidate_compilations':0}
p=b/('STD-TOY-PILOT.json' if pilot else 'STD-TOY-RECEIPT.json');p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='all_origin_rows'}))
