#!/usr/bin/env python3
"""One-shot caller package controls/audit/replay using the inherited capped
pilot and unchanged stored-occurrence instrument. No dependency rebuild."""
from pathlib import Path
import datetime,gzip,hashlib,importlib.util,json,os,shutil,time
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);o=importlib.util.module_from_spec(s);s.loader.exec_module(o);return o
P=load('caller_pilot',D/'pilot.py');I=load('caller_instrument',D/'instrument.py');base=json.loads((D/'ROOT-v1.json').read_text());O=R/base['root'];old=json.loads((R/base['licensed_persistent_manifest']).read_text());oldF=R/old['canonical_receipt'];pins={x['path']:x['sha256'] for x in old['immutable_files']}
modules=['CallerPrecontrols','CallerCaps','BinaryCallerSetup','BinaryCallerSites','BinaryCallerPayload','BinaryCallerActual','BinaryCallerControls']
ptr=D/'FINAL-ROOT-v1.json'
if ptr.exists():F=R/json.loads(ptr.read_text())['root']
else:
 F=R/'results'/('algorithm-universal233-binary-caller-final-20261016T092054Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));F.mkdir();ptr.write_text(json.dumps({'root':str(F.relative_to(R))},indent=2)+'\n')
def snap(a,b):
 b.parent.mkdir(parents=True,exist_ok=True)
 if b.exists():assert b.read_bytes()==a.read_bytes()
 elif not a.stat().st_mode&0o222:os.link(a,b)
 else:shutil.copyfile(a,b);b.chmod(0o444)
for dep in base['dependencies']:
 for f in dep['files']:
  p=R/f['linked'];assert sha(p)==f['sha256'];snap(p,F/p.name)
for n in modules:
 s=D/(n+'.lean');assert s.read_bytes()==(O/s.name).read_bytes()
 assert any((x:=json.loads(p.read_text()))['exit']==0 and x['failure'] is None and x['source_sha256']==sha(s) for p in O.glob(n+'-*.run.json'))
 snap(s,F/s.name);snap(O/(n+'.olean'),F/(n+'.olean'))
for p in O.glob('*.run.json'):
 for f in [p,p.with_name(p.name.replace('.run.json','.log.gz')),p.with_name(p.name.replace('.run.json','.source'))]:snap(f,F/'retained-runs'/f.name)
for p in D.iterdir():
 if p.is_file():snap(p,F/'provenance'/(p.stem+'-'+sha(p)[:16]+p.suffix))
(F/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n');P.O=F
false=[('CallerFalseBudgetWidth','(checkerCapacity (some pair) [pair] q8 badF).value.length≤2','have h:=original_bound_truth.1;omega'),('CallerFalseNoSetup','setupCallsWork (some pair) [pair] q8 [badF,badF]=0','rw [duplicate_setup_truth.1];have h:=duplicate_setup_truth.2.1;omega'),('CallerFalseDedup','setupCallsWork (some pair) [pair] q8 [badF,badF]=(checkerCapacity (some pair) [pair] q8 badF).work','rw [duplicate_setup_truth.1];have h:=duplicate_setup_truth.2.1;omega'),('CallerFalseFlatten','(flattenAnswers xs).value=F','rw [flatten_truth.1];simp only [badF,F,a,b];decide'),('CallerFalseTie','(bestCandidates (some pair) [pair] q8 [badF,paddedF,F]).value=some F','rw [raw_truth.1];simp only [paddedF,F,a,b];decide'),('CallerFalsePayment','decode (payBudget q8 [(),(),()]).value=6','rw [payment_truth.1];decide'),('CallerFalseSetupFloor','(bestCandidates (some pair) [pair] q8 [badF,badF]).work<setupCallsWork (some pair) [pair] q8 [badF,badF]','have h:=raw_parent_setup_paid (some pair) [pair] q8 [badF,badF];omega')]
false_records=[]
for n,claim,proof in false:
 s='import BinaryCallerControls\nopen GenericForest.BinaryCaller GenericForest.BinaryCaller.Controls GenericForest.BinaryProvider GenericForest.ScalarBits\nexample : '+claim+' := by '+proof+'\n';f=F/(n+'.lean')
 if f.exists():assert f.read_text()==s
 else:f.write_text(s)
 txt=P.run(n,False,1);assert 'is false' in txt or 'omega could not prove' in txt,(n,txt[-800:]);false_records.append({'module':n,'claim':claim,'result':'CAUGHT_AGAINST_KERNEL_CHECKED_TWIN'})
ghost='CallerAuditGhost';(F/(ghost+'.lean')).write_text('import BinaryCallerActual\nnamespace CallerAuditPlant\naxiom forbiddenCallback : False\ndef ghost : Nat := False.elim forbiddenCallback\nend CallerAuditPlant\n');P.run(ghost,True,0)
conv='CallerBadConversion';(F/(conv+'.lean')).write_text('import BinaryCallerActual\ndef callerBadDecode (q : List Bool) : Nat := GenericForest.ScalarBits.decode q\n');P.run(conv,True,0)
audit_rows=[];audits=[]
for k in range(0,len(modules),3):
 batch=modules[k:k+3];stamp=str(time.time_ns());n='CallerStored'+stamp;Q=F/('audit-'+stamp);Q.mkdir();(F/(n+'.lean')).write_text(I.source(['BinaryCallerControls'],batch,Q));P.run(n,False,0);rows=I.parse(Q,batch,F);audit_rows+=rows;audits.append({'module':n,'directory':str(Q.relative_to(R)),'producers':batch,'occurrences':len(rows)})
stamp=str(time.time_ns());Q=F/('hostile-'+stamp);Q.mkdir();n='CallerHostile'+stamp;(F/(n+'.lean')).write_text(I.source([ghost],[ghost],Q));P.run(n,False,1);I.parse(Q,[ghost],F,True)
stamp=str(time.time_ns());Q=F/('conversion-'+stamp);Q.mkdir();n='CallerConversion'+stamp;(F/(n+'.lean')).write_text(I.source([conv],[conv],Q));P.run(n,False,0);cr=I.parse(Q,[conv],F)
assert any(r['name']=='callerBadDecode' and 'GenericForest.ScalarBits.decode' in r['references'] for r in cr)
# Read only exact previous stored producer records; never merge import pools.
previous=json.loads((oldF/'receipt.json').read_text());rows={r['name']:r for r in audit_rows}
for b in previous['audits']:
 for prod in b['producers']:
  p=R/b['directory']/(prod+'.json.gz');assert sha(p)==pins[str(p.relative_to(R))]
  with gzip.open(p,'rt') as f:
   for row in json.load(f):assert row['name'] not in rows;rows[row['name']]=row
runtime=['GenericForest.BinaryCaller.'+x for x in ['acceptedFromInput','checkOptional','flattenAnswers','disjointFinish','lengthChoice','bestCandidates','checkerCallsWork','setupCallsWork','payBudget']]
banned={'GenericForest.ScalarBits.decode','GenericForest.ScalarBits.encode'}|{'GenericForest.BinaryProvider.'+x for x in ['labelValue','blockValue','forestValue','treeValue','sourcesValue','targetValue','forestOptionValue']}
def scan(starts,records):
 seen=set();boundary=set();todo=list(starts)
 while todo:
  n=todo.pop()
  if n in seen:continue
  assert n not in banned,('BANNED_RUNTIME_REFERENCE',n);seen.add(n);r=records.get(n)
  if r is None:boundary.add(n);continue
  if r['kind']=='theorem':continue
  todo.extend(r['references'])
 return seen,boundary
try:scan(['callerBadDecode'],{r['name']:r for r in cr})
except AssertionError:conversion='CAUGHT_BY_SAME_RUNTIME_SCAN'
else:raise AssertionError('BAD_DECODE_CONTROL_SURVIVED')
seen,boundary=scan(runtime,rows);assert not any(n.startswith(('GenericForest.','Universal233.','RMAF.')) for n in boundary),sorted(boundary)
(F/'runtime-audit.json').write_text(json.dumps({'status':'PASS_SOURCE_RUNTIME_BODY_SCAN','registered':runtime,'visited':sorted(seen),'standard_boundary':sorted(boundary),'conversion_control':conversion,'custom_reference_boundary':'ALL_RESOLVED','nativeIR':'OPEN'},indent=2)+'\n')
# Fresh own-source re-elaboration, importing only sealed dependencies.
V=R/'results'/('algorithm-universal233-binary-caller-replay-20261016T092054Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));V.mkdir();P.O=V
for dep in base['dependencies']:os.symlink((F/(dep['module']+'.olean')).resolve(),V/(dep['module']+'.olean'))
for n in modules:
 (V/(n+'.lean')).write_bytes((F/(n+'.lean')).read_bytes());P.run(n,True,0)
fresh=[]
for k,b in enumerate(audits):
 Q=V/('audit-'+str(k));Q.mkdir();n='CallerReplay'+str(k);(V/(n+'.lean')).write_text(I.source(['BinaryCallerControls'],b['producers'],Q));P.run(n,False,0);fresh+=I.parse(Q,b['producers'],V)
assert {r['name'] for r in fresh}=={r['name'] for r in audit_rows}
original={r['name']:r for r in audit_rows}
for r in fresh:
 for key in ['producer','index','name','kind','type','body','body_scope','axiom_references']:assert r[key]==original[r['name']][key],(r['name'],key)
rec={'version':1,'status':'SOURCE_CALL_SITE_REFINEMENT_WITH_EXPLICIT_PRODUCER_PREMISES','root':str(F.relative_to(R)),'replay_root':str(V.relative_to(R)),'modules':modules,'dependency_pairs':len(base['dependencies']),'dependency_rebuilds':0,'positive_groups':7,'positive_assertions':20,'false_controls':false_records,'hostile_axiom':'CAUGHT','conversion_control':conversion,'own_stored_occurrences':len(audit_rows),'own_audit_producers':len(modules),'previous_stored_occurrences_reused':1585,'audits':audits,'runtime_definitions':len(runtime),'runtime_references':len(seen),'standard_boundary_names':len(boundary),'source_replay':'MATCHED_ALL_OWN_TYPES_BODIES_ACTUAL_AXIOM_RECORDS','independent_credit':0,'whole_solver_runtime':'OPEN','nativeIR':'OPEN','first_remaining':'Construct represented singleton/scheduler/raw-candidate outputs at the actual producer sites and prove the displayed representation equations and stored-label/state caps for those producers; integrate the charged local bounds in the separately owned weighted recurrence.'}
(F/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');(V/'receipt.json').write_text(json.dumps({'source_root':str(F.relative_to(R)),'source_modules_rebuilt':len(modules),'frozen_dependency_rebuilds':0,'stored_records_matched':len(fresh),'independent_credit':0},indent=2)+'\n');(D/'RESULT-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
