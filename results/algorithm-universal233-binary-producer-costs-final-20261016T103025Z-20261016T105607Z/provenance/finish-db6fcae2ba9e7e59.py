#!/usr/bin/env python3
"""One-shot caller package controls/audit/replay using the inherited capped
pilot and unchanged stored-occurrence instrument. No dependency rebuild."""
from pathlib import Path
import datetime,gzip,hashlib,importlib.util,json,os,shutil,time
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);o=importlib.util.module_from_spec(s);s.loader.exec_module(o);return o
P=load('caller_pilot',D/'pilot.py');I=load('caller_instrument',D/'instrument.py');base=json.loads((D/'ROOT-v1.json').read_text());O=R/base['root'];old=json.loads((R/base['licensed_previous_manifest']).read_text());oldF=R/old['canonical_receipt'];pins={x['path']:x['sha256'] for x in old['immutable_files']}
modules=['ProducerCostPrimitives','ProducerCostAgreement','ProducerCostPretest','ProducerCostJobsSource','ProducerCostRawLedger','ProducerCostSchedulerLedger','ProducerOverlap','ProducerGeneratorColor','ProducerGeneratorTrees','ProducerGeneratorChoose','ProducerGeneratorStep','ProducerGeneratorRun','ProducerRawBinding','ProducerCostAssembly','ProducerCostsControls']
wanted=modules
ptr=D/'FINAL-ROOT-v1.json'
if ptr.exists():F=R/json.loads(ptr.read_text())['root']
else:
 F=R/'results'/('algorithm-universal233-binary-producer-costs-final-20261016T103025Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));F.mkdir();ptr.write_text(json.dumps({'root':str(F.relative_to(R))},indent=2)+'\n')
if (F/'receipt.json').exists():
 p=F/'receipt.json';shutil.copyfile(p,F/('receipt-previous-'+sha(p)[:16]+'.json'))
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
false=[
 ('CostsFalseFuel','(Generator.fuelBits q8 [(),(),()]).value.length=8','rw [fuel_truth.1];decide'),
 ('CostsFalseOverlap','(overlapProducer crossed [.leaf z,.leaf z,.leaf a]).value.map overlapValue=some ⟨1,0,[false,false]⟩','rw [overlap_truth.1];decide'),
 ('CostsFalseAddressPadding','(firstShared [[false,false]] [[false]]).value=some [false]','rw [original_address_truth.1];decide'),
 ('CostsFalsePruning','(Generator.receiptValue (Generator.generateBits crossed parity []).value).pruned=0','rw [generator_zero_truth.2.2.2];decide'),
 ('CostsFalseDedup','(branchesProducer crossed [crossed] repeated q8).value.length=1','rw [branch_truth.2];decide'),
 ('CostsFalseCallbackLedger','rawCallbackWork GenericForest.BinaryProducer.Controls.budgetAnswer (some GenericForest.BinaryProducer.Controls.pair) [GenericForest.BinaryProducer.Controls.pair] GenericForest.BinaryProducer.Controls.q8 GenericForest.BinaryProducer.Controls.rawInput=37','rw [ledger_truth.1];decide'),
 ('CostsFalsePretestFree','(pretestBits pair pair).work=0','have h:=pretest_nonzero_truth;omega'),
 ('CostsFalseMultiplicityFree','(branchesProducer crossed [crossed] repeated q8).work=2*(rawProducer crossed [crossed] [] [] q8).work','have h:=multiplicity_cost_truth;omega')
]
control_dir=F/'parser-controls';control_dir.mkdir(exist_ok=True)
def parser_fixture(tag,rs,count=None,path=None):
 Q=control_dir/tag;Q.mkdir(exist_ok=True);n='ProducerCostsControls'
 (Q/'index.json').write_text(json.dumps({'counts':[{'producer':n,'count':len(rs) if count is None else count,'path':str(path or F/(n+'.olean'))}],'rejects':[]}))
 with gzip.open(Q/(n+'.json.gz'),'wt') as f:json.dump(rs,f)
 return Q
fixture=[{'producer':'ProducerCostsControls','index':0,'name':'fixture','resolved_origin':'ProducerCostsControls','kind':'definition','body':'literal-known-answer','axiom_references':[]}]
I.parse(parser_fixture('clean',fixture),['ProducerCostsControls'],F);parser_results={'clean':'PASS'}
for tag,rs,count,path in [('missing-occurrence',fixture,2,None),('duplicate-index',fixture+fixture,None,None),('missing-body',[dict(fixture[0],body=None)],None,None),('forbidden-axiom',[dict(fixture[0],axiom_references=['forbidden'])],None,None),('foreign-path',fixture,None,R/'foreign.olean')]:
 try:I.parse(parser_fixture(tag,rs,count,path),['ProducerCostsControls'],F)
 except AssertionError:parser_results[tag]='CAUGHT'
 else:raise AssertionError('PARSER_PLANT_SURVIVED|'+tag)
false_records=[]
for n,claim,proof in false:
 s='import ProducerCostsControls\nopen GenericForest.BinaryProducer GenericForest.BinaryProducer.CostControls GenericForest.BinaryProvider GenericForest.ScalarBits\nexample : '+claim+' := by '+proof+'\n';f=F/(n+'.lean')
 if f.exists():assert f.read_text()==s
 else:f.write_text(s)
 txt=P.run(n,False,1);assert 'is false' in txt or 'omega could not prove' in txt,(n,txt[-800:]);false_records.append({'module':n,'claim':claim,'result':'CAUGHT_AGAINST_KERNEL_CHECKED_TWIN'})
ghost='CostsAuditGhost';(F/(ghost+'.lean')).write_text('import ProducerCostsControls\nnamespace CostsAuditPlant\naxiom forbiddenCallback : False\ndef ghost : Nat := False.elim forbiddenCallback\nend CostsAuditPlant\n');P.run(ghost,True,0)
conv='CostsBadConversion';(F/(conv+'.lean')).write_text('import ProducerCostsControls\ndef costsBadDecode (q : List Bool) : Nat := GenericForest.ScalarBits.decode q\n');P.run(conv,True,0)
audit_rows=[];audits=[]
for k in range(0,len(wanted),3):
 batch=wanted[k:k+3];stamp=str(time.time_ns());n='ProducerStored'+stamp;Q=F/('audit-'+stamp);Q.mkdir();(F/(n+'.lean')).write_text(I.source(modules,batch,Q));P.run(n,False,0);rows=I.parse(Q,batch,F);audit_rows+=rows;audits.append({'module':n,'directory':str(Q.relative_to(R)),'producers':batch,'occurrences':len(rows)})
stamp=str(time.time_ns());Q=F/('hostile-'+stamp);Q.mkdir();n='ProducerHostile'+stamp;(F/(n+'.lean')).write_text(I.source([ghost],[ghost],Q));P.run(n,False,1);I.parse(Q,[ghost],F,True)
stamp=str(time.time_ns());Q=F/('conversion-'+stamp);Q.mkdir();n='ProducerConversion'+stamp;(F/(n+'.lean')).write_text(I.source([conv],[conv],Q));P.run(n,False,0);cr=I.parse(Q,[conv],F)
assert any(r['name']=='costsBadDecode' and 'GenericForest.ScalarBits.decode' in r['references'] for r in cr)
# Read only exact previous stored producer records; never merge import pools.
rows={r['name']:r for r in audit_rows}
prior_audit_sources=[]
previous=json.loads((oldF/'receipt.json').read_text())
paths=list(previous.get('prior_audit_sources',[]))
for b in previous['audits']:
 for prod in b['producers']:
  p=R/b['directory']/(prod+'.json.gz');paths.append({'path':str(p.relative_to(R)),'sha256':pins[str(p.relative_to(R))]})
for item in paths:
 p=R/item['path'];assert sha(p)==pins[item['path']]==item['sha256'];prior_audit_sources.append(item)
 with gzip.open(p,'rt') as f:
  for row in json.load(f):
   if row['name'] in rows:assert rows[row['name']]==row
   else:rows[row['name']]=row
runtime=['GenericForest.BinaryProducer.'+x for x in ['rawCallbackWork','runCallbackWork','scheduleCallbackWork','zipBits','firstShared','indexLt','overlapRow','overlapRows','overlapProducer','sourceAtBits','rawProducer','indexedOutputs','branchesProducer','generatedRawParent']]+['GenericForest.BinaryProducer.Generator.'+x for x in ['colorEq','regionBits','leafListBits','colorBits','fromTreeBits','groupsBits','normalizeBits','eraseBits','mixedBits','allColors','filterColor','uniqueBits','findUnique','chooseBits','combineBits','prefixBits','childBits','detachedBits','flattenGroups','finishBits','attemptBits','stepBits','fuelBits','runBits','generateBits']]

banned={'GenericForest.ScalarBits.decode','GenericForest.ScalarBits.encode'}|{'GenericForest.BinaryProvider.'+x for x in ['labelValue','blockValue','forestValue','treeValue','sourcesValue','targetValue','forestOptionValue']}

banned|={'GenericForest.BinaryProducer.'+x for x in ['pairValue','receiptValue','treePairValue','jobValue','outputValue','branchValue','overlapValue','indexedValue']}|{'GenericForest.BinaryProducer.Generator.'+x for x in ['colorValue','groupValue','gtreeValue','groupsValue','choiceValue','receiptValue']}
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
try:scan(['costsBadDecode'],{r['name']:r for r in cr})
except AssertionError:conversion='CAUGHT_BY_SAME_RUNTIME_SCAN'
else:raise AssertionError('BAD_DECODE_CONTROL_SURVIVED')
seen,boundary=scan(runtime,rows);assert not any(n.startswith(('GenericForest.','Universal233.','RMAF.')) for n in boundary),sorted(boundary)
(F/'runtime-audit.json').write_text(json.dumps({'status':'PASS_SOURCE_RUNTIME_BODY_SCAN','registered':runtime,'visited':sorted(seen),'standard_boundary':sorted(boundary),'conversion_control':conversion,'custom_reference_boundary':'ALL_RESOLVED','nativeIR':'OPEN'},indent=2)+'\n')
# Fresh own-source re-elaboration, importing only sealed dependencies.
V=R/'results'/('algorithm-universal233-binary-producer-costs-replay-20261016T103025Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));V.mkdir();P.O=V
for dep in base['dependencies']:os.symlink((F/(dep['module']+'.olean')).resolve(),V/(dep['module']+'.olean'))
for n in modules:
 (V/(n+'.lean')).write_bytes((F/(n+'.lean')).read_bytes());P.run(n,True,0)
fresh=[]
for k,b in enumerate(audits):
 Q=V/('audit-'+str(k));Q.mkdir();n='ProducerReplay'+str(k);(V/(n+'.lean')).write_text(I.source(modules,b['producers'],Q));P.run(n,False,0);fresh+=I.parse(Q,b['producers'],V)
assert {r['name'] for r in fresh}=={r['name'] for r in audit_rows}
original={r['name']:r for r in audit_rows}
for r in fresh:
 for key in ['producer','index','name','kind','type','body','body_scope','axiom_references']:assert r[key]==original[r['name']][key],(r['name'],key)
rec={'version':1,'status':'SOURCE_LOCAL_COST_ASSEMBLY_AND_ACTUAL_GENERATION_VALUE_WITH_OPEN_GENERATION_COST_BOUND','root':str(F.relative_to(R)),'replay_root':str(V.relative_to(R)),'modules':modules,'dependency_pairs':len(base['dependencies']),'dependency_rebuilds':0,'positive_groups':12,'positive_assertions':25,'false_controls':false_records,'parser_controls':parser_results,'hostile_axiom':'CAUGHT','conversion_control':conversion,'own_stored_occurrences':sum(r['producer'] in modules for r in audit_rows),'audited_dependency_occurrences':sum(r['producer'] not in modules for r in audit_rows),'audit_producers':len(wanted),'own_audit_producers':len(modules),'previous_stored_occurrences_reused':len(rows)-len(audit_rows),'prior_audit_sources':prior_audit_sources,'audits':audits,'runtime_definitions':len(runtime),'runtime_references':len(seen),'standard_boundary_names':len(boundary),'source_replay':'MATCHED_ALL_OWN_TYPES_BODIES_ACTUAL_AXIOM_RECORDS','independent_credit':0,'whole_solver_runtime':'OPEN','nativeIR':'OPEN','first_remaining':'Close actual overlap/generator traversal, receipt-counter/copy and live-storage bounds in an explicit polynomial times2^q; derive all generated branch/callback stored caps from inputs; implement/refine production ordinary/forest recursion; bind semantic numeric interfaces and whole weighted runtime separately.'}
(F/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');(V/'receipt.json').write_text(json.dumps({'source_root':str(F.relative_to(R)),'source_modules_rebuilt':len(modules),'frozen_dependency_rebuilds':0,'stored_records_matched':len(fresh),'independent_credit':0},indent=2)+'\n');(D/'RESULT-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
