#!/usr/bin/env python3
"""One-shot continuation packager. Reuses measured pilot and stored audit;
no general toolkit capability is introduced, and no dependency is rebuilt."""
from pathlib import Path
import datetime,gzip,hashlib,importlib.util,json,os,shutil,time
D=Path(__file__).resolve().parent
R=next(p for p in D.parents if (p/'bootloops-lean').exists())
J=D/'resume_20261016T083330Z'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def load(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
P=load('binary_pilot',D/'pilot.py');I=load('binary_instrument',D/'instrument.py')
base=json.loads((D/'ROOT-v1.json').read_text());O=R/base['root']
modules=['PersistentScalar','Representation','PersistentLists','PersistentMembership','PersistentCount','PersistentPartition','PersistentTrees','PersistentFamilies','PersistentCapacity','PersistentHull','PersistentEmbeddings','PersistentProper','PersistentChecks','PersistentAccepted','PersistentEntry','ProviderPrecontrols','ProviderResumeControls']
ptr=J/'FINAL-ROOT-v1.json'
if ptr.exists():
 F=R/json.loads(ptr.read_text())['root']
else:
 F=R/'results'/('algorithm-universal233-binary-resume-20261016T083330Z-final-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));F.mkdir()
 ptr.write_text(json.dumps({'root':str(F.relative_to(R))},indent=2)+'\n')
assert shutil.disk_usage(F).free>=3*1024**3
origins=[]
def snap(a,b):
 b.parent.mkdir(parents=True,exist_ok=True)
 if b.exists():assert b.read_bytes()==a.read_bytes(),('SNAPSHOT_COLLISION',a,b)
 elif a.stat().st_mode&0o222:shutil.copyfile(a,b);b.chmod(0o444)
 else:os.link(a,b)
 origins.append({'source':str(a.relative_to(R)),'snapshot':str(b.relative_to(R)),'sha256':sha(a),'source_mode':oct(a.stat().st_mode&0o777),'source_inode':a.stat().st_ino})
for dep in base['dependencies']:
 for f in dep['files']:
  a=R/f['linked'];assert sha(a)==f['sha256'];snap(a,F/a.name)
for n in modules:
 a=D/(n+'.lean');b=O/(n+'.lean');assert a.read_bytes()==b.read_bytes()
 records=[json.loads(p.read_text()) for p in O.glob(n+'-*.run.json')]
 assert any(r['exit']==0 and r['failure'] is None and r['source_sha256']==sha(a) for r in records),('NO_SUCCESSFUL_SOURCE_RECEIPT',n)
 snap(a,F/a.name);snap(O/(n+'.olean'),F/(n+'.olean'))
for p in O.glob('*.run.json'):
 n=p.name.split('-')[0]
 if n not in set(modules+['ProviderFalsePrecontrols','ProviderLemmaProbe']):continue
 for a in [p,p.with_name(p.name.replace('.run.json','.log.gz')),p.with_name(p.name.replace('.run.json','.source'))]:
  assert a.exists();snap(a,F/'retained-runs'/a.name)
for p in [J/'CONTROL-PIN-v1.json',J/'RESUME-SKELETON-v1.json',J/'JOURNAL.md',D/'pilot.py',D/'instrument.py',D/'resume_finalize.py',D/'TARGET-v1.md',D/'CONTROLS-v1.md',D/'ROOT-v1.json']:
 snap(p,F/'provenance'/p.name)
(F/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
P.O=F
control_dir=F/'parser-controls';control_dir.mkdir(exist_ok=True)
def parser_fixture(tag,rows,count=None,path=None):
 Q=control_dir/tag;Q.mkdir(exist_ok=True)
 n='ProviderResumeControls';ix={'counts':[{'producer':n,'count':len(rows) if count is None else count,'path':str(path or F/(n+'.olean'))}],'rejects':[]}
 (Q/'index.json').write_text(json.dumps(ix))
 with gzip.open(Q/(n+'.json.gz'),'wt') as f:json.dump(rows,f)
 return Q
fixture=[{'producer':'ProviderResumeControls','index':0,'name':'fixture','resolved_origin':'ProviderResumeControls','kind':'definition','body':'literal-known-answer','axiom_references':[]}]
I.parse(parser_fixture('clean',fixture),['ProviderResumeControls'],F)
parser_results={'clean':'PASS'}
for tag,rows,count,path in [('missing-occurrence',fixture,2,None),('duplicate-index',fixture+fixture,None,None),('missing-body',[dict(fixture[0],body=None)],None,None),('forbidden-axiom',[dict(fixture[0],axiom_references=['forbidden'])],None,None),('foreign-path',fixture,None,R/'foreign.olean')]:
 try:I.parse(parser_fixture(tag,rows,count,path),['ProviderResumeControls'],F)
 except AssertionError:parser_results[tag]='CAUGHT'
 else:raise AssertionError('PARSER_PLANT_SURVIVED|'+tag)
print('PARSER_CONTROLS',len(parser_results),flush=True)
false_claims={
 'FalseCountProjection':'decode (countLabel C3 a [a,paddedA,[false]]).value=1',
 'FalseCountCharge':'(countLabel C3 a [a,paddedA,[false]]).work=0',
 'FalsePaddedEquality':'(copiedEqual a paddedA).value=false',
 'FalseDuplicatePartition':'(partitionFromInput [a] [[a],[paddedA]]).value=true',
 'FalseEmptyPartition':'(partitionFromInput [a] [[]]).value=true',
 'FalseRestriction':'(restrictLabels [one,three] T).value=some (.leaf one)',
 'FalseUnaryPrefix':'(minimalLabels [two,three] T).value=[[],[false],[true]]',
 'FalseSetupCharge':'(checkerCapacity (some pair) [pair] one [[one],[two]]).work=0',
 'FalseBudget':'(checkerFromInput (some pair) [pair] [] [[one],[two]]).value=some [[one],[two]]'
}
false_results=[]
for n,claim in false_claims.items():
 s='import ProviderResumeControls\nopen GenericForest.BinaryProvider GenericForest.BinaryProvider.ResumeControls GenericForest.BinaryProvider.Controls GenericForest.ScalarBits\nexample : '+claim+' := by decide +kernel\n'
 f=F/(n+'.lean')
 if f.exists():assert f.read_text()==s
 else:f.write_text(s)
 txt=P.run(n,False,1)
 assert 'is false' in txt,('WRONG_FALSE_FAILURE',n,txt[-1000:])
 false_results.append({'module':n,'claim':claim,'result':'CAUGHT_BY_KERNEL_DECIDE','source_sha256':sha(f)})
print('FALSE_CONTROLS',len(false_results),flush=True)
ghost='ProviderAuditGhost';gs='import PersistentEntry\nnamespace BinaryProviderAuditPlant\naxiom forbiddenCallback : False\ndef ghostCost : Nat := False.elim forbiddenCallback\nend BinaryProviderAuditPlant\n'
gf=F/(ghost+'.lean')
if gf.exists():assert gf.read_text()==gs
else:gf.write_text(gs)
P.run(ghost,True,0)
primitive=['BinaryCompare','BinaryAdd','BinarySubtract','BinaryEncoding','BinaryCounters','BinaryCopy','ForestGeometryWork','HullCheckMeters','CheckPrimitives']
wanted=modules+primitive
all_rows=[];audits=[]
for k in range(0,len(wanted),3):
 batch=wanted[k:k+3];stamp=str(time.time_ns());n='ProviderStoredAudit'+str(k)+'x'+stamp
 Q=F/('audit-'+str(k)+'-'+stamp);Q.mkdir()
 (F/(n+'.lean')).write_text(I.source(['ProviderResumeControls'],batch,Q))
 P.run(n,False,0)
 rows=I.parse(Q,batch,F);all_rows.extend(rows)
 audits.append({'module':n,'directory':str(Q.relative_to(R)),'producers':batch,'occurrences':len(rows),'status':'PASS_STORED_OCCURRENCES_FULL_NONPROOF_BODY_AND_ACTUAL_PROOF_AXIOMS'})
 print('AUDIT_BATCH',k,len(rows),flush=True)
stamp=str(time.time_ns());n='ProviderStoredHostile'+stamp;Q=F/('hostile-audit-'+stamp);Q.mkdir()
(F/(n+'.lean')).write_text(I.source([ghost],[ghost],Q));P.run(n,False,1)
hr=I.parse(Q,[ghost],F,hostile=True);assert any('BinaryProviderAuditPlant.forbiddenCallback' in r['axiom_references'] or r['name']=='BinaryProviderAuditPlant.forbiddenCallback' for r in hr)
rows={r['name']:r for r in all_rows};assert len(rows)==len(all_rows),'OWN_PRODUCER_OCCURRENCE_COLLISION'
runtime=[]
exclude={'labelValue','blockValue','forestValue','treeValue','sourcesValue','targetValue','leavesBits','LabelWidth','BlockWidth','ForestWidth','TreeWidth','SourcesWidth','Projects','TargetWidth','forestOptionValue'}
import re
for n in modules:
 if n.startswith('Provider'):continue
 for name in re.findall(r'^def\s+(\w+)',(D/(n+'.lean')).read_text(),re.M):
  if name not in exclude:runtime.append('GenericForest.BinaryProvider.'+name)
for name in runtime:
 assert name in rows,('MISSING_RUNTIME_BODY',name)
 assert rows[name]['kind']=='definition' and rows[name]['body'] is not None
banned={'GenericForest.ScalarBits.decode','GenericForest.ScalarBits.encode'}|{'GenericForest.BinaryProvider.'+x for x in ['labelValue','blockValue','forestValue','treeValue','sourcesValue','targetValue','forestOptionValue']}
seen=set();todo=list(runtime);unexpanded=set()
while todo:
 name=todo.pop()
 if name in seen:continue
 assert name not in banned,('NATIVE_CONVERSION_OR_PROJECTION_IN_RUNTIME_CLOSURE',name)
 seen.add(name)
 row=rows.get(name)
 if row is None:unexpanded.add(name);continue
 if row['kind']=='theorem':continue
 for v in row['references']:
  assert v not in banned,('BANNED_RUNTIME_REFERENCE',name,v)
  if v not in seen:todo.append(v)
runtime_rec={'status':'PASS_NO_ENCODE_DECODE_OR_VALUE_PROJECTION_IN_STORED_RUNTIME_CLOSURE','entry':'GenericForest.BinaryProvider.checkerFromInput','registered_runtime_definitions':runtime,'visited_names':sorted(seen),'unexpanded_boundary':sorted(unexpanded),'boundary_note':'Stored audited custom definitions and their references; standard Lean data/recursion/arithmetic primitives are boundary names. Full proof axiom closure is checked separately. No nativeIR/compiler theorem is claimed.','axiom_allowlist':sorted(I.ALLOW),'occurrences':len(all_rows)}
(F/'runtime-body-audit.json').write_text(json.dumps(runtime_rec,indent=2)+'\n')
receipt={'status':'SOURCE_CHECKER_BINDING_WITH_EXECUTED_CONTROLS','root':str(F.relative_to(R)),'source_modules':modules,'dependency_pairs':len(base['dependencies']),'positive_control_groups':8,'positive_assertions':22,'false_controls':false_results,'parser_controls':parser_results,'audits':audits,'hostile_audit':str(Q.relative_to(R)),'runtime_audit':'runtime-body-audit.json','independent_credit':0,'nativeIR':'OPEN','production_dispatch':'OPEN','whole_solver_runtime':'OPEN','main_2_33_acceptance':'OPEN','origins':origins}
(F/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
(J/'AUDIT-RESULT-v1.json').write_text(json.dumps({k:v for k,v in receipt.items() if k!='origins'},indent=2)+'\n')
print('AUDIT_COMPLETE',len(runtime),len(all_rows),'runtime definitions/occurrences;',F,flush=True)
